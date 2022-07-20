Require Import
  Coq.Arith.Arith
  Coq.ZArith.ZArith
  Coq.micromega.Lia
  Coq.Strings.String
  Hask.Control.Monad
  Data.Monoid
  Lib
  Ty
  Exp
  Value
  SemTy
  Pact.

(* Set Universe Polymorphism. *)

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Capability.

Import ListNotations.

Open Scope Ty_scope.

(******************************************************************************
 * Capabilities
 *)

Import EqNotations.

Definition get_value `(c : Cap s) (l : list { s : CapSig & Cap s }) :
  option (Value (valueTy s)) :=
  let '(Token n arg _) := c in
  let fix go (l : list { s : CapSig & Cap s }) :
    option (Value (valueTy s)) :=
    match l with
    | [] => None
    | existT _ s' (Token n' arg' val') :: xs =>
        match eq_dec s s' with
        | left Hs =>
            match eq_dec n n' with
            | left _ =>
                match eq_dec arg
                        (rew <- [λ x, Value (paramTy x)] Hs in arg') with
                | left _ =>
                    Some (rew <- [λ x, Value (valueTy x)] Hs in val')
                | _ => go xs
                end
            | _ => go xs
            end
        | _ => go xs
        end
    end
  in go l.

Definition set_value `(c : Cap s) (l : list { s : CapSig & Cap s }) :
  list { s : CapSig & Cap s } :=
  let '(Token n arg _) := c in
  let fix go (l : list { s : CapSig & Cap s }) :
    list { s : CapSig & Cap s } :=
    match l with
    | [] => []
    | existT _ s' (Token n' arg' _) :: xs =>
        match eq_dec s s' with
        | left Hs =>
            match eq_dec n n' with
            | left _ =>
                match eq_dec arg
                        (rew <- [λ x, Value (paramTy x)] Hs in arg') with
                | left _ => existT _ s c :: go xs
                | _ => go xs
                end
            | _ => go xs
            end
        | _ => go xs
        end
    end
  in go l.

(* The functions below all take a [DefCap] because name resolution must happen
   in the parser, since capability predicates can themselves refer to the
   current module. *)

(* "Installing" a capability assigns a resource amount associated with that
   capability, to be consumed by future calls to [with-capability].

   Note that a capability can be installed either by the user calling
   [install-capability] directly, or by the chain calling this function if it
   sees a signed capability as part of a transaction. *)
Definition install_capability `(c : Cap s) : PactM () :=
  env <- ask ;
  if in_dec EvalContext_EqDec InWithCapability (context env)
  then
    throw (Err_Capability c CapErr_CannotInstallDuringWith)
  else
    modify (λ st, {| resources := set_value c (resources st) |}).

Definition __claim_resource `(c : Cap s)
           (manager : Value (TPair (valueTy s) (valueTy s)) →
                      PactM (Value (valueTy s))) : PactM () :=
  (* Check the current amount of resource associated with this capability, and
     whether the requested amount is available. If so, update the available
     amount. Note: unit is used to represent unmanaged capabilities. *)
  if eq_dec (valueTy s) TUnit
  then
    pure ()  (* unit is always available *)
  else
    st <- get ;
    match get_value c (resources st) with
    | None => throw (Err_Capability c CapErr_NoResourceAvailable)
    | Some amt =>
      let '(Token n p req) := c in
      amt' <- manager (VPair amt req) ;
      put {| resources := set_value (Token n p amt') (resources st) |}
    end.

(** [with_capability] grants a capability [C] to the evaluation of [f].

    There are three results of this operation:

    1. a predicate is evaluated to determine if the operation can proceed,
       which raises an exception if not;

    2. [f] is able to evaluate more permissively;

    3. a resource is consumed in order to grant the capability.

    (2) is easily modeled by imagining that [with_capability] introduces a
    dynamic boolean variable (in the Lisp sense) for each capability [C] and
    sets it to true for the scope of evaluating [f], if the predicate in (1)
    succeeds. Later, [require_capability] tests if this boolean is true and
    raises an exception otherwise. There is no other functionality for
    unmanaged capabilities.

    A managed capability provides the same, but in addition deducts from a
    stateful resource after the predicate, but before defining and setting the
    dynamic boolean. If there is not enough resource available, it raises an
    exception. [install_capability] sets the initial amount of the
    resource. *)
Definition with_capability `(c : Cap s)
           `(predicate : Cap s → PactM (list ACap))
           (manager : Value (TPair (valueTy s) (valueTy s)) →
                      PactM (Value (valueTy s)))
           `(f : PactM a) : PactM a :=
  (* Check whether the capability has already been granted. If so, this
     operation is a no-op. *)
  env <- ask ;
  if get_value c (granted env)
  then
    f
  else
    (* jww (2022-07-19): This can only be executed within the module that
       declares the capability. *)

    (* If the predicate passes, we are good to grant the capability. Note that
       the predicate may return a list of other capabilities to be "composed"
       with this one. *)
    compCaps <-
      local (λ r, {| granted := granted r
                   ; context := InWithCapability :: context r |})
        (predicate c) ;

    (* Note that if the resource type is unit, the only thing this function
       could do is throw an exception. But since this is semantically
       equivalent to throwing the same exception at the end of the predicate,
       there is no reason to avoid this invocation in that case. *)
    local (λ r, {| granted := granted r
                 ; context := InWithCapability :: context r |})
      (__claim_resource c manager) ;;

    (* The process of "granting" consists merely of making the capability
       visible in the reader environment to the provided expression. *)
    local (λ r, {| granted := existT _ _ c :: map ACap_ext compCaps ++ granted r
                 ; context := context r |}) f.

Definition require_capability `(c : Cap s) : PactM () :=
  (* Note that the request resource amount must match the original
     [with-capability] exactly.

     Requiring a capability means checking whether it has been granted at any
     point within the current scope of evaluation. *)
  env <- ask ;
  if get_value c (granted env)
  then
    pure ()
  else
    throw (Err_Capability c CapErr_CapabilityNotAvailable).

End Capability.
