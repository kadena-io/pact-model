Require Import
  Hask.Control.Monad
  Hask.Control.Monad.Trans.State
  Pact.Data.Either
  Pact.Data.Monoid
  Pact.Lib
  Pact.Value
  Pact.SemTy
  Pact.Lang
  Pact.Lang.CapabilityType
  Hask.Control.Lens.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Open Scope Ty_scope.

(******************************************************************************
 * Capabilities
 *)

Import EqNotations.

Definition get_cap `(c : Cap s) (l : list ACap) :
  option (reflectTy (valueTy s)) :=
  let '(Token n arg _) := c in
  let fix go (l : list ACap) : option (reflectTy (valueTy s)) :=
    match l with
    | [] => None
    | @AToken s' (Token n' arg' val') :: xs =>
        match eq_dec s s' with
        | left Hs =>
            match eq_dec n n' with
            | left _ =>
                match eq_dec arg
                  (rew <- [λ x, reflectTy (paramTy x)] Hs in arg') with
                | left _ =>
                    Some (rew <- [λ x, reflectTy (valueTy x)] Hs in val')
                | _ => go xs
                end
            | _ => go xs
            end
        | _ => go xs
        end
    end
  in go l.

Definition set_cap `(c : Cap s) (l : list ACap) : list ACap :=
  let '(Token n arg _) := c in
  let fix go (l : list ACap) : list ACap :=
    match l with
    | [] => [AToken c]
    | x :: xs =>
        let '(@AToken s' (Token n' arg' _)) := x in
        match eq_dec s s' with
        | left Hs =>
            match eq_dec n n' with
            | left _ =>
                match eq_dec arg
                  (rew <- [λ x, reflectTy (paramTy x)] Hs in arg') with
                | left _ => AToken c :: go xs
                | _ => x :: go xs
                end
            | _ => x :: go xs
            end
        | _ => x :: go xs
        end
    end
  in go l.

Lemma get_set_cap `(c : Cap s) (l : list ACap) :
  get_cap c (set_cap c l) = Some (valueOf c).
Proof.
  unfold get_cap, set_cap.
  induction l, c; simpl.
  - now rewrite !eq_dec_refl.
  - destruct a, c; simpl.
    repeat destruct (eq_dec _ _); subst.
    all: rewrite ?IHl //.
    all: unfold eq_rect_r, eq_rect, eq_sym in *.
    all: dependent destruction e2.
    + reflexivity.
    + dependent destruction e1.
      contradiction.
Qed.

Definition __in_defcap (env : PactState) : bool :=
  in_dec EvalContext_EqDec InWithCapability (env ^_ context).

Definition __in_module (name : string) (env : PactState) : bool :=
  in_dec EvalContext_EqDec (InModule name) (env ^_ context).

(* The functions below all take [predicate] and [manager] functions because
   name resolution must happen in the parser, since capability predicates can
   themselves refer to the current module. *)

(* "Installing" a capability assigns a resource amount associated with that
   capability, to be consumed by future calls to [with-capability].

   Note that a capability can be installed either by the user calling
   [install-capability] directly, or by the chain calling this function if it
   sees a signed capability as part of a transaction. *)
Definition install_capability `(c : Cap s) : PactM unit :=
  env <- getT ;
  if __in_defcap env
  then
    throw (Err_Capability c CapErr_CannotInstallInDefcap)
  else
    rs <- getsT (view resources) ;
    match get_cap c rs with
    | None   => modifyT (over resources (set_cap c))
    | Some _ => pure tt
    end.

Definition __claim_resource `(c : Cap s)
  (manager : reflectTy (valueTy s) * reflectTy (valueTy s) →
             PactM (reflectTy (valueTy s))) : PactM unit :=
  (* Check the current amount of resource associated with this capability, and
     whether the requested amount is available. If so, update the available
     amount. Note: unit is used to represent unmanaged capabilities. *)
  if eq_dec (valueTy s) TUnit
  then
    pure tt                     (* unit is always available *)
  else
    rs <- getsT (view resources) ;
    match get_cap c rs with
    | None =>
        throw (Err_Capability c CapErr_NoResourceAvailable)

    | Some amt =>
        let '(Token n p req) := c in
        amt' <- manager (amt, req) ;
        modifyT (over resources (set_cap (Token n p amt')))
    end.

Definition __check_capability `(c : Cap s)
  `(predicate : Cap s → PactM unit)
  (manager : reflectTy (TPair (valueTy s) (valueTy s)) →
             PactM (reflectTy (valueTy s))) : PactM unit :=
  localize context (cons InWithCapability)
    ( predicate c ;;
      __claim_resource c manager
    ).

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
Definition with_capability (module : string) `(c : Cap s)
  `(predicate : Cap s → PactM unit)
  (manager : reflectTy (TPair (valueTy s) (valueTy s)) →
             PactM (reflectTy (valueTy s)))
  `(f : PactM a) : PactM a :=
  (* Check whether the capability has already been granted. If so, this
     operation is a no-op. *)
  env <- getT ;
  if get_cap c (env ^_ granted)
  then
    f
  else
    if __in_defcap env
    then
      throw (Err_Capability c CapErr_CannotWithInDefcap)
    else
      if __in_module module env
      then
        (* If the predicate passes, we are good to grant the capability. Note that
           the predicate may return a list of other capabilities to be "composed"
           with this one.

           Note that if the resource type is unit, the only thing this function
           could do is throw an exception. But since this is semantically
           equivalent to throwing the same exception at the end of the predicate,
           there is no reason to avoid this invocation in that case. *)
        __check_capability c predicate manager ;;

        composed <- exchange to_compose [] ;

        (* The process of "granting" consists merely of making the capability
           visible in the reader environment to the provided expression. *)
        localize granted (app (AToken c :: composed))
          f
      else
        throw (Err_Capability c CapErr_CannotWithOutsideDefcapModule).

Definition compose_capability (module : string) `(c : Cap s)
  `(predicate : Cap s → PactM unit)
  (manager : reflectTy (TPair (valueTy s) (valueTy s)) →
             PactM (reflectTy (valueTy s))) : PactM unit :=
  (* Check whether the capability has already been granted. If so, this
     operation is a no-op. *)
  env <- getT ;
  if get_cap c (env ^_ granted)
  then
    pure tt
  else
    if __in_defcap env
    then
      if __in_module module env
      then
        __check_capability c predicate manager ;;

        modifyT (over to_compose (cons (AToken c)))
      else
        throw (Err_Capability c CapErr_CannotComposeOutsideDefcapModule)
    else
      throw (Err_Capability c CapErr_CannotComposeOutsideDefcap).

Definition require_capability `(c : Cap s) : PactM unit :=
  (* Note that the request resource amount must match the original
     [with-capability] exactly.

     Requiring a capability means checking whether it has been granted at any
     point within the current scope of evaluation. *)
  env <- getT ;
  if get_cap c (env ^_ granted)
  then
    pure tt
  else
    throw (Err_Capability c CapErr_CapabilityNotAvailable).
