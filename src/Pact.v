Require Import
  Coq.Arith.Arith
  Coq.ZArith.ZArith
  Coq.micromega.Lia
  Coq.Strings.String
  Hask.Control.Monad
  Data.Monoid
  Lib
  Ltac
  Ty
  Exp
  Value
  Sem
  RWSE.

Set Universe Polymorphism.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Pact.

Import ListNotations.

Open Scope Ty_scope.

Notation "⟦ t ⟧" := (SemTy t) (at level 9) : type_scope.

(* This couldn't be derived due to the recursion at [VList]. *)
Equations Decidable_EqDec (t : Ty) (H : DecidableP t) : EqDec ⟦t⟧ :=
  Decidable_EqDec (TyPrim PrimUnit) _ tt tt := left _;
  Decidable_EqDec (TyPair t1 t2) (PairDecP H1 H2) (x1, y1) (x2, y2)
    with @eq_dec _ (Decidable_EqDec t1 H1) x1 x2 := {
      | left  _ with @eq_dec _ (Decidable_EqDec t2 H2) y1 y2 := {
        | left _  => left _
        | right _ => right _
      }
      | right _ => right _
  };
  Decidable_EqDec (TyPrim PrimString) _ s1 s2
    with eq_dec s1 s2 := {
      | left _  => left _
      | right _ => right _
    };
  Decidable_EqDec (TyPrim PrimInteger) _ i1 i2
    with eq_dec i1 i2 := {
      | left _  => left _
      | right _ => right _
    };
  Decidable_EqDec (TyPrim PrimDecimal) _ d1 d2
    with eq_dec d1 d2 := {
      | left _  => left _
      | right _ => right _
    };
  Decidable_EqDec (TyPrim PrimBool) _ b1 b2
    with eq_dec b1 b2 := {
      | left _  => left _
      | right _ => right _
    };
  Decidable_EqDec (TyPrim PrimTime) _ t1 t2
    with eq_dec t1 t2 := {
      | left _  => left _
      | right _ => right _
    };
  Decidable_EqDec (TyList _)  _ ([]) ([]) := left _;
  Decidable_EqDec (TyList _)  _ (_ :: _) ([]) := right _;
  Decidable_EqDec (TyList _)  _ ([]) (_ :: _) := right _;
  Decidable_EqDec (TyList ty) (ListDecP H) (x1 :: xs1) (y1 :: ys1)
    with @eq_dec _ (Decidable_EqDec ty H) x1 y1 := {
      | left _
        with @eq_dec _ (list_eqdec (Decidable_EqDec ty H)) xs1 ys1 := {
        | left _  => left _
        | right _ => right _
      }
      | right _ => right _
    }.

#[export]
Instance Decidable_EqDec' {t} : DecidableP t → EqDec ⟦t⟧ :=
  Decidable_EqDec t.

Inductive Value {t} (D : DecidableP t) : Set :=
  | Bundle : ⟦t⟧ → Value D.

Derive NoConfusion NoConfusionHom Subterm for Value.

#[export]
Program Instance Value_EqDec {t} (D : DecidableP t) : EqDec (Value D).
Next Obligation.
  destruct x, y.
  destruct (@eq_dec _ (Decidable_EqDec _ D) s s0); subst;
  try (right; intro; inv H; contradiction);
  now left.
Defined.

(******************************************************************************
 * The Pact environment
 *)

(* (defcap TRANSFER (from:string to:string amount:decimal)
      @managed amount TRANSFER_mgr
      ...)

   name    = "TRANSFER"
   paramTy = (string × string)
   valueTy = decimal
*)

Record CapSig : Set := {
  name       : string;
  paramTy    : Ty;              (* this could be a product (i.e. pair) *)
  paramTyDec : DecidableP paramTy;
  valueTy    : Ty;              (* TUnit for unmanaged caps *)
  valueTyDec : DecidableP valueTy;
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapSig.

Inductive Cap `(s : CapSig) : Set :=
  | Token : Value (paramTyDec s) → Value (valueTyDec s) → Cap s.

Derive NoConfusion NoConfusionHom Subterm EqDec for Cap.

Arguments Token {s} _.

Definition paramOf `(c : Cap s) : Value (paramTyDec s) :=
  match c with Token p _ => p end.

Definition valueOf `(c : Cap s) : Value (valueTyDec s) :=
  match c with Token _ v => v end.

Inductive CapError : Set :=
  | CapErr_CapabilityNotAvailable
  | CapErr_NoResourceAvailable
  | CapErr_CannotInstallDuringWith.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapError.

Inductive Err : Set :=
  | Err_Capability {s} : Cap s → CapError → Err.

Derive NoConfusion NoConfusionHom Subterm EqDec for Err.

Inductive EvalContext : Set :=
  | RegularEvaluation
  | InWithCapability.

Derive NoConfusion NoConfusionHom Subterm EqDec for EvalContext.

Record PactEnv : Set := {
  (* We cannot refer to capability tokens by their type here, because
     capability predicates execute in a state monad that reference this
     record type. *)
  granted : list { s : CapSig & Cap s };
  context : list EvalContext;
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactEnv.

Record PactState : Set := {
  (* We cannot refer to capability tokens by their type here, because
     capability predicates execute in a state monad that reference this
     record type. *)
  resources : list { s : CapSig & Cap s }
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactState.

Record PactLog : Set := {}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactLog.

Definition PactM : Set → Set := @RWSE PactEnv PactState PactLog Err.

(******************************************************************************
 * Capabilities
 *)

Record DefCap `(s : CapSig) : Set := {
  predicate : Cap s → PactM (list { s : CapSig & Cap s});
  manager   : Value (valueTyDec s) → Value (valueTyDec s) →
              PactM (Value (valueTyDec s))
}.

Derive NoConfusion NoConfusionHom Subterm for DefCap.

Arguments predicate {s} _.
Arguments manager {s} _.

Import EqNotations.

Definition get_value `(c : Cap s)
           (l : list { k : CapSig & Cap k }) :
  option (Value (valueTyDec s)) :=
  let '(Token p _) := c in
  let fix go (l : list {k : CapSig & Cap k}) :
    option (Value (valueTyDec s)) :=
    match l with
    | [] => None
    | existT _ s' (Token p' x') :: xs =>
        match eq_dec s s' with
        | left  Hs =>
            match eq_dec p (rew <- [λ x, Value (paramTyDec x)] Hs in p') with
            | left _ => Some (rew <- [λ x, Value (valueTyDec x)] Hs in x')
            | _ => go xs
            end
        | _ => go xs
        end
    end
  in go l.

Definition set_value `(c : Cap s)
           (l : list { k : CapSig & Cap k }) :
  list { k : CapSig & Cap k } :=
  let '(Token p _) := c in
  let fix go (l : list {k : CapSig & Cap k}) :
    list { k : CapSig & Cap k } :=
    match l with
    | [] => []
    | existT _ s' (Token p' _) :: xs =>
        match eq_dec s s' with
        | left  Hs =>
            match eq_dec p (rew <- [λ x, Value (paramTyDec x)] Hs in p') with
            | left _ => existT _ s c :: go xs
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
Definition install_capability `(D : DefCap s) (c : Cap s) : PactM () :=
  env <- ask ;
  if in_dec EvalContext_EqDec InWithCapability (context env)
  then
    throw (Err_Capability c CapErr_CannotInstallDuringWith)
  else
    modify (λ st, {| resources := set_value c (resources st) |}).

Definition __claim_resource `(D : DefCap s) (c : Cap s) : PactM () :=
  (* Check the current amount of resource associated with this capability, and
     whether the requested amount is available. If so, update the available
     amount. Note: unit is used to represent unmanaged capabilities. *)
  if eq_dec (valueTy s) (TyPrim PrimUnit)
  then
    pure ()  (* unit is always available *)
  else
    st <- get ;
    match get_value c (resources st) with
    | None => throw (Err_Capability c CapErr_NoResourceAvailable)
    | Some amt =>
      let '(Token p req) := c in
      amt' <- manager D amt req ;
      put {| resources := set_value (Token p amt') (resources st) |}
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
Definition with_capability `(D : DefCap s) (c : Cap s)
           `(f : PactM a) : PactM a :=
  (* Check whether the capability has already been granted. If so, this
     operation is a no-op. *)
  env <- ask ;
  if get_value c (granted env)
  then
    f
  else
    (* If the predicate passes, we are good to grant the capability. Note that
       the predicate may return a list of other capabilities to be "composed"
       with this one. *)
    compCaps <-
      local (λ r, {| granted := granted r
                   ; context := InWithCapability :: context r |})
        (predicate D c) ;

    (* Note that if the resource type is unit, the only thing this function
       could do is throw an exception. But since this is semantically
       equivalent to throwing the same exception at the end of the predicate,
       there is no reason to avoid this invocation in that case. *)
    local (λ r, {| granted := granted r
                 ; context := InWithCapability :: context r |})
      (__claim_resource D c) ;;

    (* The process of "granting" consists merely of making the capability
       visible in the reader environment to the provided expression. *)
    local (λ r, {| granted := existT _ _ c :: compCaps ++ granted r
                 ; context := context r |}) f.

Definition require_capability `(D : DefCap s) (c : Cap s) : PactM () :=
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

End Pact.
