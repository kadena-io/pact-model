Require Import
  Coq.Arith.Arith
  Coq.ZArith.ZArith
  Coq.micromega.Lia
  Coq.Strings.String
  Hask.Control.Monad
  Data.Monoid
  Data.PartialMap
  EnsemblesExt
  Lib
  Ltac
  RWSP.

Set Universe Polymorphism.

From Equations Require Import Equations.
Set Equations With UIP.

Derive NoConfusion NoConfusionHom Subterm EqDec for Ascii.ascii.
Derive NoConfusion NoConfusionHom Subterm EqDec for string.
Derive NoConfusion NoConfusionHom Subterm EqDec for Z.
Next Obligation. now apply Z.eq_dec. Defined.
Derive NoConfusion NoConfusionHom Subterm EqDec for nat.
Derive NoConfusion NoConfusionHom Subterm EqDec for bool.

Generalizable All Variables.

(** A partial magma defines a constrained version of its binary operation.
    This operation is typically not associative, since order of operation can
    matter. *)
Class PartialMagma (A : Type) := {
  pappendLim (x y : A) : option A;
}.

Instance nat_PartialMagma (limit : nat) : PartialMagma nat := {
  pappendLim := λ (x y : nat),
    let z := x + y in
    if limit <? z
    then None
    else Some z
}.

Section Pact.

Import ListNotations.

Inductive Ty : Set :=
  | TUnit
  | TPair : Ty → Ty → Ty
  | TString
  | TInteger
  | TDecimal
  | TBool
  | TTime
  (* | TKeyset *)
  (* | TGuard *)
  | TList : Ty → Ty
  (* | TObject *)
  (* | TFunc *)
  (* | TPact *)
  (* | TTable *)
  (* | TSchema *)
.

Derive NoConfusion NoConfusionHom Subterm EqDec for Ty.

Fixpoint denoteTy (t : Ty) : Set :=
  match t with
  | TUnit     => unit
  | TPair x y => denoteTy x * denoteTy y
  | TString   => string
  | TInteger  => Z
  | TDecimal  => nat
  | TBool     => bool
  | TTime     => nat
  | TList t   => list (denoteTy t)
  end.

Declare Scope Type_scope.
Bind Scope Type_scope with Ty.
Delimit Scope Ty_scope with ty.

Notation "⟦ t ⟧" := (denoteTy t%ty) (at level 9) : type_scope.

(* This couldn't be derived due to the recursion at [VList]. *)
Equations Value_EqDec t : EqDec ⟦t⟧ :=
  Value_EqDec TUnit tt tt := left _;
  Value_EqDec (TPair t1 t2) (x1, y1) (x2, y2)
    with @eq_dec _ (Value_EqDec t1) x1 x2 := {
      | left  _ with @eq_dec _ (Value_EqDec (t2)) y1 y2 := {
        | left _  => left _
        | right _ => right _
      }
      | right _ => right _
  };
  Value_EqDec TString s1 s2
    with eq_dec s1 s2 := {
      | left _  => left _
      | right _ => right _
    };
  Value_EqDec TInteger i1 i2
    with eq_dec i1 i2 := {
      | left _  => left _
      | right _ => right _
    };
  Value_EqDec TDecimal d1 d2
    with eq_dec d1 d2 := {
      | left _  => left _
      | right _ => right _
    };
  Value_EqDec TBool b1 b2
    with eq_dec b1 b2 := {
      | left _  => left _
      | right _ => right _
    };
  Value_EqDec TTime t1 t2
    with eq_dec t1 t2 := {
      | left _  => left _
      | right _ => right _
    };
  Value_EqDec (TList _)   ([]) ([]) := left _;
  Value_EqDec (TList _)   ((_ :: _)) ([]) := right _;
  Value_EqDec (TList _)   ([]) ((_ :: _)) := right _;
  Value_EqDec (TList ty)  ((x1 :: xs1)) ((y1 :: ys1))
    with @eq_dec _ (Value_EqDec ty) x1 y1 := {
      | left _  with @eq_dec _ (list_eqdec (Value_EqDec ty)) xs1 ys1 := {
        | left _  => left _
        | right _ => right _
      }
      | right _ => right _
    }.

#[export]
Instance Value_EqDec' {t} : EqDec ⟦t⟧ := Value_EqDec t.

(******************************************************************************
 * Capability Semantics
 *)

Record CapSig : Set := {
  name : string;
  paramTy : Ty
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapSig.

Record Cap (s : CapSig) : Set := MkCap {
  param : ⟦paramTy s⟧
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for Cap.

Record MCapSig : Set := {
  baseSig : CapSig;
  valueTy : Ty
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for MCapSig.

Record MCap (s : MCapSig) : Set := MkMCap {
  base : Cap (baseSig s);
  value : ⟦valueTy s⟧
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for MCap.

Inductive ACap : Set :=
  | Unmanaged {csig : CapSig}  : Cap csig  → ACap
  | Managed   {csig : MCapSig} : MCap csig → ACap.

Derive NoConfusion NoConfusionHom Subterm EqDec for ACap.

Record PactEnv := {
  granted : Ensemble ACap;
}.

Record PactState := {
  resources : Ensemble { s : MCapSig & ⟦valueTy s⟧ };
}.

Record PactLog := MkPactLog {}.

#[export]
Program Instance PactLog_Semigroup : Semigroup PactLog := {
  mappend := λ _ _, MkPactLog
}.

#[export]
Program Instance PactLog_Monoid : Monoid PactLog := {
  mempty := MkPactLog
}.
Next Obligation.
  destruct a.
  split; intros.
Qed.
Next Obligation.
  destruct a.
  split; intros.
Qed.

Definition PactM := @RWSP PactEnv PactState PactLog.

Record DefCap `(s : CapSig) : Type := {
  predicate : Cap s → PactM (Ensemble ACap)
}.

Derive NoConfusion NoConfusionHom Subterm for DefCap.

Arguments predicate {s} _.

Record DefMCap `(s : MCapSig) : Type := {
  base_def : DefCap (baseSig s);
  manager  : ⟦valueTy s⟧ → ⟦valueTy s⟧ → PactM ⟦valueTy s⟧
}.

Derive NoConfusion NoConfusionHom Subterm for DefMCap.

Arguments manager {s} _.

Import EqNotations.

(* The functions below all take a [DefCap] because name resolution must happen
   in the parser, since capability predicates can themselves refer to the
   current module. *)

Definition install_capability `(D : DefMCap s) (c : MCap s) : PactM () :=
  let '(MkMCap _ (MkCap _ arg) val) := c in

  (* jww (2022-07-15): This should only be possible to do in specific
     contexts, otherwise a user could install as much resource as they needed.

     jww (2022-07-15): What if the resource had already been installed? *)

  (* "Installing" a capability means assigning a resource amount associated
     with that capability, that is consumed by future calls to
     [with_capability]. *)
  modify (λ st, {| resources := insert_dep s val (resources st) |}).

Definition __claim_resource `(D : DefMCap s) (c : MCap s) : PactM () :=
  let '(MkMCap _ (MkCap _ arg) val) := c in

  (* Check the current amount of resource associated with this capability, and
     whether the requested amount is available. If so, update the available
     amount. Note: unit is used to represent unmanaged capabilities. *)
  st   <- get ;
  mng  <- demand (find_dep s (resources st)) ;
  mng' <- manager D mng val ;
  put {| resources := insert_dep s mng' (resources st) |}.

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
Definition with_capability__unmanaged `(D : DefCap s) (c : Cap s)
           `(f : PactM a) : PactM a :=
  let acap := Unmanaged c in

  (* Check whether the capability has already been granted. If so, this
     operation is a no-op. *)
  env <- ask ;
  b   <- decide (acap ∈ granted env) ;
  if b : bool
  then f
  else
    let '(MkCap _ arg) := c in

    (* If the predicate passes, we are good to grant the capability. Note that
       the predicate may return a list of other capabilities to be "composed"
       with this one. *)
    compCaps <- predicate D c ;

    (* The process of "granting" consists merely of making the capability
       visible in the reader environment to the provided expression. *)
    local (λ r, {| granted := Add _ (compCaps ∪ granted r) acap |}) f.

Definition with_capability__managed `(D : DefMCap s) (c : MCap s)
           `(f : PactM a) : PactM a :=
  let acap := Managed c in

  (* Check whether the capability has already been granted. If so, this
     operation is a no-op. *)
  env <- ask ;
  b   <- decide (acap ∈ granted env) ;
  if b : bool
  then f
  else
    let '(MkMCap _ (MkCap _ arg) val) := c in

    (* If the predicate passes, we are good to grant the capability. Note that
       the predicate may return a list of other capabilities to be "composed"
       with this one. *)
    (* jww (2022-07-18): Can the predicate for a managed capability also see
       the value passed to [with-capability]? *)
    compCaps <- predicate (base_def s D) (base _ c) ;

    __c

    (* The process of "granting" consists merely of making the capability
       visible in the reader environment to the provided expression. *)
    local (λ r, {|  granted := Add _ (compCaps ∪ granted r) acap |}) f.

Definition require_capability (c : ACap) : PactM () :=
  (* Note that the request resource amount must match the original
     with-capability exactly.

     jww (2022-07-15): Is this intended? *)

  (* Requiring a capability means checking whether it has been granted at any
     point within the current scope of evaluation. *)
  env <- ask ;
  require (c ∈ granted env).

End Pact.
