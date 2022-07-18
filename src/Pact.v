Require Import
  Coq.Arith.Arith
  Coq.ZArith.ZArith
  Coq.micromega.Lia
  Coq.Strings.String
  Hask.Control.Monad
  Hask.Data.Monoid
  ilist
  Lib
  Ltac
  RWSE.

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

Declare Scope Ty_scope.
Bind Scope Ty_scope with Ty.
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
 * The Pact environment
 *)

Record CapSig : Set := {
  name : string;
  paramTy : Ty;               (* this could be a product (i.e. pair) *)
  valueTy : Ty                (* TUnit for unmanaged caps *)
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapSig.

Inductive Cap `(S : CapSig) : Set :=
  | Token : ⟦paramTy S⟧ → ⟦valueTy S⟧ → Cap S.

Derive NoConfusion NoConfusionHom Subterm for Cap.

Arguments Token {S} _.

(* jww (2022-07-15): This couldn't be derived due to an anomaly. *)
#[export]
Program Instance Cap_EqDec `(S : CapSig) : EqDec (Cap S).
Next Obligation.
  destruct x, y, S; simpl in *.
  destruct (@eq_dec _ (Value_EqDec (paramTy0)) d d1); subst;
  destruct (@eq_dec _ (Value_EqDec (valueTy0)) d0 d2); subst;
  try (right; congruence).
  now left.
Defined.

Inductive CapError : Set :=
  | CapErr_UnknownCapability          : string → CapError
  | CapErr_InvalidParameter {t}       : ⟦t⟧ → CapError
  | CapErr_InvalidValue {t}           : ⟦t⟧ → CapError
  | CapErr_CapabilityNotAvailable {s} : Cap s → CapError
  | CapErr_ManagedError               : string → CapError
  | CapErr_NoResourceAvailable {s}    : Cap s → CapError
  | CapErr_TypeError.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapError.

Inductive Err : Type :=
  | Err_Capability : CapError → Err.

Derive NoConfusion NoConfusionHom Subterm EqDec for Err.

Record PactEnv := {
  (* We cannot refer to capability tokens by their type here, because
     capability predicates execute in a state monad that reference this
     record type. *)
  granted : list { s : CapSig & Cap s }
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactEnv.

Record PactState := {
  (* We cannot refer to capability tokens by their type here, because
     capability predicates execute in a state monad that reference this
     record type. *)
  resources : list { s : CapSig & ⟦valueTy s⟧ }
}.

Derive NoConfusion NoConfusionHom Subterm for PactState.

Record PactLog := {}.

Derive NoConfusion NoConfusionHom EqDec for PactLog.

Definition PactM := @RWSE PactEnv PactState PactLog Err.

(******************************************************************************
 * Capabilities
 *)

Record DefCap `(s : CapSig) : Type := {
  predicate : ⟦paramTy s⟧ → ⟦valueTy s⟧ → PactM (list { s : CapSig & Cap s});
  manager   : ⟦valueTy s⟧ → ⟦valueTy s⟧ → PactM ⟦valueTy s⟧
}.

Derive NoConfusion NoConfusionHom Subterm for DefCap.

Arguments predicate {s} _.
Arguments manager {s} _.

Import EqNotations.

Fixpoint is_member `{EqDec a} {B : a → Type} (k : a)
         (l : list { k : a & B k }) : bool :=
  match l with
  | [] => false
  | existT _ k' _ :: xs =>
      match eq_dec k k' with
      | left H  => true
      | right _ => is_member k xs
      end
  end.

Program Fixpoint get_value `{EqDec a} {B : a → Type} (k : a)
        (l : list { k : a & B k }) : option (B k) :=
  match l with
  | [] => None
  | existT _ k' x' :: xs =>
      match eq_dec k k' with
      | left H  => Some x'
      | right _ => get_value k xs
      end
  end.

Fixpoint set_value `{EqDec a} {B : a → Type} (k : a) (x : B k)
         (l : list { k : a & B k }) : list { k : a & B k } :=
  match l with
  | [] => [existT _ k x]
  | existT _ k' x' :: xs =>
      match eq_dec k k' with
      | left _  => existT _ k x :: xs
      | right _ => existT _ k' x' :: set_value k x xs
      end
  end.

Program Fixpoint has_value `{EqDec a} {B : a → Type} (k : a)
        `{EqDec (B k)} (x : B k) (l : list { k : a & B k }) : bool :=
  match l with
  | [] => false
  | existT _ k' x' :: xs =>
      match eq_dec k k' with
      | left _  =>
          match eq_dec x x' with
          | left _  => true
          | right _ => has_value k x xs
          end
      | right _ => has_value k x xs
      end
  end.

(* The functions below all take a [DefCap] because name resolution must happen
   in the parser, since capability predicates can themselves refer to the
   current module. *)

Definition install_capability `(D : DefCap s) (c : Cap s) : PactM () :=
  let '(Token arg val) := c in

  (* jww (2022-07-15): This should only be possible to do in specific
     contexts, otherwise a user could install as much resource as they needed.

     jww (2022-07-15): What if the resource had already been installed? *)

  (* "Installing" a capability means assigning a resource amount associated
     with that capability, that is consumed by future calls to
     [with_capability]. *)
  modify (λ st, {| resources := set_value s val (resources st) |}).

Definition __claim_resource `(D : DefCap s) (c : Cap s) : PactM () :=
  let '(Token arg val) := c in

  (* Check the current amount of resource associated with this capability, and
     whether the requested amount is available. If so, update the available
     amount. Note: unit is used to represent unmanaged capabilities. *)
  st <- get ;
  match valueTy s, get_value s (resources st) with
  | TUnit, _    => pure ()
  | _, None     => throw (Err_Capability (CapErr_NoResourceAvailable c))
  | _, Some mng =>
    mng' <- manager D mng val ;
    put {| resources := set_value s mng' (resources st) |}
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
  if has_value s c (granted env)
  then f
  else
    let '(Token arg val) := c in

    (* If the predicate passes, we are good to grant the capability. Note that
       the predicate may return a list of other capabilities to be "composed"
       with this one. *)
    compCaps <- predicate D arg val ;

    __claim_resource D c ;;

    (* The process of "granting" consists merely of making the capability
       visible in the reader environment to the provided expression. *)
    local (λ r, {| granted := set_value s c (compCaps ++ granted r) |}) f.

Definition require_capability `(D : DefCap s) (c : Cap s) : PactM () :=
  let '(Token arg val) := c in

  (* Note that the request resource amount must match the original
     with-capability exactly.

     jww (2022-07-15): Is this intended? *)

  (* Requiring a capability means checking whether it has been granted at any
     point within the current scope of evaluation. *)
  env <- ask ;
  if has_value s c (granted env)
  then pure ()
  else throw (Err_Capability (CapErr_CapabilityNotAvailable c)).

End Pact.
