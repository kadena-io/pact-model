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

Inductive Value : Ty → Type :=
  | VUnit       : Value TUnit
  | VPair {a b} : Value a → Value b → Value (TPair a b)
  | VString     : string → Value TString
  | VInteger    : Z → Value TInteger
  | VDecimal    : nat → Value TDecimal
  | VBool       : bool → Value TBool
  | VTime       : nat → Value TTime
  | VList {ty}  : list (Value ty) → Value (TList ty).

Derive Signature NoConfusion NoConfusionHom Subterm for Value.

(* This couldn't be derived due to the recursion at [VList]. *)
Equations Value_EqDec {t} : EqDec (Value t) :=
  Value_EqDec (t:=TUnit)       VUnit         VUnit         := left _;
  Value_EqDec (t:=TPair t1 t2) (VPair x1 y1) (VPair x2 y2)
    with @eq_dec _ (Value_EqDec (t:=t1)) x1 x2 := {
      | left  _ with @eq_dec _ (Value_EqDec (t:=t2)) y1 y2 := {
        | left _  => left _
        | right _ => right _
      }
      | right _ => right _
  };
  Value_EqDec (t:=TString) (VString s1) (VString s2)
    with eq_dec s1 s2 := {
      | left _  => left _
      | right _ => right _
    };
  Value_EqDec (t:=TInteger) (VInteger i1) (VInteger i2)
    with eq_dec i1 i2 := {
      | left _  => left _
      | right _ => right _
    };
  Value_EqDec (t:=TDecimal) (VDecimal d1) (VDecimal d2)
    with eq_dec d1 d2 := {
      | left _  => left _
      | right _ => right _
    };
  Value_EqDec (t:=TBool) (VBool b1) (VBool b2)
    with eq_dec b1 b2 := {
      | left _  => left _
      | right _ => right _
    };
  Value_EqDec (t:=TTime) (VTime t1) (VTime t2)
    with eq_dec t1 t2 := {
      | left _  => left _
      | right _ => right _
    };
  Value_EqDec (t:=TList _)   (VList []) (VList []) := left _;
  Value_EqDec (t:=TList _)   (VList (_ :: _)) (VList []) := right _;
  Value_EqDec (t:=TList _)   (VList []) (VList (_ :: _)) := right _;
  Value_EqDec (t:=TList ty)  (VList (x1 :: xs1)) (VList (y1 :: ys1))
    with @eq_dec _ (Value_EqDec (t:=ty)) x1 y1 := {
      | left _  with @eq_dec _ (list_eqdec (Value_EqDec (t:=ty))) xs1 ys1 := {
        | left _  => left _
        | right _ => right _
      }
      | right _ => right _
    }.

#[export]
Instance Value_EqDec' {t} : EqDec (Value t) := Value_EqDec (t:=t).

Record CapSig (n : string) : Set := {
  paramTy : Ty;               (* this could be a product (i.e. pair) *)
  valueTy : Ty                (* is TUnit for unmanaged caps *)
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapSig.

Arguments paramTy {n} _.
Arguments valueTy {n} _.

Inductive Cap `(S : CapSig n) : Set :=
  | Token : Value (paramTy S) → Value (valueTy S) → Cap S.

Derive NoConfusion NoConfusionHom Subterm for Cap.

Arguments Token {n S} _.

(* jww (2022-07-15): This couldn't be derived due to an anomaly. *)
#[export]
Program Instance Cap_EqDec `(S : CapSig n) : EqDec (Cap S).
Next Obligation.
  destruct x, y, S; simpl in *.
  destruct (@eq_dec _ (Value_EqDec (t:=paramTy0)) v v1); subst.
  - destruct (@eq_dec _ (Value_EqDec (t:=valueTy0)) v0 v2); subst.
    + now left.
    + right; congruence.
  - right; congruence.
Defined.

Record ACap : Set := {
  name : string;
  sig  : CapSig name;
  cap  : Cap sig
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for ACap.

Inductive CapError : Set :=
  | CapErr_UnknownCapability      : string → CapError
  | CapErr_InvalidParameter {t}   : Value t → CapError
  | CapErr_InvalidValue {t}       : Value t → CapError
  | CapErr_CapabilityNotAvailable : ACap → CapError
  | CapErr_ManagedError           : string → CapError
  | CapErr_NoResourceAvailable    : ACap → CapError
  | CapErr_TypeError.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapError.

Inductive Err : Type :=
  | Err_Capability : CapError → Err.

Derive NoConfusion NoConfusionHom Subterm EqDec for Err.

Record PactEnv := {
  (* We cannot refer to capability tokens by their type here, because
     capability predicates execute in a state monad that reference this
     record type. *)
  granted : list ACap
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactEnv.

Record PactState := {
  (* We cannot refer to capability tokens by their type here, because
     capability predicates execute in a state monad that reference this
     record type. *)
  resources : ∀ c : ACap, option (Value (valueTy (sig c)))
}.

Derive NoConfusion NoConfusionHom Subterm for PactState.

Record PactLog := {}.

Derive NoConfusion NoConfusionHom EqDec for PactLog.

Definition PactM := @RWSE PactEnv PactState PactLog Err.

(******************************************************************************
 * Capabilities
 *)

Record DefCap `(C : ACap) : Type := {
  predicate : Value (paramTy (sig C)) → PactM (list ACap);
  manager   : Value (valueTy (sig C)) → Value (valueTy (sig C)) →
              PactM (Value (valueTy (sig C)))
}.

Derive NoConfusion NoConfusionHom Subterm for DefCap.

Arguments predicate {C} _.
Arguments manager {C} _.

Import EqNotations.

Program Definition install_capability `(D : DefCap C) : PactM () :=
  let '(Token arg val) := cap C in

  (* jww (2022-07-15): This should only be possible to do in specific
     contexts, otherwise a user could install as much resource as they needed.

     jww (2022-07-15): What if the resource had already been installed? *)
  modify (λ st, {| resources := λ c : ACap,
                      match eq_dec c C with
                      | left H  => Some val
                      | right _ => resources st c
                      end |}).

Definition with_capability `(D : DefCap C) `(f : PactM a) : PactM a :=
  env <- ask ;
  if in_dec eq_dec C (granted env)
  then f
  else
    let '(Token arg val) := cap C in

    compCaps <- predicate D arg ;

    st <- get ;
    match valueTy (sig C), resources st C with
    | TUnit, _    => pure ()
    | _, None     => throw (Err_Capability (CapErr_NoResourceAvailable C))
    | _, Some mng =>
      mng' <- manager D mng val ;
      put {| resources := λ c : ACap,
                match eq_dec c C with
                | left H  => Some (rew <- H in mng')
                | right _ => resources st c
                end |}
    end ;;

    local (λ r, {| granted := C :: compCaps ++ granted r |}) f.

Definition require_capability `(D : DefCap C) : PactM () :=
  let '(Token arg val) := cap C in

  (* Note that the request resource amount must match the original
     with-capability exactly.

     jww (2022-07-15): Is this intended? *)
  env <- ask ;
  if in_dec eq_dec C (granted env)
  then pure ()
  else throw (Err_Capability (CapErr_CapabilityNotAvailable C)).

End Pact.
