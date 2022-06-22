Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.micromega.Lia
  Coq.Classes.Morphisms
  Coq.Relations.Relation_Definitions
  Coq.Strings.String
  Coq.Vectors.Vector
  Coq.Lists.List
  Coq.Sets.Ensembles
  EnsemblesExt
  Group.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(************************************************************************
 * The Pact language *)

Section Pact.

Inductive Ty : Set :=
  | TUnit
  | TInt
  | TString
  | TPair : Ty →  Ty → Ty.

Inductive Value : Ty → Set :=
  | VUnit     : Value TUnit
  | VInt      : nat → Value TInt
  | VString   : string → Value TString
  | VPair a b : Value a → Value b → Value (TPair a b).

End Pact.

(************************************************************************
 * Capabilities *)

Record Sig (n : string) : Set := {
  paramTy : Ty;               (* this could be a product (i.e. pair) *)
  valueTy : Ty;               (* is TUnit for unmanaged caps *)
}.

Arguments paramTy {n} _.
Arguments valueTy {n} _.

Inductive Cap `(S : Sig n) : Set :=
  | Token : Value (paramTy S) → Cap S.

Arguments Token {n S} _.

Record ACap : Set := {
  name : string;
  sig  : Sig name;
  cap  : Cap sig
}.

Inductive CapError : Set :=
  | UnknownCapability      : string → CapError
  | InvalidParameter       : ∀ t : Ty, Value t → CapError
  | InvalidValue           : ∀ t : Ty, Value t → CapError
  | CapabilityNotAvailable : ACap → CapError
  | ManagedError           : string → CapError
  | TypeError.

Record Def `(S : Sig n) : Type := {
  predicate : Value (paramTy S) → Ensemble ACap;
}.

Arguments predicate {n S} _.

Record Defs := {
  capabilities : ∀ (n : string) (S : Sig n), Ensemble (Def S)
}.

(************************************************************************
 * Handling capabilities
 *)

Inductive CExpr : Set :=
  | INSTALL {t} : ACap → Value t → CExpr
  | WITH    {t} : ACap → Value t → CExpr → CExpr
  | REQUIRE     : ACap → CExpr.

Definition is_defined (D : Defs) (C : ACap) : Ensemble (Def (sig C)) :=
  capabilities D (name C) (sig C).

Definition Available := Ensemble { C : ACap & Value (valueTy (sig C)) }.

Definition set_available (A : Available) (C : ACap)
           (v : Value (valueTy (sig C))) : Available :=
  λ e, IF projT1 e = C
       then Singleton _ (existT _ C v) e
       else A e.

Inductive CEval (D : Defs) :
  Ensemble ACap →               (* granted capability tokens prior *)
  Available →                   (* resource available prior *)
  CExpr →
  Ensemble ACap →               (* granted capability tokens after *)
  Available →                   (* resource available after *)
  Prop :=

  (* install-capability *)
  | Eval_INSTALL cs ms (C : ACap) :
    ∀ val : Value (valueTy (sig C)),
    CEval D
      cs ms
      (INSTALL C val)
      cs (set_available ms C val)

  (* with-capability *)
  | Eval_WITH cs ms ms' (C : ACap) (val : Value (valueTy (sig C))) expr :
    ∀ def, is_defined D C def →
    ∀ avail, existT _ C avail ∈ ms →
    ∀ is_monoid : Monoid (Value (valueTy (sig C))),
    ∀ remainder, avail = val ⊗ remainder →
    ∀ arg, cap C = Token arg →
    CEval D
      ({ C } ∪ predicate def arg ∪ cs)
      (set_available ms C remainder)
      expr
      cs ms' →
    CEval D
      cs ms
      (WITH C val expr)
      cs ms'

  (* require-capability *)
  | Eval_REQUIRE (C : ACap) cs ms :
    CEval D
      ({ C } ∪ cs) ms
      (REQUIRE C)
      ({ C } ∪ cs) ms.
