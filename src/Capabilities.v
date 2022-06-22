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
  EnsemblesExt.

Generalizable All Variables.

(* A variant Mealy machine that effectively goes from `a' to unit, but may
   yield an error. *)
Inductive EMealy (e a : Type) : Type :=
  | MkEMealy : (a → e + EMealy e a) → EMealy e a.

Arguments MkEMealy {e a} _.

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
  paramTy : Ty;               (* this cuold be a product (or pair) *)
}.

Arguments paramTy {n} _.

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
  managed :
    option { valueTy : Ty
           & Value valueTy -> EMealy CapError (Value valueTy) }
}.

Arguments predicate {n S} _.
Arguments managed {n S}.

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

Definition ManagedSet : Type :=
  ACap → Ensemble { valueTy : Ty & EMealy CapError (Value valueTy) }.

Inductive CEval (D : Defs) :
  Ensemble ACap →
  ManagedSet →
  CExpr →
  Ensemble ACap →
  ManagedSet →
  Prop :=

  (*  Installing an unmanaged capability is a no-op. *)
  | Eval_INSTALL_Unmanaged (C : ACap) (val : Value TUnit) cs ms def :
    capabilities D (name C) (sig C) def →
    managed def = None →
    CEval D
      cs ms
      (INSTALL C val)
      cs ms

  (* Installing a managed capability introduces the initial version of the
     mealy machine for that capability into the environment. *)
  | Eval_INSTALL_Managed (C : ACap) cs ms def :
    capabilities D (name C) (sig C) def →
    ∀ valTy mk, managed def = Some (existT _ _ mk) →
    ∀ val : Value valTy,
    CEval D
      cs ms
      (INSTALL C val)
      cs (λ C' v, IF C = C'
                  then Singleton _ (existT _ valTy (mk val)) v
                  else ms C' v)

  (* Using with-capabilities on an unmanaged capability causes the sub-
     expression to be evaluated with that capability token now available, if
     it passes the predicate. Note that the predicate may result in additional
     capability tokens that are also brought into scope for the sub-
     expression. *)
  | Eval_WITH_Unmanaged (C : ACap) (val : Value TUnit) cs ms def expr :
    capabilities D (name C) (sig C) def →
    managed def = None →
    ∀ arg, cap C = Token arg →
    CEval D
      ({ C } ∪ predicate def arg ∪ cs) ms
      expr
      cs ms →
    CEval D
      cs ms
      (WITH C val expr)
      cs ms

  (* Using with-capabilities on a managed capability first executes the mealy
     machine associated with that capability, and only if it yields a
     successor machine do we make the capability available to the sub-
     expression. The environment is also updated with the successor. *)
  | Eval_WITH_Managed (C : ACap) cs (ms : ManagedSet) def expr :
    capabilities D (name C) (sig C) def →
    ∀ arg, cap C = Token arg →
    ∀ valTy mk, managed def = Some (existT _ valTy mk) →
    ∀ val : Value valTy,
    ∀ mach, existT _ valTy (MkEMealy mach) ∈ ms C →
    ∀ mach' ms', mach val = inr mach' →
    CEval D
      ({ C } ∪ predicate def arg ∪ cs)
      (λ C' v, IF C = C'
               then Singleton _ (existT _ _ mach') v
               else ms C' v)
      expr
      cs ms' →
    CEval D
      cs ms
      (WITH C val expr)
      cs ms'

  (* If a capability token is required, then it must be available. Require
     only checks that this is so, it does not affect the environment. *)
  | Eval_REQUIRE (C : ACap) cs ms :
    CEval D
      ({ C } ∪ cs) ms
      (REQUIRE C)
      ({ C } ∪ cs) ms.
