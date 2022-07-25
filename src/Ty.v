Set Warnings "-cannot-remove-as-expected".

Require Import
  Pact.Lib.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Inductive PrimType : Set :=
  | PrimUnit
  | PrimInteger
  | PrimDecimal
  | PrimTime
  | PrimBool
  | PrimString.

Derive NoConfusion NoConfusionHom Subterm EqDec for PrimType.

Inductive Ty : Set :=
  | TyArrow : Ty → Ty → Ty

  (* The following types represent Pact beyond lambda calculus. *)
  | TyError : Ty
  | TySym   : Ty
  | TyPrim  : PrimType → Ty

  | TyList  : Ty → Ty
  | TyPair  : Ty → Ty → Ty
  | TySum   : Ty → Ty → Ty

  | TyCap   : Ty → Ty → Ty.

Derive NoConfusion NoConfusionHom Subterm EqDec for Ty.

Unset Elimination Schemes.

Inductive ConcreteP : Ty → Prop :=
  | SymDecP          : ConcreteP TySym
  | PrimDecP {ty}    : ConcreteP (TyPrim ty)
  | ListDecP {τ}     : ConcreteP τ → ConcreteP (TyList τ)
  | PairDecP {τ1 τ2} : ConcreteP τ1 → ConcreteP τ2 →
                       ConcreteP (TyPair τ1 τ2)
  | SumDecP {τ1 τ2}  : ConcreteP τ1 → ConcreteP τ2 →
                       ConcreteP (TySum τ1 τ2).

Derive Signature for ConcreteP.

Set Elimination Schemes.

Scheme ConcreteP_ind := Induction for ConcreteP Sort Prop.

Fixpoint Reifiable (t : Ty) : option (ConcreteP t) :=
  match t with
  | TySym        => Some SymDecP
  | TyPrim ty    => Some (PrimDecP (ty:=ty))
  | TyList τ     =>
      match Reifiable τ with
      | Some decP => Some (ListDecP decP)
      | None => None
      end
  | TyPair τ1 τ2 =>
      match Reifiable τ1, Reifiable τ2 with
      | Some dec1P, Some dec2P => Some (PairDecP dec1P dec2P)
      | _, _ => None
      end
  | TySum τ1 τ2 =>
      match Reifiable τ1, Reifiable τ2 with
      | Some dec1P, Some dec2P => Some (SumDecP dec1P dec2P)
      | _, _ => None
      end
  | _ => None
  end.

Lemma ConcreteP_irrelevance {τ} (H1 H2 : ConcreteP τ) :
  H1 = H2.
Proof.
  dependent induction H1;
  dependent elimination H2; sauto.
Qed.

Lemma ConcreteP_dec {τ} :
  ConcreteP τ ∨ ¬ (ConcreteP τ).
Proof. induction τ; sauto. Qed.

Declare Scope Ty_scope.
Bind Scope Ty_scope with Ty.
Delimit Scope Ty_scope with ty.

Infix "⟶" := TyArrow (at level 51, right associativity) : Ty_scope.
Infix "×"  := TyPair  (at level 41, right associativity) : Ty_scope.

Notation "x + y" := (TySum x y) : Ty_scope.

Notation "'ℤ'" := (TyPrim PrimInteger) : Ty_scope.
Notation "'𝔻'" := (TyPrim PrimDecimal) : Ty_scope.
Notation "'𝕋'" := (TyPrim PrimTime)    : Ty_scope.
Notation "'𝔹'" := (TyPrim PrimBool)    : Ty_scope.
Notation "'𝕊'" := (TyPrim PrimString)  : Ty_scope.
Notation "'𝕌'" := (TyPrim PrimUnit)    : Ty_scope.
