Set Warnings "-cannot-remove-as-expected".

Require Import
  Lib.

From Equations Require Import Equations.
Set Equations With UIP.

Section Ty.

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
  | TyPrim  : PrimType → Ty
  | TySym   : Ty

  | TyList  : Ty → Ty
  | TyPair  : Ty → Ty → Ty

  | TyACap  : Ty
  | TyCap   : Ty → Ty → Ty.

Derive NoConfusion NoConfusionHom Subterm EqDec for Ty.

Inductive ConcreteP : Ty → Set :=
  | PrimDecP {ty}    : ConcreteP (TyPrim ty)
  | SymDecP          : ConcreteP TySym
  | ListDecP {τ}     : ConcreteP τ → ConcreteP (TyList τ)
  | PairDecP {τ1 τ2} : ConcreteP τ1 → ConcreteP τ2 →
                       ConcreteP (TyPair τ1 τ2).

Derive Signature NoConfusion NoConfusionHom EqDec for ConcreteP.

Fixpoint Concreteness (t : Ty) : option (ConcreteP t) :=
  match t with
  | TyPrim ty    => Some (PrimDecP (ty:=ty))
  | TySym        => Some SymDecP
  | TyList τ     =>
      match Concreteness τ with
      | Some decP => Some (ListDecP decP)
      | None => None
      end
  | TyPair τ1 τ2 =>
      match Concreteness τ1, Concreteness τ2 with
      | Some dec1P, Some dec2P => Some (PairDecP dec1P dec2P)
      | _, _ => None
      end
  | _ => None
  end.

Lemma ConcreteP_irrelevance {τ} (H1 H2 : ConcreteP τ) :
  H1 = H2.
Proof.
  dependent induction H1;
  dependent elimination H2; auto;
  f_equal; congruence.
Qed.

Lemma ConcreteP_dec {τ} :
  ConcreteP τ + (ConcreteP τ → False).
Proof.
  induction τ; try solve [now left; constructor|now right].
  - destruct IHτ;
    try (now left; constructor);
    right; intro; inversion H; contradiction.
  - destruct IHτ1, IHτ2;
    try (now left; constructor);
    right; intro; inversion H; contradiction.
Qed.

End Ty.

Arguments ListDecP {τ} _.
Arguments PairDecP {τ1 τ2} _ _.

Declare Scope Ty_scope.
Bind Scope Ty_scope with Ty.
Delimit Scope Ty_scope with ty.

Infix "⟶" := TyArrow (at level 51, right associativity) : Ty_scope.
Infix "×"  := TyPair  (at level 40, left associativity) : Ty_scope.

Notation "'ℤ'" := (TyPrim PrimInteger).
Notation "'𝔻'" := (TyPrim PrimDecimal).
Notation "'𝕋'" := (TyPrim PrimTime).
Notation "'𝔹'" := (TyPrim PrimBool).
Notation "'𝕊'" := (TyPrim PrimString).
Notation "'𝕌'" := (TyPrim PrimUnit).
