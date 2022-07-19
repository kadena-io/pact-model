Set Warnings "-cannot-remove-as-expected".

Require Import
  Lib.

From Equations Require Import Equations.
Set Equations With UIP.

Section Ty.

Inductive PrimType : Set :=
  | PrimInteger
  | PrimDecimal
  | PrimTime
  | PrimBool
  | PrimString
  | PrimUnit.

Derive NoConfusion NoConfusionHom Subterm EqDec for PrimType.

Inductive Ty : Set :=
  | TyPrim : PrimType → Ty

  | TyList : Ty → Ty
  | TyPair : Ty → Ty → Ty

  (* | TyCap : Ty → Ty → Ty *)

  (* The arrow type is the only type in the base lambda calculus *)
  | TyArrow : Ty → Ty → Ty.

Derive NoConfusion NoConfusionHom Subterm EqDec for Ty.

Inductive DecidableP : Ty → Set :=
  | PrimDecP {ty} : DecidableP (TyPrim ty)
  | ListDecP {τ} : DecidableP τ → DecidableP (TyList τ)
  | PairDecP {τ1 τ2} : DecidableP τ1 → DecidableP τ2 →
                       DecidableP (TyPair τ1 τ2).

Derive Signature NoConfusion NoConfusionHom EqDec for DecidableP.

Lemma DecidableP_irrelevance {τ} (H1 H2 : DecidableP τ) :
  H1 = H2.
Proof.
  dependent induction H1;
  dependent elimination H2; auto;
  f_equal; congruence.
Qed.

Lemma DecidableP_dec {τ} :
  DecidableP τ + (DecidableP τ → False).
Proof.
  induction τ; try solve [now left; constructor|now right].
  - destruct IHτ.
    + now left; constructor.
    + right; intro; inversion H; contradiction.
  - destruct IHτ1, IHτ2.
    + now left; constructor.
    + right; intro; inversion H; contradiction.
    + right; intro; inversion H; contradiction.
    + right; intro; inversion H; contradiction.
Qed.

End Ty.

Arguments PrimDecP.
Arguments ListDecP {τ} _.
Arguments PairDecP {τ1 τ2} _ _.

Declare Scope Ty_scope.
Bind Scope Ty_scope with Ty.
Delimit Scope Ty_scope with ty.

Infix "⟶" := TyArrow (at level 51, right associativity) : Ty_scope.
Infix "×"  := TyPair  (at level 40, left associativity) : Ty_scope.
