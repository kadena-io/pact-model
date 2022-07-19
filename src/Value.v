Require Import
  Lib
  Ltac
  Ty
  Exp.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Value.

Import ListNotations.

Open Scope Ty_scope.

Unset Elimination Schemes.

(* [ValueP] is an inductive proposition that indicates whether an expression
   represents a value, i.e., that it does reduce any further. *)
Inductive ValueP Γ : ∀ {τ}, Exp Γ τ → Prop :=
  | LiteralP {ty l} : ValueP Γ (Lit (ty:=ty) l)
  | BuiltinP {τ b} : ValueP Γ (Bltn (τ:=τ) b)
  | PairP {τ1 τ2} {x : Exp Γ τ1} {y : Exp Γ τ2} :
    ValueP Γ x → ValueP Γ y → ValueP Γ (Pair x y)
  | NilP {τ} : ValueP Γ (Nil (τ:=τ))
  | ConsP {τ} (x : Exp Γ τ) xs :
    ValueP Γ x → ValueP Γ xs → ValueP Γ (Cons x xs)
  | LambdaP {dom cod} (e : Exp (dom :: Γ) cod) : ValueP Γ (LAM e).

Derive Signature for ValueP.

Inductive ErrorP Γ : ∀ {τ}, Exp Γ τ → Prop :=
  | IsError {τ} m : ErrorP Γ (Error (τ:=τ) m).

Derive Signature for ErrorP.

Set Elimination Schemes.

Scheme ValueP_ind := Induction for ValueP Sort Prop.
Scheme ErrorP_ind := Induction for ErrorP Sort Prop.

#[local] Hint Constructors ValueP ErrorP : core.

Lemma ValueP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ValueP _ v) :
  H1 = H2.
Proof.
  dependent induction H1;
  dependent elimination H2; auto;
  f_equal; congruence.
Qed.

Lemma ErrorP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ErrorP _ v) :
  H1 = H2.
Proof.
  dependent induction H1;
  dependent elimination H2; auto;
  f_equal; congruence.
Qed.

Lemma ValueP_dec {Γ τ} (e : Exp Γ τ) :
  ValueP Γ e ∨ ¬ ValueP Γ e.
Proof.
  induction e; try solve [now left|now right].
  - destruct IHe1, IHe2.
    + now left; constructor.
    + right; intro; inv H1; contradiction.
    + right; intro; inv H1; contradiction.
    + right; intro; inv H1; contradiction.
  - destruct IHe1, IHe2.
    + now left; constructor.
    + right; intro; inv H1; contradiction.
    + right; intro; inv H1; contradiction.
    + right; intro; inv H1; contradiction.
Qed.

Lemma ErrorP_dec {Γ τ} (e : Exp Γ τ) :
  ErrorP Γ e ∨ ¬ ErrorP Γ e.
Proof.
  induction e; solve [now left|now right].
Qed.

End Value.

Arguments ValueP {Γ τ} _.
Arguments LiteralP {Γ}.
Arguments BuiltinP {Γ}.
Arguments PairP {Γ τ1 τ2 x y} _ _.
Arguments NilP {Γ τ}.
Arguments ConsP {Γ τ _ _} _ _.
Arguments LambdaP {Γ dom cod} _.

Arguments ErrorP {Γ τ} _.
