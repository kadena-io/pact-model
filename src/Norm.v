Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List
  Coq.Logic.Classical
  Ty
  Exp
  Sub
  Sem
  Eval.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'.

Theorem value_is_nf {τ} (v : Exp [] τ) :
  ValueP v → normal_form Step v.
Proof.
  intros.
  unfold normal_form.
  dependent induction v using Exp_rect';
  inv H; intro; reduce.
  - now inversion H.
  - inv H.
    apply Forall_app in H2.
    reduce.
    inv H0.
    apply isplit in X; simpl in *; reduce.
    now eapply n; eauto.
  - now inversion H.
Qed.

Lemma substitution_reduces {τ ty} (e : Exp [ty] τ) v :
  STmExp {|v|} e ≠ APP (LAM e) v.
Proof.
  intro.
  dependent induction e; simpl in H; inv H.
  - dependent elimination v; simp consSub in H1.
    + induction v0; inv H1.
      now intuition.
    + now induction v; inv H1.
  - admit.
Admitted.

(* A term never reduces to itself. *)
Fixpoint Step_irr {τ} {x : Exp [] τ} : ¬ (x ---> x).
Proof.
  intro.
  dependent induction x.
  - now inv H.
  - inv H.
    clear -H4.
    induction x2; inv H4.
    now eapply IHx2_2; eauto.
  - induction l.
    + inv H.
      destruct pre; simpl in *;
      now inv H1.
    + inv H.
      destruct pre; simpl in *;
      inv H1; inv H2.
      * exact (Step_irr _ _ H4).
      * apply app_inv_head in H0.
        inv H0.
        apply IHl.
        constructor; auto.
        now inv H3.
  - now inv H.
  - now inv H.
  - now inv H.
  - inv H.
    + now eapply substitution_reduces; eauto.
    + now eapply IHx1; eauto.
    + now eapply IHx2; eauto.
Qed.

(* This injectivity theorem says that there is exactly one way to reduce terms
   at any given step. *)
Theorem Step_inj {τ} {x y z : Exp [] τ} :
  x ---> y → x ---> z → y = z.
Proof.
  intros.
  dependent induction x; intros; try solve [ now inv H ].
  - now inv H; inv H0.
  - admit.
  - now inv H; inv H0.
  - admit.
Abort.

Definition deterministic {X : Type} (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Theorem step_deterministic τ :
  deterministic (@Step τ).
Proof.
  repeat intro.
  dependent induction x using Exp_rect'; try inv H.
  - now inv H0.
  - apply isplit in X; simpl in *; reduce.
    now rewrite (Step_List_inv H0 H5).
  - now inv H0.
  - inv H0; auto.
    + now inversion H3.
    + apply value_is_nf in H3.
      destruct H3.
      now exists e2'.
  - inv H0.
    + now inversion H3.
    + f_equal.
      now eapply IHx1.
    + apply value_is_nf in H4.
      destruct H4.
      now exists e1'.
  - inv H0.
    + apply value_is_nf in H2.
      destruct H2.
      now exists e2'.
    + apply value_is_nf in H4.
      destruct H4.
      now exists e1'.
    + f_equal.
      now eapply IHx2.
Qed.

Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e ∨ ∃ e', e ---> e'.
Proof.
  dependent induction e using Exp_rect'.
  - now left; constructor.
  - right.
    eexists e2.
    now constructor.
  - induction l; simpl in *.
    + left.
      now constructor.
    + destruct X.
      destruct (o _ eq_refl JMeq_refl).
      * intuition.
        ** left.
           constructor.
           inv H1.
           now constructor.
        ** right.
           destruct H1.
           inv H0.
           exists (List (a :: pre ++ x' :: post)).
           now apply ST_ListElem
             with (pre:=a :: pre) (post:=post) (x:=x0) (x':=x'); auto.
      * right.
        destruct H.
        exists (List (x :: l)).
        now apply ST_ListElem
          with (pre:=[]) (post:=l) (x:=a) (x':=x); auto.
  - right.
    exists (APP (LAM e2) e1).
    now constructor.
  - now inversion v.
  - left.
    now constructor.
  - right.
    destruct (IHe1 _ eq_refl JMeq_refl); clear IHe1.
    + destruct (IHe2 _ eq_refl JMeq_refl); clear IHe2.
      * dependent elimination e1; inv H.
        exists (STmExp {| e2 |} e4).
        now constructor.
      * dependent elimination e1; inv H.
        exists (APP (LAM e4) x).
        constructor; auto.
        now constructor.
    + reduce.
      destruct (IHe2 _ eq_refl JMeq_refl); clear IHe2.
      * exists (APP x e2).
        now constructor.
      * reduce.
        exists (APP x e2).
        now constructor.
Qed.

Corollary nf_is_value τ (v : Exp [] τ) :
  normal_form Step v → ValueP v.
Proof.
  intros.
  destruct (strong_progress v); auto.
  exfalso.
  now apply H.
Qed.

Corollary nf_same_as_value τ (v : Exp [] τ) :
  normal_form Step v ↔ ValueP v.
Proof.
  split.
  - now apply nf_is_value.
  - now apply value_is_nf.
Qed.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : ∀ (x : X), multi R x x
  | multi_step : ∀ (x y z : X),
      R x y →
      multi R y z →
      multi R x z.

Notation " t '--->*' t' " := (multi Step t t') (at level 40).

Theorem multi_R : ∀ (X : Type) (R : relation X) (x y : X),
  R x y → (multi R) x y.
Proof.
  intros.
  eapply multi_step; eauto.
  now constructor.
Qed.

Theorem multi_trans : ∀ (X : Type) (R : relation X) (x y z : X),
  multi R x y →
  multi R y z →
  multi R x z.
Proof.
  intros.
  induction H; auto.
  now eapply multi_step; eauto.
Qed.

Definition halts {τ} (e : Exp [] τ) : Prop :=
  ∃ e', e --->* e' ∧ ValueP e'.

Lemma value_halts {τ} (v : Exp [] τ) : ValueP v → halts v.
Proof.
  intros.
  unfold halts.
  now dependent induction H; eexists; split; constructor.
Qed.

Lemma step_preserves_halting {τ} (e e' : Exp [] τ) :
  (e ---> e') → (halts e ↔ halts e').
Proof.
  intros.
  unfold halts.
  split.
  - intros [e'' [H1 H2]].
    destruct H1.
    + apply value_is_nf in H2.
      destruct H2.
      now exists e'.
    + rewrite (step_deterministic _ _ _ _ H H0).
      now exists z.
  - intros [e'0 [H1 H2]].
    exists e'0.
    split; auto.
    now eapply multi_step; eauto.
Qed.

Definition normal_form_of {τ} (e e' : Exp [] τ) :=
  (e --->* e' ∧ normal_form Step e').

Theorem normal_forms_unique τ :
  deterministic (normal_form_of (τ:=τ)).
Proof.
  unfold normal_form_of, normal_form.
  repeat intro.
  reduce.
Admitted.

Definition normalizing {X : Type} (R : relation X) :=
  ∀ t, ∃ t', (multi R) t t' ∧ normal_form R t'.
