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
  dependent induction v;
  inv H; intro; reduce;
  try now inversion H.
  inv H.
  - now eapply IHv1; eauto.
  - now eapply IHv2; eauto.
Qed.

Ltac normality :=
  exfalso;
  lazymatch goal with
    | [ H1 : ValueP ?X, H2 : ?X ---> ?Y |- False ] =>
        apply value_is_nf in H1; destruct H1;
        now exists Y
  end.

Lemma If_loop_true {τ} b {x : Exp [] τ} {y : Exp [] τ} :
  ¬ (If b x y = x).
Proof.
  induction x; intro; inv H.
  now eapply IHx2; eauto.
Qed.

Lemma If_loop_false {τ} b {x : Exp [] τ} {y : Exp [] τ} :
  ¬ (If b x y = y).
Proof.
  induction y; intro; inv H.
  now eapply IHy3; eauto.
Qed.

Lemma Seq_loop {τ ty} {x : Exp [] ty} {y : Exp [] τ} :
  ¬ (Seq x y = y).
Proof.
  induction y; intro; inv H.
  now eapply IHy2; eauto.
Qed.

Lemma Let_loop {τ ty} {v : Exp [] ty} {e : Exp [ty ] τ} :
  ¬ (STmExp {|v|} e = Let v e).
Proof.
  dependent induction e; repeat intro; inv H.
  - admit.
  - dependent induction v0; simp consSub in *.
    + now induction v; inv H1; intuition.
    + now induction v0; inv H1; intuition.
Admitted.

Lemma App_Lam_loop {τ ty} {v : Exp [] ty} {e : Exp [ty ] τ} :
  ¬ (STmExp {|v|} e = APP (LAM e) v).
Proof.
  dependent induction e; repeat intro; inv H.
  - dependent induction v0; simp consSub in *.
    + now induction v; inv H1; intuition.
    + now induction v0; inv H1; intuition.
  - admit.
Admitted.

(* A term never reduces to itself. *)
Theorem Step_irr {τ} {x : Exp [] τ} : ¬ (x ---> x).
Proof.
  intro.
  dependent induction x; try solve [ now inv H ].
  - inv H.
    + now eapply If_loop_true; eauto.
    + now eapply If_loop_false; eauto.
    + now firstorder.
  - inv H.
    + now eapply IHx1; eauto.
    + now eapply IHx2; eauto.
  - inv H.
    + now eapply IHx; eauto.
    + now eapply IHx; eauto.
  - inv H.
    + now eapply IHx; eauto.
    + now eapply IHx; eauto.
  - inv H.
    now eapply Seq_loop; eauto.
  - inv H.
    + now eapply IHx1; eauto.
    + now eapply Let_loop; eauto.
  - inv H.
    + now eapply App_Lam_loop; eauto.
    + now eapply IHx1; eauto.
    + now eapply IHx2; eauto.
Qed.

Corollary Step_productive {τ} {x x' : Exp [] τ} : x ---> x' → x ≠ x'.
Proof.
  repeat intro; subst.
  now eapply Step_irr; eauto.
Qed.

(* This injectivity theorem says that there is exactly one way to reduce terms
   at any given step. *)
Fixpoint Step_inj {τ} {x y z : Exp [] τ} :
  x ---> y → x ---> z → y = z.
Proof.
  intros.
  dependent induction x; intros; try solve [ now inv H ].
  - inv H; inv H0; auto.
    + now inv H2.
    + now inv H2.
    + now inv H3.
    + now inv H3.
    + now f_equal; intuition.
  - inv H; inv H0; auto.
    + now f_equal; intuition.
    + now normality.
    + now normality.
    + now f_equal; intuition.
  - inv H; inv H0; auto.
    + now f_equal; intuition.
    + now inv H3; normality.
    + now inv H2; normality.
  - inv H; inv H0; auto.
    + now f_equal; intuition.
    + now inv H3; normality.
    + now inv H2; normality.
  - now inv H; inv H0.
  - inv H; inv H0; auto.
    + now f_equal; intuition.
    + now normality.
    + now normality.
  - inv H; inv H0; auto; try solve [ now inv H2 ].
    + now normality.
    + now f_equal; intuition.
    + now normality.
    + now normality.
    + now f_equal; intuition.
Qed.

Definition deterministic {X : Type} (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Theorem step_deterministic τ :
  deterministic (@Step τ).
Proof.
  repeat intro.
  generalize dependent y2.
  dependent induction x; intros; inv H.
  (* ST_IfTrue *)
  - inv H0; auto.
    now inv H2.
  (* ST_IfFalse *)
  - inv H0; auto.
    now inv H2.
  (* ST_If *)
  - inv H0.
    + now inv H3.
    + now inv H3.
    + now f_equal; intuition.
  (* ST_Pair1 *)
  - inv H0.
    + now f_equal; intuition.
    + now normality.
  (* ST_Pair2 *)
  - inv H0.
    + now normality.
    + now f_equal; intuition.
  (* ST_Fst1 *)
  - inv H0.
    + now f_equal; intuition.
    + exfalso.
      now inv H3; normality.
  (* ST_FstPair *)
  - inv H0; auto.
    now inv H2; normality.
  (* ST_Snd1 *)
  - inv H0.
    + now f_equal; intuition.
    + exfalso.
      now inv H3; normality.
  (* ST_SndPair *)
  - inv H0; auto.
    now inv H2; normality.
  (* ST_Seq *)
  - inv H0.
    now intuition.
  (* ST_Let1 *)
  - inv H0.
    + now f_equal; intuition.
    + now normality.
  (* ST_Let2 *)
  - inv H0; auto.
    now normality.
  (* ST_AppAbs *)
  - inv H0; auto.
    + now inv H2.
    + now normality.
  (* ST_App1 *)
  - inv H0.
    + now inv H3.
    + now f_equal; intuition.
    + now normality.
  (* ST_App2 *)
  - inv H0.
    + now normality.
    + now normality.
    + now f_equal; intuition.
Qed.

Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e ∨ ∃ e', e ---> e'.
Proof.
  dependent induction e.
  - now left; constructor.
  - now left; constructor.
  - now left; constructor.
  - now left; constructor.
  - right.
    destruct (IHe1 _ eq_refl JMeq_refl); reduce.
    + inv H.
      * now exists e2; constructor.
      * now exists e3; constructor.
    + now exists (If x e2 e3); constructor.
  - destruct (IHe1 _ eq_refl JMeq_refl); reduce.
    + destruct (IHe2 _ eq_refl JMeq_refl); reduce.
      * left.
        now constructor.
      * right.
        now exists (Pair e1 x); constructor.
    + destruct (IHe2 _ eq_refl JMeq_refl); reduce.
      * right.
        now exists (Pair x e2); constructor.
      * right.
        now exists (Pair x e2); constructor.
  - destruct (IHe _ eq_refl JMeq_refl); reduce.
    + right.
      inv H.
      now exists x; constructor.
    + right.
      now exists (Fst x); constructor.
  - destruct (IHe _ eq_refl JMeq_refl); reduce.
    + right.
      inv H.
      now exists y; constructor.
    + right.
      now exists (Snd x); constructor.
  - right.
    now exists e2; constructor.
  - right.
    destruct (IHe1 _ eq_refl JMeq_refl); clear IHe1.
    + exists (STmExp {| e1 |} e2).
      now constructor.
    + destruct H.
      now exists (Let x e2); constructor.
  - now inversion v.
  - left.
    now constructor.
  - right.
    destruct (IHe1 _ eq_refl JMeq_refl); clear IHe1.
    + destruct (IHe2 _ eq_refl JMeq_refl); clear IHe2.
      * dependent elimination e1; inv H.
        exists (STmExp {| e2 |} e11).
        now constructor.
      * dependent elimination e1; inv H.
        exists (APP (LAM e11) x).
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
  unfold deterministic, normal_form_of.
  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12].
  destruct P2 as [P21 P22].
  generalize dependent y2.
  induction P11; intros.
  - inversion P21; auto.
    induction P12.
    now exists y.
  - apply IHP11; auto.
    inv P21.
    + destruct P22.
      now exists y.
    + assert (y = y0) by now apply step_deterministic with x.
      now subst.
Qed.

Definition normalizing {X : Type} (R : relation X) :=
  ∀ t, ∃ t', (multi R) t t' ∧ normal_form R t'.
