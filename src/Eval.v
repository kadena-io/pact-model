Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List
  Coq.Logic.Classical
  Ty
  Exp
  Sub
  Sem.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Reserved Notation " t '--->' t' " (at level 40).

(************************************************************************
 * Small-step operational semantics
 *)

Inductive Step : ∀ {τ}, Exp [] τ → Exp [] τ → Prop :=
  | ST_Seq τ τ' (e1 : Exp [] τ') (e2 : Exp [] τ) :
    Seq e1 e2 ---> e2

  | ST_ListElem τ (l1 l2 : list (Exp [] τ)) pre x x' post :
    l1 = pre ++ x  :: post →
    l2 = pre ++ x' :: post →
    x ---> x' →
    List l1 ---> List l2

  | ST_Let τ ty (x : Exp [] ty) (body : Exp [ty] τ) :
    Let x body ---> APP (LAM body) x

  | ST_AppAbs dom cod (e : Exp [dom] cod) (v : Exp [] dom) :
    ValueP v ->
    APP (LAM e) v ---> STmExp {| v |} e

  | ST_App1 dom cod (e1 : Exp [] (dom ⟶ cod)) e1' (e2 : Exp [] dom) :
    e1 ---> e1' →
    APP e1 e2 ---> APP e1' e2

  | ST_App2 dom cod (v1 : Exp [] (dom ⟶ cod)) (e2 : Exp [] dom) e2' :
    ValueP v1 →
    e2 ---> e2' →
    APP v1 e2 ---> APP v1 e2'

  where " t '--->' t' " := (Step t t').

Theorem soundness τ (e : Exp [] τ) v :
  Step e v → SemExp e = SemExp v.
Proof.
  intros.
  induction H; simpl; auto;
  extensionality E;
  destruct E.
  - subst.
    rewrite !map_app; f_equal.
    rewrite !map_cons; f_equal.
    now rewrite !IHStep.
  - now rewrite <- SemSubComm.
  - now rewrite IHStep.
  - now rewrite IHStep.
Qed.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'.

Ltac reduce :=
  repeat lazymatch goal with
         | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
             apply inj_pair2 in H; subst
         | [ H : _ ∧ _ |- _ ] => destruct H
         | [ H : _ * _ |- _ ] => destruct H
         | [ H : ∃ _, _ |- _ ] => destruct H
         end.

Ltac inv H := inversion H; subst; clear H; reduce.

Theorem value_is_nf {τ} (v : Exp [] τ) :
  ValueP v → normal_form Step v.
Proof.
  intros.
  unfold normal_form.
  dependent induction v using Exp_rect';
  inv H; intro; reduce.
  - now inversion H.
  - induction l; simpl in *.
    + inv H.
      destruct pre; simpl in *;
      now inversion H1.
    + reduce.
      inv H2.
      intuition.
      inv H.
      destruct pre; simpl in *.
      * inv H2.
        now eapply n; eauto.
      * admit.
  - now inversion H.
Admitted.

Definition deterministic {X : Type} (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Theorem step_deterministic τ :
  deterministic (@Step τ).
Proof.
  repeat intro.
  induction H.
  - now inv H0.
  - subst.
    inv H0.
    admit.
  - now inv H0.
  - inv H0; auto.
    + now inversion H3.
    + apply value_is_nf in H.
      destruct H.
      now exists e2'.
  - inv H0.
    + now inversion H.
    + f_equal.
      now apply IHStep.
    + apply value_is_nf in H4.
      destruct H4.
      now exists e1'.
  - inv H0.
    + apply value_is_nf in H4.
      destruct H4.
      now exists e2'.
    + apply value_is_nf in H.
      destruct H.
      now exists e1'.
    + f_equal.
      now apply IHStep.
Admitted.

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
Admitted.

Definition normalizing {X : Type} (R : relation X) :=
  ∀ t, ∃ t', (multi R) t t' ∧ normal_form R t'.
