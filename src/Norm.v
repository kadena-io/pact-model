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

Theorem value_is_nf {Γ τ} (v : Exp Γ τ) :
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

Lemma If_loop_true {Γ τ} b {x : Exp Γ τ} {y : Exp Γ τ} :
  ¬ (If b x y = x).
Proof.
  induction x; intro; inv H.
  now eapply IHx2; eauto.
Qed.

Lemma If_loop_false {Γ τ} b {x : Exp Γ τ} {y : Exp Γ τ} :
  ¬ (If b x y = y).
Proof.
  induction y; intro; inv H.
  now eapply IHy3; eauto.
Qed.

Lemma Seq_loop {Γ τ ty} {x : Exp Γ ty} {y : Exp Γ τ} :
  ¬ (Seq x y = y).
Proof.
  induction y; intro; inv H.
  now eapply IHy2; eauto.
Qed.

Lemma Let_loop {Γ τ ty} {v : Exp Γ ty} {e : Exp (ty :: Γ) τ} :
  ¬ (STmExp {||v||} e = Let v e).
Proof.
  generalize dependent Γ.
  dependent induction e; repeat intro; inv H.
  - admit.
  - dependent induction v0; simp consSub in *.
    + now induction v; inv H1; intuition.
    + now induction v0; inv H1; intuition.
Admitted.

Lemma App_Lam_loop {Γ τ ty} {v : Exp Γ ty} {e : Exp (ty :: Γ) τ} :
  ¬ (STmExp {||v||} e = APP (LAM e) v).
Proof.
  dependent induction e; repeat intro; inv H.
  - dependent induction v0; simp consSub in *.
    + now induction v; inv H1; intuition.
    + now induction v0; inv H1; intuition.
  - admit.
Admitted.

(* A term never reduces to itself. *)
Theorem Step_irr {Γ τ} {x : Exp Γ τ} : ¬ (x ---> x).
Proof.
  intro.
  dependent induction x; try solve [ now inv H ].
  - inv H.
    + now eapply If_loop_true; eauto.
    + now eapply If_loop_false; eauto.
    + now firstorder.
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

Corollary Step_productive {Γ τ} {x x' : Exp Γ τ} : x ---> x' → x ≠ x'.
Proof.
  repeat intro; subst.
  now eapply Step_irr; eauto.
Qed.

(* This injectivity theorem says that there is exactly one way to reduce terms
   at any given step. *)
Fixpoint Step_inj {Γ τ} {x y z : Exp Γ τ} :
  x ---> y → x ---> z → y = z.
Proof.
  intros.
  dependent induction x; intros; try solve [ now inv H ].
  - inv H; inv H0; auto.
    + now inv H3.
    + now inv H3.
    + now inv H4.
    + now inv H4.
    + now f_equal; intuition.
  - inv H; inv H0; auto.
    + now f_equal; intuition.
    + now normality.
    + now normality.
    + now f_equal; intuition.
  - inv H; inv H0; auto.
    + now f_equal; intuition.
    + now inv H4; normality.
    + now inv H3; normality.
  - inv H; inv H0; auto.
    + now f_equal; intuition.
    + now inv H4; normality.
    + now inv H3; normality.
  - now inv H; inv H0.
  - inv H; inv H0; auto.
    + now f_equal; intuition.
    + now normality.
    + now normality.
  - inv H; inv H0; auto; try solve [ now inv H3 ].
    + now normality.
    + now f_equal; intuition.
    + now normality.
    + now normality.
    + now f_equal; intuition.
Qed.

Definition deterministic {X : Type} (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Theorem step_deterministic Γ τ :
  deterministic (@Step Γ τ).
Proof.
  repeat intro.
  generalize dependent y2.
  dependent induction x; intros; inv H.
  (* ST_IfTrue *)
  - inv H0; auto.
    now inv H3.
  (* ST_IfFalse *)
  - inv H0; auto.
    now inv H3.
  (* ST_If *)
  - inv H0.
    + now inv H4.
    + now inv H4.
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
      now inv H4; normality.
  (* ST_FstPair *)
  - inv H0; auto.
    now inv H3; normality.
  (* ST_Snd1 *)
  - inv H0.
    + now f_equal; intuition.
    + exfalso.
      now inv H4; normality.
  (* ST_SndPair *)
  - inv H0; auto.
    now inv H3; normality.
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
    + now inv H3.
    + now normality.
  (* ST_App1 *)
  - inv H0.
    + now inv H4.
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
    + exists (STmExp {|| e1 ||} e2).
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
        exists (STmExp {|| e2 ||} e11).
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

Corollary nf_is_value {τ} (v : Exp [] τ) :
  normal_form Step v → ValueP v.
Proof.
  intros.
  destruct (strong_progress v); auto.
  exfalso.
  now apply H.
Qed.

Corollary nf_same_as_value {τ} (v : Exp [] τ) :
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

Definition halts {Γ τ} (e : Exp Γ τ) : Prop :=
  ∃ e', e --->* e' ∧ ValueP e'.

Lemma value_halts {Γ τ} (v : Exp Γ τ) : ValueP v → halts v.
Proof.
  intros.
  unfold halts.
  now dependent induction H; eexists; split; constructor.
Qed.

Lemma step_preserves_halting {Γ τ} (e e' : Exp Γ τ) :
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
    + rewrite (step_deterministic _ _ _ _ _ H H0).
      now exists z.
  - intros [e'0 [H1 H2]].
    exists e'0.
    split; auto.
    now eapply multi_step; eauto.
Qed.

Definition normal_form_of {Γ τ} (e e' : Exp Γ τ) :=
  (e --->* e' ∧ normal_form Step e').

Theorem normal_forms_unique Γ τ :
  deterministic (normal_form_of (Γ:=Γ) (τ:=τ)).
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

Equations R {Γ τ} (e : Γ ⊢ τ) : Prop :=
  R (τ:=TyPrim _) e := halts e;
  R (τ:=TyUnit)   e := halts e;
  R (τ:=TyBool)   e := halts e;
  R (τ:=_ × _)    e := halts e ∧ R (Fst e) ∧ R (Snd e);
  R (τ:=_ ⟶ _)   e := halts e ∧ ∀ e', R e' → R (APP e e').

Lemma R_halts {Γ τ} {e : Γ ⊢ τ} : R e → halts e.
Proof. intros; induction τ; simp R in H; now reduce. Qed.

Lemma step_preserves_R {Γ τ} {e e' : Γ ⊢ τ} :
  (e ---> e') → R e → R e'.
Proof.
  intros.
  induction τ; simp R in *;
  pose proof H as H1;
  apply step_preserves_halting in H1; intuition.
  - eapply IHτ1; eauto.
    now constructor.
  - eapply IHτ2; eauto.
    now constructor.
  - eapply IHτ2; eauto.
    now constructor.
Qed.

Lemma multistep_preserves_R {Γ τ} {e e' : Γ ⊢ τ} :
  (e --->* e') → R e → R e'.
Proof.
  intros.
  induction H; auto.
  apply IHmulti.
  now eapply step_preserves_R; eauto.
Qed.

Lemma step_preserves_R' {Γ τ} {e e' : Γ ⊢ τ} :
  (e ---> e') → R e' → R e.
Proof.
  intros.
  induction τ; simp R in *;
  pose proof H as H1;
  apply step_preserves_halting in H1; intuition.
  - eapply IHτ1; eauto.
    now constructor.
  - eapply IHτ2; eauto.
    now constructor.
  - eapply IHτ2; eauto.
    now constructor.
Qed.

Lemma multistep_preserves_R' {Γ τ} {e e' : Γ ⊢ τ} :
  (e --->* e') → R e' → R e.
Proof.
  intros.
  induction H; auto.
  now eapply step_preserves_R'; eauto.
Qed.

Inductive ExpEnv : Env → Type :=
  | Nil : ExpEnv []
  | Cons {Γ τ} : Exp Γ τ → ExpEnv Γ →  ExpEnv (τ :: Γ).

Equations msubst `(e : Γ ⊢ τ) `(ss : ExpEnv Γ) : [] ⊢ τ :=
  msubst (Γ:=[]) e Nil => e;
  msubst e (Cons x xs) => msubst (STmExp {|| x ||} _) xs.

Definition mupdate := app.

Lemma msubst_closed `(e : [] ⊢ τ) ss :
  msubst e ss = e.
Proof.
  dependent induction ss.
  now simp msubst.
Qed.

Inductive instantiation : ∀ Γ, ExpEnv Γ → Prop :=
  | V_nil :
      instantiation [] Nil
  | V_cons {Γ τ} (v : Γ ⊢ τ) ee :
      ValueP v → R v →
      instantiation Γ ee →
      instantiation (τ :: Γ) (Cons v ee).

Lemma multistep_App2 {Γ dom cod} {e e' : Γ ⊢ dom} {v : Γ ⊢ (dom ⟶ cod)} :
  ValueP v → (e --->* e') → APP v e --->* APP v e'.
Proof.
  intros.
  induction H0.
  - now apply multi_refl.
  - eapply multi_step; eauto.
    now constructor.
Qed.

(* Equations ExpGet `(se : ExpEnv Γ) `(v : Var Γ τ) : Γ ⊢ τ := *)
(*   ExpGet (Cons x _)   ZV    := x; *)
(*   ExpGet (Cons _ xs) (SV v) := ExpGet xs v. *)

Lemma msubst_R : ∀ Γ (env : ExpEnv Γ) τ (t : Exp Γ τ),
  instantiation Γ env →
  R (msubst t env).
Proof.
  intros Γ env τ t V.
  generalize dependent env.
  (* We need to generalize the hypothesis a bit before setting up the induction. *)
  generalize dependent Γ.
  induction t; intros.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  (* - apply instantiation_R. *)
Admitted.

Theorem normalization {τ} (e : [] ⊢ τ) : halts e.
Proof.
  replace e with (msubst e Nil) by reflexivity.
  apply R_halts.
  apply (msubst_R nil); eauto.
  now constructor.
Qed.
