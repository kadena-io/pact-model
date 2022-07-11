Require Import
  Coq.Unicode.Utf8
  Coq.Program.Program
  Coq.Lists.List
  Coq.Relations.Relation_Definitions
  Coq.Classes.CRelationClasses
  Coq.Classes.Morphisms
  Ty
  Exp
  Sub
  Sem
  Eval.

From Equations Require Import Equations.

Generalizable All Variables.

Section Norm.

Import ListNotations.

Context {A : Type}.
Context `{L : HostLang A}.

Definition normal_form `(R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'.

Definition normalizing `(R : relation X) : Prop :=
  ∀ t, ∃ t', multi R t t' ∧ normal_form R t'.

Definition deterministic `(R : relation X) : Prop :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Definition halts {Γ τ} (e : Exp Γ τ) : Prop :=
  ∃ e', e --->* e' ∧ inhabited (ValueP e').

Notation " e '⇓' " := (halts e) (at level 11).

Definition normal_form_of {Γ τ} (e e' : Exp Γ τ) : Prop :=
  (e --->* e' ∧ normal_form Step e').

Lemma value_is_nf {Γ τ} (v : Exp Γ τ) :
  ValueP v → normal_form Step v.
Proof.
  intros.
  unfold normal_form.
  dependent induction v;
  inv X; intro; reduce;
  try now inversion H.
  - inv H.
    + now eapply IHv1; eauto.
    + now eapply IHv2; eauto.
  - inv H.
    + now eapply IHv1; eauto.
    + now eapply IHv2; eauto.
Qed.

Lemma nf_is_value {τ} (v : Exp [] τ) :
  normal_form Step v → ValueP v.
Proof.
  intros.
  destruct (strong_progress v); auto.
  reduce.
  destruct H.
  now exists x.
Qed.

Theorem nf_same_as_value {τ} (v : Exp [] τ) :
  iffT (normal_form Step v) (ValueP v).
Proof.
  split.
  - now apply nf_is_value.
  - now apply value_is_nf.
Qed.

Lemma value_halts {Γ τ} (v : Exp Γ τ) : ValueP v → halts v.
Proof.
  intros.
  unfold halts.
  now induction X; eexists; repeat constructor.
Qed.

Ltac normality :=
  exfalso;
  lazymatch goal with
    | [ H1 : ValueP ?X, H2 : ?X ---> ?Y |- False ] =>
        apply value_is_nf in H1; destruct H1;
        now exists Y
  end.

Ltac invert_step :=
  try lazymatch goal with
  | [ H : _ ---> _ |- _ ] => now inv H
  end;
  try solve [ f_equal; intuition eauto | normality ].

Theorem step_deterministic Γ τ :
  deterministic (@Step _ _ Γ τ).
Proof.
  repeat intro.
  generalize dependent y2.
  dependent induction x; intros; inv H;
  inv H0; invert_step.
  - inv H4; now invert_step.
  - inv H3; now invert_step.
  - inv H4; now invert_step.
  - inv H3; now invert_step.
  - inv H4; now invert_step.
  - inv H3; now invert_step.
  - inv H5; now invert_step.
  - inv H4; now invert_step.
  - now f_equal; apply ValueP_irrelevance.
Qed.

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

Lemma step_preserves_halting {Γ τ} (e e' : Exp Γ τ) :
  (e ---> e') → (halts e ↔ halts e').
Proof.
  intros.
  unfold halts.
  split.
  - intros [e'' [H1 H2]].
    destruct H1.
    + destruct H2.
      apply value_is_nf in X.
      destruct X.
      now exists e'.
    + rewrite (step_deterministic _ _ _ _ _ H H0).
      now exists z.
  - intros [e'0 [H1 H2]].
    exists e'0.
    split; auto.
    now eapply multi_step; eauto.
Qed.

Section Log.

Context {Γ : Env}.

Variable P : ∀ {τ}, Exp Γ τ → Prop.

(** [ExpP] is a logical predicate that permits type-directed induction on
    expressions. *)
Equations ExpP `(e : Exp Γ τ) : Prop :=
  ExpP (τ:=_ ⟶ _)   f := P f ∧ (∀ x, ExpP x → ExpP (APP f x));
  ExpP (τ:=_ × _)    p := P p ∧ ExpP (Fst p) ∧ ExpP (Snd p);
  (* ExpP (τ:=TyList _) l := P l ∧ (∀ d, ExpP d → ExpP (Car d l)); *)
  ExpP e := P e.

Inductive SubP : ∀ {Γ'}, Sub Γ Γ' → Prop :=
  | NoSubP : SubP (NoSub (Γ:=Γ))
  | PushP {Γ' τ} (e : Exp Γ τ) (s : Sub Γ Γ') :
    ExpP e → SubP s → SubP (Push e s).

Derive Signature for SubP.

Lemma ExpP_P {τ} {e : Γ ⊢ τ} : ExpP e → P e.
Proof. intros; induction τ; simpl in *; simp ExpP in H; now reduce. Qed.

End Log.

Definition SN {Γ τ} : Γ ⊢ τ → Prop := ExpP (@halts Γ).
Arguments SN {Γ τ} _ /.

Definition SN_Sub {Γ Γ'} : Sub Γ' Γ → Prop := SubP (@halts Γ').
Arguments SN_Sub {Γ Γ'} /.

Definition SN_halts {Γ τ} {e : Γ ⊢ τ} : SN e → halts e := ExpP_P _.

Lemma step_preserves_SN {Γ τ} {e e' : Γ ⊢ τ} :
  (e ---> e') → SN e → SN e'.
Proof.
  intros.
  induction τ; simpl in *; simp SN in *;
  pose proof H as H1;
  apply step_preserves_halting in H1; intuition.
  - eapply IHτ1; eauto.
    now constructor.
  - eapply IHτ2; eauto.
    now constructor.
  - eapply IHτ2; eauto.
    now constructor.
Qed.

Lemma multistep_preserves_SN {Γ τ} {e e' : Γ ⊢ τ} :
  (e --->* e') → SN e → SN e'.
Proof.
  intros.
  induction H; auto.
  apply IHmulti.
  now eapply step_preserves_SN; eauto.
Qed.

Lemma step_preserves_SN' {Γ τ} {e e' : Γ ⊢ τ} :
  (e ---> e') → SN e' → SN e.
Proof.
  intros.
  induction τ; simpl in *; simp SN in *;
  pose proof H as H1;
  apply step_preserves_halting in H1; intuition.
  - eapply IHτ1; eauto.
    now constructor.
  - eapply IHτ2; eauto.
    now constructor.
  - eapply IHτ2; eauto.
    now constructor.
Qed.

Lemma multistep_preserves_SN' {Γ τ} {e e' : Γ ⊢ τ} :
  (e --->* e') → SN e' → SN e.
Proof.
  intros.
  induction H; auto.
  now eapply step_preserves_SN'; eauto.
Qed.

Lemma multistep_Seq {Γ τ} {e1 : Γ ⊢ τ} {τ'} {e2 : Γ ⊢ τ'} :
  Seq e1 e2 --->* e2.
Proof.
  intros.
  eapply multi_step; eauto.
  - now constructor.
  - now apply multi_refl.
Qed.

Ltac simpl_multistep :=
  intros;
  match goal with
  | [ H : _ --->* _ |- _ ] => induction H
  end;
  [ now apply multi_refl
  | eapply multi_step; eauto;
    now constructor ].

Lemma multistep_If {Γ} {e1 e1' : Γ ⊢ TyBool} {τ} {e2 e3 : Γ ⊢ τ} :
  (e1 --->* e1') → If e1 e2 e3 --->* If e1' e2 e3.
Proof. now simpl_multistep. Qed.

Lemma multistep_Pair1 {Γ τ1 τ2} {e1 e1' : Γ ⊢ τ1} {e2 : Γ ⊢ τ2} :
  (e1 --->* e1') → Pair e1 e2 --->* Pair e1' e2.
Proof. now simpl_multistep. Qed.

Lemma multistep_Pair2 {Γ τ1 τ2} {e1 : Γ ⊢ τ1} {e2 e2' : Γ ⊢ τ2} :
  ValueP e1 → (e2 --->* e2') → Pair e1 e2 --->* Pair e1 e2'.
Proof. now simpl_multistep. Qed.

Lemma multistep_Pair {Γ τ1 τ2} {e1 e1' : Γ ⊢ τ1} {e2 e2' : Γ ⊢ τ2} :
  ValueP e1' →
  (e1 --->* e1') → (e2 --->* e2') → Pair e1 e2 --->* Pair e1' e2'.
Proof.
  intros.
  induction H; intros.
  - now apply multistep_Pair2; auto.
  - rewrite <- IHmulti; auto.
    apply multistep_Pair1; auto.
    now econstructor; eauto.
Qed.

Lemma multistep_Fst1 {Γ τ1 τ2} {p p' : Γ ⊢ (τ1 × τ2)} :
  (p --->* p') → Fst p --->* Fst p'.
Proof. now simpl_multistep. Qed.

Lemma multistep_FstPair {Γ τ1 τ2} {e1 e1' : Γ ⊢ τ1} {e2 e2' : Γ ⊢ τ2} :
  ValueP e1' → (e1 --->* e1') →
  ValueP e2' → (e2 --->* e2') → Fst (Pair e1 e2) --->* e1'.
Proof.
  intros.
  induction H; intros.
  - induction H0; intros.
    + apply multi_R.
      now constructor.
    + rewrite <- IHmulti at 2; auto.
      apply multistep_Fst1.
      apply multistep_Pair; eauto.
      constructor.
      now apply multi_R.
  - rewrite <- IHmulti; auto.
    apply multistep_Fst1; auto.
    apply multistep_Pair1; auto.
    now apply multi_R.
Qed.

Lemma multistep_Snd1 {Γ τ1 τ2} {p p' : Γ ⊢ (τ1 × τ2)} :
  (p --->* p') → Snd p --->* Snd p'.
Proof. now simpl_multistep. Qed.

Lemma multistep_SndPair {Γ τ1 τ2} {e1 e1' : Γ ⊢ τ1} {e2 e2' : Γ ⊢ τ2} :
  ValueP e1' → (e1 --->* e1') →
  ValueP e2' → (e2 --->* e2') → Snd (Pair e1 e2) --->* e2'.
Proof.
  intros.
  induction H; intros.
  - induction H0; intros.
    + apply multi_R.
      now constructor.
    + rewrite <- IHmulti; auto.
      apply multistep_Snd1.
      apply multistep_Pair; eauto.
      constructor.
      now apply multi_R.
  - rewrite <- IHmulti; auto.
    apply multistep_Snd1; auto.
    apply multistep_Pair1; auto.
    now apply multi_R.
Qed.

Lemma multistep_Cons1 {Γ τ} {x x' : Γ ⊢ τ} {xs : Γ ⊢ (TyList τ)} :
  (x --->* x') → Cons x xs --->* Cons x' xs.
Proof. now simpl_multistep. Qed.

Lemma multistep_Cons2 {Γ τ} {x : Γ ⊢ τ} {xs xs' : Γ ⊢ (TyList τ)} :
  ValueP x → (xs --->* xs') → Cons x xs --->* Cons x xs'.
Proof. now simpl_multistep. Qed.

Lemma multistep_Cons {Γ τ} {e1 e1' : Γ ⊢ τ} {e2 e2' : Γ ⊢ (TyList τ)} :
  ValueP e1' →
  (e1 --->* e1') → (e2 --->* e2') → Cons e1 e2 --->* Cons e1' e2'.
Proof.
  intros.
  induction H; intros.
  - now apply multistep_Cons2; auto.
  - rewrite <- IHmulti; auto.
    apply multistep_Cons1; auto.
    now econstructor; eauto.
Qed.

Lemma multistep_Car1 {Γ τ} {d d' : Γ ⊢ τ} {xs : Γ ⊢ (TyList τ)} :
  (d --->* d') → Car d xs --->* Car d' xs.
Proof. now simpl_multistep. Qed.

Lemma multistep_Car2 {Γ τ} {d : Γ ⊢ τ} {xs xs' : Γ ⊢ (TyList τ)} :
  ValueP d → (xs --->* xs') → Car d xs --->* Car d xs'.
Proof. now simpl_multistep. Qed.

Lemma multistep_Car {Γ τ} {d d' : Γ ⊢ τ} {xs xs' : Γ ⊢ (TyList τ)} :
  ValueP d' →
  (d --->* d') → (xs --->* xs') → Car d xs --->* Car d' xs'.
Proof.
  intros.
  induction H; intros.
  - now apply multistep_Car2.
  - rewrite <- IHmulti; eauto.
    apply multistep_Car1; auto.
    now econstructor; eauto.
Qed.

Lemma multistep_CarNil {Γ τ} {d d' : Γ ⊢ τ} {xs : Γ ⊢ (TyList τ)} :
  ValueP d' → (d --->* d') →
  (xs --->* Nil) → Car d xs --->* d'.
Proof.
  intros.
  dependent induction H.
  - erewrite multistep_Car2; eauto.
    apply multi_R.
    now constructor.
  - rewrite <- IHmulti; eauto.
    apply multistep_Car1.
    now apply multi_R.
Qed.

Lemma multistep_CarCons {Γ τ} {d e1 : Γ ⊢ τ} {e2 xs : Γ ⊢ (TyList τ)} :
  ValueP d → ValueP e1 → ValueP e2 →
  (xs --->* Cons e1 e2) → Car d xs --->* e1.
Proof.
  intros.
  dependent induction H.
  - erewrite multistep_Car2; eauto.
    + apply multi_R.
      now constructor; eauto.
    + now constructor; eauto.
  - specialize (IHmulti L _ _ d _ _ _ X X0 X1
                        eq_refl JMeq_refl JMeq_refl JMeq_refl).
    rewrite <- IHmulti; auto.
    apply multistep_Car2; auto.
    now apply multi_R.
Fail Qed.
Admitted.

Lemma multistep_Cdr1 {Γ τ} {xs xs' : Γ ⊢ (TyList τ)} :
  (xs --->* xs') → Cdr xs --->* Cdr xs'.
Proof. now simpl_multistep. Qed.

Lemma multistep_CdrNil {Γ τ} {xs : Γ ⊢ (TyList τ)} :
  (xs --->* Nil) → Cdr xs --->* Nil.
Proof.
  intros.
  dependent induction H.
  - apply multi_R.
    now constructor.
  - rewrite <- IHmulti; eauto.
    apply multi_R.
    now constructor.
Qed.

Lemma multistep_CdrCons {Γ τ} {e1 : Γ ⊢ τ} {e2 xs : Γ ⊢ (TyList τ)} :
  ValueP e1 → ValueP e2 →
  (xs --->* Cons e1 e2) → Cdr xs --->* e2.
Proof.
  intros.
  dependent induction H.
  - apply multi_R.
    now constructor.
  - specialize (IHmulti L _ _ _ _ y X X0
                        eq_refl JMeq_refl JMeq_refl JMeq_refl).
    rewrite <- IHmulti.
    apply multistep_Cdr1.
    now apply multi_R.
Fail Qed.
Admitted.

(*
Lemma multistep_CdrCons {Γ τ} {e1 e1' : Γ ⊢ τ} {e2 e2' : Γ ⊢ (TyList τ)} :
  ValueP e1' → (e1 --->* e1') →
  ValueP e2' → (e2 --->* e2') → Cdr (Cons e1 e2) --->* e2'.
Proof.
  intros.
  induction H; intros.
  - induction H0; intros.
    + apply multi_R.
      now constructor.
    + rewrite <- IHmulti; auto.
      apply multistep_Cdr1.
      apply multistep_Cons2; eauto.
      now apply multi_R.
  - rewrite <- IHmulti; auto.
    apply multistep_Cdr1; auto.
    apply multistep_Cons1; auto.
    now apply multi_R.
Qed.
*)

Lemma multistep_App2 {Γ dom cod} {e e' : Γ ⊢ dom} {v : Γ ⊢ (dom ⟶ cod)} :
  ValueP v → (e --->* e') → APP v e --->* APP v e'.
Proof. now simpl_multistep. Qed.

#[export]
Program Instance multi_Step_respects {Γ τ} :
  Proper (multi Step --> multi Step ==> impl) (multi (Step (Γ:=Γ) (τ:=τ))).
Next Obligation.
  generalize dependent y0.
  generalize dependent y.
  induction H1; intros; eauto;
  unfold flip in *.
  - now transitivity x.
  - pose proof (multi_step _ _ _ _ H H1).
    pose proof (multi_trans _ _ _ _ H0 H3).
    now transitivity z.
Qed.

Lemma SubExp_SN {Γ Γ'} (env : Sub Γ' Γ) {τ} (e : Exp Γ τ) :
  SN_Sub env →
  SN (SubExp env e).
Proof.
  generalize dependent env.
  induction e; intros; simpl.
  - admit.
  - admit.
  - admit.
  - now eexists; repeat constructor.
  - now eexists; repeat constructor.
  - now eexists; repeat constructor.
  - destruct (SN_halts (IHe1 env H)) as [v [P [Q]]].
    apply (multistep_preserves_SN'
             (e':=If v (SubExp env e2) (SubExp env e3))); auto.
    + now apply multistep_If.
    + inv Q; simpl.
      * apply (step_preserves_SN' (e':=SubExp env e2)); auto.
        now constructor.
      * apply (step_preserves_SN' (e':=SubExp env e3)); auto.
        now constructor.
  - split.
    + destruct (SN_halts (IHe1 env H)) as [v1 [P1 [Q1]]].
      destruct (SN_halts (IHe2 env H)) as [v2 [P2 [Q2]]].
      exists (Pair v1 v2).
      split.
      * now apply multistep_Pair.
      * now repeat constructor.
    + split.
      * destruct (SN_halts (IHe1 env H)) as [v1 [P1 [Q1]]].
        destruct (SN_halts (IHe2 env H)) as [v2 [P2 [Q2]]].
        apply (multistep_preserves_SN' (e':=v1)); auto.
        ** now eapply multistep_FstPair; eauto.
        ** apply (multistep_preserves_SN (e:=SubExp env e1));
           now intuition.
      * destruct (SN_halts (IHe1 env H)) as [v1 [P1 [Q1]]].
        destruct (SN_halts (IHe2 env H)) as [v2 [P2 [Q2]]].
        apply (multistep_preserves_SN' (e':=v2)); auto.
        ** now eapply multistep_SndPair; eauto.
        ** apply (multistep_preserves_SN (e:=SubExp env e2));
           now intuition.
  - now destruct (IHe env H).
  - now destruct (IHe env H).
  - now eexists; repeat constructor.
  - destruct (SN_halts (IHe1 env H)) as [v1 [P1 [Q1]]].
    destruct (SN_halts (IHe2 env H)) as [v2 [P2 [Q2]]].
    exists (Cons v1 v2).
    split.
    * now apply multistep_Cons.
    * now repeat constructor.
  - destruct (SN_halts (IHe1 env H)) as [v1 [P1 [Q1]]].
    destruct (SN_halts (IHe2 env H)) as [v2 [P2 [Q2]]].
    inv Q2.
    + apply (multistep_preserves_SN' (e':=v1)); auto.
      * now eapply multistep_CarNil.
      * apply (multistep_preserves_SN (e:=SubExp env e1));
        now intuition.
    + apply (multistep_preserves_SN' (e':=x)); auto.
      * erewrite multistep_Car1; eauto.
        now eapply multistep_CarCons; eauto.
      * admit.
  - destruct (SN_halts (IHe env H)) as [v [P [Q]]].
    inv Q.
    + exists Nil.
      split.
      * now apply multistep_CdrNil.
      * now repeat constructor.
    + exists xs.
      split.
      * now eapply multistep_CdrCons; eauto.
      * now repeat constructor.
  - eapply step_preserves_SN'; eauto.
    now constructor.
  - induction env.
    + now inv v.
    + simpl in *.
      inv H.
      now dependent elimination v; simp SubVar.
  - eexists.
    + now eexists; repeat constructor.
    + intros.
      destruct (SN_halts H0) as [v [P [Q]]].
      apply (multistep_preserves_SN' (e':=SubExp (Push v env) e)); auto.
      eapply multi_trans; eauto.
      * eapply multistep_App2; eauto.
        now constructor.
      * apply multi_R; auto.
        rewrite SubExp_Push.
        now apply ST_AppAbs.
      * apply IHe.
        constructor; auto.
        now eapply multistep_preserves_SN; eauto.
  - now apply IHe1, IHe2.
Admitted.

Theorem Exp_SN {τ} (e : Exp [] τ) : SN e.
Proof.
  intros.
  replace e with (SubExp (Γ:=[]) NoSub e).
    apply SubExp_SN.
    now constructor.
  now rewrite NoSub_idSub, SubExp_idSub.
Qed.

Corollary strong_normalization {τ} (e : Exp [] τ) : e ⇓.
Proof.
  pose proof (Exp_SN e).
  induction τ; now simpl in H.
Qed.

End Norm.
