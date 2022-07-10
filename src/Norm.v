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

(** [SN] is a logical predicate that establishes the evidence needing to show
    halting. *)

Equations SN {Γ τ} (e : Γ ⊢ τ) : Prop :=
  SN (τ:=_ ⟶ _) f := f ⇓ ∧ (∀ x, SN x → SN (APP f x));
  SN (τ:=_ × _) p := p ⇓ ∧ SN (Fst p) ∧ SN (Snd p);
  SN e := e ⇓.

Lemma SN_halts {Γ τ} {e : Γ ⊢ τ} : SN e → halts e.
Proof. intros; induction τ; simp SN in H; now reduce. Qed.

Lemma step_preserves_SN {Γ τ} {e e' : Γ ⊢ τ} :
  (e ---> e') → SN e → SN e'.
Proof.
  intros.
  induction τ; simp SN in *;
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
  induction τ; simp SN in *;
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

Lemma multistep_App2 {Γ dom cod} {e e' : Γ ⊢ dom} {v : Γ ⊢ (dom ⟶ cod)} :
  ValueP v → (e --->* e') → APP v e --->* APP v e'.
Proof.
  intros.
  induction H.
  - now apply multi_refl.
  - eapply multi_step; eauto.
    now constructor.
Qed.

Inductive SN_Sub : ∀ {Γ Γ'}, Sub Γ' Γ → Prop :=
  | NoSub_SN {Γ} : SN_Sub (NoSub (Γ:=Γ))
  | Push_SN {Γ Γ' τ} (e : Exp Γ' τ) (s : Sub Γ' Γ) :
    SN e → SN_Sub s → SN_Sub (Push e s).

Lemma SubExp_Push {Γ Γ' τ ty} (x : Exp Γ' ty) (s : Sub Γ' Γ) (e : Exp (ty :: Γ) τ) :
  SubExp (Push x s) e = SubExp {||x||} (SubExp (Keepₛ s) e).
Proof.
Admitted.

Lemma SubExp_SN {Γ Γ'} (env : Sub Γ' Γ) τ (e : Exp Γ τ) :
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
  - admit.
  - admit.
  - now destruct (IHe env H).
  - now destruct (IHe env H).
  - now eexists; repeat constructor.
  - admit.
  - admit.
  - admit.
  - admit.
  - induction env.
    + now inv v.
    + inv H.
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

Theorem strong_normalization {τ} (e : Exp [] τ) : SN e.
Proof.
  intros.
  replace e with (SubExp (Γ:=[]) NoSub e).
    apply SubExp_SN.
    now constructor.
  now rewrite NoSub_idSub, SubExp_idSub.
Qed.

End Norm.
