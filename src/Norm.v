Set Warnings "-cannot-remove-as-expected".

Require Import
  Lib
  Ltac
  Ty
  Exp
  Value
  Ren
  Sub
  Log
  Sem
  Multi
  Lang
  Sound
  Step.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Norm.

Import ListNotations.

Context {A : Type}.
Context `{L : HostLang A}.

Definition normalizing `(R : relation X) : Prop :=
  ∀ t, ∃ t', multi R t t' ∧ normal_form R t'.

Definition halts {Γ τ} (e : Exp Γ τ) : Prop :=
  ∃ e', e --->* e' ∧ (ValueP e' ∨ ErrorP e').

Notation " e '⇓' " := (halts e) (at level 11).

Definition normal_form_of {Γ τ} (e e' : Exp Γ τ) : Prop :=
  (e --->* e' ∧ normal_form Step e').

Ltac normality :=
  exfalso;
  lazymatch goal with
    | [ H1 : ValueP ?X, H2 : ?X ---> ?Y |- False ] =>
        apply value_is_nf in H1; destruct H1;
        now exists Y
    | [ H1 : normal_form ?R ?X, H2 : ?R ?X ?Y |- False ] =>
        exfalso; now apply (H1 Y)
  end.

Ltac invert_step :=
  try lazymatch goal with
  | [ H : _ ---> _ |- _ ] => now inv H
  end;
  try solve [ f_equal; intuition eauto | normality ].

Lemma value_halts {Γ τ} (v : Exp Γ τ) : ValueP v → halts v.
Proof.
  intros X.
  unfold halts.
  now induction X; eexists; repeat constructor.
Qed.

Lemma error_halts {Γ τ} (v : Exp Γ τ) : ErrorP v → halts v.
Proof.
  intros X.
  unfold halts.
  now induction X; eexists; repeat constructor.
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
    now einduction P12; eauto.
  - apply IHP11; auto.
    inv P21.
    + now edestruct P22; eauto.
    + assert (y = y0) by now apply Step_deterministic with x.
      now subst.
Qed.

Lemma step_preserves_halting {Γ τ} (e e' : Exp Γ τ) :
  (e ---> e') → (halts e ↔ halts e').
Proof.
  intros.
  unfold halts.
  split.
  - intros [e'' [H1 [H2|H3]]].
    + destruct H1.
      * apply value_is_nf in H2.
        now edestruct H2; eauto.
      * rewrite (Step_deterministic _ _ _ _ _ H H0).
        now intuition eauto.
    + destruct H1.
      * apply error_is_nf in H3.
        now edestruct H3; eauto.
      * rewrite (Step_deterministic _ _ _ _ _ H H0).
        now intuition eauto.
  - intros [e'0 [H1 [H2|H3]]].
    + exists e'0.
      split; auto.
      now eapply multi_step; eauto.
    + exists e'0.
      split; auto.
      now eapply multi_step; eauto.
Qed.

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
  (* - eapply IHτ1; eauto. *)
  (*   now constructor. *)
  (* - eapply IHτ2; eauto. *)
  (*   now constructor. *)
  (* - eapply IHτ2; eauto. *)
  (*   now constructor. *)
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
  (* - eapply IHτ1; eauto. *)
  (*   now constructor. *)
  (* - eapply IHτ2; eauto. *)
  (*   now constructor. *)
  (* - eapply IHτ2; eauto. *)
  (*   now constructor. *)
Qed.

Lemma multistep_preserves_SN' {Γ τ} {e e' : Γ ⊢ τ} :
  (e --->* e') → SN e' → SN e.
Proof.
  intros.
  induction H; auto.
  now eapply step_preserves_SN'; eauto.
Qed.

Lemma ErrorP_SN {Γ τ} (e : Exp Γ τ) :
  ErrorP e → SN e.
Proof.
  intro H.
  induction H; simpl.
  now induction τ.
Qed.

Lemma SubExp_SN {Γ Γ'} (env : Sub Γ' Γ) {τ} (e : Exp Γ τ) :
  SN_Sub env →
  SN (SubExp env e).
Proof.
  generalize dependent env.
  induction e; intros; simpl.
  (* - *)
  (* - *)
  (* - *)
  (* - now eexists; repeat constructor. *)
  (* - now eexists; repeat constructor. *)
  (* - now eexists; repeat constructor. *)
  (* - destruct (SN_halts (IHe1 env H)) as [v [P [Q]]]. *)
  (*   apply (multistep_preserves_SN' *)
  (*            (e':=If v (SubExp env e2) (SubExp env e3))); auto. *)
  (*   + now apply multistep_If. *)
  (*   + inv Q; simpl. *)
  (*     * apply (step_preserves_SN' (e':=SubExp env e2)); auto. *)
  (*       now constructor. *)
  (*     * apply (step_preserves_SN' (e':=SubExp env e3)); auto. *)
  (*       now constructor. *)
  (* - split. *)
  (*   + destruct (SN_halts (IHe1 env H)) as [v1 [P1 [Q1]]]. *)
  (*     destruct (SN_halts (IHe2 env H)) as [v2 [P2 [Q2]]]. *)
  (*     exists (Pair v1 v2). *)
  (*     split. *)
  (*     * now apply multistep_Pair. *)
  (*     * now repeat constructor. *)
  (*   + split. *)
  (*     * destruct (SN_halts (IHe1 env H)) as [v1 [P1 [Q1]]]. *)
  (*       destruct (SN_halts (IHe2 env H)) as [v2 [P2 [Q2]]]. *)
  (*       apply (multistep_preserves_SN' (e':=v1)); auto. *)
  (*       ** now eapply multistep_FstPair; eauto. *)
  (*       ** apply (multistep_preserves_SN (e:=SubExp env e1)); *)
  (*          now intuition. *)
  (*     * destruct (SN_halts (IHe1 env H)) as [v1 [P1 [Q1]]]. *)
  (*       destruct (SN_halts (IHe2 env H)) as [v2 [P2 [Q2]]]. *)
  (*       apply (multistep_preserves_SN' (e':=v2)); auto. *)
  (*       ** now eapply multistep_SndPair; eauto. *)
  (*       ** apply (multistep_preserves_SN (e:=SubExp env e2)); *)
  (*          now intuition. *)
  (* - now destruct (IHe env H). *)
  (* - now destruct (IHe env H). *)
  (* - now eexists; repeat constructor. *)
  (* - destruct (SN_halts (IHe1 env H)) as [v1 [P1 [Q1]]]. *)
  (*   destruct (SN_halts (IHe2 env H)) as [v2 [P2 [Q2]]]. *)
  (*   exists (Cons v1 v2). *)
  (*   split. *)
  (*   * now apply multistep_Cons. *)
  (*   * now repeat constructor. *)
  (* - destruct (SN_halts (IHe1 env H)) as [v1 [P1 [Q1]]]. *)
  (*   destruct (SN_halts (IHe2 env H)) as [v2 [P2 [Q2]]]. *)
  (*   inv Q2. *)
  (*   + apply (multistep_preserves_SN' (e':=v1)); auto. *)
  (*     * now eapply multistep_CarNil. *)
  (*     * apply (multistep_preserves_SN (e:=SubExp env e1)); *)
  (*       now intuition. *)
  (*   + apply (multistep_preserves_SN' (e':=x)); auto. *)
  (*     * erewrite multistep_Car1; eauto. *)
  (*       now eapply multistep_CarCons; eauto. *)
  (*     * *)
  (* - destruct (SN_halts (IHe env H)) as [v [P [Q]]]. *)
  (*   inv Q. *)
  (*   + exists Nil. *)
  (*     split. *)
  (*     * now apply multistep_CdrNil. *)
  (*     * now repeat constructor. *)
  (*   + exists xs. *)
  (*     split. *)
  (*     * now eapply multistep_CdrCons; eauto. *)
  (*     * now repeat constructor. *)
  (* - destruct (SN_halts (IHe env H)) as [v [P [Q]]]. *)
  (*   inv Q. *)
  (*   + exists ETrue. *)
  (*     split. *)
  (*     * now apply multistep_IsNilNil. *)
  (*     * now repeat constructor. *)
  (*   + exists EFalse. *)
  (*     split. *)
  (*     * now eapply multistep_IsNilCons; eauto. *)
  (*     * now repeat constructor. *)
  (* - eapply step_preserves_SN'; eauto. *)
  (*   now constructor. *)
  - now apply ErrorP_SN.
  - induction env.
    + now inv v.
    + dependent elimination H.
      now dependent elimination v; simpl in *; simp SubVar.
  - split.
    + now eexists; repeat constructor.
    + intros.
      destruct (SN_halts H0) as [v [P [Q|R]]].
      * apply (multistep_preserves_SN' (e':=SubExp (Push v env) e)); auto.
        eapply multi_trans; eauto.
        ** eapply multistep_AppR; eauto.
           now constructor.
           intro.
           now inv H1; inv Q.
        ** apply multi_R; auto.
           rewrite SubExp_Push.
           now repeat econstructor.
        ** apply IHe.
           constructor; auto.
           now eapply multistep_preserves_SN; eauto.
      * inv R.
        apply (multistep_preserves_SN' (e':=Error m)); auto.
        ** remember (SubExp (Keepₛ env) e) as s; clear -P.
           inv P.
           *** apply multi_R.
               exact (StepError (Plug_AppR _ (LambdaP _)
                                           (Plug_Hole (Error m)))).
           *** pose proof (multi_step _ _ _ _ H H0); clear H H0.
               apply multistep_AppR_Error; auto.
               now constructor.
        ** now induction cod; intuition eauto.
  - now apply IHe1, IHe2.
Qed.

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
  pose proof (Exp_SN e) as H.
  now induction τ; intuition eauto.
Qed.

End Norm.
