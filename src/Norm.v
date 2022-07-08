Require Import
  Coq.Unicode.Utf8
  Coq.Program.Program
  Coq.Relations.Relation_Definitions
  Coq.Classes.CRelationClasses
  Coq.Lists.List
  Ty
  Exp
  Sub
  Sem
  Eval.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Ltac reduce :=
  repeat (lazymatch goal with
          | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
              apply inj_pair2 in H; subst
          | [ H : _ ∧ _ |- _ ] => destruct H
          | [ H : _ * _ |- _ ] => destruct H
          | [ H : ∃ _, _ |- _ ] => destruct H
          | [ H : { _ : _ | _ } |- _ ] => destruct H
          | [ H : { _ : _ & _ } |- _ ] => destruct H
          end; subst).

Ltac inv H := inversion H; subst; clear H; reduce.

Section Norm.

Import ListNotations.

Context {A : Type}.
Context `{L : HostLang A}.

Definition normal_form {X : Type} (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'.

Theorem value_is_nf {Γ τ} (v : Exp Γ τ) :
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

Lemma App_Lam_loop {Γ τ ty} {v : Exp Γ ty} {e : Exp (ty :: Γ) τ} :
  ¬ (SubExp {||v||} e = APP (LAM e) v).
Proof.
  dependent induction e; repeat intro; inv H.
  - dependent induction v0; simp consSub in *.
    + simp SubVar in H1.
      now induction v; inv H1; intuition.
    + simp SubVar in H1.
      rewrite SubVar_idSub in H1.
      now induction v0; inv H1; intuition.
  - admit.
Admitted.

(* A term never reduces to itself. *)
Theorem Step_irr {Γ τ} {x : Exp Γ τ} : ¬ (x ---> x).
Proof.
  intro.
  dependent induction x; try solve [ now inv H ].
  - inv H.
    + now apply Reduce_irr in H4.
  - inv H.
    + now eapply If_loop_true; eauto.
    + now eapply If_loop_false; eauto.
    + now firstorder.
  - inv H.
    now eapply Seq_loop; eauto.
  - inv H.
    + now eapply CallHost_irr; eauto.
    + now eapply App_Lam_loop; eauto.
    + now eapply IHx1; eauto.
    + now eapply IHx2; eauto.
Qed.

Corollary Step_productive {Γ τ} {x x' : Exp Γ τ} : x ---> x' → x ≠ x'.
Proof.
  repeat intro; subst.
  now eapply Step_irr; eauto.
Qed.

Ltac invert_step :=
  try lazymatch goal with
  | [ H : _ ---> _ |- _ ] => now inv H
  end;
  try solve [ f_equal; intuition eauto | normality ].

Definition deterministic {X : Type} (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Lemma ValueP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ValueP v) :
  H1 = H2.
Proof.
  induction H1; dependent elimination H2; auto.
  - now erewrite IHValueP1, IHValueP2; eauto.
  - now erewrite IHValueP1, IHValueP2; eauto.
Qed.

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
  - now f_equal; apply ValueP_irrelevance.
Qed.

Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e + { e' | e ---> e' }.
Proof.
  dependent induction e.
  - destruct τ;
    right; now exists (projT1 (Reduce h)); constructor.
  - now left; constructor.
  - now left; constructor.
  - now left; constructor.
  - now left; constructor.
  - now left; constructor.
  - right.
    destruct (IHe1 _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); reduce.
    + inv v.
      * now exists e2; constructor.
      * now exists e3; constructor.
    + reduce.
      now exists (If x e2 e3); constructor.
  - destruct (IHe1 _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); reduce.
    + destruct (IHe2 _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); reduce.
      * left.
        now constructor.
      * right; reduce.
        now exists (Pair e1 x); constructor.
    + destruct (IHe2 _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); reduce.
      * right; reduce.
        now exists (Pair x e2); constructor.
      * right; reduce.
        now exists (Pair x e2); constructor.
  - destruct (IHe _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); reduce.
    + right.
      inv v; reduce.
      * now exists x; constructor.
    + right; reduce.
      now exists (Fst x); constructor.
  - destruct (IHe _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); reduce.
    + right.
      inv v.
      * now exists y; constructor.
    + right; reduce.
      now exists (Snd x); constructor.
  - now left; constructor.
  - destruct (IHe1 _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); clear IHe1.
    + destruct (IHe2 _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); clear IHe2.
      * now left; constructor.
      * right; reduce.
        now exists (Cons e1 x); constructor.
    + destruct (IHe2 _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); clear IHe2.
      * right; reduce.
        now exists (Cons x e2); constructor.
      * right; reduce.
        now exists (Cons x0 e2); constructor.
  - right.
    now exists e2; constructor.
  - now inversion v.
  - left.
    now constructor.
  - right.
    destruct (IHe1 _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); clear IHe1.
    + destruct (IHe2 _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); clear IHe2.
      * dependent elimination e1; inv v.
        ** now exists (CallHost h1 e2 v0); constructor.
        ** exists (SubExp {|| e2 ||} e11).
           now constructor.
      * dependent elimination e1; inv v.
        ** exists (APP (HostedFun h1) x); constructor; auto.
           now constructor.
        ** exists (APP (LAM e11) x).
           constructor; auto.
           now constructor.
    + reduce.
      destruct (IHe2 _ _ _ eq_refl JMeq_refl JMeq_refl JMeq_refl); clear IHe2.
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
  reduce.
  destruct H.
  now exists x.
Qed.

Corollary nf_same_as_value {τ} (v : Exp [] τ) :
  iffT (normal_form Step v) (ValueP v).
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
  ∃ e', e --->* e' ∧ inhabited (ValueP e').

Lemma value_halts {Γ τ} (v : Exp Γ τ) : ValueP v → halts v.
Proof.
  intros.
  unfold halts.
  now induction X; eexists; repeat constructor.
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
  R (τ:=TyHost _) e := halts e; (* jww (2022-07-07): should be an obligation *)
  R (τ:=TyUnit)   e := halts e;
  R (τ:=TyBool)   e := halts e;
  R (τ:=TyList _) e := halts e; (* jww (2022-07-07): NYI *)
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

Inductive SN {Γ τ} (e : Exp Γ τ) : Type :=
  | IsSN {e'} : e ---> e' → SN e' → SN e.

(*
Equations msubst {Γ Γ' τ} (e : Γ' ⊢ τ) (ss : Sub Γ Γ') : [] ⊢ τ :=
  msubst e NoSub       := e;
  msubst e (Push x xs) := msubst (SubExp {|| x ||} e) xs.

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

Lemma msubst_R : ∀ Γ (env : ExpEnv Γ) τ (t : Exp Γ τ),
  instantiation Γ env →
  R (msubst t env).
Proof.
*)

Lemma RenExp_ValueP {Γ Γ' τ} {v : Exp Γ τ} (σ : Ren Γ' Γ) :
  ValueP v → ValueP (RenExp σ v).
Proof.
  intros.
  now induction X; simpl; intros; try constructor.
Qed.

Lemma SubExp_ValueP {Γ Γ' τ} {v : Exp Γ τ} (σ : Sub Γ' Γ) :
  ValueP v → ValueP (SubExp σ v).
Proof.
  intros.
  now induction X; simpl; intros; try constructor.
Qed.

Lemma RenExp_Step {Γ Γ' τ} {e e' : Exp Γ τ} (σ : Ren Γ' Γ) :
  e ---> e' → RenExp σ e ---> RenExp σ e'.
Proof.
  intros.
  induction e; simpl; invert_step.
  - destruct τ;
    inv H; now apply Reduce_preserves_renaming.
  - now inv H; constructor; intuition.
  - inv H; simpl;
    constructor; intuition;
    now apply RenExp_ValueP.
  - inv H; constructor; intuition.
    + now apply RenExp_ValueP.
    + now apply RenExp_ValueP.
  - inv H; constructor; intuition.
    + now apply RenExp_ValueP.
    + now apply RenExp_ValueP.
  - inv H; constructor; intuition;
    now apply RenExp_ValueP.
  - now inv H; simpl; try constructor; intuition.
  - inv H; simpl; try constructor; intuition.
    + rewrite <- SubExp_ScR.
      simp ScR.
      rewrite <- RcS_idSub.
      pose proof (SubExp_RcS (Keep σ) (Push (RenExp σ e2) idSub) e0).
      simp RcS in H.
      rewrite H.
      constructor.
      now apply RenExp_ValueP.
    + now apply RenExp_ValueP.
Qed.

Lemma SubExp_Step {Γ Γ' τ} {e e' : Exp Γ τ} (σ : Sub Γ' Γ) :
  e ---> e' → SubExp σ e ---> SubExp σ e'.
Proof.
  intros.
  induction e; simpl; invert_step.
  - destruct τ;
    inv H; now apply Reduce_preserves_substitution.
  - now inv H; constructor; intuition.
  - inv H; simpl;
    constructor; intuition;
    now apply SubExp_ValueP.
  - inv H; constructor; intuition.
    + now apply SubExp_ValueP.
    + now apply SubExp_ValueP.
  - inv H; constructor; intuition.
    + now apply SubExp_ValueP.
    + now apply SubExp_ValueP.
  - inv H; constructor; intuition;
    now apply SubExp_ValueP.
  - now inv H; simpl; try constructor; intuition.
  - inv H; simpl; try constructor; intuition.
    + rewrite <- SubExp_ScS.
      simpl ScS.
      rewrite ScS_idSub_left.
      pose proof (SubExp_ScS (Keepₛ σ) (Push (SubExp σ e2) idSub) e0).
      simpl in H.
      simp SubVar in H.
      unfold Dropₛ in H.
      rewrite ScS_ScR in H.
      rewrite RcS_skip1 in H.
      rewrite ScS_idSub_right in H.
      rewrite H.
      constructor.
      now apply SubExp_ValueP.
    + now apply SubExp_ValueP.
Qed.

(*
Equations RenExp_Step {Γ Γ' τ} {e : Exp Γ τ} {σ : Ren Γ' Γ} {e'}
          (S : RenExp σ e ---> e') :
  ∃ e'', e ---> e'' ∧ RenExp σ e'' = e' :=
  RenExp_Step (e:=APP (VAR v) a)     (ST_App2 _ _ _ _ _ _ _ step)       with RenExp_Step step := {
    | exist _ e'' (conj p eq_refl) => exist _ (APP (VAR v) e'') (conj (ST_App2 _ _ _ _ _ _ _  p) eq_refl)
  };
  RenExp_Step (e:=APP (LAM f) a) (σ:=σ) (ST_AppAbs _ _ _ _ _ _) := _;
    (* SubExp (idₛ , a) f , β _ _ , Tm-ₛ∘ₑ (idₛ , a) σ f ⁻¹ ◾ (λ x →  SubExp (x , RenExp σ a) f) & (idrₑₛ σ ⁻¹) ◾ Tm-ₑ∘ₛ (keep σ) (idₛ , RenExp σ a) f *)
  RenExp_Step (e:=APP (LAM f) a)     (ST_App1 _ _ _ _ _ _ (LAM step)) with RenExp_Step step := {
    | exist _ e'' (conj p eq_refl) => exist _ (APP (LAM e'') a) (conj (app₁ (lam p)) eq_refl)
  };
  RenExp_Step (e:=APP (LAM f) a)     (ST_App2 _ _ _ _ _ _ _ step)       with RenExp_Step step := {
    | exist _ e'' (conj p eq_refl) => exist _ (APP (LAM f) e'') (conj (app₂ p) eq_refl)
  };
  RenExp_Step (e:=APP (APP f a) a')  (ST_App1 _ _ _ _ _ _ step)       with RenExp_Step step := {
    | exist _ e'' (conj p eq_refl) => exist _ (APP e'' a') (conj (app₁ p) eq_refl)
  };
  RenExp_Step (e:=APP (APP f a) a'') (ST_App2 _ _ _ _ _ _ _ step)       with RenExp_Step step := {
    | exist _ e'' (conj p eq_refl) => exist _ (APP (APP f a) e'') (conj (ST_App2 _ _ _ _ _ _ _ p) eq_refl)
  }.
*)

Lemma RenExp_Step_trans {Γ Γ' τ} {e : Exp Γ τ} {σ : Ren Γ' Γ} {e'} :
  RenExp σ e ---> e' →
  ∃ e'', e ---> e'' ∧ RenExp σ e'' = e'.
Proof.
  intros.
  generalize dependent Γ'.
  induction e; simpl; intros; try solve [ inv H ].
(*
  (* Hosted *)
  -
  (* If *)
  -
  (* Pair *)
  -
  (* Fst *)
  - inv H.
    + destruct (IHe _ _ _ H3); reduce.
      exists (Fst x).
      split; now constructor.
    +
  (* Snd *)
  -
  (* Seq *)
  -
  (* App *)
  -
*)
Admitted.

(*
-- Strong normalization
--------------------------------------------------------------------------------

-- SN annotated all the way down with a predicate on terms
data SN* {τ} (P : ∀ {Γ} → Exp Γ τ → Set) {Γ}(t : Exp Γ τ) : Set where
  sn* : P t → (∀ {t'} → t ---> t' → SN* P t') → SN* P t

SN*-SN : ∀ {Γ τ}{P : ∀ {Γ} → Exp Γ τ → Set}{t : Exp Γ τ} → SN* P t → SN t
SN*-SN (sn* p q) = sn (λ st → SN*-SN (q st))


Expᴾ : ∀ {τ Γ} → Exp Γ τ → Set
Expᴾ {Γ = Γ} (lam t) =
  ∀ {Γ'}(σ : Ren Γ' Γ){u} → SN* Expᴾ u → SN* Expᴾ (SubExp (idₛ ₛ∘ₑ σ , u) t)
Expᴾ _ = ⊤

-- the actual induction predicate used in the "fundamental theorem"
P : ∀ {τ Γ} → Exp Γ τ → Set
P = SN* Expᴾ

Expᴾₑ : ∀ {Γ Γ' τ}(σ : Ren Γ Γ'){t : Exp Γ' τ} → Expᴾ t → Expᴾ (RenExp σ t)
Expᴾₑ σ {lam t} tᴾ =
  λ δ {u} uᴾ → coe (P & ((λ x → SubExp (u :: x) t) &
                   ((assₛₑₑ idₛ σ δ ⁻¹ ◾ (_ₛ∘ₑ δ) & idrₑₛ σ ⁻¹) ◾ assₑₛₑ σ idₛ δ)
                     ◾ Tm-ₑ∘ₛ _ _ t))
                   (tᴾ (σ ∘ₑ δ) uᴾ)
Expᴾₑ σ {var _} tᴾ = tt
Expᴾₑ σ {app _ _} tᴾ = tt

P---> : ∀ {Γ τ}{t t' : Exp Γ τ} → t ---> t' → P t → P t'
P---> st (sn* p q) = q st

Pₑ : ∀ {Γ Γ' τ}(σ : Ren Γ Γ'){t : Exp Γ' τ} → P t → P (RenExp σ t)
Pₑ σ (sn* p q) =
  sn* (Expᴾₑ σ p) λ st → case RenExp_Step st of λ {(t'' , st' , refl) → Pₑ σ (q st')}

P-lam : ∀ {Γ τ B}{t : Exp (τ :: Γ) B} → Expᴾ (lam t) → P t → P (lam t)
P-lam lamtᴾ (sn* p q) =
  sn* lamtᴾ (λ {(lam st) → P-lam (λ σ uᴾ → P---> (SubExp_Step _ st) (lamtᴾ σ uᴾ) ) (q st)})

P-app : ∀ {Γ τ B}{t : Exp Γ (τ ⟶ B)}{u : Exp Γ τ} → P t → P u → P (app t u)
P-app =
  ind-help
    (λ t u → P (app t u))
    (λ { {t} {u} (sn* tp tq) uᴾ f g →
      sn* tt (λ {(β t t')  → coe ((λ x → P (SubExp (u :: x) t)) & (idrₑₛ _ ⁻¹ ◾ idlₑₛ _))
                                (tp idRen uᴾ) ;
                (app₁ st) → f st ;
                (app₂ st) → g st})})
  where
    ind-help : ∀ {Γ τ B}(R : Exp Γ τ → Exp Γ B → Set)
             → (∀ {t u} → P t → P u
                 → (∀ {t'} → t ---> t' → R t' u)
                 → (∀ {u'} → u ---> u' → R t u')
                → R t u)
             → ∀ {t u} → P t → P u → R t u
    ind-help R f (sn* tp tq) (sn* up uq) =
      f (sn* tp tq) (sn* up uq)
        (λ st → ind-help R f (tq st) (sn* up uq))
        (λ st → ind-help R f (sn* tp tq) (uq st))

data Subᴾ {Γ} : ∀ {Γ'} → Sub Γ Γ' → Set where
  NoSubᴾ : Subᴾ NoSub
  _,_ : ∀ {τ Γ'}{σ : Sub Γ Γ'}{t : Exp Γ τ}(σᴾ : Subᴾ σ)(tᴾ : P t) → Subᴾ (t :: σ)

Subᴾₑ : ∀ {Γ Γ' Γ''}{σ : Sub Γ' Γ''}(δ : Ren Γ Γ') → Subᴾ σ → Subᴾ (σ ₛ∘ₑ δ)
Subᴾₑ σ NoSub    = NoSubᴾ
Subᴾₑ σ (δ , tᴾ) = Subᴾₑ σ δ , Pₑ σ tᴾ

-- "fundamental theorem"
fth : ∀ {Γ τ}(t : Exp Γ τ) → ∀ {Γ'}{σ : Sub Γ' Γ} → Subᴾ σ → P (SubExp σ t)
fth (var ZV) (σᴾ , tᴾ) = tᴾ
fth (var (SV x)) (σᴾ , tᴾ) = fth (var x) σᴾ
fth (lam t) {Γ'}{σ} σᴾ =
  P-lam (λ δ {u} uᴾ →
          coe (P & ((λ x → SubExp (u :: x) t)&
                       ((((_ₛ∘ₑ δ) & (idrₛ σ ⁻¹) ◾ assₛₛₑ σ idₛ δ)
                       ◾ (σ ∘ₛ_) & idlₑₛ (idₛ ₛ∘ₑ δ) ⁻¹)
                       ◾ assₛₑₛ σ skip1 (idₛ ₛ∘ₑ δ , u) ⁻¹) ◾ Tm-∘ₛ _ _ t))
              (fth t (Subᴾₑ δ σᴾ , uᴾ)))
        (fth t (Subᴾₑ skip1 σᴾ , sn* tt (λ ())))
fth (app t u) σᴾ = P-app (fth t σᴾ) (fth u σᴾ)

idₛᴾ : ∀ {Γ} → Subᴾ (idₛ {Γ})
idₛᴾ {[]}     = NoSubᴾ
idₛᴾ {τ :: Γ} = Subᴾₑ skip1 idₛᴾ , sn* tt (λ ())

*)

Theorem strong_normalization {Γ τ} (e : Exp Γ τ) : SN e.
Proof.
Abort.
(*
strongNorm t = coe (SN & Tm-idₛ t) (SN*-SN (fth t idₛᴾ))
*)

End Norm.

Notation " t '--->*' t' " := (multi Step t t') (at level 40).
