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

Lemma msubst_SN {Γ Γ'} (env : Sub Γ' Γ) τ (e : Exp Γ τ) :
  SN_Sub env →
  SN (SubExp env e).
Proof.
  generalize dependent env.
  induction e; intros.
  - admit.
  - admit.
  - admit.
  - rewrite msubst_EUnit.
    now eexists; repeat constructor.
  - rewrite msubst_ETrue.
    now eexists; repeat constructor.
  - rewrite msubst_EFalse.
    now eexists; repeat constructor.
  - rewrite msubst_If.
    admit.
  - rewrite msubst_Pair.
    admit.
  - rewrite msubst_Fst.
    now destruct (IHe env H).
  - rewrite msubst_Snd.
    now destruct (IHe env H).
  - rewrite msubst_Nil.
    now eexists; repeat constructor.
  - rewrite msubst_Cons.
    admit.
  - rewrite msubst_Car.
    admit.
  - rewrite msubst_Cdr.
    admit.
  - rewrite msubst_Seq.
    admit.
  - induction env.
    + now inv v.
    + inv H.
      dependent induction v.
      * now rewrite msubst_VAR_ZV.
      * rewrite msubst_VAR_SV.
        now apply IHenv.
  - rewrite msubst_LAM.
    admit.
  - rewrite msubst_APP.
    now apply IHe1, IHe2.
Admitted.

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
    ind-help : ∀ {Γ τ B}(SN : Exp Γ τ → Exp Γ B → Set)
             → (∀ {t u} → P t → P u
                 → (∀ {t'} → t ---> t' → SN t' u)
                 → (∀ {u'} → u ---> u' → SN t u')
                → SN t u)
             → ∀ {t u} → P t → P u → SN t u
    ind-help SN f (sn* tp tq) (sn* up uq) =
      f (sn* tp tq) (sn* up uq)
        (λ st → ind-help SN f (tq st) (sn* up uq))
        (λ st → ind-help SN f (sn* tp tq) (uq st))

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
  intros.
  replace e with (msubst idSub e) by reflexivity.
  now apply msubst_SN.
Qed.

End Norm.
