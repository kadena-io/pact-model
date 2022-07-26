Require Import
  Coq.ZArith.ZArith
  Coq.Logic.PropExtensionality
  Hask.Control.Monad
  Hask.Data.Either
  Pact.ilist
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Value
  Pact.Ren
  Pact.Sub
  Pact.SemTy
  Pact.Lang
  Pact.Lang.Capability
  Pact.SemExp
  Coq.Classes.RelationClasses
  Coq.Classes.Morphisms
  Pact.Ltac.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Section Pred.

Definition env   : Type := PactEnv.
Definition state : Type := PactState.

Definition rprop   : Type := env → Prop.
Definition sprop   : Type := state → Prop.
Definition eprop   : Type := Err → Prop.
Definition vprop τ : Type := SemTy (m:=PactM) τ → sprop.

Implicit Type G : rprop.
Implicit Type H : sprop.
Implicit Type Z : eprop.

Definition hoare G H `(e : Exp [] τ) (Q : vprop τ) Z : Prop :=
  ∀ (r : env), G r →
  ∀ (s : state), H s ->
  match ⟦e⟧ r s : Err + ⟦τ⟧ * (state * _) with
  | inr (v, (s', _)) => Q v s'
  | inl err => Z err
  end.

Declare Scope pred_scope.
Open Scope pred_scope.

Notation "{ G & H } x ← e { Q | Z }" :=
  (hoare G H e (λ x, Q) Z) (at level 1, e at next level) : pred_scope.

#[local] Hint Unfold hoare : core.

Theorem hoare_post_true G H `(Q : vprop τ) Z e :
  (∀ v s, Q v s) →
  (∀ err, Z err) →
  { G & H } x ← e { Q x | Z }.
Proof.
  unfold hoare; sauto.
Qed.

Theorem hoare_pre_false G H `(Q : vprop τ) Z e :
  (∀ r, ¬ (G r)) ∨ (∀ s, ¬ (H s)) →
  { G & H } x ← e { Q x | Z }.
Proof.
  unfold hoare; sauto.
Qed.

Definition sprop_conj (H H' : sprop) : sprop :=
  λ st, H st ∧ H' st.

Arguments sprop_conj _ _ /.

#[local] Hint Unfold sprop_conj : core.

Notation "Q \∧ H" := (sprop_conj Q H) (at level 10) : pred_scope.

Definition quadruple
  (G : rprop)
  (H : sprop)
  `(e : Exp [] τ)
  (Q : vprop τ)
  (Z : eprop) : Prop :=
  ∀ H', { G & H \∧ H' } x ← e { Q x \∧ H' | Z }.

#[local] Hint Unfold quadruple : core.

Theorem frame_rule {G H} `{e : Exp [] τ} {Q Z H'} :
  quadruple G H e Q Z →
  quadruple G (H \∧ H') e (λ x, Q x \∧ H') Z.
Proof.
  unfold quadruple, hoare.
  intros.
  destruct H2, H2.
  pose proof (H0 _ _ H1 _ (conj H2 H4)).
  pose proof (H0 _ _ H1 _ (conj H2 H3)).
  sauto lq: on.
Qed.

Definition WP : Type :=
  ∀ τ (e : Exp [] τ) (Q : vprop τ) (Z : eprop), env → sprop.

Definition wp
  `(e : Exp [] τ)
  (Q : vprop τ)
  (Z : eprop) : env → sprop :=
  λ r st,
    ∃ (G : rprop) (H : sprop),
      G r ∧ (H \∧ (λ _, quadruple G H e Q Z) st).

#[local] Hint Unfold wp : core.

Definition himpl (P Q : sprop) : Prop :=
  ∀ s, P s → Q s.

#[local] Hint Unfold himpl : core.

Notation "P ==> Q" :=
  (himpl P Q) (at level 55, Q at level 55) : pred_scope.

Definition hrimpl (G : rprop) (P : sprop) (Q : env → sprop) : Prop :=
  ∀ r s, G r → P s → Q r s.

#[local] Hint Unfold hrimpl : core.

Notation "P =[ G ]=> Q" :=
  (hrimpl G P Q) (at level 55, G at level 55, Q at level 55) : pred_scope.

Lemma dehrimpl `(H : P =[ G ]=> Q) : ∀ r, G r → P ==> Q r.
Proof.
  unfold himpl, hrimpl in *.
  intuition.
Defined.

Lemma hrimplize `(H : ∀ r, G r → P ==> Q r) : P =[ G ]=> Q.
Proof.
  unfold himpl, hrimpl in *.
  intuition.
Defined.

Corollary dehrimpl_hrimplize `(H : ∀ r, G r → P ==> Q r) :
  dehrimpl (hrimplize H) = H.
Proof. reflexivity. Qed.

Corollary hrimplize_dehrimpl `(H : P =[ G ]=> Q) :
  hrimplize (dehrimpl H) = H.
Proof. reflexivity. Qed.

Definition qimpl {τ} (Q R : vprop τ) : Prop :=
  ∀ v, Q v ==> R v.

#[local] Hint Unfold qimpl : core.

Notation "Q ===> R" := (qimpl Q R) (at level 55) : pred_scope.

Theorem wp_equiv {G H} `{e : Exp [] τ} {Q Z} :
  (H =[G]=> wp e Q Z) ↔ (quadruple G H e Q Z).
Proof.
  unfold hrimpl, wp, quadruple, hoare, sprop_conj.
  split; intros.
  - reduce.
    specialize (H0 _ _ H1 H2).
    reduce.
    unshelve epose proof (H5 _ r _ s (conj _ H3)); auto.
  - exists G.
    exists H.
    split; auto.
Qed.

Lemma pred_ext_1 (A1 : Type) :
  ∀ (P Q : ∀ (x1 : A1), Prop),
    (forall x1, P x1 <-> Q x1) -> P = Q.
Proof.
  intros.
  extensionality x.
  now apply propositional_extensionality.
Qed.

Lemma himpl_refl {H} :
  H ==> H.
Proof. now repeat intro. Qed.

Lemma himpl_trans {H1 H2 H3} :
  (H1 ==> H2) →
  (H2 ==> H3) →
  (H1 ==> H3).
Proof.
  repeat intro.
  unfold himpl in *.
  intuition.
Qed.

#[export]
Program Instance himpl_PreOrder : PreOrder himpl.

Lemma himpl_antisym {H1 H2} :
  (H1 ==> H2) →
  (H2 ==> H1) →
  (H1 = H2).
Proof.
  unfold himpl.
  intros.
  apply pred_ext_1.
  sauto.
Qed.

Theorem wp_unique (wp1 wp2 : WP) :
  (∀ G H τ (e : Exp [] τ) Q Z,
     quadruple G H e Q Z ↔ H =[G]=> wp1 _ e Q Z) →
  (∀ G H τ (e : Exp [] τ) Q Z,
     quadruple G H e Q Z ↔ H =[G]=> wp2 _ e Q Z) →
  wp1 = wp2.
Proof.
  intros.
  extensionality τ.
  extensionality e.
  extensionality Q.
  extensionality Z.
  extensionality r.
  apply himpl_antisym.
  - destruct (H0 (λ r', r = r') (wp1 τ e Q Z r) τ e Q Z) as [H5 H6]; clear H0.
    eapply dehrimpl in H5; eauto.
    apply H; intros.
    subst.
    apply hrimplize; intros; subst.
    apply himpl_refl.
  - destruct (H (λ r', r = r') (wp2 τ e Q Z r) τ e Q Z) as [H5 H6]; clear H.
    eapply dehrimpl in H5; eauto.
    apply H0; intros.
    subst.
    apply hrimplize; intros; subst.
    apply himpl_refl.
Qed.

Theorem triple_conseq {G τ} {e : Exp [] τ} {H' Q' H Q Z} :
  quadruple G H' e Q' Z →
  H ==> H' →
  Q' ===> Q →
  quadruple G H e Q Z.
Proof.
  intros.
  repeat intro.
  destruct H4.
  specialize (H1 _ H4).
  specialize (H0 H'0 _ H3 _ (conj H1 H5)).
  matches.
  reduce.
  unfold sprop_conj in *.
  intuition.
Qed.

Lemma vimpl_refl {τ} {Q : vprop τ} :
  Q ===> Q.
Proof. now repeat intro. Qed.

Theorem wp_from_weakest_pre (wp' : WP) :
  (∀ G H τ (e : Exp [] τ) Q Z r,
     quadruple G (wp' _ e Q Z r) e Q Z) →          (* wp_pre *)
  (∀ G H τ (e : Exp [] τ) Q Z,
     quadruple G H e Q Z → ∀ r, G r → H ==> wp' _ e Q Z r) → (* wp_weakest *)
  (∀ G H τ (e : Exp [] τ) Q Z,
     ∀ r, G r → H ==> wp' _ e Q Z r ↔ quadruple G H e Q Z).  (* wp_equiv *)
Proof.
  intros M1 M2.
  split; intro M.
  - eapply triple_conseq; eauto.
  - eapply M2; eauto.
Qed.

#[local] Hint Unfold RWSE_join : core.
#[local] Hint Unfold RWSE_ap : core.
#[local] Hint Unfold Either_map : core.
#[local] Hint Unfold Tuple.first : core.
#[local] Hint Unfold Basics.compose : core.
#[local] Hint Unfold Datatypes.id : core.

Notation "G =====> H" :=
  (∀ Q Z r, wp G Q Z r ==> wp H Q Z r) (at level 100, H at next level) : pred_scope.

Lemma quadruple_if G H b τ (t1 t2 : Exp [] τ) Q Z :
  quadruple G H (if b then t1 else t2) Q Z →
  quadruple G H (If (Lit (LitBool b)) t1 t2) Q Z.
Proof.
  autounfold.
  repeat intro.
  reduce.
  simp SemExp; simpl.
  autounfold.
  specialize (H0 _ _ H1 _ (conj H2 H3)).
  destruct b; sauto.
Qed.

(* An if statement simply propagates the environment. *)
Lemma wp_if b τ (t1 t2 : Exp [] τ) :
  (if b then t1 else t2) =====> If (Lit (LitBool b)) t1 t2.
Proof.
  intros.
  apply (dehrimpl (G:=λ r', r = r')); eauto.
  eapply wp_equiv.
  apply quadruple_if.
  eapply wp_equiv.
  apply hrimplize; intros.
  subst.
  reflexivity.
Qed.

Lemma quadruple_app_fun G H `(v : Exp [] dom) `(e : Exp [dom] cod) Q Z :
  ValueP v →
  quadruple G H (SubExp {|| v ||} e) Q Z →
  quadruple G H (APP (LAM e) v) Q Z.
Proof.
  autounfold.
  simp SemExp; simpl.
  autounfold.
  intros.
  specialize (H1 _ _ H2 _ H3).
  autounfold.
  pose proof (SemExp_ValueP (Γ:=[]) tt H0).
  reduce.
  rewrite H4; simpl.
  rewrite NoSub_idSub in H1.
  erewrite SemExp_SubExp in H1; eauto.
  simpl in *.
  destruct (⟦ (x, ()) ⊨ e ⟧ r s); auto.
  reduce.
  intuition.
Qed.

(* This encodes a boolean predicate in positive normal form. *)
Inductive Pred Γ : ∀ {τ}, Γ ⊢ τ → Set :=
  | P_True : Pred (Γ:=Γ) (Lit (LitBool true))
  | P_Or {τ} {x y : Γ ⊢ τ} : Pred x → Pred y → Pred (Pair x y)
  | P_And {τ} {x y : Γ ⊢ τ} : Pred x → Pred y → Pred (Pair x y)

  | P_APP {dom cod} {e1 : Γ ⊢ (dom ⟶ cod)} {e2 : Γ ⊢ dom} :
    Pred e1 → Pred e2 → Pred (APP e1 e2)

  | P_Car {τ} {xs : Γ ⊢ (TyList τ)} :
    Pred xs → Pred (Car xs).

#[local] Hint Constructors Pred : core.

Inductive EnvPred : ∀ {Γ}, SemEnv Γ → Type :=
  | Empty : EnvPred (Γ:=[]) tt
  | Add {Γ τ} {e : Γ ⊢ τ} v se :
    Pred e → ⟦ se ⊨ e⟧ = pure v → EnvPred se →
    EnvPred (Γ:=τ :: Γ) (v, se).

End Pred.
