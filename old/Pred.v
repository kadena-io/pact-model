Require Import
  Coq.ZArith.ZArith
  Coq.Logic.PropExtensionality
  Hask.Control.Monad
  Data.Either
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

Definition state : Type := PactState.

Definition hprop   : Type := state → Prop.
Definition vprop τ : Type := SemTy (m:=PactM) τ → hprop.
Definition eprop   : Type := Err → Prop.

Implicit Type H : hprop.
Implicit Type Z : eprop.

Definition hoare H `(e : expM τ) (Q : vprop τ) Z : Prop :=
  ∀ (s : state), H s ->
  match e s : Err + ⟦τ⟧ * state with
  | inr (v, s') => Q v s'
  | inl err => Z err
  end.

Declare Scope pred_scope.
Open Scope pred_scope.

Notation "{{ H }} x ← e { Q | Z }" :=
  (hoare H e (λ x, Q) Z) (at level 1, e at next level) : pred_scope.

#[local] Hint Unfold hoare : core.

Theorem hoare_post_true H `(Q : vprop τ) Z e :
  (∀ v s, Q v s) →
  (∀ err, Z err) →
  {{H}} x ← e {Q x|Z}.
Proof.
  unfold hoare; sauto.
Qed.

Theorem hoare_pre_false H `(Q : vprop τ) Z e :
  (∀ s, ¬ (H s)) →
  {{H}} x ← e {Q x|Z}.
Proof.
  unfold hoare; sauto.
Qed.

Definition hprop_conj (H H' : hprop) : hprop :=
  λ st, H st ∧ H' st.

Arguments hprop_conj _ _ /.

#[local] Hint Unfold hprop_conj : core.

Notation "Q \∧ H" := (hprop_conj Q H) (at level 10) : pred_scope.

Definition quadruple
  (H : hprop)
  `(e : expM τ)
  (Q : vprop τ)
  (Z : eprop) : Prop :=
  ∀ H', {{ H \∧ H' }} x ← e { Q x \∧ H' | Z }.

#[local] Hint Unfold quadruple : core.

Theorem frame_rule {H} `{e : expM τ} {Q : vprop τ} {Z H'} :
  quadruple H e Q Z →
  quadruple (H \∧ H') e (λ x, Q x \∧ H') Z.
Proof.
  unfold quadruple, hoare.
  intros.
  destruct H1, H1.
  pose proof (H0 _ _ (conj H1 H3)).
  pose proof (H0 _ _ (conj H1 H2)).
  sauto lq: on.
Qed.

Definition WP : Type :=
  ∀ τ (e : expM τ) (Q : vprop τ) (Z : eprop), hprop.

Definition wp `(e : expM τ) (Q : vprop τ) (Z : eprop) : hprop :=
  λ st, ∃ (H : hprop), (H \∧ (λ _, quadruple H e Q Z) st).

#[local] Hint Unfold wp : core.

Definition himpl (P Q : hprop) : Prop :=
  ∀ s, P s → Q s.

#[local] Hint Unfold himpl : core.

Notation "P ==> Q" :=
  (himpl P Q) (at level 55, Q at level 55) : pred_scope.

Definition vimpl {τ} (Q R : vprop τ) : Prop :=
  ∀ v, Q v ==> R v.

#[local] Hint Unfold vimpl : core.

Notation "Q ===> R" := (vimpl Q R) (at level 55) : pred_scope.

Theorem wp_equiv {H} `{e : expM τ} {Q : vprop τ} {Z} :
  (H ==> wp e Q Z) ↔ (quadruple H e Q Z).
Proof.
  unfold wp, quadruple, hoare, hprop_conj.
  split; intros.
  - reduce.
    specialize (H0 _ H1).
    simpl in H0.
    reduce.
    unshelve epose proof (H3 _ _ (conj _ H2)); auto.
  - exists H.
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
  (∀ H τ (e : expM τ) (Q : vprop τ) Z,
     quadruple H e Q Z ↔ H ==> wp1 _ e Q Z) →
  (∀ H τ (e : expM τ) (Q : vprop τ) Z,
     quadruple H e Q Z ↔ H ==> wp2 _ e Q Z) →
  wp1 = wp2.
Proof.
  intros.
  extensionality τ.
  extensionality e.
  extensionality Q.
  extensionality Z.
  apply himpl_antisym.
  - destruct (H0 (wp1 τ e Q Z) τ e Q Z) as [H5 H6]; clear H0.
    apply H5; intros.
    apply H.
    reflexivity.
  - destruct (H (wp2 τ e Q Z) τ e Q Z) as [H5 H6]; clear H.
    apply H5; intros.
    apply H0.
    reflexivity.
Qed.

Theorem quadruple_conseq {τ} {e : expM τ} {H' H} {Q' Q : vprop τ} {Z} :
  quadruple H' e Q' Z →
  H ==> H' →
  Q' ===> Q →
  quadruple H e Q Z.
Proof.
  intros.
  repeat intro.
  destruct H3.
  specialize (H1 _ H3).
  specialize (H0 _ _ (conj H1 H4)).
  matches.
  reduce.
  unfold hprop_conj in *.
  intuition.
Qed.

#[export]
Program Instance vimpl_PreOrder {τ} : PreOrder (vimpl (τ:=τ)).
Next Obligation. now apply H0, H. Qed.

Theorem wp_from_weakest_pre (wp' : WP) :
  (∀ H τ (e : expM τ) (Q : vprop τ) Z,
     quadruple (wp' _ e Q Z) e Q Z) →          (* wp_pre *)
  (∀ H τ (e : expM τ) (Q : vprop τ) Z,
     quadruple H e Q Z → H ==> wp' _ e Q Z) → (* wp_weakest *)
  (∀ H τ (e : expM τ) (Q : vprop τ) Z,
     H ==> wp' _ e Q Z ↔ quadruple H e Q Z).  (* wp_equiv *)
Proof.
  intros M1 M2.
  split; intro M.
  - eapply quadruple_conseq; eauto.
  - eapply M2; eauto.
Qed.

Notation "e =====> e'" :=
  (∀ Q Z, wp e Q Z ==> wp e' Q Z) (at level 100, e' at next level) : pred_scope.

Lemma eval_if_trm (t0 : Exp [] 𝔹) v0 {τ} (t1 t2 : Exp [] τ)
  (v : SemTy τ) s s' s'' :
  t0 ~[s => s']~> v0 →
  If (Lit (LitBool v0)) t1 t2 ~[s' => s'']~> v →
  If t0 t1 t2 ~[s => s'']~> v.
Proof.
  unfold eval.
  intros.
  simp SemExp in *; simpl in *; autounfold in *.
  now rewrite H.
Qed.

Lemma hoare_if H (b : Exp [] 𝔹) τ (t1 t2 : Exp [] τ)
  (Q' : vprop 𝔹) (Q : vprop τ) Z :
  hoare H ⟦b⟧ Q' Z →
  (∀ v, hoare (Q' v) ⟦If (Lit (LitBool v)) t1 t2⟧ Q Z) →
  hoare H ⟦If b t1 t2⟧ Q Z.
Proof.
  autounfold.
  repeat intro.
  simp SemExp in *; simpl in *; autounfold in *.
  specialize (H0 _ H2).
  destruct (⟦b⟧ _) eqn:Heqe; auto.
  reduce.
  specialize (H1 _ _ H0).
  simp SemExp in *; simpl in *; autounfold in *.
  exact H1.
Qed.

Lemma quadruple_if H (b : Exp [] 𝔹) τ (t1 t2 : Exp [] τ)
  (Q' : vprop 𝔹) (Q : vprop τ) Z :
  quadruple H ⟦b⟧ Q' Z →
  (∀ v, quadruple (Q' v) ⟦If (Lit (LitBool v)) t1 t2⟧ Q Z) →
  quadruple H ⟦If b t1 t2⟧ Q Z.
Proof.
  unfold quadruple.
  intros.
  eapply hoare_if; eauto.
  intros.
  apply H1.
Qed.

Ltac wp r H :=
  intros;
  eapply wp_equiv;
  eapply H; eauto;
  eapply wp_equiv;
  subst; reflexivity.

(* An if statement simply propagates the environment. *)
Corollary wp_if (b : Exp [] 𝔹) τ (t1 t2 : Exp [] τ) (Q : vprop τ) Z :
  wp ⟦b⟧ (λ v, wp ⟦If (Lit (LitBool v)) t1 t2⟧ Q Z) Z
    ==> wp ⟦If b t1 t2⟧ Q Z.
Proof.
  unfold wp.
  simpl.
  repeat intro.
  destruct H as [H [HH H0]].
  exists H.
  split; auto.
  eapply quadruple_if; eauto; intros.
  simpl.
  unfold quadruple, hoare in *.
  intros.
  simpl in *.
  reduce.
  specialize (H0 _ _ (conj HH HH)).
  destruct (⟦b⟧ _);
  simp SemExp in *; simpl in *;
  unravel; reduce;
  exact (H3 _ _ (conj H1 H2)).
Qed.

Lemma quadruple_app_fun H `(v : Exp [] dom) x `(e : Exp [dom] cod)
  (Q : vprop cod) Z :
  (∀ s, v ~[ s => s ]~> x) →
  quadruple H ⟦ (x, tt) ⊨ e ⟧ Q Z →
  quadruple H ⟦APP (LAM e) v⟧ Q Z.
Proof.
  intros.
  repeat intro.
  specialize (H1 _ _ H2).
  simpl in *.
  erewrite sem_app_lam; eauto.
Qed.

Lemma wp_app_fun `(v : Exp [] dom) x `(e : Exp [dom] cod) :
  (∀ s, v ~[ s => s ]~> x) →
  ⟦ (x, tt) ⊨ e ⟧ =====> ⟦APP (LAM e) v⟧.
Proof. wp r quadruple_app_fun. Qed.

(* This encodes a boolean predicate in positive normal form. *)
Inductive Pred : Ty → Set :=
  | P_True : Pred 𝔹
  | P_False : Pred 𝔹
  | P_Eq {τ} : Pred τ → Pred τ → Pred 𝔹
  | P_Or : Pred 𝔹 → Pred 𝔹 → Pred 𝔹
  | P_And : Pred 𝔹 → Pred 𝔹 → Pred 𝔹.

#[local] Hint Constructors Pred : core.

(*
Equations wpc `(e : Exp [] τ) {τ'}
  (Q : SemTy (m:=PactM) τ → state → Pred τ') Z :
  state → Pred τ' :=
  wpc (Lit l) Q Z := Q (SemLit l);
  (* wpc (APP f v) Q Z := wp ⟦APP f v⟧ Q Z; *)
  wpc (Seq e1 e2) Q Z := wpc e1 (λ _, wpc e2 Q Z) Z;
  wpc (If b t e) Q Z :=
    wpc b (λ b', if b' then wpc t Q Z else wpc e Q Z) Z;
  wpc _ Q Z := _.
*)

(*
Equations wpc `(e : Exp [] τ) (Q : vprop τ) Z : hprop :=
  wpc (Lit l) Q Z := Q (SemLit l);
  wpc (APP f v) Q Z := wp ⟦APP f v⟧ Q Z;
  wpc (Seq e1 e2) Q Z := wpc e1 (λ _, wpc e2 Q Z) Z;
  wpc (If b t e) Q Z :=
    wpc b (λ b', if b' then wpc t Q Z else wpc e Q Z) Z;
  wpc _ Q Z := _.
*)

End Pred.
