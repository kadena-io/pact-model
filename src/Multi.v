Require Import
  Lib
  Ty
  Exp
  Value
  Ren
  Sub
  Sem
  Step.

From Equations Require Import Equations.
Set Equations With UIP.

Section Multi.

Generalizable All Variables.

Import ListNotations.

Context {A : Type}.
Context `{S : HostExprsSem A}.

Inductive multi `(R : relation X) : relation X :=
  | multi_refl (x : X) : multi R x x
  | multi_step (x y z : X) :
      R x y → multi R y z → multi R x z.

Derive Signature for multi.

Theorem multi_R `(R : relation X) (x y : X) :
  R x y → multi R x y.
Proof.
  intros.
  eapply multi_step; eauto.
  now constructor.
Qed.

Theorem multi_trans `(R : relation X) (x y z : X) :
  multi R x y →
  multi R y z →
  multi R x z.
Proof.
  intros.
  induction H; auto.
  now eapply multi_step; eauto.
Qed.

#[export]
Program Instance multi_PreOrder `(R : relation X) :
  PreOrder (multi R).
Next Obligation. now constructor. Qed.
Next Obligation. now eapply multi_trans; eauto. Qed.

Notation " t '--->*' t' " := (multi Step t t') (at level 40).

#[export]
Program Instance multi_respects_Step {Γ τ} :
  Proper (Step --> Step ==> impl) (multi (Step (Γ:=Γ) (τ:=τ))).
Next Obligation.
  econstructor; eauto.
  generalize dependent y0.
  generalize dependent y.
  induction H1; intros; eauto.
  - now do 4 (econstructor; eauto).
  - unfold flip in *.
    now econstructor; eauto.
Qed.

#[export]
Program Instance multi_respects_multi `(R : relation X) :
  Proper (multi R --> multi R ==> impl) (multi R).
Next Obligation.
  unfold flip in *.
  transitivity x; eauto.
  now transitivity x0; eauto.
Qed.

(*
#[export]
Program Instance APP_respects_multi {Γ dom cod} (v : Exp Γ (dom ⟶ cod)) :
  ValueP v → Proper (multi Step ==> multi Step) (APP v).
Next Obligation.
  induction H0.
  - now apply multi_refl.
  - rewrite <- IHmulti; clear IHmulti H1.
    dependent elimination H.
    destruct (AppR_LAM (e:= e) H0).
*)

(*
Lemma multistep_Seq {Γ τ} {e1 : Γ ⊢ τ} {τ'} {e2 : Γ ⊢ τ'} :
  Seq e1 e2 --->* e2.
Proof.
  intros.
  eapply multi_step; eauto.
  - now constructor.
  - now apply multi_refl.
Qed.
*)

Ltac simpl_multistep :=
  intros;
  match goal with
  | [ H : _ --->* _ |- _ ] => induction H
  end;
  [ now apply multi_refl
  | eapply multi_step; eauto;
    now econstructor; eauto ].

(*
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
  induction H; simpl; intros; reduce.
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

Lemma multistep_IsNil1 {Γ τ} {xs xs' : Γ ⊢ (TyList τ)} :
  (xs --->* xs') → IsNil xs --->* IsNil xs'.
Proof. now simpl_multistep. Qed.

Lemma multistep_IsNilNil {Γ τ} {xs : Γ ⊢ (TyList τ)} :
  (xs --->* Nil) → IsNil xs --->* ETrue.
Proof.
  intros.
  dependent induction H.
  - apply multi_R.
    now constructor.
  - rewrite <- IHmulti; eauto.
    apply multi_R.
    now constructor.
Qed.
*)

#[local] Hint Constructors ValueP Step : core.

#[local] Hint Extern 1 (¬ ErrorP _) => inversion 1 : core.
#[local] Hint Extern 7 (_ ---> _) => repeat econstructor : core.

Lemma no_intermediate_errors {Γ τ} {e e' : Γ ⊢ τ} :
  ¬ ErrorP e' → (e --->* e') → ∀ i, i --->* e' → ¬ ErrorP i.
Proof.
  repeat intro.
  destruct H1.
  - contradiction.
  - apply error_is_nf in H2.
    now edestruct H2; eauto.
Qed.

Corollary values_final {Γ τ} {e e' : Exp Γ τ} :
  e --->* e' → ValueP e → e = e'.
Proof.
  intros.
  apply value_is_nf in H0.
  unfold normal_form in H0.
  induction H; auto.
  now intuition.
Qed.

Corollary errors_final {Γ τ} {e e' : Exp Γ τ} :
  e --->* e' → ErrorP e → e = e'.
Proof.
  intros.
  apply error_is_nf in H0.
  unfold normal_form in H0.
  induction H; auto.
  now intuition.
Qed.

Lemma not_error_backpropagate {Γ τ} {x y : Γ ⊢ τ} :
  ¬ ErrorP y → x --->* y → ¬ ErrorP x.
Proof.
  intros.
  now eapply no_intermediate_errors in H; eauto.
Qed.

Lemma multistep_AppR {Γ dom cod} {e e' : Γ ⊢ dom} {v : Γ ⊢ (dom ⟶ cod)} :
  ¬ ErrorP e' → (e --->* e') → ValueP v → APP v e --->* APP v e'.
Proof.
  intros.
  induction H0.
  - now apply multi_refl.
  - rewrite <- IHmulti; clear IHmulti; auto.
    inv H1.
    eapply (AppR_LAM (e:=e)) in H0.
    + now apply multi_R.
    + now eapply not_error_backpropagate; eauto.
Qed.

Lemma multistep_AppR_Error {Γ dom cod} {e : Γ ⊢ dom}
      {v : Γ ⊢ (dom ⟶ cod)} {m : Err} :
  (e --->* Error m) → ValueP v → APP v e --->* Error m.
Proof.
  intros.
  dependent induction H.
  - apply multi_R.
    now eauto 6.
  - specialize (IHmulti _ _ _ _ v m eq_refl JMeq_refl JMeq_refl JMeq_refl H1).
    rewrite <- IHmulti.
    apply multistep_AppR; auto.
Abort.

End Multi.

Notation " t '--->*' t' " := (multi Step t t') (at level 40).

(** The following two definitions cannot be completed, due to a typeclass
    instance mismatch, when defined within the section above. *)

(*
Lemma multistep_CarCons {A : Type} {S : HostExprsSem A}
      {Γ τ} {d e1 : Γ ⊢ τ} {e2 xs : Γ ⊢ (TyList τ)} :
  ValueP d → ValueP e1 → ValueP e2 →
  (xs --->* Cons e1 e2) → Car d xs --->* e1.
Proof.
  intros.
  dependent induction H.
  - erewrite multistep_Car2; eauto.
    + apply multi_R.
      now constructor; eauto.
    + now constructor; eauto.
  - specialize (IHmulti _ _ _ d _ _ _ X X0 X1
                        eq_refl JMeq_refl JMeq_refl JMeq_refl).
    rewrite <- IHmulti; auto.
    apply multistep_Car2; auto.
    now apply multi_R.
Qed.

Lemma multistep_CdrCons {A : Type} {S : HostExprsSem A}
      {Γ τ} {e1 : Γ ⊢ τ} {e2 xs : Γ ⊢ (TyList τ)} :
  ValueP e1 → ValueP e2 →
  (xs --->* Cons e1 e2) → Cdr xs --->* e2.
Proof.
  intros.
  dependent induction H.
  - apply multi_R.
    now constructor.
  - specialize (IHmulti _ _ _ _ _ y X X0
                        eq_refl JMeq_refl JMeq_refl JMeq_refl).
    rewrite <- IHmulti.
    apply multistep_Cdr1.
    now apply multi_R.
Qed.

Lemma multistep_IsNilCons {A : Type} {S : HostExprsSem A}
      {Γ τ} {e1 : Γ ⊢ τ} {e2 xs : Γ ⊢ (TyList τ)} :
  ValueP e1 → ValueP e2 →
  (xs --->* Cons e1 e2) → IsNil xs --->* EFalse.
Proof.
  intros.
  dependent induction H.
  - apply multi_R.
    now constructor.
  - specialize (IHmulti _ _ _ _ _ y X X0
                        eq_refl JMeq_refl JMeq_refl JMeq_refl).
    rewrite <- IHmulti.
    apply multistep_IsNil1.
    now apply multi_R.
Qed.
*)
