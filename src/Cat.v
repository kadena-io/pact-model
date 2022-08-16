Set Warnings "-notation-overridden".

Require Import
  Hask.Control.Monad
  Hask.Control.Monad.Trans.State
  Pact.Data.Either
  Pact.Lib
  Pact.Ty
  Pact.Value
  Pact.Exp
  Pact.SemTy
  Pact.SemBltn
  Pact.SemExp
  Pact.Lang.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.BiCCC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Section Cat.

Definition identity Γ τ : Exp Γ (τ ⟶ τ) := LAM (λ x, VAR x).

Definition composition {Γ τ τ' τ''}
           (f : Exp Γ (τ' ⟶ τ''))
           (g : Exp Γ (τ ⟶ τ')) : Exp Γ (τ ⟶ τ'') :=
  LAM (λ x, APP f (APP g (VAR x))).

Definition curry {Γ a b c} (f : Exp Γ (a × b ⟶ c)) : Exp Γ (a ⟶ b ⟶ c) :=
  LAM (λ a, LAM (λ b, APP f (Pair (VAR a) (VAR b)))).

Definition uncurry {Γ a b c} (f : Exp Γ (a ⟶ b ⟶ c)) : Exp Γ (a × b ⟶ c) :=
  LAM (λ p, APP (APP f (Fst (VAR p))) (Snd (VAR p))).

Lemma SemExp_identity {τ} : ⟦ identity SemTy τ ⟧ = pure pure.
Proof. now f_equal. Qed.

Lemma SemExp_composition {τ τ' τ''}
  (f : Exp SemTy (τ' ⟶ τ'')) (g : Exp SemTy (τ ⟶ τ')) :
  ⟦ composition f g ⟧ =
    pure (λ x, f' <- SemExp f ;
               g' <- SemExp g ;
               f' =<< g' x).
Proof.
  fold (SemTy (m:=PactM)).
  unfold composition.
  simp SemExp; simpl.
  unravel.
  extensionality st.
  repeat f_equal.
  extensionality x.
  simp SemExp; simpl.
  unravel.
  extensionality st0.
  destruct (⟦ f ⟧ _); auto.
  destruct p, p; simpl.
  destruct (⟦ g ⟧ _); auto.
  destruct p, p; simpl.
  sauto.
Qed.

Lemma SemExp_composition_identity_right {τ τ'} (f : Exp SemTy (τ ⟶ τ')) :
  ValueP f →
  ⟦ composition f (identity SemTy τ) ⟧ = ⟦ f ⟧.
Proof.
  intros.
  destruct (SemExp_ValueP H).
  rewrite H0 SemExp_composition.
  fold (SemTy (m:=PactM)).
  f_equal.
  extensionality y.
  extensionality st; simpl; unravel.
  rewrite H0 /=.
  unfold identity.
  simp SemExp; simpl.
  simp SemExp; simpl.
  now destruct (x _ _).
Qed.

Lemma SemExp_composition_identity_left {τ τ'} (f : Exp SemTy (τ ⟶ τ')) :
  ValueP f →
  ⟦ composition (identity SemTy τ') f ⟧ = ⟦ f ⟧.
Proof.
  intros.
  destruct (SemExp_ValueP H).
  rewrite H0 SemExp_composition.
  fold (SemTy (m:=PactM)).
  f_equal.
  extensionality y.
  extensionality st; simpl; unravel.
  rewrite H0 /=.
  simp SemExp; simpl.
  unfold identity.
  simp SemExp; simpl.
  destruct (x _ _); auto.
  destruct p, p; simpl.
  now simp SemExp; simpl.
Qed.

Lemma SemExp_composition_assoc {τ τ' τ'' τ'''}
      (f : Exp SemTy (τ'' ⟶ τ'''))
      (g : Exp SemTy (τ' ⟶ τ''))
      (h : Exp SemTy (τ ⟶ τ')) :
  ValueP f →
  ValueP g →
  ValueP h →
  ⟦ composition f (composition g h) ⟧ =
  ⟦ composition (composition f g) h ⟧.
Proof.
  intros.
  destruct (SemExp_ValueP H).
  destruct (SemExp_ValueP H0).
  destruct (SemExp_ValueP H1).
  rewrite !SemExp_composition.
  fold (SemTy (m:=PactM)).
  f_equal.
  extensionality y.
  extensionality st; simpl; unravel.
  rewrite H2 H3 H4; simpl.
  sauto.
Qed.

Lemma extend_f {A B : Type} (f g : A → B) :
  (λ x, f x) = (λ x, g x) → (∀ x, f x = g x).
Proof.
  intros.
  setoid_rewrite <- eta_expansion in H.
  now rewrite H.
Qed.

Program Instance Exp_Setoid {dom cod} : Setoid (Exp SemTy (dom ⟶ cod)) := {
  equiv := λ f g, SemExp f = SemExp g
}.

Program Instance Value_Setoid {dom cod} :
  Setoid { e : Exp SemTy (dom ⟶ cod) | ValueP e } := {
  equiv := λ f g, SemExp f = SemExp g
}.

Program Instance composition_respects {τ τ' τ''} :
  Proper (equiv ==> equiv ==> equiv) (@composition SemTy τ τ' τ'').
Next Obligation.
  repeat intro.
  unfold composition.
  simp SemExp; f_equal.
  extensionality x1.
  simp SemExp.
  f_equal; [|rewrite H //].
  extensionality f.
  fold (SemTy (m:=PactM)) in f.
  extensionality st.
  simpl; unravel.
  rewrite H0 //.
Qed.

Definition actual_f {A B} :
  { e : Exp (SemTy (m:=PactM)) (A ⟶ B) | ValueP e }
    → SemTy (m:=PactM) A → PactM (SemTy (m:=PactM) B).
Proof.
  intros [e v] x.
  dependent elimination e;
  try solve [ exfalso; inv v ].
  - exact (SemExp (e x)).
  - exact (SemBltn b x).
Defined.

Notation " `2  t " := (proj2_sig t) (at level 0, t at next level) : program_scope.

Program Definition Pact : Category := {|
  obj     := Ty;

  hom     := λ dom cod : Ty, { e : Exp SemTy (dom ⟶ cod) | ValueP e };
  homset  := λ _ _, Value_Setoid;

  id      := λ x, exist _ (@identity SemTy x) (LambdaP _);
  compose := λ _ _ _ f g, exist _ (composition f g) (LambdaP _);

  compose_respects := @composition_respects;

  id_left := λ _ _ f,
    SemExp_composition_identity_left (`2 f);
  id_right := λ _ _ f,
    SemExp_composition_identity_right (`2 f);
  comp_assoc := λ _ _ _ _ f g h,
    SemExp_composition_assoc (`2 f) (`2 g) (`2 h);
  comp_assoc_sym := λ _ _ _ _ f g h,
    symmetry (SemExp_composition_assoc (`2 f) (`2 g) (`2 h))
|}.

#[export]
Program Instance Pact_Terminal : @Terminal Pact := {
  terminal_obj := TyPrim PrimVoid;
  one := λ _, exist _ (LAM (λ _, Error)) (LambdaP _)
}.
Next Obligation.
  destruct (SemExp_ValueP H0) as [f' H3].
  destruct (SemExp_ValueP H)  as [g' H4].
  rewrite {}H3 {}H4.
  extensionality st.
  simpl.
  repeat f_equal.
  extensionality arg.
  fold (SemTy (m:=PactM)) in arg.
  simpl in *.
  extensionality st0.
  destruct (f' arg), (g' arg); try tauto.
  f_equal.
Admitted.

(*
#[export]
Program Instance Pact_Cartesian Γ : @Cartesian (Pact Γ) := {
  product_obj := TyPair;
  fork := λ _ _ _ f g,
    LAM (Pair (APP (wk f) (VAR ZV)) (APP (wk g) (VAR ZV)));
  exl  := λ _ _, LAM (Fst (VAR ZV));
  exr  := λ _ _, LAM (Snd (VAR ZV));
}.
Next Obligation.
  extensionality se.
  extensionality x2.
  fold SemTy in x2.
  simpl.
  unfold wk.
  rewrite <- !SemExp_RenSem.
  rewrite !RenSem_skip1.
  simpl.
  now rewrite H, H0.
Qed.
Next Obligation.
  split; intros.
  - split.
    + extensionality se.
      extensionality x2.
      fold SemTy in x2.
      unfold wk.
      rewrite <- !SemExp_RenSem.
      rewrite !RenSem_skip1.
      simpl.
      simp Keep; simpl.
      rewrite H; simpl.
      unfold wk.
      rewrite <- !SemExp_RenSem.
      now rewrite !RenSem_skip1.
    + extensionality se.
      extensionality x2.
      fold SemTy in x2.
      unfold wk.
      rewrite <- !SemExp_RenSem.
      rewrite !RenSem_skip1.
      simpl.
      simp Keep; simpl.
      rewrite H; simpl.
      unfold wk.
      rewrite <- !SemExp_RenSem.
      now rewrite !RenSem_skip1.
  - destruct H.
    extensionality se.
    extensionality x2.
    fold SemTy in x2.
    unfold wk.
    rewrite <- !SemExp_RenSem.
    rewrite <- e, <- e0.
    simp Keep; simpl.
    unfold wk.
    rewrite <- !SemExp_RenSem.
    rewrite !RenSem_skip1; simpl.
    now destruct (SemExp h se x2).
Qed.

#[export]
Program Instance Pact_Closed Γ : @Closed (Pact Γ) _ := {
  exponent_obj := TyArrow;
  exp_iso := λ _ _ _,
    {| to   := {| morphism := curry |}
     ; from := {| morphism := uncurry |} |}
}.
Next Obligation.
  extensionality se.
  extensionality x0.
  extensionality x1.
  fold SemTy in x0.
  fold SemTy in x1.
  simpl.
  unfold wk.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  now rewrite H2.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  destruct x0.
  simpl.
  unfold wk.
  rewrite <- !SemExp_RenSem.
  repeat setoid_rewrite RenSem_skip1; simpl.
  now rewrite H2.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  extensionality x1.
  fold SemTy in x0.
  fold SemTy in x1.
  unfold wk.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  simp RenVar.
  simpl.
  now repeat setoid_rewrite RenSem_skip1.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  unfold wk.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  simp RenVar.
  simpl.
  repeat setoid_rewrite RenSem_skip1.
  now destruct x0.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  destruct x0.
  unfold wk.
  simp RenVar.
  simpl.
  rewrite <- !SemExp_RenSem.
  simp RenSem.
  rewrite !RenSem_skip1.
  now setoid_rewrite RenSem_skip1.
Qed.
*)

End Cat.
