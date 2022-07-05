Set Warnings "-notation-overridden".

Require Import
  Coq.Unicode.Utf8
  Ty
  Exp
  Sem.

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Structure.BiCCC.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Import ListNotations.

Program Definition Pact Γ : Category := {|
  obj     := Ty;
  hom     := λ A B : Ty, Exp Γ (A ⟶ B);
  homset  := λ _ _, {| equiv := λ f g, SemExp f = SemExp g |};
  id      := @Ren.identity Γ;
  compose := @Ren.compose Γ
|}.
Next Obligation. equivalence; congruence. Qed.
Next Obligation.
  extensionality se.
  rewrite !SemExp_compose.
  now rewrite H, H0.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  simp RTmL; simpl.
  unfold wk.
  rewrite <- SemRenComm.
  now rewrite SemRen_skip1.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  simp RTmL; simpl.
  unfold wk.
  rewrite <- SemRenComm.
  now rewrite SemRen_skip1.
Qed.
Next Obligation.
  extensionality se.
  pose proof (SemExp_compose_assoc se f g h).
  simpl in H.
  now apply H.
Qed.
Next Obligation.
  extensionality se.
  pose proof (SemExp_compose_assoc se f g h).
  symmetry in H.
  simpl in H.
  now apply H.
Qed.

#[global]
Program Instance Pact_Terminal Γ : @Terminal (Pact Γ) := {
  terminal_obj := TyUnit;
  one := λ _, LAM EUnit
}.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  now destruct (SemExp f se x0), (SemExp g se x0).
Qed.

#[global]
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
  rewrite <- !SemRenComm.
  rewrite !SemRen_skip1.
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
      rewrite <- !SemRenComm.
      rewrite !SemRen_skip1.
      simpl.
      simp RTmL; simpl.
      rewrite H; simpl.
      unfold wk.
      rewrite <- !SemRenComm.
      now rewrite !SemRen_skip1.
    + extensionality se.
      extensionality x2.
      fold SemTy in x2.
      unfold wk.
      rewrite <- !SemRenComm.
      rewrite !SemRen_skip1.
      simpl.
      simp RTmL; simpl.
      rewrite H; simpl.
      unfold wk.
      rewrite <- !SemRenComm.
      now rewrite !SemRen_skip1.
  - destruct H.
    extensionality se.
    extensionality x2.
    fold SemTy in x2.
    unfold wk.
    rewrite <- !SemRenComm.
    rewrite <- e, <- e0.
    simp RTmL; simpl.
    unfold wk.
    rewrite <- !SemRenComm.
    rewrite !SemRen_skip1; simpl.
    now destruct (SemExp h se x2).
Qed.

#[global]
Program Instance Pact_Closed Γ : @Closed (Pact Γ) _ := {
  exponent_obj := TyArrow;
  exp_iso := λ _ _ _,
    {| to   := {| morphism := λ f,
                   LAM (LAM (APP (wk (wk f)) (Pair (VAR (SV ZV)) (VAR ZV)))) |}
     ; from := {| morphism := λ f,
                   LAM (APP (APP (wk f) (Fst (VAR ZV))) (Snd (VAR ZV))) |} |}
}.
Next Obligation.
  extensionality se.
  extensionality x0.
  extensionality x1.
  fold SemTy in x0.
  fold SemTy in x1.
  simpl.
  unfold wk.
  rewrite <- !SemRenComm.
  rewrite !SemRen_skip1; simpl.
  now rewrite H2.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  destruct x0.
  simpl.
  unfold wk.
  rewrite <- !SemRenComm.
  rewrite !SemRen_skip1; simpl.
  now rewrite H2.
Qed.
Next Obligation.
  extensionality se.
  extensionality x0.
  extensionality x1.
  fold SemTy in x0.
  fold SemTy in x1.
  unfold wk.
  rewrite <- !SemRenComm.
  simp RTmL.
  simpl SemVar.
  simpl fst.
  simpl snd.
  f_equal.
Admitted.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  destruct x0.
Admitted.
Next Obligation.
  extensionality se.
  extensionality x0.
  fold SemTy in x0.
  destruct x0.
Admitted.
