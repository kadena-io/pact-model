Require Import
  Pact.Lib
  Pact.Exp
  Pact.SemTy
  Pact.Ren
  Pact.SemExp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Equations SemRen {Γ Γ'} (r : Ren Γ Γ') (se : SemEnv Γ) : SemEnv Γ' :=
  SemRen NoRen    se      := se;
  SemRen (Drop r) (_, se) := SemRen r se;
  SemRen (Keep r) (e, se) := (e, SemRen r se).

Lemma SemRen_inil (r : Ren [] []) :
  SemRen r tt = tt.
Proof.
  now dependent destruction r.
Qed.

Lemma SemRen_idRen {Γ} (se : SemEnv Γ) :
  SemRen idRen se = se.
Proof.
  induction Γ; destruct se; simpl; simp SemRen; sauto.
Qed.

Lemma SemRen_skip1 {Γ τ} (e : SemTy τ) (se : SemEnv Γ) :
  SemRen skip1 (e, se) = se.
Proof.
  induction Γ; destruct se; auto.
  unfold skip1; simp SemRen.
  now rewrite SemRen_idRen.
Qed.

Lemma SemVar_SemRen Γ τ (v : Var Γ τ) Γ' (r : Ren Γ' Γ) (se : SemEnv Γ') :
  SemVar v (SemRen r se) = SemVar (RenVar r v) se.
Proof.
  induction r; simp SemRen; simp RenVar; simpl;
  destruct se; simp SemRen; auto.
  now dependent elimination v; simpl; simp RenVar.
Qed.

Lemma SemRen_RcR {Γ Γ' Γ''} (f : Ren Γ' Γ'') (g : Ren Γ Γ') (se : SemEnv Γ) :
  SemRen (RcR f g) se = SemRen f (SemRen g se).
Proof.
  generalize dependent Γ''.
  generalize dependent Γ'.
  induction Γ; destruct se; simpl; intros; auto.
  - inversion g; subst.
    rewrite SemRen_inil.
    inversion f; subst.
    now rewrite !SemRen_inil.
  - dependent elimination g; simp SemRen.
    + now rewrite <- IHΓ; simp RcR; simp SemRen.
    + dependent elimination f; simp SemRen;
      now rewrite <- IHΓ; simp RcR; simp SemRen.
Qed.

Lemma SemExp_SemRen {Γ Γ' τ} (e : Exp Γ τ) (r : Ren Γ' Γ) (se : SemEnv Γ') :
  ⟦ SemRen r se ⊨ e ⟧ = ⟦ se ⊨ RenExp r e ⟧.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto; simp SemExp.
  1: now rewrite SemVar_SemRen.
  1: {
    f_equal.
    extensionality z.
    sauto lq: on.
  }
  2: {
    f_equal; auto.
    extensionality z.
    sauto lq: on.
  }
  all: sauto lq: on.
Qed.

Lemma SemExp_wk `(se : SemEnv Γ) {τ τ'} (y : SemTy τ') (e : Exp Γ τ) :
  ⟦ (y, se) ⊨ wk e ⟧ = ⟦ se ⊨ e ⟧.
Proof.
  rewrite /wk -SemExp_SemRen SemRen_skip1 //.
Qed.
