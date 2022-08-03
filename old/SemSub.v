Require Import
  Hask.Control.Monad
  Hask.Control.Monad.Trans.State
  Pact.Data.Either
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Ren
  Pact.Sub
  Pact.SemTy
  Pact.SemExp
  Pact.SemRen
  Pact.Lang.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Equations SemSub {Γ Γ'} (s : Sub Γ Γ') (se : SemEnv Γ) : PactM (SemEnv Γ') :=
  SemSub NoSub      se := pure tt;
  SemSub (Push t σ) se :=
    v  <- SemExp t se ;
    vs <- SemSub σ se ;
    pure (v, vs).

Lemma SemSub_inil (s : Sub [] []) :
  SemSub s tt = pure tt.
Proof. now dependent elimination s. Qed.

Lemma SemSub_ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') (se : SemEnv Γ) :
  SemSub (ScR s r) se = SemSub s (SemRen r se).
Proof.
  generalize dependent Γ''.
  generalize dependent Γ'.
  destruct Γ, se; simpl; intros; auto.
  - dependent elimination r; simp SemRen.
    rewrite NoRen_idRen.
    now rewrite ScR_idRen.
  - clear.
    dependent induction s1; simp ScR.
    + now simp SemSub.
    + simp SemSub.
      f_equal.
      * extensionality v.
        rwse.
        simpl.
        autounfold.
        rewrite IHs1.
        reflexivity.
      * now rewrite SemExp_SemRen.
Qed.

Lemma SemSub_idSub {Γ} (se : SemEnv Γ) :
  SemSub idSub se = pure se.
Proof.
  induction Γ; destruct se; simpl; simp SemSub; simpl; intros; auto.
  rewrite SemSub_ScR.
  rewrite SemRen_skip1.
  now rewrite IHΓ.
Qed.

Lemma SemVar_SemSub {Γ Γ' τ} (v : Var Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemVar v <$> SemSub s se = SemExp (SubVar s v) se.
Proof.
  intros.
  generalize dependent τ.
  generalize dependent se.
  simpl.
  autounfold.
  induction s; simp SemSub; simp SubVar; simpl; intros.
  - now inversion v.
  - rwse.
    dependent induction v; simp SubVar.
    + simp SemSub; simpl; autounfold.
      destruct (⟦ se ⊨ e ⟧ r s0); auto; reduce.
      admit.
    + rewrite <- IHs.
      destruct (SemSub s se r s0); auto.
      reduce.
Admitted.

(*
Lemma SemExp_SemSub {Γ Γ' τ} (e : Exp Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SubP (@concrete Γ' se) s →
  SemExp e =<< SemSub s se = SemExp (SubExp s e) se.
Proof.
  generalize dependent τ.
  generalize dependent se.
  induction s; simpl; intros;
  autounfold; rwse;
  simp SemSub; simpl;
  autounfold.
  - admit.
  - inv H.
    simp ExpP in H3; reduce.
    simpl in *; reduce.
    rewrite H.
    autounfold in *.
    admit.
Abort.
(*
  - simp SemExp; simpl.
    extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    unfold Keepₛ, Dropₛ; simp SemSub.
    repeat f_equal.
    rewrite SemSub_ScR.
    now rewrite SemRen_skip1.
  - now rewrite IHe1, IHe2.
Qed.
*)

Lemma SemSub_ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (t : Sub Γ Γ') (se : SemEnv Γ) :
  (∃ x, SemSub t se = pure x) →
  SemSub (ScS s t) se = SemSub s =<< SemSub t se.
Proof.
  intros.
  destruct H.
  generalize dependent Γ''.
  induction s; intros; simpl; simp SemSub; auto.
  simpl; autounfold; rwse.
  - rewrite H; sauto.
  - rwse; simpl; autounfold.


Abort.

Lemma SemSub_RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') (se : SemEnv Γ) :
  SubP (@concrete Γ se) s →
  SemSub (RcS r s) se = SemRen r <$> SemSub s se.
Proof.
  generalize dependent Γ.
  induction r; intros;
  simpl; simp RcS; simp SemRen; auto;
  dependent elimination s;
  simp RcS; simp SemSub; simp SemRen;
  simpl; rwse.
  - sauto.
  - inv H.
    rewrite IHr; auto.
    simpl; autounfold.
    simp ExpP in H3; reduce.
    simpl in H; reduce.
    rewrite H.
    destruct (SemSub _ _ _ _); auto.
    reduce.
    simp SemRen.
    sauto lq: on.
  - inv H.
    rewrite IHr; auto.
    simpl; autounfold.
    simp ExpP in H3; reduce.
    simpl in H; reduce.
    rewrite H.
    destruct (SemSub _ _ _ _); auto.
    reduce.
    simp SemRen.
    sauto lq: on.
Qed.

Lemma SemExp_SubExp `(se : SemEnv Γ) `(e : Exp (dom :: Γ) τ) (v : Exp Γ dom) x :
  SubP (@concrete Γ se) idSub →
  ⟦ se ⊨ v ⟧ = pure x →
  ⟦ se ⊨ SubExp {|| v ||} e ⟧ = ⟦ (x, se) ⊨ e ⟧.
Proof.
  intros.
  generalize dependent v.
  generalize dependent x.
  dependent induction e;
  simp SemExp; simpl;
  autounfold; intros; rwse;
  simp SemExp; simpl;
  autounfold.
  1: {
    dependent elimination v; simp SubVar.
    - rewrite H0 //.
    - rewrite SubVar_idSub.
      now simp SemExp.
  }
  1: {
    repeat f_equal.
    specialize (IHe dom0 (dom :: Γ) (x, se) e JMeq_refl JMeq_refl).
    extensionality x0.
    simpl in IHe.
    admit.
  }
  1: {
    erewrite IHe1; eauto.
    erewrite IHe2; eauto.
  }
  all: sauto lq: on.
Admitted.
*)
