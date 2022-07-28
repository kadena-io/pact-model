Require Import
  Coq.ZArith.ZArith
  Hask.Control.Monad
  Pact.Data.Either
  Pact.Data.IList
  Pact.Lib
  Pact.Ty
  Pact.Bltn
  Pact.Exp
  Pact.Value
  Pact.Ren
  Pact.SemTy
  Pact.Lang
  Pact.Lang.Capability
  Pact.SemBltn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Definition SemEnv Γ : Type := ilist (SemTy (m:=PactM)) Γ.

Definition SemLit {ty : PrimType} (l : Literal ty) : SemPrimTy ty :=
  match l with
  | LitString s    => s
  | LitInteger i   => i
  | LitDecimal d _ => d (* jww (2022-07-21): TODO *)
  | LitUnit        => tt
  | LitBool b      => b
  | LitTime t      => t
  end.

Fixpoint SemVar `(v : Var Γ τ) : SemEnv Γ → SemTy τ :=
  match v with
  | ZV   => λ se, fst se
  | SV v => λ se, SemVar v (snd se)
  end.

Equations RenSem {Γ Γ'} (r : Ren Γ Γ') (se : SemEnv Γ) : SemEnv Γ' :=
  RenSem NoRen    se      := se;
  RenSem (Drop r) (_, se) := RenSem r se;
  RenSem (Keep r) (e, se) := (e, RenSem r se).

Lemma RenSem_inil (r : Ren [] []) :
  RenSem r tt = tt.
Proof.
  now dependent destruction r.
Qed.

Lemma RenSem_idRen {Γ} (se : SemEnv Γ) :
  RenSem idRen se = se.
Proof.
  induction Γ; destruct se; simpl; simp RenSem; sauto.
Qed.

Lemma RenSem_skip1 {Γ τ} (e : SemTy τ) (se : SemEnv Γ) :
  RenSem skip1 (e, se) = se.
Proof.
  induction Γ; destruct se; auto.
  unfold skip1; simp RenSem.
  now rewrite RenSem_idRen.
Qed.

Lemma SemVar_RenSem Γ τ (v : Var Γ τ) Γ' (r : Ren Γ' Γ) (se : SemEnv Γ') :
  SemVar v (RenSem r se) = SemVar (RenVar r v) se.
Proof.
  induction r; simp RenSem; simp RenVar; simpl;
  destruct se; simp RenSem; auto.
  now dependent elimination v; simpl; simp RenVar.
Qed.

Lemma RenSem_RcR {Γ Γ' Γ''} (f : Ren Γ' Γ'') (g : Ren Γ Γ') (se : SemEnv Γ) :
  RenSem (RcR f g) se = RenSem f (RenSem g se).
Proof.
  generalize dependent Γ''.
  generalize dependent Γ'.
  induction Γ; destruct se; simpl; intros; auto.
  - inversion g; subst.
    rewrite RenSem_inil.
    inversion f; subst.
    now rewrite !RenSem_inil.
  - dependent elimination g; simp RenSem.
    + now rewrite <- IHΓ; simp RcR; simp RenSem.
    + dependent elimination f; simp RenSem;
      now rewrite <- IHΓ; simp RcR; simp RenSem.
Qed.

Notation "f =<< x" := (x >>= f) (at level 42, right associativity).

Import EqNotations.

Equations SemExp `(e : Exp Γ τ) (se : SemEnv Γ) : PactM (SemTy (m:=PactM) τ) :=
  SemExp (VAR v)     se := pure (SemVar v se);
  SemExp (LAM e)     se := pure (λ x, SemExp e (x, se));
  SemExp (APP e1 e2) se :=
    f <- SemExp e1 se ;
    x <- SemExp e2 se ;
    f x;

  SemExp Error     _ := throw Err_Expr;
  SemExp (Catch e) _ :=
    λ r s,
      match SemExp e se r s with
      | inl err           => pure (inl tt) r s
      | inr (v, (s', w')) => inr (inr v, (s', w'))
      end;

  SemExp (Symbol n) _ := pure n;
  SemExp (Lit l)    _ := pure (SemLit l);
  SemExp (Bltn b)   _ := pure (SemBltn b);

  SemExp (If b t e) se :=
    b' <- SemExp b se ;
    if b' : bool
    then SemExp t se
    else SemExp e se;

  SemExp (Pair x y) se :=
    x' <- SemExp x se ;
    y' <- SemExp y se ;
    pure (x', y');
  SemExp (Fst p) se := fst <$> SemExp p se;
  SemExp (Snd p) se := snd <$> SemExp p se;

  SemExp (Inl p) se := inl <$> SemExp p se;
  SemExp (Inr p) se := inr <$> SemExp p se;
  SemExp (Case e f g) se :=
    e' <- SemExp e se ;
    match e' with
    | inl l => SemExp f se >>= λ f', f' l
    | inr r => SemExp g se >>= λ g', g' r
    end;

  SemExp Nil se := pure [];
  SemExp (Cons x xs) se :=
    x'  <- SemExp x se ;
    xs' <- SemExp xs se ;
    pure (x' :: xs');

  SemExp (Car xs) se :=
    xs' <- SemExp xs se ;
    match xs' with
    | []     => throw Err_CarOfNil
    | x :: _ => pure x
    end;
  SemExp (Cdr xs) se :=
    xs' <- SemExp xs se ;
    match xs' with
    | []      => throw Err_CdrOfNil
    | _ :: xs => pure xs
    end;

  SemExp (IsNil (τ:=ty) xs) se :=
    xs' <- SemExp xs se ;
    match xs' with
    | []        => pure true
    | (_ :: xs) => pure false
    end;

  SemExp (Seq exp1 exp2) se := SemExp exp1 se >> SemExp exp2 se;

  SemExp (Capability (p:=tp) (v:=tv) Hp Hv nm arg val) se :=
    nm'  <- SemExp nm se ;
    arg' <- SemExp arg se ;
    val' <- SemExp val se ;
    pure (Token (s:={| paramTy := reifyTy tp
                     ; valueTy := reifyTy tv |})
                nm'
                (rew <- [λ x, x] (reflectTy_reifyTy (m:=PactM) Hp) in arg')
                (rew <- [λ x, x] (reflectTy_reifyTy (m:=PactM) Hv) in val'));

  SemExp (WithCapability (p:=tp) (v:=tv) Hv modname prd mng c e) se :=
    mn'  <- SemExp modname se ;
    c'   <- SemExp c se ;
    prd' <- SemExp prd se ;
    mng' <- SemExp mng se ;
    with_capability
      mn'
      (s:={| paramTy := reifyTy tp
           ; valueTy := reifyTy tv |})
      c'
      prd'
      (rew <- [λ x, x → PactM _] (reflectTy_reifyTy (m:=PactM) (PairDecP Hv Hv)) in
       rew <- [λ x, _ → PactM x] (reflectTy_reifyTy (m:=PactM) Hv) in mng')
      (SemExp e se);

  SemExp (ComposeCapability (p:=tp) (v:=tv) Hv modname prd mng c) se :=
    mn'  <- SemExp modname se ;
    c'   <- SemExp c se ;
    prd' <- SemExp prd se ;
    mng' <- SemExp mng se ;
    compose_capability
      mn'
      (s:={| paramTy := reifyTy tp
           ; valueTy := reifyTy tv |})
      c'
      prd'
      (rew <- [λ x, x → PactM _] (reflectTy_reifyTy (m:=PactM) (PairDecP Hv Hv)) in
       rew <- [λ x, _ → PactM x] (reflectTy_reifyTy (m:=PactM) Hv) in mng');

  SemExp (InstallCapability c) se := install_capability =<< SemExp c se;
  SemExp (RequireCapability c) se := require_capability =<< SemExp c se.

Notation "⟦ se ⊨ e ⟧" := (SemExp e se)  (at level 9).
Notation "⟦ e ⟧"      := (SemExp e tt) (at level 9).

Lemma SemExp_RenSem {Γ Γ' τ} (e : Exp Γ τ) (r : Ren Γ' Γ) (se : SemEnv Γ') :
  ⟦ RenSem r se ⊨ e ⟧ = ⟦ se ⊨ RenExp r e ⟧.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto; simp SemExp.
  1: now rewrite SemVar_RenSem.
  1: {
    f_equal.
    extensionality z.
    sauto lq: on.
  }
  all: sauto lq: on.
Qed.

Lemma SemExp_wk `(se : SemEnv Γ) {τ τ'} (y : SemTy τ') (e : Exp Γ τ) :
  ⟦ (y, se) ⊨ wk e ⟧ = ⟦ se ⊨ e ⟧.
Proof.
  rewrite /wk -SemExp_RenSem RenSem_skip1 //.
Qed.

Corollary SemExp_VAR_ZV `(se : SemEnv Γ) `(x : ⟦τ⟧) :
  ⟦ (x, se) ⊨ VAR ZV ⟧ = pure x.
Proof. reflexivity. Qed.

Lemma SemExp_ValueP {Γ τ} (e : Exp Γ τ) (se : SemEnv Γ) :
  ValueP e -> ∃ x, ⟦ se ⊨ e ⟧ = pure x.
Proof.
  induction 1; reduce; simp SemExp;
  eexists; rwse; sauto lq: on.
Qed.

Definition expM τ := PactM (SemTy (m:=PactM) τ).

(* An expression is considered "pure" if its denotation has no impact
   whatsoever on the state. *)
Definition pureP `(se : SemEnv Γ)
  `(v : Exp Γ τ) (x : SemTy (m:=PactM) τ) : Prop :=
  ⟦ se ⊨ v ⟧ = pure x.

Arguments pureP {_} _ {_} _ _ /.

(* An expression is considered "safe" if its denotation can never result in an
   error. *)
Definition safeP `(se : SemEnv Γ)
  `(v : Exp Γ τ) (x : SemTy (m:=PactM) τ) : Prop :=
  ∀ r s, ∃ s' w, ⟦ se ⊨ v ⟧ r s = inr (x, (s', w)).

Arguments safeP {_} _ {_} _ _ /.

(************************************************************************
 * SubSem
 *)

Require Import Pact.Sub.
Require Import Pact.Log.

#[local] Hint Unfold RWSE_join : core.
#[local] Hint Unfold RWSE_ap : core.
#[local] Hint Unfold Either_map : core.
#[local] Hint Unfold Tuple.first : core.

Equations SubSem {Γ Γ'} (s : Sub Γ Γ') (se : SemEnv Γ) : PactM (SemEnv Γ') :=
  SubSem NoSub      se := pure tt;
  SubSem (Push t σ) se :=
    v  <- SemExp t se ;
    vs <- SubSem σ se ;
    pure (v, vs).

Lemma SubSem_inil (s : Sub [] []) :
  SubSem s tt = pure tt.
Proof. now dependent elimination s. Qed.

Lemma SubSem_ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') (se : SemEnv Γ) :
  SubSem (ScR s r) se = SubSem s (RenSem r se).
Proof.
  generalize dependent Γ''.
  generalize dependent Γ'.
  destruct Γ, se; simpl; intros; auto.
  - dependent elimination r; simp RenSem.
    rewrite NoRen_idRen.
    now rewrite ScR_idRen.
  - clear.
    dependent induction s1; simp ScR.
    + now simp SubSem.
    + simp SubSem.
      f_equal.
      * extensionality v.
        rwse.
        simpl.
        autounfold.
        rewrite IHs1.
        reflexivity.
      * now rewrite SemExp_RenSem.
Qed.

Lemma SubSem_idSub {Γ} (se : SemEnv Γ) :
  SubSem idSub se = pure se.
Proof.
  induction Γ; destruct se; simpl; simp SubSem; simpl; intros; auto.
  rewrite SubSem_ScR.
  rewrite RenSem_skip1.
  now rewrite IHΓ.
Qed.

Lemma SemVar_SubSem {Γ Γ' τ} (v : Var Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemVar v <$> SubSem s se = SemExp (SubVar s v) se.
Proof.
  intros.
  generalize dependent τ.
  generalize dependent se.
  simpl.
  autounfold.
  induction s; simp SubSem; simp SubVar; simpl; intros.
  - now inversion v.
  - rwse.
    dependent induction v; simp SubVar.
    + simp SubSem; simpl; autounfold.
      destruct (⟦ se ⊨ e ⟧ r s0); auto; reduce.
      admit.
    + rewrite <- IHs.
      destruct (SubSem s se r s0); auto.
      reduce.
Admitted.

(*
Lemma SemExp_SubSem {Γ Γ' τ} (e : Exp Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SubP (@concrete Γ' se) s →
  SemExp e =<< SubSem s se = SemExp (SubExp s e) se.
Proof.
  generalize dependent τ.
  generalize dependent se.
  induction s; simpl; intros;
  autounfold; rwse;
  simp SubSem; simpl;
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
    unfold Keepₛ, Dropₛ; simp SubSem.
    repeat f_equal.
    rewrite SubSem_ScR.
    now rewrite RenSem_skip1.
  - now rewrite IHe1, IHe2.
Qed.
*)

Lemma SubSem_ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (t : Sub Γ Γ') (se : SemEnv Γ) :
  (∃ x, SubSem t se = pure x) →
  SubSem (ScS s t) se = SubSem s =<< SubSem t se.
Proof.
  intros.
  destruct H.
  generalize dependent Γ''.
  induction s; intros; simpl; simp SubSem; auto.
  simpl; autounfold; rwse.
  - rewrite H; sauto.
  - rwse; simpl; autounfold.


Abort.

Lemma SubSem_RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') (se : SemEnv Γ) :
  SubP (@concrete Γ se) s →
  SubSem (RcS r s) se = RenSem r <$> SubSem s se.
Proof.
  generalize dependent Γ.
  induction r; intros;
  simpl; simp RcS; simp RenSem; auto;
  dependent elimination s;
  simp RcS; simp SubSem; simp RenSem;
  simpl; rwse.
  - sauto.
  - inv H.
    rewrite IHr; auto.
    simpl; autounfold.
    simp ExpP in H3; reduce.
    simpl in H; reduce.
    rewrite H.
    destruct (SubSem _ _ _ _); auto.
    reduce.
    simp RenSem.
    sauto lq: on.
  - inv H.
    rewrite IHr; auto.
    simpl; autounfold.
    simp ExpP in H3; reduce.
    simpl in H; reduce.
    rewrite H.
    destruct (SubSem _ _ _ _); auto.
    reduce.
    simp RenSem.
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

Definition eval `(e : Exp [] τ) s (v : ⟦τ⟧) s' :=
  ∀ r, ∃ w, ⟦ e ⟧ r s = inr (v, (s', w)).

Notation "e ~[ s => v ]~> t" :=
  (eval e s t v) (at level 40, v at next level, t at next level).

Lemma sem_app_lam `(e : Exp [dom] cod) (v : Exp [] dom) x r s s' :
  v ~[ s => s' ]~> x →
  ⟦ APP (LAM e) v ⟧ r s = ⟦ (x, tt) ⊨ e ⟧ r s'.
Proof.
  unfold eval.
  intros.
  simp SemExp; simpl.
  autounfold.
  specialize (H r).
  reduce.
  rewrite H.
  destruct (⟦ (x, tt) ⊨ e ⟧ r s'); auto.
  sauto lq: on.
Qed.
