Require Import
  Coq.ZArith.ZArith
  Hask.Control.Monad
  Hask.Data.Either
  Pact.ilist
  Pact.Lib
  Pact.Ty
  Pact.Bltn
  Pact.Exp
  Pact.Value
  Pact.Ren
  Pact.Sub
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
  RenSem r () = ().
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

Corollary string_sem : SemTy (m:=PactM) 𝕊 = string.
Proof. reflexivity. Qed.

Equations SemExp `(e : Exp Γ τ) (se : SemEnv Γ) : PactM (SemTy (m:=PactM) τ) :=
  SemExp (VAR v)     se := pure (SemVar v se);
  SemExp (LAM e)     se := pure (λ x, SemExp e (x, se));
  SemExp (APP e1 e2) se :=
    f <- SemExp e1 se ;
    x <- SemExp e2 se ;
    f x;

  SemExp (Raise e) _ := throw =<< SemExp e se;
  SemExp (Catch e) _ :=
    λ r s w,
      match SemExp e se r s w with
      | inl err           => pure (inl err) r s w
      | inr (v, (s', w')) => pure (inr v) r s' w'
      end;

  SemExp (Symbol n) _ := pure n;
  SemExp (Lit l)  _   := pure (SemLit l);
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
    | []     => throw (Err_Expr "car of nil")
    | x :: _ => pure x
    end;
  SemExp (Cdr xs) se :=
    xs' <- SemExp xs se ;
    match xs' with
    | []      => throw (Err_Expr "cdr of nil")
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

  SemExp (InstallCapability c) se :=
    install_capability =<< SemExp c se;
  SemExp (RequireCapability c) se :=
    require_capability =<< SemExp c se.

Notation "⟦ E ⊨ e ⟧" := (SemExp e E)  (at level 9).
Notation "⟦ e ⟧"     := (SemExp e tt) (at level 9).

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

Lemma SemExp_wk `(E : SemEnv Γ) {τ τ'} (y : SemTy τ') (e : Exp Γ τ) :
  ⟦ (y, E) ⊨ wk e ⟧ = ⟦ E ⊨ e ⟧.
Proof.
  rewrite /wk -SemExp_RenSem RenSem_skip1 //.
Qed.

Lemma SemExp_ValueP {Γ τ} (e : Exp Γ τ) (se : SemEnv Γ) :
  ValueP e → ∃ x, ⟦ se ⊨ e ⟧ = pure x.
Proof.
  induction 1; reduce; simp SemExp;
  eexists; rwse; sauto lq: on.
Qed.
