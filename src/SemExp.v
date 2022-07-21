Require Import
  Coq.ZArith.ZArith
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
  Pact.Lang.Capability.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section SemExp.

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

Definition SemBltn {τ} (bltn : Builtin τ) : SemTy τ :=
  match bltn with
  | AddInt => λ n, pure (λ m, pure (n + m)%Z)
  | SubInt => λ n, pure (λ m, pure (n - m)%Z)
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
Proof. now dependent destruction r. Qed.

Lemma RenSem_idRen {Γ} (se : SemEnv Γ) :
  RenSem idRen se = se.
Proof.
  induction Γ; destruct se; simpl; simp RenSem; intros; auto.
  now rewrite IHΓ.
Qed.

Lemma RenSem_skip1 {Γ τ} (e : SemTy τ) (se : SemEnv Γ) :
  RenSem skip1 (e, se) = se.
Proof.
  induction Γ; destruct se; simpl; intros; auto.
  unfold skip1; simp RenSem.
  now rewrite RenSem_idRen.
Qed.

Lemma SemVar_RenSem Γ τ (v : Var Γ τ) Γ' (r : Ren Γ' Γ) (se : SemEnv Γ') :
  SemVar v (RenSem r se) = SemVar (RenVar r v) se.
Proof.
  intros.
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

  SemExp (Error e)  _ := throw (Err_Exp e);
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

  SemExp Nil se := pure [];
  SemExp (Cons x xs) se :=
    x'  <- SemExp x se ;
    xs' <- SemExp xs se ;
    pure (x' :: xs');

  SemExp (Car xs) se :=
    xs' <- SemExp xs se ;
    match xs' with
    | []     => throw (Err_Exp Err_CarNil)
    | x :: _ => pure x
    end;
  SemExp (Cdr xs) se :=
    xs' <- SemExp xs se ;
    match xs' with
    | []      => throw (Err_Exp Err_CdrNil)
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

Lemma SemExp_RenSem {Γ Γ' τ} (e : Exp Γ τ) (r : Ren Γ' Γ) (se : SemEnv Γ') :
  SemExp e (RenSem r se) = SemExp (RenExp r e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto; simp SemExp;
  try now rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3, ?IHe4, ?IHe5.
  - now rewrite SemVar_RenSem.
  - f_equal.
    extensionality z.
    rewrite <- IHe; clear IHe.
    simpl.
    now repeat f_equal.
Qed.

Lemma SemExp_wk `(E : SemEnv Γ) {τ τ'} (y : SemTy τ') (e : Exp Γ τ) :
  SemExp (wk e) (y, E) = SemExp e E.
Proof.
  unfold wk.
  rewrite <- SemExp_RenSem; simpl.
  f_equal.
  now rewrite RenSem_skip1.
Qed.

Lemma SemExp_ValueP {Γ τ} (e : Exp Γ τ) (se : SemEnv Γ) :
  ValueP e → ∃ x, SemExp e se = pure x.
Proof.
  induction 1; simpl; intros;
  try (now eexists; eauto); reduce; simp SemExp.
  - simpl.
    eexists.
    reflexivity.
  - eexists.
    extensionality env.
    extensionality s.
    extensionality w.
    admit.                      (* jww (2022-07-20): TODO *)
  - eexists.
    extensionality env.
    extensionality s.
    extensionality w.
    admit.                      (* jww (2022-07-20): TODO *)
  - simpl.
    eexists.
    reflexivity.
  - exists (x1, x0).
    now rewrite H1, H2; simpl.
  - exists [].
    reflexivity.
  - exists (x1 :: x0).
    now rewrite H1, H2; simpl.
  - eexists.
    extensionality nm'.
    extensionality nm'0.
    extensionality nm'1.
    rewrite H2, H3, H4; simpl.
    unfold RWSE_join.
    reflexivity.
Abort.

End SemExp.

Notation "f =<< x" := (x >>= f) (at level 42, right associativity).
