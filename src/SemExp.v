Require Import
  Hask.Control.Monad
  Hask.Control.Monad.Trans.State
  Pact.Data.Either
  Pact.Data.IList
  Pact.Lib
  Pact.Ty
  Pact.Bltn
  Pact.Exp
  Pact.Value
  Pact.SemTy
  Pact.Lang
  Pact.Lang.CapabilityType
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

Notation "f =<< x" := (x >>= f) (at level 42, right associativity).

Import EqNotations.

Equations SemExp `(e : Exp Γ τ) (se : SemEnv Γ) : PactM (SemTy (m:=PactM) τ) :=
  SemExp (VAR v)     se := pure (SemVar v se);
  SemExp (LAM e)     se := pure (λ x, SemExp e (x, se));
  SemExp (APP e1 e2) se :=
    f <- SemExp e1 se ;
    x <- SemExp e2 se ;
    f x;

  SemExp (Let x body) se :=
    x' <- SemExp x se ;
    SemExp body (x', se);

  SemExp Error     _ := throw Err_Expr;
  SemExp (Catch e) _ :=
    λ s,
      match SemExp e se s with
      | inl err     => pure (inl tt) s
      | inr (v, s') => inr (inr v, s')
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

Corollary SemExp_VAR_ZV `(se : SemEnv Γ) `(x : ⟦τ⟧) :
  ⟦ (x, se) ⊨ VAR ZV ⟧ = pure x.
Proof. reflexivity. Qed.

Lemma SemExp_ValueP {Γ τ} (e : Exp Γ τ) (se : SemEnv Γ) :
  ValueP e -> ∃ x, ⟦ se ⊨ e ⟧ = pure x.
Proof.
  induction 1; reduce; simp SemExp;
  eexists; extensionality st; sauto lq: on.
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
  ∀ s, ∃ s', ⟦ se ⊨ v ⟧ s = inr (x, s').

Arguments safeP {_} _ {_} _ _ /.

Definition eval `(e : Exp [] τ) s (v : ⟦τ⟧) s' :=
  ⟦ e ⟧ s = inr (v, s').

Notation "e ~[ s => u ]~> t" :=
  (eval e s t u) (at level 40, u at next level, t at next level).

Lemma sem_app_lam `(e : Exp [dom] cod) (v : Exp [] dom) x s s' :
  v ~[ s => s' ]~> x →
  ⟦ APP (LAM e) v ⟧ s = ⟦ (x, tt) ⊨ e ⟧ s'.
Proof.
  unfold eval.
  intros.
  simp SemExp; simpl.
  autounfold.
  unfold StateT_join, Ltac.comp, Prelude.apply, Tuple.curry.
  simpl.
  unfold Either_map, Either_join, Tuple.first.
  rewrite H.
  destruct (⟦ (x, tt) ⊨ e ⟧ s'); auto.
Qed.
