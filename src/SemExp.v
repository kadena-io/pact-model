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

Definition Φ : Ty → Type := SemTy (m:=PactM).

Definition SemLit {ty : PrimType} (l : Literal ty) : SemPrimTy ty :=
  match l with
  | LitString s    => s
  | LitInteger i   => i
  | LitDecimal d _ => d (* jww (2022-07-21): TODO *)
  | LitUnit        => tt
  | LitBool b      => b
  | LitTime t      => t
  end.

Notation "f =<< x" := (x >>= f) (at level 42, right associativity).

Import EqNotations.

Equations SemExp `(e : Exp Φ τ) : PactM (Φ τ) :=
  SemExp (VAR v) := pure v;
  SemExp (LAM e) := pure (λ x, SemExp (e x));

  SemExp (APP e1 e2) :=
    f <- SemExp e1 ;
    x <- SemExp e2 ;
    f x;

  SemExp (Let x body) :=
    x' <- SemExp x ;
    SemExp (body x');

  SemExp Error     := throw Err_Expr;
  SemExp (Catch e) :=
    λ s, match SemExp e s with
         | inl err     => pure (inl tt) s
         | inr (v, s') => inr (inr v, s')
         end;

  SemExp (Symbol n) := pure n;
  SemExp (Lit l)    := pure (SemLit l);
  SemExp (Bltn b)   := pure (SemBltn b);

  SemExp (If b t e) :=
    b' <- SemExp b ;
    if b' : bool
    then SemExp t
    else SemExp e;

  SemExp (Pair x y) :=
    x' <- SemExp x ;
    y' <- SemExp y ;
    pure (x', y');

  SemExp (Fst p) := fst <$> SemExp p;
  SemExp (Snd p) := snd <$> SemExp p;

  SemExp (Inl p) := inl <$> SemExp p;
  SemExp (Inr p) := inr <$> SemExp p;

  SemExp (Case e f g) :=
    e' <- SemExp e ;
    match e' with
    | inl l => SemExp f >>= λ f', f' l
    | inr r => SemExp g >>= λ g', g' r
    end;

  SemExp Nil := pure [];

  SemExp (Cons x xs) :=
    x'  <- SemExp x ;
    xs' <- SemExp xs ;
    pure (x' :: xs');

  SemExp (Car xs) :=
    xs' <- SemExp xs ;
    match xs' with
    | []     => throw Err_CarOfNil
    | x :: _ => pure x
    end;
  SemExp (Cdr xs) :=
    xs' <- SemExp xs ;
    match xs' with
    | []      => throw Err_CdrOfNil
    | _ :: xs => pure xs
    end;

  SemExp (IsNil (τ:=ty) xs) :=
    xs' <- SemExp xs ;
    match xs' with
    | []        => pure true
    | (_ :: xs) => pure false
    end;

  SemExp (Seq exp1 exp2) := SemExp exp1 >> SemExp exp2;

  SemExp (Capability (p:=tp) (v:=tv) Hp Hv nm arg val) :=
    nm'  <- SemExp nm ;
    arg' <- SemExp arg ;
    val' <- SemExp val ;
    pure (Token (s:={| paramTy := reifyTy tp
                     ; valueTy := reifyTy tv |})
                nm'
                (rew <- [λ x, x] (reflectTy_reifyTy (m:=PactM) Hp) in arg')
                (rew <- [λ x, x] (reflectTy_reifyTy (m:=PactM) Hv) in val'));

  SemExp (WithCapability (p:=tp) (v:=tv) Hv modname prd mng c e) :=
    mn'  <- SemExp modname ;
    c'   <- SemExp c ;
    prd' <- SemExp prd ;
    mng' <- SemExp mng ;
    with_capability
      mn'
      (s:={| paramTy := reifyTy tp
           ; valueTy := reifyTy tv |})
      c'
      prd'
      (rew <- [λ x, x → PactM _] (reflectTy_reifyTy (m:=PactM) (PairDecP Hv Hv)) in
       rew <- [λ x, _ → PactM x] (reflectTy_reifyTy (m:=PactM) Hv) in mng')
      (SemExp e);

  SemExp (ComposeCapability (p:=tp) (v:=tv) Hv modname prd mng c) :=
    mn'  <- SemExp modname ;
    c'   <- SemExp c ;
    prd' <- SemExp prd ;
    mng' <- SemExp mng ;
    compose_capability
      mn'
      (s:={| paramTy := reifyTy tp
           ; valueTy := reifyTy tv |})
      c'
      prd'
      (rew <- [λ x, x → PactM _] (reflectTy_reifyTy (m:=PactM) (PairDecP Hv Hv)) in
       rew <- [λ x, _ → PactM x] (reflectTy_reifyTy (m:=PactM) Hv) in mng');

  SemExp (InstallCapability c) := install_capability =<< SemExp c;
  SemExp (RequireCapability c) := require_capability =<< SemExp c.

Notation "⟦ e ⟧" := (SemExp e)  (at level 9).

Lemma SemExp_ValueP {τ} (e : Exp SemTy τ) :
  ValueP e -> ∃ x, ⟦ e ⟧ = pure x.
Proof.
  induction 1; reduce; simp SemExp;
  eexists; extensionality st; sauto lq: on.
Qed.

Definition expM τ := PactM (Φ τ).

(* An expression is considered "pure" if its denotation has no impact
   whatsoever on the state. *)
Definition pureP `(v : Exp SemTy τ) (x : Φ τ) : Prop :=
  ⟦ v ⟧ = pure x.

Arguments pureP {_} _ _ /.

(* An expression is considered "safe" if its denotation can never result in an
   error. *)
Definition safeP `(v : Exp SemTy τ) (x : Φ τ) : Prop :=
  ∀ s, ∃ s', ⟦ v ⟧ s = inr (x, s').

Arguments safeP {_} _ _ /.

Definition eval `(e : Exp SemTy τ) s (v : ⟦τ⟧) s' :=
  ⟦ e ⟧ s = inr (v, s').

Notation "e ~[ s => u ]~> t" :=
  (eval e s t u) (at level 40, u at next level, t at next level).

Lemma sem_app_lam `(e : SemTy dom → Exp SemTy cod) (v : Exp SemTy dom) x s s' :
  v ~[ s => s' ]~> x →
  ⟦ APP (LAM e) v ⟧ s = ⟦ e x ⟧ s'.
Proof.
  unfold eval.
  intros.
  simp SemExp; simpl.
  autounfold.
  unfold StateT_join, Ltac.comp, Prelude.apply, Tuple.curry.
  simpl.
  unfold Either_map, Either_join, Tuple.first.
  rewrite H.
  destruct (⟦ e x ⟧ s'); auto.
Qed.
