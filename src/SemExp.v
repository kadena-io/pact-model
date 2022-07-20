Require Import
  Coq.ZArith.ZArith
  Hask.Control.Monad
  Hask.Data.Either
  ilist
  Lib
  Ty
  Exp
  Value
  Ren
  Sub
  SemTy
  Pact
  Pact.Capability.

From Equations Require Import Equations.

Generalizable All Variables.

Section SemExp.

Import ListNotations.

Definition SemEnv Γ : Type := ilist (SemTy (m:=PactM)) Γ.

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

Definition liftJoin2 `{Monad m} `(f : a -> b -> m c)
           (ma : m a) (mb : m b) : m c :=
   join (liftA2 f ma mb).

Notation "f =<< x" := (x >>= f) (at level 42, right associativity).

Program Fixpoint SemExp `(e : Exp Γ τ) : SemEnv Γ → PactM (SemTy τ) :=
  match e with
  | VAR v         => λ se, pure (SemVar v se)
  | LAM e         => λ se, pure (λ x, SemExp e (x, se))
  | APP e1 e2     => λ se, liftJoin2 (m:=PactM) id (SemExp e1 se) (SemExp e2 se)

  | Error e       => λ _,  throw (Err_Exp e)
  | Lit l         => λ _,  throw (Err_Exp Err_CarNil) (* jww (2022-07-18): TODO *)
  | Bltn b        => λ _,  throw (Err_Exp Err_CarNil) (* jww (2022-07-18): TODO *)
  | Symbol n      => λ _,  pure n
  | If b t e      => λ se, b' <- SemExp b se ;
                           if b' : bool
                           then SemExp t se
                           else SemExp e se
  | Pair x y      => λ se, liftA2 pair (SemExp x se) (SemExp y se)
  | Fst p         => λ se, fst <$> SemExp p se
  | Snd p         => λ se, snd <$> SemExp p se
  | Nil           => λ se, pure nil
  | Cons x xs     => λ se, x'  <- SemExp x se ;
                           xs' <- SemExp xs se ;
                           pure (x' :: xs')
  | Car xs        => λ se, xs' <- SemExp xs se ;
                           match xs' with
                           | []     => throw (Err_Exp Err_CarNil)
                           | x :: _ => pure x
                           end
  | Cdr xs        => λ se, xs' <- SemExp xs se ;
                           match xs' with
                           | []      => throw (Err_Exp Err_CdrNil)
                           | _ :: xs => pure xs
                           end
  | IsNil xs      => λ se, xs' <- SemExp xs se ;
                           match xs' with
                           | []      => pure true
                           | _ :: xs => pure false
                           end
  | Seq exp1 exp2 => λ se, SemExp exp1 se >> SemExp exp2 se

  | @Capability _ tp tv n p v => λ se,
      match Concreteness tp with
      | Some Hp =>
          match Concreteness tv with
          | Some Hv =>
              n' <- SemExp n se ;
              p' <- SemExp p se ;
              v' <- SemExp v se ;
              pure (Token n' (concrete Hp p') (concrete Hv v'))
          | None => throw (Err_Exp Err_CarNil) (* jww (2022-07-19): TODO *)
          end
      | None => throw (Err_Exp Err_CarNil) (* jww (2022-07-19): TODO *)
      end

  | InstallCapability c => λ se, install_capability _ =<< SemExp c se
  | WithCapability c e  => λ se,
      c' <- SemExp c se ;
      with_capability _ c' (SemExp e se)
  | RequireCapability c => λ se, require_capability _ =<< SemExp c se
  end.

Definition sem `(e : Exp [] τ) : Err + SemTy τ := SemExp e tt.
Arguments sem {_} _ /.

Lemma SemExp_RenSem {Γ Γ' τ} (e : Exp Γ τ) (r : Ren Γ' Γ) (se : SemEnv Γ') :
  SemExp e (RenSem r se) = SemExp (RenExp r e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  - rewrite IHe1; repeat f_equal.
    extensionality b.
    now destruct b; simpl.
  - rewrite IHe2; repeat f_equal.
    now apply IHe1.
  - now rewrite IHe.
  - now rewrite IHe.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe.
  - now rewrite IHe.
  - now rewrite IHe.
  - now rewrite IHe1, IHe2.
  - now rewrite SemVar_RenSem.
  - f_equal.
    extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    now repeat f_equal.
  - now rewrite IHe1, IHe2.
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
  try (now eexists; eauto); reduce.
  - admit.                      (* jww (2022-07-18): TODO *)
  - admit.                      (* jww (2022-07-18): TODO *)
  - exists (x1, x0).
    now rewrite H1, H2; simpl.
  - exists (x1 :: x0).
    now rewrite H1, H2; simpl.
Abort.

End SemExp.

Notation "f =<< x" := (x >>= f) (at level 42, right associativity).
