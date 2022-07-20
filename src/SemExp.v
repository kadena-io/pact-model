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

(* Set Universe Polymorphism. *)

From Equations Require Import Equations.
Set Equations With UIP.

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

Notation "f =<< x" := (x >>= f) (at level 42, right associativity).

Equations SemExp `(e : Exp Γ τ) (se : SemEnv Γ) : PactM (SemTy (m:=PactM) τ) :=
  SemExp (VAR v)     se := pure (SemVar v se);
  SemExp (LAM e)     se := pure (λ x, SemExp e (x, se));
  SemExp (APP e1 e2) se :=
    f <- SemExp e1 se ;
    x <- SemExp e2 se ;
    f x;

  SemExp (Error e)  _ := throw (Err_Exp e);
  SemExp (Lit l)    _ := throw (Err_Exp Err_CarNil); (* jww (2022-07-18): TODO *)
  SemExp (Bltn b)   _ := throw (Err_Exp Err_CarNil); (* jww (2022-07-18): TODO *)
  SemExp (Symbol n) _ := pure (VSymbol n);

  SemExp (If b t e) se :=
    vb <- SemExp b se ;
    match vb : Value TBool with
    | VBool b' =>
      if b' : bool
      then SemExp t se
      else SemExp e se
    end;

  (* SemExp (Pair x y)      se := liftA2 VPair (SemExp x se) (SemExp y se); *)
  (* SemExp (Fst p)         se := fst <$> SemExp p se; *)
  (* SemExp (Snd p)         se := snd <$> SemExp p se; *)

  SemExp Nil           se := pure (VList []);
  (* SemExp (Cons x xs)     se := x'  <- SemExp x se ; *)
  (*                          xs' <- SemExp xs se ; *)
  (*                          pure (x' :: xs'); *)

  (* SemExp (Car xs)        se := xs' <- SemExp xs se ; *)
  (*                          match xs' with *)
  (*                          | []     => throw (Err_Exp Err_CarNil) *)
  (*                          | x :: _ => pure x *)
  (*                          end; *)
  (* SemExp (Cdr xs)        se := xs' <- SemExp xs se ; *)
  (*                          match xs' with *)
  (*                          | []      => throw (Err_Exp Err_CdrNil) *)
  (*                          | _ :: xs => pure xs *)
  (*                          end; *)

  SemExp (IsNil (τ:=ty) xs) se :=
    xs' <- SemExp xs se ;
    match xs' : Value (TList (concreteTy ty)) with
    | VList []        => pure (VBool true)
    | VList (_ :: xs) => pure (VBool false)
    end;

  SemExp (Seq exp1 exp2) se := SemExp exp1 se >> SemExp exp2 se;

  SemExp (Capability (p:=tp) (v:=tv) Hp Hv nm arg val) se :=
      nm'  <- SemExp nm se ;
      arg' <- SemExp arg se ;
      val' <- SemExp val se ;
      match nm' : Value TSymbol with
      | VSymbol name =>
        pure (f:=PactM)
             (Token (s:={| paramTy := concreteTy tp
                         ; valueTy := concreteTy tv |})
                    name (concreteH arg' Hp)
                         (concreteH val' Hv))
      end;

  SemExp (@WithCapability _ tp tv τ Hp Hv prd mng c e) se :=
      c'   <- SemExp c se ;
      prd' <- SemExp prd se ;
      mng' <- SemExp mng se ;
      with_capability
        (s:={| paramTy := concreteTy tp
             ; valueTy := concreteTy tv |})
        c'
        (_ prd')
        (concreteH1 (m:=PactM) (M:=PactM_Monad)
                    (dom:=TyPair tv tv) mng' Hv)
        (SemExp e se);

  SemExp (InstallCapability c) se :=
    install_capability =<< SemExp c se ;;
    pure VUnit;
  SemExp (RequireCapability c) se :=
    require_capability =<< SemExp c se ;;
    pure VUnit;
  SemExp _ _ := _.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation.
  inv Harg;
  now simpl in arg'.
Defined.
Next Obligation.
  inv Hval;
  now simpl in val'.
Defined.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation.

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
