Require Import
  Hask.Control.Monad
  Hask.Data.Either
  ilist
  Lib
  Ty
  Exp
  Value
  Ren
  Sub.

From Equations Require Import Equations.

Generalizable All Variables.

Section Sem.

Import ListNotations.

Fixpoint SemTy `{HostExprs A} (τ : Ty) : Type :=
  match τ with
  (* | TyHost τ        => HostTySem τ *)
  | TyUnit          => unit
  (* | TyBool          => bool *)
  (* | TyList τ        => list (SemTy τ) *)
  (* | TyPair t1 t2    => SemTy t1 * SemTy t2 *)
  | TyArrow dom cod => SemTy dom → Err + SemTy cod
  (* | TyArrow dom cod => SemTy dom → SemTy cod *)
  end.

Class HostExprsSem (A : Type) : Type := {
  has_host_exprs :> HostExprs A;
  (* HostExpSem {τ} : HostExp τ → Err + SemTy τ; *)
  HostExpSem {τ} : HostExp τ → SemTy τ;

  (* HostExpSem_valid {ty} (e : HostExp ty) : *)
  (*   ∃ x, HostExpSem e = pure x; *)

  CallHost {Γ dom cod} :
    HostExp (dom ⟶ cod) → ∀ v : Exp Γ dom, ValueP v → Exp Γ cod;

  Reduce {Γ τ} : HostExp τ → { v : Exp Γ τ & ValueP v };
}.

Context {A : Type}.
Context `{HostExprsSem A}.

Definition SemEnv Γ : Type := ilist SemTy Γ.

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

Fixpoint SemExp `(e : Exp Γ τ) : SemEnv Γ → Err + SemTy τ :=
  match e with
  (* | HostedExp x   => λ _,  HostExpSem x *)
  (* | HostedVal x   => λ _,  HostExpSem x *)
  (* | HostedFun x   => λ _,  HostExpSem x *)
  | Error e       => λ _,  inl e
  | EUnit         => λ _,  pure tt
  (* | ETrue         => λ _,  pure true *)
  (* | EFalse        => λ _,  pure false *)
  (* | If b t e      => λ se, b' <- SemExp b se ; *)
  (*                          SemExp (if b' : bool *)
  (*                                  then t *)
  (*                                  else e) se *)
  (* | Pair x y      => λ se, liftA2 prod (SemExp x se) (SemExp ys se) *)
  (* | Fst p         => λ se, fst <$> SemExp p se *)
  (* | Snd p         => λ se, snd <$> SemExp p se *)
  (* | Nil           => λ se, pure nil *)
  (* | Cons x xs     => λ se, x'  <- SemExp x se ; *)
  (*                          xs' <- SemExp xs se ; *)
  (*                          pure (x' :: xs') *)
  (* | Car xs        => λ se, xs' <- SemExp xs se ; *)
  (*                          match xs' with *)
  (*                          | []     => inl CarOfNil *)
  (*                          | x :: _ => pure x *)
  (*                          end *)
  (* | Cdr xs        => λ se, xs' <- SemExp xs se ; *)
  (*                          pure (match xs' with *)
  (*                                | []      => nil *)
  (*                                | _ :: xs => xs *)
  (*                                end) *)
  (* | IsNil xs      => λ se, xs' <- SemExp xs se ; *)
  (*                          pure (match xs' with *)
  (*                                | []      => true *)
  (*                                | _ :: xs => false *)
  (*                                end) *)
  (* | Seq exp1 exp2 => λ se, SemExp exp1 se >> SemExp exp2 se *)

  | VAR v         => λ se, pure (SemVar v se)
  | LAM e         => λ se, pure (λ x, SemExp e (x, se))
  | APP e1 e2     => λ se, liftJoin2 id (SemExp e1 se) (SemExp e2 se)
  end.

Definition sem `(e : Exp [] τ) : Err + SemTy τ := SemExp e tt.
Arguments sem {_} _ /.

(*
Lemma SemExp_RenSem {Γ Γ' τ} (e : Exp Γ τ) (r : Ren Γ' Γ) (se : SemEnv Γ') :
  SemExp e (RenSem r se) = SemExp (RenExp r e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  (* - now rewrite IHe1, IHe2, IHe3. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe1, IHe2. *)
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
Qed.
(*
  - pose proof (HostExpSem_valid x).
    reduce.
    rewrite H0.
    now eexists.
  - pose proof (HostExpSem_valid f).
    reduce.
    rewrite H0.
    now eexists.
  - rewrite H0, H1; simpl.
    now eexists.
  - rewrite H0, H1; simpl.
    now eexists.
Qed.
*)

(************************************************************************
 * SubSem
 *)

(*
Equations SubSem {Γ Γ'} (s : Sub Γ Γ') (se : SemEnv Γ) : SemEnv Γ' :=
  SubSem NoSub      _  := tt;
  SubSem (Push t σ) se := (SemExp t se, SubSem σ se).

Lemma SubSem_inil (s : Sub [] []) :
  SubSem s () = ().
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
      * now rewrite SemExp_RenSem.
      * dependent elimination r; simp RenSem;
        now rewrite IHs1.
Qed.

Lemma SubSem_idSub {Γ} (se : SemEnv Γ) :
  SubSem idSub se = se.
Proof.
  induction Γ; destruct se; simpl; simp SubSem; simpl; intros; auto.
  rewrite SubSem_ScR.
  rewrite RenSem_skip1.
  now rewrite IHΓ.
Qed.

Lemma SemVar_SubSem {Γ Γ' τ} (v : Var Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemVar v (SubSem s se) = SemExp (SubVar s v) se.
Proof.
  intros.
  induction s; simp SubSem; simp SubVar; simpl.
  - now inversion v.
  - now dependent elimination v; simpl; simp RenVar.
Qed.

Lemma SemExp_SubSem {Γ Γ' τ} (e : Exp Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemExp e (SubSem s se) = SemExp (SubExp s e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  (* - now rewrite IHe1, IHe2, IHe3. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  - now rewrite SemVar_SubSem.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    unfold Keepₛ, Dropₛ; simp SubSem.
    repeat f_equal.
    rewrite SubSem_ScR.
    now rewrite RenSem_skip1.
  - now rewrite IHe1, IHe2.
Qed.

Lemma SubSem_ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (t : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (ScS s t) se = SubSem s (SubSem t se).
Proof.
  generalize dependent Γ''.
  induction s; intros; simpl; simp SubSem; auto.
  now rewrite <- SemExp_SubSem, IHs.
Qed.

Lemma SubSem_RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (RcS r s) se = RenSem r (SubSem s se).
Proof.
  generalize dependent Γ.
  induction r; intros; simpl; simp RcS; simp RenSem; auto;
  dependent elimination s; simp RcS; simp SubSem; simp RenSem.
  now rewrite IHr.
Qed.
*)

(*
Inductive SubSem {Γ Γ'} (s : Sub Γ Γ') (se : SemEnv Γ) : SemEnv Γ' → Type :=
  SubSem NoSub      _  := inr tt;
  SubSem (Push t σ) se := t' <- SemExp t se ;
                          ρ' <- SubSem σ se ;
                          pure (t', ρ').

Equations SubSem {Γ Γ'} (s : Sub Γ Γ') (se : SemEnv Γ) : Err + SemEnv Γ' :=
  SubSem NoSub      _  := inr tt;
  SubSem (Push t σ) se := t' <- SemExp t se ;
                          ρ' <- SubSem σ se ;
                          pure (t', ρ').

Lemma SubSem_inil (s : Sub [] []) :
  SubSem s () = inr ().
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
    dependent induction s1; simp ScR; simp SubSem; auto.
    repeat f_equal; simpl.
    + extensionality z.
      now repeat f_equal.
    + dependent elimination r; simpl in *; simp RenSem in *;
      now rewrite <- SemExp_RenSem.
Qed.

Lemma SubSem_idSub {Γ} (se : SemEnv Γ) :
  SubSem idSub se = inr se.
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
  induction s; simp SubSem; simp SubVar; simpl.
  - now inversion v.
  - dependent elimination v;
    simp SubVar in *; simp SubSem in *; simpl in *.
    rewrite H0 in *; simpl in *.
(*
    dependent elimination v; simpl; simp RenVar; simp SubVar.
    simpl in *.
    destruct (SemExp e se); simpl; auto.
    destruct (SubSem s se); simpl; auto.
    simpl in *.
    cbv.
Qed.
*)

Notation "f =<< x" := (x >>= f) (at level 42, right associativity).

Lemma SemExp_SubSem {Γ Γ' τ} (e : Exp Γ τ) (s : Sub Γ' Γ) (se : SemEnv Γ') :
  SemExp e =<< SubSem s se = SemExp (SubExp s e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  (* - destruct (HostExpSem_valid h) as [? H1]. *)
  (*   rewrite H1; simpl. *)
  -
  (* - now rewrite IHe1, IHe2, IHe3. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe1, IHe2. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  (* - now rewrite IHe. *)
  - now rewrite SemVar_SubSem.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    unfold Keepₛ, Dropₛ; simp SubSem.
    repeat f_equal.
    rewrite SubSem_ScR.
    now rewrite RenSem_skip1.
  - now rewrite IHe1, IHe2.
Qed.

Lemma SubSem_ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (t : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (ScS s t) se = SubSem s (SubSem t se).
Proof.
  generalize dependent Γ''.
  induction s; intros; simpl; simp SubSem; auto.
  now rewrite <- SemExp_SubSem, IHs.
Qed.

Lemma SubSem_RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') (se : SemEnv Γ) :
  SubSem (RcS r s) se = RenSem r (SubSem s se).
Proof.
  generalize dependent Γ.
  induction r; intros; simpl; simp RcS; simp RenSem; auto;
  dependent elimination s; simp RcS; simp SubSem; simp RenSem.
  now rewrite IHr.
Qed.
*)
*)

End Sem.

Notation "f =<< x" := (x >>= f) (at level 42, right associativity).
