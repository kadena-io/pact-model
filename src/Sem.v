Require Export
  Coq.Program.Program
  Ty
  Exp
  Ren
  Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Section Sem.

Definition SemPrim (p : PrimType) : Type :=
  match p with
  | PrimInteger => Z
  | PrimDecimal => Q
  | PrimTime    => UTCTime
  | PrimString  => string
  end.

Fixpoint SemTy (τ : Ty) : Type :=
  match τ with
  | TyPrim p        => SemPrim p
  | TyUnit          => unit
  | TyBool          => bool
  | TyPair t1 t2    => SemTy t1 * SemTy t2
  | TyArrow dom cod => SemTy dom → SemTy cod
  end.

Definition SemEnv Γ : Type := ilist SemTy Γ.

Equations trunc {Γ} Γ' `(E : SemEnv (Γ' ++ Γ)) : SemEnv Γ :=
  trunc []        E := E;
  trunc (x :: xs) E := trunc xs (snd E).

Fixpoint SemVar `(v : Var Γ τ) : SemEnv Γ → SemTy τ :=
  match v with
  | ZV   => λ se, fst se
  | SV v => λ se, SemVar v (snd se)
  end.

Fixpoint SemRen {Γ Γ'} : Ren Γ' Γ → SemEnv Γ → SemEnv Γ' :=
  match Γ' with
  | []     => λ r se, tt
  | _ :: _ => λ r se, (SemVar (hdRen r) se, SemRen (tlRen r) se)
  end.

Lemma SemRenVarComm Γ τ (v : Var Γ τ) Γ' (r : Ren Γ Γ') :
  ∀ se, SemVar v (SemRen r se) = SemVar (r _ v) se.
Proof.
  intros.
  generalize dependent Γ'.
  induction v; simpl; intros; auto.
  unfold tlRen.
  specialize (IHv _ (RcR r skip1)).
  unfold RcR, skip1 in IHv.
  now rewrite <- IHv; clear IHv.
Qed.

Lemma SemRen_RcR {Γ Γ' Γ''} (f : Ren Γ'' Γ') (g : Ren Γ' Γ) :
  SemRen (RcR g f) = SemRen f ∘ SemRen g.
Proof.
  extensionality E.
  unfold Basics.compose.
  unfold RcR.
  induction Γ''; simpl; auto.
  f_equal.
  - unfold hdRen.
    clear.
    now rewrite SemRenVarComm.
  - unfold tlRen.
    specialize (IHΓ'' (RcR f skip1)).
    unfold skip1, RcR in IHΓ''.
    now rewrite <- IHΓ''.
Qed.

Lemma SemRen_skip1_f Γ Γ' (f : Ren Γ' Γ)
      τ (x : SemTy τ) (E : SemEnv Γ) :
  SemRen (RcR skip1 f) (x, E) = SemRen f E.
Proof.
  generalize dependent τ.
  induction Γ'; simpl; intros; auto.
  unfold hdRen.
  f_equal.
  rewrite !tlRen_skip1.
  rewrite !SemRen_RcR.
  rewrite <- compose_assoc.
  rewrite <- !SemRen_RcR.
  now rewrite IHΓ'.
Qed.

Lemma SemRen_id Γ :
  SemRen idRen = @id (SemEnv Γ).
Proof.
  unfold id.
  extensionality E.
  induction Γ; simpl; intros; auto.
  - now destruct E.
  - destruct E as [x E]; simpl.
    f_equal.
    rewrite tlRen_skip1.
    rewrite RcR_idRen_left.
    rewrite <- (RcR_idRen_right _ _ skip1).
    rewrite SemRen_skip1_f.
    apply IHΓ.
Qed.

Lemma SemRen_skip1 Γ τ :
  SemRen skip1 = @snd (SemTy τ) (SemEnv Γ).
Proof.
  extensionality E.
  induction Γ; simpl; intros; auto.
  - now destruct E as [x ()].
  - destruct E as [x [y E]]; simpl.
    f_equal.
    rewrite tlRen_skip1.
    rewrite SemRen_skip1_f.
    rewrite <- (RcR_idRen_right _ _ skip1).
    rewrite SemRen_skip1_f.
    now rewrite SemRen_id.
Qed.

Lemma SemRen_skipn Γ Γ' :
  @SemRen (Γ ++ Γ') _ (skipn Γ) = trunc Γ.
Proof.
  generalize dependent Γ'.
  induction Γ; simpl; intros.
  - rewrite skipn_equation_1.
    extensionality E.
    rewrite trunc_equation_1.
    now rewrite SemRen_id.
  - rewrite skipn_equation_2.
    extensionality E.
    rewrite trunc_equation_2.
    rewrite <- IHΓ.
    replace (λ τ v,
              @SV (Γ ++ Γ') τ a (@skipn Γ' Γ τ v))
       with (RcR (Γ:=Γ') (skip1 (τ:=a)) (skipn Γ))
         by reflexivity.
    rewrite SemRen_RcR.
    now rewrite SemRen_skip1.
Qed.

Corollary SemRen_SV_snd Γ τ :
  SemRen (λ _, SV) = @snd (SemTy τ) (SemEnv Γ).
Proof. exact (SemRen_skipn [τ] Γ). Qed.

Lemma SemRen_RTmL Γ Γ' τ (x : SemTy τ) (se : SemEnv Γ') (r : Ren Γ Γ') :
  SemRen (RTmL r) (x, se) = (x, SemRen r se).
Proof.
  generalize dependent τ.
  induction Γ'; simpl; intros.
Abort.

Corollary SemRen_SV `(E : SemEnv Γ) `(x : SemTy τ) :
  SemRen (λ _, SV) (x, E) = E.
Proof. now rewrite SemRen_SV_snd. Qed.

Definition SemLit `(l : Literal ty) : SemPrim ty :=
  match l with
  | LString  s => s
  | LInteger z => z
  | LDecimal q => q
  | LTime    t => t
  end.

Program Fixpoint SemExp `(e : Exp Γ τ) : SemEnv Γ → SemTy τ :=
  match e with
  | Constant lit  => λ _, SemLit lit
  | EUnit         => λ _, tt
  | ETrue         => λ _, true
  | EFalse        => λ _, false
  | If b t e      => λ se, if SemExp b se then SemExp t se else SemExp e se
  | Pair x y      => λ se, (SemExp x se, SemExp y se)
  | Fst p         => λ se, fst (SemExp p se)
  | Snd p         => λ se, snd (SemExp p se)
  | Seq exp1 exp2 => λ se, SemExp exp2 se
  | Let x body    => λ se, SemExp body (SemExp x se, se)

  | VAR v         => SemVar v
  | LAM e         => λ se x, SemExp e (x, se)
  | APP e1 e2     => λ se, SemExp e1 se (SemExp e2 se)
  end.

Fixpoint SemSub {Γ Γ'} : Sub Γ' Γ → SemEnv Γ → SemEnv Γ' :=
  match Γ' with
  | []     => λ s se, ()
  | _ :: _ => λ s se, (SemExp (hdSub s) se, SemSub (tlSub s) se)
  end.

Lemma SemExp_Let Γ τ ty (e1 : Exp Γ ty) (e2 : Exp (ty :: Γ) τ) se :
  SemExp (Let e1 e2) se = SemExp (APP (LAM e2) e1) se.
Proof. reflexivity. Qed.

Lemma SemRenComm Γ τ (e : Exp Γ τ) Γ' (r : Ren Γ Γ') :
  ∀ se, SemExp e (SemRen r se) = SemExp (RTmExp r e) se.
Proof.
  intros.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  - now rewrite IHe1, IHe2, IHe3.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe.
  - now rewrite IHe.
  - rewrite IHe1; clear IHe1.
    rewrite <- IHe2; clear IHe2.
    simpl.
    repeat f_equal.
    generalize (SemExp (RTmExp r e1) se); intros.
    clear.
    induction Γ; simpl; intros; auto.
    f_equal.
    now rewrite IHΓ.
  - simpl; induction v; simpl.
    + reflexivity.
    + now rewrite IHv.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    repeat f_equal.
    clear.
    induction Γ; simpl; auto.
    f_equal.
    now rewrite IHΓ.
  - now rewrite IHe1, IHe2.
Qed.

Lemma SemExp_wk `(E : SemEnv Γ)
      {τ τ'} (y : SemTy τ') (e : Exp Γ τ) :
  SemExp (wk e) (y, E) = SemExp e E.
Proof.
  unfold wk.
  rewrite <- SemRenComm; simpl.
  f_equal.
  now eapply SemRen_SV; eauto.
Qed.

Lemma SemSubComm Γ τ (e : Exp Γ τ) Γ' (s : Sub Γ Γ') :
  ∀ se, SemExp e (SemSub s se) = SemExp (STmExp s e) se.
Proof.
  intros.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  - now rewrite IHe1, IHe2, IHe3.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe.
  - now rewrite IHe.
  - rewrite IHe1; clear IHe1.
    rewrite <- IHe2; clear IHe2.
    simpl.
    repeat f_equal.
    generalize (SemExp (STmExp s e1) se); intros.
    clear.
    unfold tlSub.
    induction Γ; simpl; intros; auto.
    f_equal.
    + unfold hdSub.
      clear.
      rewrite STmL_equation_2.
      now rewrite SemExp_wk.
    + unfold tlSub.
      rewrite IHΓ; clear IHΓ.
      reflexivity.
  - induction v; simpl.
    + reflexivity.
    + now rewrite IHv.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    repeat f_equal.
    clear.
    unfold tlSub.
    induction Γ; simpl; auto.
    f_equal.
    + unfold hdSub.
      clear.
      rewrite STmL_equation_2.
      now rewrite SemExp_wk.
    + unfold tlSub.
      rewrite IHΓ; clear IHΓ.
      reflexivity.
  - now rewrite IHe1, IHe2.
Qed.

Lemma SemExp_identity `(E : SemEnv Γ) τ :
  SemExp (identity Γ τ) E = id.
Proof. now extensionality z. Qed.

Lemma SemExp_compose `(E : SemEnv Γ)
      {τ τ' τ''} (f : Exp Γ (τ' ⟶ τ'')) (g : Exp Γ (τ ⟶ τ')) :
  SemExp (compose f g) E = SemExp f E ∘ SemExp g E.
Proof.
  extensionality z.
  fold SemTy in z.
  unfold compose; simpl.
  now rewrite !SemExp_wk.
Qed.

Lemma SemExp_compose_identity_right `(E : SemEnv Γ)
      {τ τ'} (f : Exp Γ (τ ⟶ τ')) :
  SemExp (compose f (identity Γ τ)) E = SemExp f E.
Proof.
  rewrite SemExp_compose.
  reflexivity.
Qed.

Lemma SemExp_compose_identity_left `(E : SemEnv Γ)
      {τ τ'} (f : Exp Γ (τ ⟶ τ')) :
  SemExp (compose (identity Γ τ') f) E = SemExp f E.
Proof.
  rewrite SemExp_compose.
  reflexivity.
Qed.

Lemma SemExp_compose_assoc `(E : SemEnv Γ)
      {τ τ' τ'' τ'''}
      (f : Exp Γ (τ'' ⟶ τ'''))
      (g : Exp Γ (τ' ⟶ τ''))
      (h : Exp Γ (τ ⟶ τ')) :
  SemExp (compose f (compose g h)) E =
  SemExp (compose (compose f g) h) E.
Proof.
  rewrite !SemExp_compose.
  now rewrite compose_assoc.
Qed.

End Sem.
