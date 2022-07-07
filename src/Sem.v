Require Export
  Coq.Program.Program
  ilist
  Ty
  Exp
  Ren
  Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Sem.

Import ListNotations.

Fixpoint SemTy `{HostTypes A} (τ : Ty) : Type :=
  match τ with
  | TyHost τ        => HostTySem τ
  | TyUnit          => unit
  | TyBool          => bool
  | TyList τ        => list (SemTy τ)
  | TyPair t1 t2    => SemTy t1 * SemTy t2
  | TyArrow dom cod => SemTy dom → SemTy cod
  end.

Class HostExprsSem (A : Type) : Type := {
  has_host_exprs :> HostExprs A;
  HostExpSem {τ} : HostExp τ → SemTy τ;

  CallHost {Γ dom cod} :
    HostExp (dom ⟶ cod) → ∀ v : Exp Γ dom, ValueP v → Exp Γ cod;

  GetBool {Γ} :
    HostExp TyBool → { v : Exp Γ TyBool & ValueP v };
  GetPair {Γ a b} :
    HostExp (TyPair a b) → { v : Exp Γ (TyPair a b) & ValueP v };
  GetList {Γ τ} :
    HostExp (TyList τ) → { v : Exp Γ (TyList τ) & ValueP v };
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

Fixpoint SemExp `(e : Exp Γ τ) : SemEnv Γ → SemTy τ :=
  match e with
  | Hosted x      => λ _, HostExpSem x
  | EUnit         => λ _, tt
  | ETrue         => λ _, true
  | EFalse        => λ _, false
  | If b t e      => λ se, if SemExp b se then SemExp t se else SemExp e se
  | Pair x y      => λ se, (SemExp x se, SemExp y se)
  | Fst p         => λ se, fst (SemExp p se)
  | Snd p         => λ se, snd (SemExp p se)
  | Nil           => λ se, nil
  | Cons x xs     => λ se, SemExp x se :: SemExp xs se
  | Seq exp1 exp2 => λ se, SemExp exp2 se

  | VAR v         => SemVar v
  | LAM e         => λ se x, SemExp e (x, se)
  | APP e1 e2     => λ se, SemExp e1 se (SemExp e2 se)
  end.

Equations SubSem {Γ Γ'} (s : Sub Γ Γ') (se : SemEnv Γ) : SemEnv Γ' :=
  SubSem NoSub      _  := tt;
  SubSem (Push t σ) se := (SemExp t se, SubSem σ se).

Lemma SubSem_inil (s : Sub [] []) :
  SubSem s () = ().
Proof. now dependent elimination s. Qed.

Lemma SemExp_RenSem {Γ Γ' τ} (e : Exp Γ τ) (r : Ren Γ' Γ) (se : SemEnv Γ') :
  SemExp e (RenSem r se) = SemExp (RenExp r e) se.
Proof.
  generalize dependent Γ'.
  induction e; simpl; intros; auto.
  - now rewrite IHe1, IHe2, IHe3.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe.
  - now rewrite IHe.
  - now rewrite IHe1, IHe2.
  - now rewrite SemVar_RenSem.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    now repeat f_equal.
  - now rewrite IHe1, IHe2.
Qed.

Lemma ScR_idRen {Γ Γ'} (s : Sub Γ Γ') :
  ScR s idRen = s.
Proof.
  induction s; simp ScR; auto.
  now rewrite RenExp_idRen, IHs.
Qed.

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

Lemma SemExp_wk `(E : SemEnv Γ) {τ τ'} (y : SemTy τ') (e : Exp Γ τ) :
  SemExp (wk e) (y, E) = SemExp e E.
Proof.
  unfold wk.
  rewrite <- SemExp_RenSem; simpl.
  f_equal.
  now rewrite RenSem_skip1.
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
  - now rewrite IHe1, IHe2, IHe3.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe.
  - now rewrite IHe.
  - now rewrite IHe1, IHe2.
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

Lemma SemExp_identity {Γ τ} (se : SemEnv Γ) :
  SemExp (identity Γ τ) se = id.
Proof. now extensionality e. Qed.

Lemma SemExp_composition `(E : SemEnv Γ)
      {τ τ' τ''} (f : Exp Γ (τ' ⟶ τ'')) (g : Exp Γ (τ ⟶ τ')) :
  SemExp (composition f g) E = SemExp f E ∘ SemExp g E.
Proof.
  extensionality z.
  fold SemTy in z.
  unfold composition; simpl.
  now rewrite !SemExp_wk.
Qed.

Lemma SemExp_composition_identity_right `(E : SemEnv Γ)
      {τ τ'} (f : Exp Γ (τ ⟶ τ')) :
  SemExp (composition f (identity Γ τ)) E = SemExp f E.
Proof.
  rewrite SemExp_composition.
  reflexivity.
Qed.

Lemma SemExp_composition_identity_left `(E : SemEnv Γ)
      {τ τ'} (f : Exp Γ (τ ⟶ τ')) :
  SemExp (composition (identity Γ τ') f) E = SemExp f E.
Proof.
  rewrite SemExp_composition.
  reflexivity.
Qed.

Lemma SemExp_composition_assoc `(E : SemEnv Γ)
      {τ τ' τ'' τ'''}
      (f : Exp Γ (τ'' ⟶ τ'''))
      (g : Exp Γ (τ' ⟶ τ''))
      (h : Exp Γ (τ ⟶ τ')) :
  SemExp (composition f (composition g h)) E =
  SemExp (composition (composition f g) h) E.
Proof.
  rewrite !SemExp_composition.
  now rewrite compose_assoc.
Qed.

End Sem.
