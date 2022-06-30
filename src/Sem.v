Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.Lists.List
  Ty
  Exp
  Ren
  Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Section Sem.

Context {t : Type}.
Variable SemT : t → Type.

Fixpoint SemTy (τ : Ty t) : Type :=
  match τ with
  | TYP y => SemT y
  | TARR dom cod => SemTy dom → SemTy cod
  end.

Fixpoint SemEnv E : Type :=
  match E with
  | []     => unit
  | τ :: E => SemTy τ * SemEnv E
  end.

Equations trunc {Γ} Γ' `(E : SemEnv (Γ' ++ Γ)) : SemEnv Γ :=
  trunc []        E := E;
  trunc (x :: xs) E := trunc xs (snd E).

Fixpoint SemVar `(v : Var t Γ τ) : SemEnv Γ → SemTy τ :=
  match v with
  | ZV   => λ se, fst se
  | SV v => λ se, SemVar v (snd se)
  end.

Fixpoint SemRen {Γ Γ'} : Ren Γ' Γ → SemEnv Γ → SemEnv Γ' :=
  match Γ' with
  | []     => λ r se, tt
  | _ :: _ => λ r se, (SemVar (hdRen r) se, SemRen (tlRen r) se)
  end.

Lemma SemRenVarComm Γ τ (v : Var t Γ τ) Γ' (r : Ren Γ Γ') :
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
  generalize dependent Γ'.
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
              @SV t (Γ ++ Γ') τ a (@skipn t Γ' Γ τ v))
       with (RcR (Γ:=Γ') (skip1 (τ:=a)) (skipn Γ))
         by reflexivity.
    rewrite SemRen_RcR.
    now rewrite SemRen_skip1.
Qed.

Corollary SemRen_SV_snd Γ τ :
  SemRen (λ _, SV) = @snd (SemTy τ) (SemEnv Γ).
Proof. exact (SemRen_skipn [τ] Γ). Qed.

Corollary SemRen_SV `(E : SemEnv Γ) `(x : SemTy τ) :
  SemRen (λ _, SV) (x, E) = E.
Proof. now rewrite SemRen_SV_snd. Qed.

Context {x : Ty t → Type}.

Variable SemX : ∀ Γ (τ : Ty t), x τ → SemEnv Γ → SemTy τ.

Hypothesis SemX_SemRen : ∀ Γ Γ' τ z r E,
  SemX Γ τ z (SemRen r E) = SemX Γ' τ z E.

Fixpoint SemExp `(e : Exp t x Γ τ) : SemEnv Γ → SemTy τ :=
  match e with
  | TERM r    => SemX _ _ r
  | VAR v     => SemVar v
  | LAM e     => λ se, λ x, SemExp e (x, se)
  | APP e1 e2 => λ se, SemExp e1 se (SemExp e2 se)
  end.

Fixpoint SemSub {Γ Γ'} : Sub Γ' Γ → SemEnv Γ → SemEnv Γ' :=
  match Γ' with
  | []     => λ s se, tt
  | _ :: _ => λ s se, (SemExp (hdSub s) se, SemSub (tlSub s) se)
  end.

Hypothesis SemX_SemSub : ∀ Γ Γ' τ z s E,
  SemX Γ τ z (SemSub s E) = SemX Γ' τ z E.

Lemma SemRenComm Γ τ (e : Exp t x Γ τ) Γ' (r : Ren Γ Γ') :
  ∀ se, SemExp e (SemRen r se) = SemExp (RTmExp r e) se.
Proof.
  intros.
  generalize dependent Γ'.
  induction e; simpl; intros.
  - now apply SemX_SemRen.
  - induction v; simpl.
    + reflexivity.
    + now rewrite IHv.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    f_equal.
    clear.
    f_equal.
    unfold tlRen.
    induction Γ; simpl; auto.
    f_equal.
    rewrite IHΓ; clear IHΓ.
    reflexivity.
  - now rewrite IHe1, IHe2.
Qed.

Lemma SemExp_wk `(E : SemEnv Γ)
      {τ τ'} (y : SemTy τ') (e : Exp t x Γ τ) :
  SemExp (wk e) (y, E) = SemExp e E.
Proof.
  unfold wk.
  rewrite <- SemRenComm; simpl.
  f_equal.
  now eapply SemRen_SV; eauto.
Qed.

Lemma SemSubComm Γ τ (e : Exp t x Γ τ) Γ' (s : Sub Γ Γ') :
  ∀ se, SemExp e (SemSub s se) = SemExp (STmExp s e) se.
Proof.
  intros.
  generalize dependent Γ'.
  induction e; simpl; intros.
  - now apply SemX_SemSub.
  - induction v; simpl.
    + reflexivity.
    + now rewrite IHv.
  - extensionality z.
    fold SemTy in z.
    rewrite <- IHe; clear IHe.
    simpl.
    f_equal.
    clear -SemX_SemRen.
    f_equal.
    unfold tlSub.
    induction Γ; simpl; auto.
    f_equal.
    + unfold hdSub.
      clear -SemX_SemRen.
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
      {τ τ' τ''} (f : Exp t x Γ (τ' ⟶ τ'')) (g : Exp t x Γ (τ ⟶ τ')) :
  SemExp (compose f g) E = SemExp f E ∘ SemExp g E.
Proof.
  extensionality z.
  fold SemTy in z.
  unfold compose; simpl.
  now rewrite !SemExp_wk.
Qed.

Lemma SemExp_compose_identity_right `(E : SemEnv Γ)
      {τ τ'} (f : Exp t x Γ (τ ⟶ τ')) :
  SemExp (compose f (identity Γ τ)) E = SemExp f E.
Proof.
  rewrite SemExp_compose.
  reflexivity.
Qed.

Lemma SemExp_compose_identity_left `(E : SemEnv Γ)
      {τ τ'} (f : Exp t x Γ (τ ⟶ τ')) :
  SemExp (compose (identity Γ τ') f) E = SemExp f E.
Proof.
  rewrite SemExp_compose.
  reflexivity.
Qed.

Lemma SemExp_compose_assoc `(E : SemEnv Γ)
      {τ τ' τ'' τ'''}
      (f : Exp t x Γ (τ'' ⟶ τ'''))
      (g : Exp t x Γ (τ' ⟶ τ''))
      (h : Exp t x Γ (τ ⟶ τ')) :
  SemExp (compose f (compose g h)) E = SemExp (compose (compose f g) h) E.
Proof.
  rewrite !SemExp_compose.
  now rewrite compose_assoc.
Qed.

End Sem.

Class Sem (t : Type) (x : Ty t → Type) := {
  SemT : t → Type;
  SemX {Γ τ} : x τ → SemEnv SemT Γ → SemTy SemT τ;

  SemX_SemRen {Γ Γ' τ z} r E :
    SemX (Γ:=Γ) (τ:=τ) z (SemRen SemT r E) = SemX (Γ:=Γ') z E;
  SemX_SemSub {Γ Γ' τ z} s E :
    SemX (Γ:=Γ) (τ:=τ) z (SemSub SemT (@SemX) s E) = SemX (Γ:=Γ') z E
}.
