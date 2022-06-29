Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.Lists.List
  STLC.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Fixpoint SemTy (τ : Ty) : Type :=
  match τ with
  | TUNIT => unit
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

Fixpoint SemVar `(v : Var Γ τ) : SemEnv Γ → SemTy τ :=
  match v with
  | ZV   => λ se, fst se
  | SV v => λ se, SemVar v (snd se)
  end.

Fixpoint SemExp `(e : Exp Γ τ) : SemEnv Γ → SemTy τ :=
  match e with
  | VAR v     => SemVar v
  | LAM e     => λ se, λ x, SemExp e (x, se)
  | APP e1 e2 => λ se, SemExp e1 se (SemExp e2 se)
  end.

Fixpoint SemSub {Γ Γ'} : Sub Γ' Γ → SemEnv Γ → SemEnv Γ' :=
  match Γ' with
  | []     => λ s se, tt
  | _ :: _ => λ s se, (SemExp (hdSub s) se, SemSub (tlSub s) se)
  end.

Fixpoint SemRen {Γ Γ'} : Ren Γ' Γ → SemEnv Γ → SemEnv Γ' :=
  match Γ' with
  | []     => λ r se, tt
  | _ :: _ => λ r se, (SemVar (hdRen r) se, SemRen (tlRen r) se)
  end.

Lemma SemRenComm Γ τ (e : Exp Γ τ) Γ' (r : Ren Γ Γ') :
  ∀ se, SemExp e (SemRen r se) = SemExp (RTmExp r e) se.
Proof.
  intros.
  generalize dependent Γ'.
  induction e; simpl; intros.
  - induction v; simpl.
    + reflexivity.
    + now rewrite IHv.
  - extensionality x.
    fold SemTy in x.
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

Definition SemEnv_rect (P : ∀ Γ : Env, SemEnv Γ → Type) :
  P [] tt →
  (∀ (τ : Ty) (Γ : Env) (x : SemTy τ) (E : SemEnv Γ),
      P Γ E → P (τ :: Γ) (x, E)) →
  ∀ (Γ : Env) (E : SemEnv Γ), P Γ E.
Proof.
  intros.
  induction Γ; destruct E.
  - exact X.
  - now apply X0, IHΓ.
Defined.

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

Lemma SemRen_skip1_f (Γ Γ' : Env) (f : Ren Γ' Γ)
      (τ : Ty) (x : SemTy τ) (E : SemEnv Γ) :
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

Lemma SemRen_id (Γ : Env) :
  SemRen idRen = @id (SemEnv Γ).
Proof.
  unfold id.
  extensionality E.
  induction Γ; simpl; intros; auto.
  - now destruct E as [x ()].
  - destruct E as [x E]; simpl.
    f_equal.
    rewrite tlRen_skip1.
    rewrite RcR_idRen_left.
    rewrite <- (RcR_idRen_right _ _ skip1).
    rewrite SemRen_skip1_f.
    apply IHΓ.
Qed.

Lemma SemRen_skip1 (Γ : Env) (τ : Ty) :
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

Lemma SemRen_skipn (Γ Γ' : Env) :
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
    replace (λ (τ : Ty) (v : Var Γ' τ),
              @SV (Γ ++ Γ') τ a (@skipn Γ' Γ τ v))
       with (RcR (Γ:=Γ') (skip1 (τ:=a)) (skipn Γ))
         by reflexivity.
    rewrite SemRen_RcR.
    now rewrite SemRen_skip1.
Qed.

Corollary SemRen_SV_snd (Γ : Env) (τ : Ty) :
  SemRen (λ _, SV) = @snd (SemTy τ) (SemEnv Γ).
Proof. exact (SemRen_skipn [τ] Γ). Qed.

Corollary SemRen_SV `(E : SemEnv Γ) `(x : SemTy τ) :
  SemRen (λ _, SV) (x, E) = E.
Proof. now rewrite SemRen_SV_snd. Qed.

Lemma SemExp_wk `(E : SemEnv Γ)
      {τ τ'} (x : SemTy τ') (e : Exp Γ τ) :
  SemExp (wk e) (x, E) = SemExp e E.
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
  induction e; simpl; intros.
  - induction v; simpl.
    + reflexivity.
    + now rewrite IHv.
  - extensionality x.
    fold SemTy in x.
    rewrite <- IHe; clear IHe.
    simpl.
    f_equal.
    clear.
    f_equal.
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

Theorem Soundness τ (e : Exp [] τ) v :
  Ev e v → SemExp e = SemExp v.
Proof.
  intros.
  induction H; simpl; auto.
  extensionality se.
  destruct se.
  rewrite IHEv1.
  rewrite IHEv2.
  rewrite <- IHEv3.
  simpl.
  rewrite <- SemSubComm.
  simpl.
  unfold hdSub.
  rewrite consSub_equation_1.
  reflexivity.
Qed.

Lemma SemExp_identity `(E : SemEnv Γ) τ :
  SemExp (identity Γ τ) E = id.
Proof.
  extensionality x.
  reflexivity.
Qed.

Lemma SemExp_compose `(E : SemEnv Γ)
      {τ τ' τ''} (f : Exp Γ (τ' ⟶ τ'')) (g : Exp Γ (τ ⟶ τ')) :
  SemExp (compose f g) E = SemExp f E ∘ SemExp g E.
Proof.
  extensionality x.
  fold SemTy in x.
  unfold compose; simpl.
  now rewrite !SemExp_wk.
Qed.

Lemma compose_identity_right `(E : SemEnv Γ)
      {τ τ'} (f : Exp Γ (τ ⟶ τ')) :
  SemExp (compose f (identity Γ τ)) E = SemExp f E.
Proof.
  rewrite SemExp_compose.
  reflexivity.
Qed.

Lemma compose_identity_left `(E : SemEnv Γ)
      {τ τ'} (f : Exp Γ (τ ⟶ τ')) :
  SemExp (compose (identity Γ τ') f) E = SemExp f E.
Proof.
  rewrite SemExp_compose.
  reflexivity.
Qed.

Lemma compose_assoc `(E : SemEnv Γ)
      {τ τ' τ'' τ'''}
      (f : Exp Γ (τ'' ⟶ τ'''))
      (g : Exp Γ (τ' ⟶ τ''))
      (h : Exp Γ (τ ⟶ τ')) :
  SemExp (compose f (compose g h)) E = SemExp (compose (compose f g) h) E.
Proof.
  rewrite !SemExp_compose.
  now rewrite compose_assoc.
Qed.