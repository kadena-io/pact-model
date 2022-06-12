Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.micromega.Lia
  Coq.Classes.Morphisms
  Coq.Relations.Relation_Definitions
  Coq.Strings.String
  Coq.Vectors.Vector
  Coq.Lists.List
  Coq.Sets.Ensembles
  Coq.Logic.EqdepFacts.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Inductive Ty :=
  | TUnit
  | TFunc : Ty → Ty → Ty.

Infix "⟶" := TFunc (at level 30, right associativity).

Fixpoint SemTy (τ : Ty) : Type :=
  match τ with
  | TUnit => unit
  | TFunc dom cod => SemTy dom → SemTy cod
  end.

Definition Env := list Ty.

Fixpoint SemEnv E : Type :=
  match E with
  | []     => ()
  | τ :: E => SemTy τ * SemEnv E
  end.

(* This version also works, but is a little more difficult *)

(* Inductive SemEnv : Env → Type := *)
(*   | ANil      : SemEnv [] *)
(*   | ACons τ Γ : SemTy τ → SemEnv Γ → SemEnv (τ :: Γ). *)

(* Notation "·" := Empty. *)
(* Notation "Γ ⸴ A ： τ" := (@Cons τ A _ _ Γ) (at level 80, right associativity). *)

Inductive Var : Env → Ty → Set :=
  | ZV Γ τ    : Var (τ :: Γ) τ
  | SV Γ τ τ' : Var Γ τ → Var (τ' :: Γ) τ.

Arguments ZV {_ _}.
Arguments SV {_ _ _} _.

(* Notation "Γ ∋ A ： τ" := (@Var _ _ Γ τ A) (at level 80, no associativity). *)

Inductive Exp Γ : Ty → Set :=
  | VAR {τ}       : Var Γ τ → Exp Γ τ
  | ABS {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod.

Arguments VAR {Γ τ} _.
Arguments ABS {Γ dom cod} _.
Arguments APP {Γ dom cod} _ _.

Definition Sub Γ Γ' := ∀ {τ}, Var Γ τ → Exp Γ' τ.

Definition idSub {Γ} : Sub Γ Γ := @VAR Γ.

(*
Program Definition consSub {Γ Γ' τ} (e : Exp Γ' τ)
        (s : Sub Γ Γ') : Sub (τ :: Γ) Γ' :=
  λ _ v, match v with
         | ZV    => e
         | SV v' => s _ v'
         end.
*)

Equations consSub {Γ Γ' τ} (e : Exp Γ' τ) (s : Sub Γ Γ')
          τ' (v : Var (τ :: Γ) τ') : Exp Γ' τ' :=
  consSub e s τ' ZV      := e;
  consSub e s τ' (SV v') := s _ v'.

Notation "{| e ; .. ; f |}" := (consSub e .. (consSub f idSub) ..).

Definition tlSub {Γ Γ' τ} (s : Sub (τ :: Γ) Γ') : Sub Γ Γ' :=
  fun τ' v => s τ' (SV v).
Definition hdSub {Γ Γ' τ} (s : Sub (τ :: Γ) Γ') : Exp Γ' τ := s τ ZV.

Definition Ren Γ Γ' := ∀ {τ}, Var Γ τ → Var Γ' τ.

Definition idRen {Γ} : Ren Γ Γ := λ _, id.

Definition tlRen {Γ Γ' τ} (r : Ren (τ :: Γ) Γ') : Ren Γ Γ' :=
  fun τ' v => r τ' (SV v).
Definition hdRen {Γ Γ' τ} (r : Ren (τ :: Γ) Γ') : Var Γ' τ := r τ ZV.

Definition skip1 {Γ τ} : Ren Γ (τ :: Γ) := λ _, SV.

Equations skipn {Γ} Γ' : Ren Γ (Γ' ++ Γ) :=
  skipn []        := λ _, id;
  skipn (x :: xs) := λ τ v, SV (skipn xs τ v).

Equations trunc {Γ} Γ' `(E : SemEnv (Γ' ++ Γ)) : SemEnv Γ :=
  trunc []        E := E;
  trunc (x :: xs) E := trunc xs (snd E).

(*
Program Definition RTmL {Γ Γ' τ} (r : Ren Γ Γ') :
        Ren (τ :: Γ) (τ :: Γ') :=
  λ _ v, match v with
         | ZV    => ZV
         | SV v' => SV (r _ v')
         end.
*)

(* This version gives better rewriting equations. *)
Equations RTmL {Γ Γ' τ} (r : Ren Γ Γ')
          τ' (v : Var (τ :: Γ) τ') : Var (τ :: Γ') τ' :=
  RTmL r τ' ZV      := ZV;
  RTmL r τ' (SV v') := SV (r _ v').

Lemma RTmL_id {Γ τ} : @RTmL Γ Γ τ (λ _, id) = λ _, id.
Proof.
  extensionality τ'.
  extensionality v.
  dependent induction v.
  - now rewrite RTmL_equation_1.
  - now rewrite RTmL_equation_2.
Qed.

Fixpoint RTmExp {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ τ) : Exp Γ' τ :=
  match e with
  | VAR v     => VAR (r _ v)
  | APP e1 e2 => APP (RTmExp r e1) (RTmExp r e2)
  | ABS e     => ABS (RTmExp (RTmL r) e)
  end.

Definition wk {Γ τ τ'} : Exp Γ τ → Exp (τ' :: Γ) τ := RTmExp (λ _, SV).

(*
Program Definition STmL {Γ Γ' τ} (s : Sub Γ Γ') :
        Sub (τ :: Γ) (τ :: Γ') :=
  λ _ v, match v with
         | ZV    => VAR ZV
         | SV v' => wk (s _ v')
         end.
*)

Equations STmL {Γ Γ' τ} (s : Sub Γ Γ') τ' (v : Var (τ :: Γ) τ') :
  Exp (τ :: Γ') τ' :=
  STmL _ τ' ZV      := VAR ZV;
  STmL _ τ' (SV v') := wk (s _ v').

Fixpoint STmExp {Γ Γ' τ} (s : Sub Γ Γ') (e : Exp Γ τ) : Exp Γ' τ :=
  match e with
  | VAR v     => s _ v
  | APP e1 e2 => APP (STmExp s e1) (STmExp s e2)
  | ABS e     => ABS (STmExp (STmL s) e)
  end.

Inductive Ev : ∀ {τ}, Exp [] τ → Exp [] τ → Prop :=
  | EvAbs t1 t2 (e : Exp [t1] t2) : Ev (ABS e) (ABS e)
  | EvApp t1 t2 e v w (e1 : Exp [] (t1 ⟶ t2)) e2 :
    Ev e1 (ABS e) → Ev e2 w → Ev (STmExp {| w |} e) v →
    Ev (APP e1 e2) v.

(* Notation "Γ ⊢ e ： τ" := (Judgment Γ τ e) (at level 80, no associativity). *)

Definition identity Γ τ : Exp Γ (τ ⟶ τ) := ABS (VAR ZV).

Definition compose {Γ τ τ' τ''}
           (f : Exp Γ (τ' ⟶ τ''))
           (g : Exp Γ (τ ⟶ τ')) : Exp Γ (τ ⟶ τ'') :=
  ABS (APP (wk f) (APP (wk g) (VAR ZV))).

Fixpoint SemVar `(v : Var Γ τ) : SemEnv Γ → SemTy τ :=
  match v with
  | ZV   => λ se, fst se
  | SV v => λ se, SemVar v (snd se)
  end.

Fixpoint SemExp `(e : Exp Γ τ) : SemEnv Γ → SemTy τ :=
  match e with
  | VAR v     => SemVar v
  | ABS e     => λ se, λ x, SemExp e (x, se)
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

Definition RcR {Γ Γ' Γ''} (r : Ren Γ' Γ'') (r' : Ren Γ Γ') :=
  (λ τ v, r τ (r' τ v)) : Ren Γ Γ''.

Definition ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') :=
  (λ τ v, s τ (r τ v)) : Sub Γ Γ''.

Definition RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') :=
  (λ τ v, RTmExp r (s τ v)) : Sub Γ Γ''.

Definition ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (s' : Sub Γ Γ') :=
  (λ τ v, STmExp s (s' τ v)) : Sub Γ Γ''.

Lemma LiftRcR Γ Γ' Γ'' τ (r : Ren Γ' Γ'') (r' : Ren Γ Γ') :
  RTmL (τ := τ) (RcR r r') = RcR (RTmL r) (RTmL r').
Proof.
  extensionality τ'.
  extensionality v.
  now dependent induction v.
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
  (∀ (τ : Ty) (x : SemTy τ) (Γ : Env) (E : SemEnv Γ),
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

Corollary tlRen_skip1 Γ τ τ' :
  @tlRen _ (τ :: τ' :: Γ) _ skip1 = RcR skip1 skip1.
Proof. reflexivity. Qed.

Lemma SemRen_skip1 (Γ : Env) (τ : Ty) :
  SemRen skip1 = @snd (SemTy τ) (SemEnv Γ).
Proof.
  extensionality E.
  generalize dependent τ.
  induction Γ; simpl; intros; auto.
  - now destruct E as [x ()].
  - destruct E as [x [y E]]; simpl.
    f_equal.
    rewrite tlRen_skip1.
    rewrite SemRen_RcR.
    unfold Basics.compose.
    rewrite IHΓ.
Admitted.

Lemma SemRen_id (Γ : Env) :
  SemRen idRen = @id (SemEnv Γ).
Proof.
  unfold id.
  extensionality E.
  induction E using SemEnv_rect; simpl; auto.
  f_equal.
  replace (tlRen idRen) with (skip1 (Γ:=Γ) (τ:=τ)) by auto.
  now rewrite SemRen_skip1.
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

Lemma compose_left_identity `(E : SemEnv Γ)
      {τ τ'} (f : Exp Γ (τ ⟶ τ')) :
  SemExp (compose f (identity Γ τ)) E = SemExp f E.
Proof.
  rewrite SemExp_compose.
  reflexivity.
Qed.

Lemma compose_right_identity `(E : SemEnv Γ)
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
