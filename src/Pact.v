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

Fixpoint tdenote (τ : Ty) : Type :=
  match τ with
  | TUnit => unit
  | TFunc dom cod => tdenote dom → tdenote cod
  end.

Definition Env := list Ty.

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

Program Definition consSub {Γ Γ' τ} (e : Exp Γ' τ)
        (s : Sub Γ Γ') : Sub (τ :: Γ) Γ' :=
  λ _ v, match v with
         | ZV    => e
         | SV v' => s _ v'
         end.

Notation "{| e ; .. ; f |}" := (consSub e .. (consSub f idSub) ..).

Definition tlSub {Γ Γ' τ} (s : Sub (τ :: Γ) Γ') : Sub Γ Γ' :=
  fun τ' v => s τ' (SV v).
Definition hdSub {Γ Γ' τ} (s : Sub (τ :: Γ) Γ') : Exp Γ' τ := s τ ZV.

Definition Ren Γ Γ' := ∀ {τ}, Var Γ τ → Var Γ' τ.

(*
Program Definition RTmL {Γ Γ' τ} (r : Ren Γ Γ') : Ren (τ :: Γ) (τ :: Γ') :=
  λ τ' v,
    match v with
    | ZV    => ZV
    | SV v' => SV (r _ v')
    end.
*)

(* This version gives better rewriting equations. *)
Equations RTmL {Γ Γ' τ} (r : Ren Γ Γ')
          τ' (v : Var (τ :: Γ) τ') : Var (τ :: Γ') τ' :=
  RTmL r τ' ZV      := ZV;
  RTmL r τ' (SV v') := SV (r _ v').

Fixpoint rename {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ τ) : Exp Γ' τ :=
  match e with
  | VAR v     => VAR (r _ v)
  | APP e1 e2 => APP (rename r e1) (rename r e2)
  | ABS e     => ABS (rename (RTmL r) e)
  end.

Definition weaken {Γ τ τ'} : Exp Γ τ → Exp (τ' :: Γ) τ := rename (λ _, SV).

Program Definition STmL {Γ Γ' τ} (s : Sub Γ Γ') : Sub (τ :: Γ) (τ :: Γ') :=
  λ _ v, match v with
         | ZV    => VAR ZV
         | SV v' => weaken (s _ v')
         end.

Fixpoint STmExp {Γ Γ' τ} (s : Sub Γ Γ') (e : Exp Γ τ) :=
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
  ABS (APP (weaken f) (APP (weaken g) (VAR ZV))).

Inductive Args (P : Ty → Type) : Env → Type :=
  | ANil      : Args P []
  | ACons τ Γ : P τ → Args P Γ → Args P (τ :: Γ).

Arguments ANil {P}.
Arguments ACons {P _ _} _ _.

Equations get (P : Ty → Type) {Γ : Env} (A : Args P Γ)
          {τ} (v : Var Γ τ) : P τ :=
  get P (ACons x _)  ZV      := x;
  get P (ACons _ xs) (SV v') := get P xs v'.

Equations denote `(A : Args tdenote Γ) `(e : Exp Γ τ) : tdenote τ :=
  denote A (VAR v)   := get tdenote A v;
  denote A (ABS e)   := λ x, denote (ACons x A) e;
  denote A (APP f x) := denote A f (denote A x).

Lemma denote_identity `(A : Args tdenote Γ) τ :
  denote A (identity Γ τ) = id.
Proof.
  extensionality x.
  unfold identity, id.
  rewrite denote_equation_2.
  rewrite denote_equation_1.
  now rewrite get_equation_2.
Qed.

Lemma denote_rename `(A : Args tdenote Γ)
      `(r : Ren Γ Γ') `(A' : Args tdenote Γ') `(e : Exp Γ τ) :
  denote A' (rename r e) = denote A e.
Proof.
  induction e; simpl.
  - rewrite !denote_equation_1.
    admit.
  - rewrite !denote_equation_2.
    extensionality x.
    fold tdenote in x.
    admit.
  - rewrite !denote_equation_3.
    now erewrite IHe1, IHe2.
Admitted.

Lemma helper
  (Γ : Env)
  (A : Args tdenote Γ)
  (τ τ' τ'' : Ty)
  (x : tdenote τ'')
  (dom cod : Ty)
  (f : Exp (dom :: Γ) cod)
  (x0 : tdenote dom)
  :
  denote (ACons x0 (ACons x A)) (rename (RTmL (λ τ0 : Ty, SV)) f) =
  denote (ACons x (ACons x0 A)) (rename (λ τ0 : Ty, SV) f).
Proof.
  dependent induction f; simpl.
  - rewrite !denote_equation_1.
    rewrite get_equation_3.
    dependent destruction v.
    + rewrite !get_equation_2.
      reflexivity.
    + rewrite RTmL_equation_2.
      rewrite !get_equation_3.
      reflexivity.
  - rewrite !denote_equation_2.
    extensionality x1.
    fold tdenote in x1.
    rewrite IHf; auto; clear IHf.
    admit.
  - rewrite !denote_equation_3.
    now rewrite IHf1, IHf2.
Admitted.

Lemma denote_weaken `(A : Args tdenote Γ)
      {τ τ' τ''} (x : tdenote τ'') (f : Exp Γ (τ ⟶ τ')) :
  denote (ACons x A) (weaken f) = denote A f.
Proof.
  unfold weaken.
  induction f; simpl.
  - now rewrite !denote_equation_1.
  - rewrite !denote_equation_2.
    extensionality x0.
    fold tdenote in x0.
    rewrite <- IHf; clear IHf.
    admit.
  - rewrite denote_equation_3.
    now rewrite IHf1, IHf2.
Admitted.

Lemma denote_compose `(A : Args tdenote Γ)
      {τ τ' τ''} (f : Exp Γ (τ' ⟶ τ'')) (g : Exp Γ (τ ⟶ τ')) :
  denote A (compose f g) = denote A f ∘ denote A g.
Proof.
  extensionality x.
  fold tdenote in x.
  unfold compose.
  rewrite denote_equation_2.
  rewrite !denote_equation_3.
  rewrite denote_equation_1.
  rewrite get_equation_2.
  now rewrite !denote_weaken.
Qed.

Lemma compose_left_identity `(A : Args tdenote Γ)
      {τ τ'} (f : Exp Γ (τ ⟶ τ')) :
  denote A (compose f (identity Γ τ)) = denote A f.
Proof.
  rewrite denote_compose.
  now rewrite denote_identity.
Qed.

Lemma compose_right_identity `(A : Args tdenote Γ)
      {τ τ'} (f : Exp Γ (τ ⟶ τ')) :
  denote A (compose (identity Γ τ') f) = denote A f.
Proof.
  rewrite denote_compose.
  now rewrite denote_identity.
Qed.

Lemma compose_assoc `(A : Args tdenote Γ)
      {τ τ' τ'' τ'''}
      (f : Exp Γ (τ'' ⟶ τ'''))
      (g : Exp Γ (τ' ⟶ τ''))
      (h : Exp Γ (τ ⟶ τ')) :
  denote A (compose f (compose g h)) = denote A (compose (compose f g) h).
Proof.
  rewrite !denote_compose.
  now rewrite compose_assoc.
Qed.
