Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.micromega.Lia
  Coq.Classes.Morphisms
  Coq.Relations.Relation_Definitions
  Coq.Strings.String
  Coq.Vectors.Vector
  Coq.Sets.Ensembles
  Coq.Logic.EqdepFacts.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Generalizable All Variables.

Import VectorNotations.

Inductive type :=
  | TUnit
  | TBool
  | TFunc : type → type → type.

Infix "⟶" := TFunc (at level 30, right associativity).

Fixpoint tdenote (τ : type) : Type :=
  match τ with
  | TUnit => unit
  | TBool => bool
  | TFunc dom cod => tdenote dom → tdenote cod
  end.

Inductive Env : ∀ {n}, Vector.t type n → Type :=
  | Empty : Env []
  | Cons {τ} : tdenote τ → ∀ {n} {ts : Vector.t type n}, Env ts → Env (τ :: ts).

Notation "·" := Empty.
Notation "Γ ⸴ A ： τ" := (@Cons τ A _ _ Γ) (at level 80, right associativity).

Import EqNotations.

Equations get {n} {ts : Vector.t type n} (Γ : Env ts) (i : Fin.t n) :
  tdenote ts[@i] :=
  get (Γ ⸴ A ： _) Fin.F1     := A;
  get (Γ ⸴ _ ： _) (Fin.FS i) := get Γ i.

Inductive Lookup :
  ∀ {n} {ts : Vector.t type n}, Env ts → ∀ {τ : type}, tdenote τ → Type :=
  | Here {τ} (A : tdenote τ) {n} {ts : Vector.t type n} (Γ : Env ts) :
    Lookup (Γ ⸴ A ： τ) A
  | There {τ} (A : tdenote τ) {n} {ts : Vector.t type n} (Γ : Env ts) :
    Lookup Γ A → ∀ {u} {B : tdenote u}, Lookup (Γ ⸴ B ： u) A.

Notation "Γ ∋ A ： τ" := (@Lookup _ _ Γ τ A) (at level 80, no associativity).

Fixpoint Position {n} {ts : Vector.t type n} {Γ : Env ts} {τ} {A : tdenote τ}
         (H : Γ ∋ A ： τ) : Fin.t n :=
  match H with
  | Here _ _     => Fin.F1
  | There _ _ Γ' => Fin.FS (Position Γ')
  end.

Inductive exp : ∀ {n}, Vector.t type n → type → Set :=
  | Var {n} {ts : Vector.t type n} (i : Fin.t n) : exp ts ts[@i]
  | Abs {n} {ts : Vector.t type n} dom {cod} :
    exp (dom :: ts) cod → exp ts (dom ⟶ cod)
  | App {n} {ts : Vector.t type n} {dom cod} :
    exp ts (dom ⟶ cod) → exp ts dom → exp ts cod.

Equations denote {n} {ts : Vector.t type n} (Γ : Env ts)
          {τ} (e : exp ts τ) : tdenote τ :=
  denote Γ (Var i)     := get Γ i;
  denote Γ (Abs dom e) := λ x : tdenote dom, denote (Γ ⸴ x ： dom) e;
  denote Γ (App f x)   := denote Γ f (denote Γ x).

Inductive Judgment :
  ∀ {n} {ts : Vector.t type n}, Env ts → ∀ τ : type, exp ts τ → Type :=
  | Emptiness τ e : Judgment · τ e

  | Assignment {n} {ts : Vector.t type n} (Γ : Env ts) τ x i :
    ∀ (H : Γ ∋ x ： τ), i = Position H →
    Judgment Γ ts[@i] (Var i)

  | Abstraction {n} {ts : Vector.t type n} (Γ : Env ts) τ τ' x e :
    Judgment (Γ ⸴ x ： τ) τ' e →
    Judgment Γ (τ ⟶ τ') (Abs τ e)

  | Application {n} {ts : Vector.t type n} (Γ : Env ts) τ τ' e₀ e₁ :
    Judgment Γ (τ ⟶ τ') e₀ →
    Judgment Γ τ e₁ →
    Judgment Γ τ' (App e₀ e₁).

Notation "Γ ⊢ e ： τ" := (Judgment Γ τ e) (at level 80, no associativity).

Definition Exp t := ∀ {n} {ts : Vector.t type n}, exp ts t.

Definition identity τ : Exp (τ ⟶ τ) := λ _ _, Abs τ (Var Fin.F1).

(* (f : Y -> Z) (g : X -> Y) : X -> Z := λ x : X, f (g x) *)

(*
Definition subst {n} (f : Vector.t type n → Vector.t type n)
           {ts : Vector.t type n} {τ} (e : exp ts τ) : exp (f ts) τ.
Proof.
  induction e.
  - admit.
  - apply Abs.
    simpl in IHe.
    admit.
  - eapply App; eauto.
*)

(* Equations swap {n} {ts : Vector.t type n} {τ τ' τ''} *)
(*           (e : exp (τ :: τ' :: ts) τ'') : exp (τ' :: τ :: ts) τ'' := *)
(*   swap (Var Fin.F1)          := Var (Fin.FS Fin.F1); *)
(*   swap (Var (Fin.FS Fin.F1)) := Var Fin.F1; *)
(*   swap (Var i)               := Var i; *)
(*   swap (Abs dom body)        := Abs dom (swap body); *)
(*   swap (App f x)             := App (swap f) (swap x). *)

(* Equations weaken {n} {ts : Vector.t type n} {τ τ'} *)
(*           (e : exp ts τ) : exp (τ' :: ts) τ := *)
(*   weaken (Var i)        := Var (Fin.FS i); *)
(*   weaken (Abs dom body) := Abs dom _; *)
(*   weaken (App f x)      := App (weaken f) (weaken x). *)
(* Next Obligation. *)
(* Admitted. *)

Definition compose {τ τ' τ''}
           (f : Exp (τ' ⟶ τ''))
           (g : Exp (τ ⟶ τ')) : Exp (τ ⟶ τ'') :=
  λ n ts, Abs τ (App (f _ _) (App (g _ _) (@Var (S n) (τ :: ts) Fin.F1))).

Lemma denote_identity {n} {ts : Vector.t type n} (Γ : Env ts) τ :
  denote Γ (identity τ n ts) = id.
Proof.
  extensionality t.
  unfold identity, id.
  rewrite denote_equation_2.
  rewrite denote_equation_1.
  now rewrite get_equation_2.
Qed.

Lemma denote_compose {n} {ts : Vector.t type n} (Γ : Env ts)
      {τ τ' τ''} (f : Exp (τ' ⟶ τ'')) (g : Exp (τ ⟶ τ')) :
  denote Γ (compose f g n ts) = denote Γ (f n ts) ∘ denote Γ (g n ts).
Proof.
  extensionality t.
  unfold compose, Basics.compose.
  rewrite denote_equation_2.
  rewrite !denote_equation_3.
  pose proof (denote_equation_1 (S n) (τ :: ts) (Γ ⸴ t ： τ) Fin.F1).
  simpl in H.
  rewrite H; clear H.
  rewrite get_equation_2.
Admitted.

Lemma compose_left_identity
      {n} {ts : Vector.t type n} (Γ : Env ts)
      {τ τ'} (f : Exp (τ ⟶ τ')) :
  denote Γ (compose f (identity _) n ts) = denote Γ (f n ts).
Proof.
  rewrite denote_compose.
  rewrite denote_identity.
  reflexivity.
Qed.

Lemma compose_right_identity
      {n} {ts : Vector.t type n} (Γ : Env ts)
      {τ τ'} (f : Exp (τ ⟶ τ')) :
  denote Γ (compose (identity _) f n ts) = denote Γ (f n ts).
Proof.
  rewrite denote_compose.
  rewrite denote_identity.
  reflexivity.
Qed.

Lemma compose_assoc
      {n} {ts : Vector.t type n} (Γ : Env ts)
      {τ τ' τ'' τ'''}
      (f : Exp (τ'' ⟶ τ'''))
      (g : Exp (τ' ⟶ τ''))
      (h : Exp (τ ⟶ τ')) :
  denote Γ (compose f (compose g h) n ts) =
  denote Γ (compose (compose f g) h n ts).
Proof.
  rewrite !denote_compose.
  rewrite compose_assoc.
  reflexivity.
Qed.
