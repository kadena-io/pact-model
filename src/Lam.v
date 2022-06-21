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

Definition Env := list Ty.

Inductive Var : Env → Ty → Set :=
  | ZV Γ τ    : Var (τ :: Γ) τ
  | SV Γ τ τ' : Var Γ τ → Var (τ' :: Γ) τ.

Arguments ZV {_ _}.
Arguments SV {_ _ _} _.

(* Notation "Γ ∋ A ： τ" := (@Var _ _ Γ τ A) (at level 80, no associativity). *)

Inductive Exp Γ : Ty → Set :=
  | VAR {τ}       : Var Γ τ → Exp Γ τ
  | LAM {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod.

Arguments VAR {Γ τ} _.
Arguments LAM {Γ dom cod} _.
Arguments APP {Γ dom cod} _ _.

Definition Sub Γ Γ' := ∀ τ, Var Γ τ → Exp Γ' τ.

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

Definition Ren Γ Γ' := ∀ τ, Var Γ τ → Var Γ' τ.

Definition idRen {Γ} : Ren Γ Γ := λ _, id.

Definition tlRen {Γ Γ' τ} (r : Ren (τ :: Γ) Γ') : Ren Γ Γ' :=
  fun τ' v => r τ' (SV v).
Definition hdRen {Γ Γ' τ} (r : Ren (τ :: Γ) Γ') : Var Γ' τ := r τ ZV.

Definition skip1 {Γ τ} : Ren Γ (τ :: Γ) := λ _, SV.

Equations skipn {Γ} Γ' : Ren Γ (Γ' ++ Γ) :=
  skipn []        := λ _, id;
  skipn (x :: xs) := λ τ v, SV (skipn xs τ v).

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
  | LAM e     => LAM (RTmExp (RTmL r) e)
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
  | LAM e     => LAM (STmExp (STmL s) e)
  end.

Inductive Ev : ∀ {τ}, Exp [] τ → Exp [] τ → Prop :=
  | EvAbs t1 t2 (e : Exp [t1] t2) : Ev (LAM e) (LAM e)
  | EvApp t1 t2 e v w (e1 : Exp [] (t1 ⟶ t2)) e2 :
    Ev e1 (LAM e) → Ev e2 w → Ev (STmExp {| w |} e) v →
    Ev (APP e1 e2) v.

(* Notation "Γ ⊢ e ： τ" := (Judgment Γ τ e) (at level 80, no associativity). *)

Definition identity Γ τ : Exp Γ (τ ⟶ τ) := LAM (VAR ZV).

Definition compose {Γ τ τ' τ''}
           (f : Exp Γ (τ' ⟶ τ''))
           (g : Exp Γ (τ ⟶ τ')) : Exp Γ (τ ⟶ τ'') :=
  LAM (APP (wk f) (APP (wk g) (VAR ZV))).

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

Corollary tlRen_skip1 Γ τ τ' :
  @tlRen _ (τ :: τ' :: Γ) _ skip1 = RcR skip1 skip1.
Proof. reflexivity. Qed.
