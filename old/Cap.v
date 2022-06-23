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

Fixpoint uniq `(l : list A) : Prop :=
  match l with
  | [] => True
  | x :: xs => ~ List.In x xs ∧ uniq xs
  end.

Inductive Ty :=
  | TUnit
  | TPair : Ty → Ty → Ty
  | TSum : Ty → Ty → Ty
  | TList : Ty → Ty
  | TFunc : Ty → Ty → Ty.

Derive NoConfusion for Ty.
Derive Subterm for Ty.
Derive EqDec for Ty.

Derive NoConfusion for Ascii.ascii.
Derive Subterm for Ascii.ascii.
Derive EqDec for Ascii.ascii.

Derive NoConfusion for string.
Derive Subterm for string.
Derive EqDec for string.

Infix "⟶" := TFunc (at level 30, right associativity).

Definition Env := list Ty.

Inductive Var : Env → Ty → Set :=
  | ZV {Γ τ}    : Var (τ :: Γ) τ
  | SV {Γ τ τ'} : Var Γ τ → Var (τ' :: Γ) τ.

Arguments ZV {_ _}.
Arguments SV {_ _ _} _.

(* Notation "Γ ∋ A ： τ" := (@Var _ _ Γ τ A) (at level 80, no associativity). *)

Definition CEnv := list (string * Ty).

Fixpoint is_in `{EqDec A} (v : A) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: xs => if eq_dec v x then true else is_in v xs
  end.

Fixpoint included `{EqDec A} (l m : list A) : bool :=
  match l with
  | [] => true
  | x :: xs => is_in x m && included xs m
  end.

(* [C] represents the set of capabilities that must be provided for this
   expression to be evaluated. *)
Inductive Exp Γ : CEnv → Ty → Type :=
  | VAR {C τ} : Var Γ τ → Exp Γ C τ

  | LAM {C C' dom cod} : Exp (dom :: Γ) C' cod → Exp Γ C (dom ⟶ cod)
  | APP {C dom cod} : Exp Γ C (dom ⟶ cod) → Exp Γ C dom → Exp Γ C cod

  | WITH {C C' : CEnv} n {a τ} :
    Exp Γ C a → Exp Γ C' τ → included C C' = true → is_in (n, a) C' = true → Exp Γ C τ
  | REQ {C C' : CEnv} n {a τ} :
    Exp Γ C a → Exp Γ C' τ → included C C' = true → is_in (n, a) C' = true → Exp Γ C' τ

  | LIFT {C C' τ} : Exp Γ C' τ → Exp Γ C τ.

Inductive Cap (e : Ty) Γ : CEnv → Type :=
  | CAP  {name a}   : Cap e Γ [(name, a)]
  | MCAP {name a b} : Exp Γ [] (b ⟶ b ⟶ TSum e b) → Cap e Γ [(name, TPair a b)]
  | COMP {x xs}     : Cap e Γ [x] → Cap e Γ xs → Cap e Γ (x :: xs).

Arguments VAR {Γ C τ} _.
Arguments LAM {Γ C dom cod} _.
Arguments APP {Γ C dom cod} _ _.
Arguments WITH {Γ C C'} n {a τ} _ _ _ _.
Arguments REQ {Γ C C'} n {a τ} _ _ _ _.
Arguments LIFT {Γ C C' τ} _.

Definition Sub Γ Γ' := ∀ C τ, Var Γ τ → Exp Γ' C τ.

Definition idSub {Γ} : Sub Γ Γ := @VAR Γ.

(*
Program Definition consSub {Γ Γ' τ} (e : Exp Γ' τ)
        (s : Sub Γ Γ') : Sub (τ :: Γ) Γ' :=
  λ _ v, match v with
         | ZV    => e
         | SV v' => s _ v'
         end.
*)

Definition empty_included `{EqDec A} `(C : list A) : included [] C = true.
Proof. reflexivity. Qed.

Equations consSub {Γ Γ' C τ} (e : Exp Γ' C τ) (s : Sub Γ Γ')
          C' τ' (v : Var (τ :: Γ) τ') : Exp Γ' C' τ' :=
  consSub e s C' τ' ZV      := LIFT e;
  consSub e s C' τ' (SV v') := s _ _ v'.

Notation "{| e ; .. ; f |}" := (consSub e .. (consSub f idSub) ..).

Definition tlSub {Γ Γ' τ} (s : Sub (τ :: Γ) Γ') : Sub Γ Γ' :=
  fun C τ' v => s C τ' (SV v).
Definition hdSub {Γ Γ' C τ} (s : Sub (τ :: Γ) Γ') : Exp Γ' C τ := s C τ ZV.

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
Program Definition RTmL {Γ Γ' C τ} (r : Ren Γ Γ') :
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

Fixpoint RTmExp {Γ Γ' C τ} (r : Ren Γ Γ') (e : Exp Γ C τ) : Exp Γ' C τ :=
  match e with
  | VAR v            => VAR (r _ v)
  | APP e1 e2        => APP (RTmExp r e1) (RTmExp r e2)
  | LAM e            => LAM (RTmExp (RTmL r) e)
  | WITH n d e H1 H2 => WITH n (RTmExp r d) (RTmExp r e) H1 H2
  | REQ n d e H1 H2  => REQ n  (RTmExp r d) (RTmExp r e) H1 H2
  | LIFT e           => LIFT (RTmExp r e)
  end.

Definition wk {Γ C τ τ'} : Exp Γ C τ → Exp (τ' :: Γ) C τ := RTmExp (λ _, SV).

(*
Program Definition STmL {Γ Γ' C τ} (s : Sub Γ Γ') :
        Sub (τ :: Γ) (τ :: Γ') :=
  λ _ v, match v with
         | ZV    => VAR ZV
         | SV v' => wk (s _ v')
         end.
*)

Equations STmL {Γ Γ' τ} (s : Sub Γ Γ')
          C τ' (v : Var (τ :: Γ) τ') : Exp (τ :: Γ') C τ' :=
  STmL _ C τ' ZV      := VAR ZV;
  STmL _ C τ' (SV v') := wk (s _ _ v').

Equations STmExp {Γ Γ'} (s : Sub Γ Γ') {C τ} (e : Exp Γ C τ) : Exp Γ' C τ :=
  STmExp s (VAR v)            := s _ _ v;
  STmExp s (APP e1 e2)        := APP (STmExp s e1) (STmExp s e2);
  STmExp s (LAM e)            := LAM (STmExp (STmL s) e);
  STmExp s (WITH n d e H1 H2) := WITH n (STmExp s d) (STmExp s e) H1 H2;
  STmExp s (REQ n d e H1 H2)  := REQ n (STmExp s d) (STmExp s e) H1 H2;
  STmExp s (LIFT e)           := LIFT (STmExp s e).

(*
Definition Chg C C' := ∀ Γ τ, Exp Γ C τ → Exp Γ C' τ.

Equations CTmExp {C C'} (c : Chg C C') {Γ τ} (e : Exp Γ C τ) : Exp Γ C' τ :=
  CTmExp c (VAR v)      := s _ _ v;
  CTmExp c (APP e1 e2)  := APP (STmExp s e1) (STmExp s e2);
  CTmExp c (LAM e)      := LAM (STmExp (STmL s) e);
  CTmExp c (WITH n a e) := WITH n (STmExp s a0) (STmExp s e);
  CTmExp c (REQ n a e)  := REQ n (STmExp s a) (STmExp s e);
  CTmExp c (LIFT e H)   := LIFT (STmExp s e) H.
*)

Lemma empty_incl `(C : list A) : incl [] C.
Proof.
  repeat intro.
  inversion H.
Qed.

(* Having a capability in hand discharges an expressions liability with regard
   to that capability. *)
(* Definition discharge *)

Inductive Ev : ∀ C {τ}, Exp [] C τ → ∀ C', Exp [] C' τ → Prop :=
  | EvAbs C t1 t2 (e : Exp [t1] C t2) : Ev C (LAM e) C (LAM e)

  | EvApp C C1 C2 t1 t2 (e1 : Exp [] C (t1 ⟶ t2)) e e2 (w : Exp [] C2 t1) v :
    Ev C e1 C1 (LAM e) →
    Ev C e2 C2 w →
    Ev C1 (STmExp (consSub w idSub) e) C1 v →
    Ev C (APP e1 e2) C1 v

  | EvWith C t n a (d d' : Exp [] C a) C' (e : Exp [] C' t) v err :
    Cap err [] C' →
    ∀ H1 : included C C' = true,
    ∀ H2 : is_in (n, a) C' = true,
    List.In (n, a) C' →
    Ev C d d' →
    Ev C' e v →
    Ev C (WITH n d e H1 H2) v

  | EvReq C t n a (d d' : Exp [] C a) C' (e : Exp [] C' t) v err :
    Cap err [] C' →
    ∀ H1 : included C C' = true,
    ∀ H2 : is_in (n, a) C' = true,
    List.In (n, a) C' →
    Ev C d d' →
    Ev C' e v →
    Ev C' (REQ n d e H1 H2) (LIFT v).

  | EvLift C t n a (d d' : Exp [] C a) C' (e : Exp [] C' t) v err :
    Cap err [] C' →
    ∀ H1 : included C C' = true,
    ∀ H2 : is_in (n, a) C' = true,
    List.In (n, a) C' →
    Ev C d d' →
    Ev C' e v →
    Ev C (LIFT e) (LIFT v).

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
