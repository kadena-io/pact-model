Require Export
  Ty
  Lit
  ilist
  Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Import ListNotations.

Definition Env := list Ty.

Inductive Var : Env → Ty → Type :=
  | ZV Γ τ    : Var (τ :: Γ) τ
  | SV Γ τ τ' : Var Γ τ → Var (τ' :: Γ) τ.

Derive Signature NoConfusion for Var.

Inductive Exp Γ : Ty → Type :=
  | Constant {ty} : Literal ty → Exp Γ (TyPrim ty)

  | EUnit         : Exp Γ TyUnit

  | ETrue         : Exp Γ TyBool
  | EFalse        : Exp Γ TyBool
  | If {τ}        : Exp Γ TyBool → Exp Γ τ → Exp Γ τ → Exp Γ τ

  | Pair {τ1 τ2}  : Exp Γ τ1 → Exp Γ τ2 → Exp Γ (TyPair τ1 τ2)
  | Fst {τ1 τ2}   : Exp Γ (TyPair τ1 τ2) → Exp Γ τ1
  | Snd {τ1 τ2}   : Exp Γ (TyPair τ1 τ2) → Exp Γ τ2

  | Seq {τ τ'}    : Exp Γ τ' → Exp Γ τ → Exp Γ τ

  | Let {τ ty}    : Exp Γ ty → Exp (ty :: Γ) τ → Exp Γ τ

  (* These are the terms of the base lambda calculus *)
  | VAR {τ}       : Var Γ τ → Exp Γ τ
  | LAM {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod.

Derive Signature NoConfusionHom Subterm for Exp.

Notation "Γ ⊢ τ" := (Exp Γ τ) (at level 100).

Fixpoint Exp_size {Γ τ} (e : Exp Γ τ) : nat :=
  match e with
  | Constant _ x => 1
  | EUnit _      => 1
  | ETrue _      => 1
  | EFalse _     => 1
  | If _ b t e   => 1 + Exp_size b + Exp_size t + Exp_size e
  | Pair _ x y   => 1 + Exp_size x + Exp_size y
  | Fst _ p      => 1 + Exp_size p
  | Snd _ p      => 1 + Exp_size p
  | Seq _ x y    => 1 + Exp_size x + Exp_size y
  | Let _ x body => 1 + Exp_size x + Exp_size body
  | VAR _ v      => 1
  | LAM _ e      => 1 + Exp_size e
  | APP _ e1 e2  => 1 + Exp_size e1 + Exp_size e2
  end.

Corollary Exp_size_preserved {Γ τ} (e1 e2 : Exp Γ τ) :
  Exp_size e1 ≠ Exp_size e2 → e1 ≠ e2.
Proof. repeat intro; subst; contradiction. Qed.

(* [ValueP] is an inductive proposition that indicates whether an expression
   represents a value, i.e., that it does reduce any further. *)
Inductive ValueP Γ : ∀ {τ}, Exp Γ τ → Prop :=
  | ConstantP {ty} (l : Literal ty) :
    ValueP Γ (Constant Γ l)
  | UnitP : ValueP Γ (EUnit Γ)
  | TrueP : ValueP Γ (ETrue Γ)
  | FalseP : ValueP Γ (EFalse Γ)
  | PairP {τ1 τ2} {x : Exp Γ τ1} {y : Exp Γ τ2} :
    ValueP Γ x → ValueP Γ y → ValueP Γ (Pair Γ x y)
  | ClosureP {dom cod} (e : Exp (dom :: Γ) cod) : ValueP Γ (LAM Γ e).

Arguments ZV {_ _}.
Arguments SV {_ _ _} _.

Arguments Constant {Γ ty} _.
Arguments EUnit {Γ}.
Arguments ETrue {Γ}.
Arguments EFalse {Γ}.
Arguments If {Γ τ} _ _ _.
Arguments Pair {Γ τ1 τ2} _ _.
Arguments Fst {Γ τ1 τ2} _.
Arguments Snd {Γ τ1 τ2} _.
Arguments Seq {Γ τ τ'} _ _.
Arguments Let {Γ τ ty} _ _.
Arguments VAR {Γ τ} _.
Arguments LAM {Γ dom cod} _.
Arguments APP {Γ dom cod} _ _.

Arguments ValueP {Γ τ} _.
Arguments ConstantP {Γ ty} _.
Arguments UnitP {Γ}.
Arguments TrueP {Γ}.
Arguments FalseP {Γ}.
Arguments PairP {Γ τ1 τ2 x y} _ _.
Arguments ClosureP {Γ dom cod} _.
