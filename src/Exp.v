Require Export
  Ty
  Lit
  Coq.Lists.List.

From Equations Require Import Equations.
Set Equations With UIP.

Import ListNotations.

Section Exp.

Definition Env := list Ty.

Inductive Var : Env → Ty → Type :=
  | ZV Γ τ    : Var (τ :: Γ) τ
  | SV Γ τ τ' : Var Γ τ → Var (τ' :: Γ) τ.

Derive Signature NoConfusion for Var.

Inductive Exp Γ : Ty → Type :=
  | Constant {ty} : Literal ty → Exp Γ (TyPrim ty)
  | Seq {τ τ'}    : Exp Γ τ' → Exp Γ τ → Exp Γ τ
  | Nil {τ}       : Exp Γ (TyList τ)
  | Cons {τ}      : Exp Γ τ → Exp Γ (TyList τ) → Exp Γ (TyList τ)
  | Let {τ ty}    : Exp Γ ty → Exp (ty :: Γ) τ → Exp Γ τ

  (* These are the terms of the base lambda calculus *)
  | VAR {τ}       : Var Γ τ → Exp Γ τ
  | LAM {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod.

Derive Signature for Exp.

End Exp.

Arguments ZV {_ _}.
Arguments SV {_ _ _} _.

Arguments Constant {Γ ty} _.
Arguments Seq {Γ τ τ'} _ _.
Arguments Nil {Γ τ}.
Arguments Cons {Γ τ} _ _.
Arguments Let {Γ τ ty} _ _.
Arguments VAR {Γ τ} _.
Arguments LAM {Γ dom cod} _.
Arguments APP {Γ dom cod} _ _.
