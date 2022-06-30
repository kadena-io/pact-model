Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List
  Ty.

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
  | VAR {τ}       : Var Γ τ → Exp Γ τ
  | LAM {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod

  .

Derive Signature for Exp.

End Exp.

Arguments ZV {_ _}.
Arguments SV {_ _ _} _.

Arguments VAR {Γ τ} _.
Arguments LAM {Γ dom cod} _.
Arguments APP {Γ dom cod} _ _.
