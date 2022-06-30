Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List
  Ty.

From Equations Require Import Equations.
Set Equations With UIP.

Import ListNotations.

Section Exp.

Variable t : Type.

Definition Env := list (Ty t).

Inductive Var : Env → Ty t → Type :=
  | ZV Γ τ    : Var (τ :: Γ) τ
  | SV Γ τ τ' : Var Γ τ → Var (τ' :: Γ) τ.

Derive Signature NoConfusion for Var.

Variable x : Env → Ty t → Type.

Inductive Exp Γ : Ty t → Type :=
  | TERM {τ}      : x Γ τ → Exp Γ τ
  | VAR {τ}       : Var Γ τ → Exp Γ τ
  | LAM {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod.

Derive Signature for Exp.

End Exp.

Arguments ZV {_ _ _}.
Arguments SV {_ _ _ _} _.

Arguments TERM {t x Γ τ} _.
Arguments VAR {t x Γ τ} _.
Arguments LAM {t x Γ dom cod} _.
Arguments APP {t x Γ dom cod} _ _.
