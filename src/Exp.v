Require Export
  Ty
  Lit
  ilist
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
  | List {τ}      : list (Exp Γ τ) → Exp Γ (TyList τ)
  | Let {τ ty}    : Exp Γ ty → Exp (ty :: Γ) τ → Exp Γ τ

  (* These are the terms of the base lambda calculus *)
  | VAR {τ}       : Var Γ τ → Exp Γ τ
  | LAM {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod.

Derive Signature for Exp.

Variable P : ∀ Γ τ, Exp Γ τ → Type.

Variable Pconstant : ∀ Γ ty (lit : Literal ty),
  P Γ (TyPrim ty) (Constant Γ lit).
Variable Pseq      : ∀ Γ τ τ' (e1 : Exp Γ τ') (e2 : Exp Γ τ),
  P Γ τ' e1 → P Γ τ e2 → P Γ τ (Seq Γ e1 e2).
Variable Plist     : ∀ Γ τ l,
  ilist (P Γ τ) l → P Γ (TyList τ) (List Γ l).
Variable Plet      : ∀ Γ τ ty (x : Exp Γ ty) (body : Exp (ty :: Γ) τ),
  P Γ ty x →
  P (ty :: Γ) τ body →
  P Γ τ (Let _ x body).
Variable Pvar      : ∀ Γ τ (v : Var Γ τ),
  P Γ τ (VAR Γ v).
Variable Plam      : ∀ Γ dom cod (e : Exp (dom :: Γ) cod),
  P (dom :: Γ) cod e → P Γ (dom ⟶ cod) (LAM Γ e).
Variable Papp      : ∀ Γ dom cod (e1 : Exp Γ (dom ⟶ cod)) (e2 : Exp Γ dom),
  P Γ (dom ⟶ cod) e1 →
  P Γ dom e2 →
  P Γ cod (APP Γ e1 e2).

Equations Exp_rect' {Γ τ} (e : Exp Γ τ) : P Γ τ e :=
  Exp_rect' (Constant _ lit) := Pconstant _ _ lit;
  Exp_rect' (Seq _ e1 e2)    := Pseq _ _ _ _ _ (Exp_rect' e1) (Exp_rect' e2);
  Exp_rect' (List _ l)       := Plist _ _ _ (Exp_sub_rect' l);
  Exp_rect' (Let _ x body)   := Plet _ _ _ _ _ (Exp_rect' x) (Exp_rect' body);
  Exp_rect' (VAR _ v)        := Pvar _ _ v;
  Exp_rect' (LAM _ e)        := Plam _ _ _ _ (Exp_rect' e);
  Exp_rect' (APP _ e1 e2)    := Papp _ _ _ _ _ (Exp_rect' e1) (Exp_rect' e2);

where Exp_sub_rect' {Γ τ} (l : list (Exp Γ τ)) : ilist (P Γ τ) l :=
  Exp_sub_rect' [] := tt;
  Exp_sub_rect' (x :: xs) := (Exp_rect' x, Exp_sub_rect' xs).

End Exp.

Arguments ZV {_ _}.
Arguments SV {_ _ _} _.

Arguments Constant {Γ ty} _.
Arguments Seq {Γ τ τ'} _ _.
Arguments List {Γ τ} _.
Arguments Let {Γ τ ty} _ _.
Arguments VAR {Γ τ} _.
Arguments LAM {Γ dom cod} _.
Arguments APP {Γ dom cod} _ _.
