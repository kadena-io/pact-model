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
  | Seq {τ τ'}    : Exp Γ τ' → Exp Γ τ → Exp Γ τ
  (* The first list contains terms that need to be evaluated;
     the second is a reversed list of terms in normal form. *)
  | List {τ}      : list (Exp Γ τ) → Exp Γ (TyList τ)
  | Let {τ ty}    : Exp Γ ty → Exp (ty :: Γ) τ → Exp Γ τ

  (* These are the terms of the base lambda calculus *)
  | VAR {τ}       : Var Γ τ → Exp Γ τ
  | LAM {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod.

Derive Signature NoConfusionHom Subterm for Exp.

Fixpoint Exp_size {Γ τ} (e : Exp Γ τ) : nat :=
  match e with
  | Constant _ x => 1
  | Seq _ x y    => 1 + Exp_size x + Exp_size y
  | List _ x     => 1 + fold_left plus (map Exp_size x) 0%nat
  | Let _ x body => 1 + Exp_size x + Exp_size body
  | VAR _ v      => 1
  | LAM _ e      => 1 + Exp_size e
  | APP _ e1 e2  => 1 + Exp_size e1 + Exp_size e2
  end.

Corollary Exp_size_preserved {Γ τ} (e1 e2 : Exp Γ τ) :
  Exp_size e1 ≠ Exp_size e2 → e1 ≠ e2.
Proof.
  repeat intro; subst.
  contradiction.
Qed.

Section Exp_rect.

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

Fixpoint Exp_rect' {Γ τ} (e : Exp Γ τ) : P Γ τ e.
Proof.
  induction e.
  - now apply Pconstant.
  - now apply Pseq.
  - apply Plist.
    induction l.
    * exact tt.
    * split.
      ** now apply Exp_rect'.
      ** exact IHl.
  - now apply Plet.
  - now apply Pvar.
  - now apply Plam.
  - now apply Papp.
Qed.

End Exp_rect.

(* [ValueP] is an inductive proposition that indicates whether an expression
   represents a value, i.e., that it does reduce any further. *)
Inductive ValueP Γ : ∀ {τ}, Exp Γ τ → Prop :=
  | ConstantP {ty} (l : Literal ty) :
    ValueP Γ (Constant Γ l)
  | ListP {τ} (l : list (Exp Γ τ)) :
    Forall (ValueP Γ) l →
    ValueP Γ (List Γ l)
  | ClosureP {dom cod} (e : Exp (dom :: Γ) cod) :
    ValueP Γ (LAM Γ e).

Arguments ZV {_ _}.
Arguments SV {_ _ _} _.

Arguments Constant {Γ ty} _.
Arguments Seq {Γ τ τ'} _ _.
Arguments List {Γ τ} _.
Arguments Let {Γ τ ty} _ _.
Arguments VAR {Γ τ} _.
Arguments LAM {Γ dom cod} _.
Arguments APP {Γ dom cod} _ _.

Arguments ValueP {Γ τ} _.
Arguments ConstantP {Γ ty} _.
Arguments ListP {Γ τ} _.
Arguments ClosureP {Γ dom cod} _.
