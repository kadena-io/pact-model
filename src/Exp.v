Require Export
  Ty
  Coq.Lists.List.

From Equations Require Import Equations.

Generalizable All Variables.

Section Exp.

Import ListNotations.

Class HostExprs (A : Type) : Type := {
  has_host_types :> HostTypes A;
  HostExp : Ty → Type
}.

Context {A : Type}.
Context `{HostExprs A}.

Open Scope Ty_scope.

Definition Env := list Ty.

Inductive Var : Env → Ty → Type :=
  | ZV Γ τ    : Var (τ :: Γ) τ
  | SV Γ τ τ' : Var Γ τ → Var (τ' :: Γ) τ.

Derive Signature NoConfusion for Var.

Inductive Exp Γ : Ty → Type :=
  | HostedExp {τ}       : HostExp τ → Exp Γ τ
  | HostedVal {ty}      : HostExp (TyHost ty) → Exp Γ (TyHost ty)
  | HostedFun {dom cod} : HostExp (dom ⟶ cod) → Exp Γ (dom ⟶ cod)

  | EUnit               : Exp Γ TyUnit
  | ETrue               : Exp Γ TyBool
  | EFalse              : Exp Γ TyBool
  | If {τ}              : Exp Γ TyBool → Exp Γ τ → Exp Γ τ → Exp Γ τ

  | Pair {τ1 τ2}        : Exp Γ τ1 → Exp Γ τ2 → Exp Γ (TyPair τ1 τ2)
  | Fst {τ1 τ2}         : Exp Γ (TyPair τ1 τ2) → Exp Γ τ1
  | Snd {τ1 τ2}         : Exp Γ (TyPair τ1 τ2) → Exp Γ τ2

  | Nil {τ}             : Exp Γ (TyList τ)
  | Cons {τ}            : Exp Γ τ → Exp Γ (TyList τ) → Exp Γ (TyList τ)
  | Car {τ}             : Exp Γ τ → Exp Γ (TyList τ) → Exp Γ τ
  | Cdr {τ}             : Exp Γ (TyList τ) → Exp Γ (TyList τ)

  | Seq {τ τ'}          : Exp Γ τ' → Exp Γ τ → Exp Γ τ

  (* These are the terms of the base lambda calculus *)
  | VAR {τ}             : Var Γ τ → Exp Γ τ
  | LAM {dom cod}       : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)
  | APP {dom cod}       : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod.

Derive Signature NoConfusionHom for Exp.

Fixpoint Exp_size {Γ τ} (e : Exp Γ τ) : nat :=
  match e with
  | HostedExp _ x => 1
  | HostedVal _ x => 1
  | HostedFun _ x => 1
  | EUnit _       => 1
  | ETrue _       => 1
  | EFalse _      => 1
  | If _ b t e    => 1 + Exp_size b + Exp_size t + Exp_size e
  | Pair _ x y    => 1 + Exp_size x + Exp_size y
  | Fst _ p       => 1 + Exp_size p
  | Snd _ p       => 1 + Exp_size p
  | Nil _         => 1
  | Cons _ x xs   => 1 + Exp_size x + Exp_size xs
  | Car _ d xs    => 1 + Exp_size d + Exp_size xs
  | Cdr _ xs      => 1 + Exp_size xs
  | Seq _ x y     => 1 + Exp_size x + Exp_size y
  | VAR _ v       => 1
  | LAM _ e       => 1 + Exp_size e
  | APP _ e1 e2   => 1 + Exp_size e1 + Exp_size e2
  end.

Corollary Exp_size_preserved {Γ τ} (e1 e2 : Exp Γ τ) :
  Exp_size e1 ≠ Exp_size e2 → e1 ≠ e2.
Proof. repeat intro; subst; contradiction. Qed.

End Exp.

Arguments ZV {A H _ _}.
Arguments SV {A H _ _ _} _.

Arguments HostedExp {A H Γ τ} _.
Arguments HostedVal {A H Γ ty} _.
Arguments HostedFun {A H Γ dom cod} _.
Arguments EUnit {A H Γ}.
Arguments ETrue {A H Γ}.
Arguments EFalse {A H Γ}.
Arguments If {A H Γ τ} _ _ _.
Arguments Pair {A H Γ τ1 τ2} _ _.
Arguments Fst {A H Γ τ1 τ2} _.
Arguments Snd {A H Γ τ1 τ2} _.
Arguments Nil {A H Γ τ}.
Arguments Cons {A H Γ τ} _ _.
Arguments Car {A H Γ τ} _ _.
Arguments Cdr {A H Γ τ} _.
Arguments Seq {A H Γ τ τ'} _ _.
Arguments VAR {A H Γ τ} _.
Arguments LAM {A H Γ dom cod} _.
Arguments APP {A H Γ dom cod} _ _.

Notation "Γ ∋ τ" := (Var Γ τ) (at level 10).
Notation "Γ ⊢ τ" := (Exp Γ τ) (at level 10).
