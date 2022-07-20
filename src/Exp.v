Require Import
  Coq.ZArith.ZArith
  Lib
  Ty.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Exp.

Import ListNotations.

Inductive Literal : PrimType → Set :=
  | LitString  : string → Literal PrimString
  | LitInteger : Z → Literal PrimInteger
  | LitDecimal : N → N → Literal PrimDecimal
  | LitUnit    : Literal PrimUnit
  | LitBool    : bool → Literal PrimBool
  | LitTime    : nat → Literal PrimTime.

Derive Signature NoConfusion NoConfusionHom Subterm EqDec for Literal.

Open Scope Ty_scope.

Inductive Builtin : Ty → Set :=
  | AddInt : Builtin (ℤ ⟶ ℤ ⟶ ℤ).

Derive Signature NoConfusion NoConfusionHom Subterm EqDec for Builtin.

Definition Env := list Ty.

Inductive Var : Env → Ty → Set :=
  | ZV {Γ τ}    : Var (τ :: Γ) τ
  | SV {Γ τ τ'} : Var Γ τ → Var (τ' :: Γ) τ.

Derive Signature NoConfusion NoConfusionHom Subterm EqDec for Var.

Inductive Err : Set :=
  | Err_CarNil
  | Err_CdrNil.

Derive NoConfusion NoConfusionHom Subterm EqDec for Err.

Inductive Exp Γ : Ty → Set :=
  | VAR {τ}       : Var Γ τ → Exp Γ τ
  | LAM {dom cod} : Exp (dom :: Γ) cod → Exp Γ (dom ⟶ cod)
  | APP {dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Exp Γ cod

  (* The following terms represent Pact beyond lambda calculus. *)
  | Error {τ}     : Err → Exp Γ τ

  | Lit {ty}      : Literal ty → Exp Γ (TyPrim ty)
  | Bltn {τ}      : Builtin τ → Exp Γ τ

  | Symbol        : string → Exp Γ TySym

  | If {τ}        : Exp Γ 𝔹 → Exp Γ τ → Exp Γ τ → Exp Γ τ

  | Pair {τ1 τ2}  : Exp Γ τ1 → Exp Γ τ2 → Exp Γ (TyPair τ1 τ2)
  | Fst {τ1 τ2}   : Exp Γ (TyPair τ1 τ2) → Exp Γ τ1
  | Snd {τ1 τ2}   : Exp Γ (TyPair τ1 τ2) → Exp Γ τ2

  | Nil {τ}       : Exp Γ (TyList τ)
  | Cons {τ}      : Exp Γ τ → Exp Γ (TyList τ) → Exp Γ (TyList τ)
  | Car {τ}       : Exp Γ (TyList τ) → Exp Γ τ
  | Cdr {τ}       : Exp Γ (TyList τ) → Exp Γ (TyList τ)
  | IsNil {τ}     : Exp Γ (TyList τ) → Exp Γ 𝔹

  | Seq {τ τ'}    : Exp Γ τ' → Exp Γ τ → Exp Γ τ

  | Capability {p v} :
    ConcreteP p →
    ConcreteP v →
    Exp Γ TySym →
    Exp Γ p →
    Exp Γ v →
    Exp Γ (TyCap p v)

  | WithCapability {p v τ} :
    ConcreteP p →
    ConcreteP v →
    Exp Γ (TyCap p v ⟶ TyList TyACap) →
    Exp Γ (v × v ⟶ v) →
    Exp Γ (TyCap p v) → Exp Γ τ → Exp Γ τ

  | ComposeCapability {p v} :
    ConcreteP p →
    ConcreteP v →
    Exp Γ (TyCap p v ⟶ TyList TyACap) →
    Exp Γ (v × v ⟶ v) →
    Exp Γ (TyCap p v) → Exp Γ 𝕌

  | InstallCapability {p v} : Exp Γ (TyCap p v) → Exp Γ 𝕌
  | RequireCapability {p v} : Exp Γ (TyCap p v) → Exp Γ 𝕌.

Derive Signature NoConfusionHom Subterm EqDec for Exp.

Fixpoint Exp_size {Γ τ} (e : Exp Γ τ) : nat :=
  match e with
  | VAR _ v     => 1
  | LAM _ e     => 1 + Exp_size e
  | APP _ e1 e2 => 1 + Exp_size e1 + Exp_size e2

  | Error _ _   => 1
  | Lit _ _     => 1
  | Bltn _ _    => 1
  | Symbol _ _  => 1
  | If _ b t e  => 1 + Exp_size b + Exp_size t + Exp_size e
  | Pair _ x y  => 1 + Exp_size x + Exp_size y
  | Fst _ p     => 1 + Exp_size p
  | Snd _ p     => 1 + Exp_size p
  | Nil _       => 1
  | Cons _ x xs => 1 + Exp_size x + Exp_size xs
  | Car _ xs    => 1 + Exp_size xs
  | Cdr _ xs    => 1 + Exp_size xs
  | IsNil _ xs  => 1 + Exp_size xs
  | Seq _ x y   => 1 + Exp_size x + Exp_size y

  | Capability _ _ _ n p v => 1 + Exp_size n + Exp_size p + Exp_size v
  | WithCapability _ _ _ p m c e =>
      1 + Exp_size p + Exp_size m + Exp_size c + Exp_size e
  | ComposeCapability _ _ _ p m c =>
      1 + Exp_size p + Exp_size m + Exp_size c
  | InstallCapability _ c => 1 + Exp_size c
  | RequireCapability _ c => 1 + Exp_size c
  end.

Corollary Exp_size_preserved {Γ τ} (e1 e2 : Exp Γ τ) :
  Exp_size e1 ≠ Exp_size e2 → e1 ≠ e2.
Proof. repeat intro; subst; contradiction. Qed.

End Exp.

Arguments ZV {_ _}.
Arguments SV {_ _ _} _.

Arguments VAR {Γ τ} _.
Arguments LAM {Γ dom cod} _.
Arguments APP {Γ dom cod} _ _.
Arguments Error {Γ τ} _.
Arguments Lit {Γ ty} _.
Arguments Bltn {Γ τ} _.
Arguments Symbol {Γ} _.
Arguments If {Γ τ} _ _ _.
Arguments Pair {Γ τ1 τ2} _ _.
Arguments Fst {Γ τ1 τ2} _.
Arguments Snd {Γ τ1 τ2} _.
Arguments Nil {Γ τ}.
Arguments Cons {Γ τ} _ _.
Arguments Car {Γ τ} _.
Arguments Cdr {Γ τ} _.
Arguments IsNil {Γ τ} _.
Arguments Seq {Γ τ τ'} _ _.
Arguments Capability {_ p v} _ _ _.
Arguments WithCapability {_ p v τ} _ _ _ _ _ _.
Arguments ComposeCapability {_ p v} _ _ _ _ _.
Arguments InstallCapability {_ p v} _.
Arguments RequireCapability {_ p v} _.

Declare Scope Var_scope.
Bind Scope Var_scope with Var.
Delimit Scope Var_scope with var.

Declare Scope Exp_scope.
Bind Scope Exp_scope with Exp.
Delimit Scope Exp_scope with exp.

Notation "Γ ∋ τ" := (Var Γ τ%ty) (at level 10) : type_scope.
Notation "Γ ⊢ τ" := (Exp Γ τ%ty) (at level 10) : type_scope.
