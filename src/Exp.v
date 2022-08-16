Require Import
  Coq.ZArith.ZArith
  Pact.Lib
  Pact.Ty
  Pact.Bltn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Inductive Literal : PrimType → Set :=
  | LitString  : string → Literal PrimString
  | LitInteger : Z      → Literal PrimInteger
  | LitDecimal : N → N  → Literal PrimDecimal
  | LitUnit    :          Literal PrimUnit
  | LitBool    : bool   → Literal PrimBool
  | LitTime    : nat    → Literal PrimTime.

Derive Signature NoConfusion NoConfusionHom Subterm EqDec for Literal.

Section Exp.

Open Scope Ty_scope.

Variable Γ : Ty → Type.

Inductive Exp : Ty → Type :=
  | VAR {τ}        : Γ τ → Exp τ
  | LAM {dom cod}  : (Γ dom → Exp cod) → Exp (dom ⟶ cod)
  | APP {dom cod}  : Exp (dom ⟶ cod) → Exp dom → Exp cod

  | Let {τ' τ}     : Exp τ' → (Γ τ' → Exp τ) → Exp τ

  (* The following terms represent Pact beyond lambda calculus. *)
  | Error {τ}      : Exp τ
  | Catch {τ}      : Exp τ → Exp (TySum 𝕌 τ)

  | Lit {ty}       : Literal ty → Exp (TyPrim ty)
  | Bltn {τ}       : Builtin τ → Exp τ

  | Symbol         : string → Exp TySym

  | If {τ}         : Exp 𝔹 → Exp τ → Exp τ → Exp τ

  | Pair {τ1 τ2}   : Exp τ1 → Exp τ2 → Exp (TyPair τ1 τ2)
  | Fst {τ1 τ2}    : Exp (TyPair τ1 τ2) → Exp τ1
  | Snd {τ1 τ2}    : Exp (TyPair τ1 τ2) → Exp τ2

  | Inl {τ1 τ2}    : Exp τ1 → Exp (TySum τ1 τ2)
  | Inr {τ1 τ2}    : Exp τ2 → Exp (TySum τ1 τ2)
  | Case {τ1 τ2 τ} : Exp (TySum τ1 τ2) →
                     Exp (τ1 ⟶ τ) → Exp (τ2 ⟶ τ) → Exp τ

  | Nil {τ}        : Exp (TyList τ)
  | Cons {τ}       : Exp τ → Exp (TyList τ) → Exp (TyList τ)
  | Car {τ}        : Exp (TyList τ) → Exp τ
  | Cdr {τ}        : Exp (TyList τ) → Exp (TyList τ)
  | IsNil {τ}      : Exp (TyList τ) → Exp 𝔹

  | Seq {τ τ'}     : Exp τ' → Exp τ → Exp τ

  (** Capabilities *)

  | Capability {p v} :
    ConcreteP p →
    ConcreteP v →
    Exp TySym →
    Exp p →
    Exp v →
    Exp (TyCap p v)

  | WithCapability {p v τ} :
    ConcreteP v →
    Exp TySym →                (* name of the defining module *)
    Exp (TyCap p v ⟶ 𝕌) →     (* throws exception on failure *)
    Exp (v × v ⟶ v) →         (* throws exception on failure *)
    Exp (TyCap p v) → Exp τ → Exp τ

  | ComposeCapability {p v} :
    ConcreteP v →
    Exp TySym →                (* name of the defining module *)
    Exp (TyCap p v ⟶ 𝕌) →     (* throws exception on failure *)
    Exp (v × v ⟶ v) →         (* throws exception on failure *)
    Exp (TyCap p v) → Exp 𝕌

  | InstallCapability {p v} : Exp (TyCap p v) → Exp 𝕌
  | RequireCapability {p v} : Exp (TyCap p v) → Exp 𝕌.

Derive Signature NoConfusionHom Subterm for Exp.

End Exp.

Fixpoint Exp_size `(e : Exp (λ _, unit) τ) : nat :=
  match e with
  | VAR v      => 1
  | LAM e      => 1 + Exp_size (e tt)
  | APP e1 e2  => 1 + Exp_size e1 + Exp_size e2

  | Let x body => 1 + Exp_size x + Exp_size (body tt)

  | Error _    => 1
  | Catch e    => 1 + Exp_size e

  | Lit _ _    => 1
  | Bltn _ _   => 1
  | Symbol _ _ => 1

  | If b t e   => 1 + Exp_size b + Exp_size t + Exp_size e
  | Pair x y   => 1 + Exp_size x + Exp_size y
  | Fst p      => 1 + Exp_size p
  | Snd p      => 1 + Exp_size p

  | Inl p      => 1 + Exp_size p
  | Inr p      => 1 + Exp_size p
  | Case p l r => 1 + Exp_size p + Exp_size l + Exp_size r

  | Nil _      => 1
  | Cons x xs  => 1 + Exp_size x + Exp_size xs
  | Car xs     => 1 + Exp_size xs
  | Cdr xs     => 1 + Exp_size xs
  | IsNil xs   => 1 + Exp_size xs
  | Seq x y    => 1 + Exp_size x + Exp_size y

  | Capability _ _ n p v => 1 + Exp_size n + Exp_size p + Exp_size v
  | WithCapability _ nm p m c e =>
      1 + Exp_size nm + Exp_size p + Exp_size m + Exp_size c + Exp_size e
  | ComposeCapability _ nm p m c =>
      1 + Exp_size nm + Exp_size p + Exp_size m + Exp_size c
  | InstallCapability c => 1 + Exp_size c
  | RequireCapability c => 1 + Exp_size c
  end.

Corollary Exp_size_preserved {τ} (e1 e2 : Exp (λ _, unit) τ) :
  Exp_size e1 ≠ Exp_size e2 → e1 ≠ e2.
Proof. repeat intro; subst; contradiction. Qed.

Arguments Lit {Γ ty} _.
Arguments Bltn {Γ τ} _.
Arguments Error {Γ τ}.
Arguments Symbol {Γ} _.
Arguments Nil {Γ τ}.

Declare Scope Exp_scope.
Bind Scope Exp_scope with Exp.
Delimit Scope Exp_scope with exp.
