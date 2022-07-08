Require Export
  Ty
  Exp.

From Equations Require Import Equations.

Generalizable All Variables.

Section Value.

Import ListNotations.

Context {A : Type}.
Context `{HostExprs A}.

Open Scope Ty_scope.

Inductive Value : Ty → Type :=
  | HostValue {ty}         : HostExp (TyHost ty) → Value (TyHost ty)
  | VUnit                  : Value TyUnit
  | VTrue                  : Value TyBool
  | VFalse                 : Value TyBool
  | VPair {τ1 τ2}          : Value τ1 → Value τ2 → Value (TyPair τ1 τ2)
  | VNil {τ}               : Value (TyList τ)
  | VCons {τ}              : Value τ → Value (TyList τ) → Value (TyList τ)
  | ClosureExp {dom cod}   : Closure dom cod → Value (dom ⟶ cod)

with Closure : Ty → Ty → Type :=
  | Lambda {dom cod}   : Exp [dom] cod → Closure dom cod
  | Func {dom cod}     : HostExp (dom ⟶ cod) → Closure dom cod.

Derive Signature NoConfusion NoConfusionHom for Value.
Derive Signature NoConfusion NoConfusionHom Subterm for Closure.

Inductive ValEnv : Env → Type :=
  | Empty : ValEnv []
  | Val {Γ τ} : Value τ → ValEnv Γ → ValEnv (τ :: Γ).

Derive Signature NoConfusion NoConfusionHom for ValEnv.

Equations get_value `(s : ValEnv Γ) `(v : Var Γ τ) : Value τ :=
  get_value (Val x _)  ZV     := x;
  get_value (Val _ xs) (SV v) := get_value xs v.

End Value.
