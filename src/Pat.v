Require Export
  Ty
  Coq.Lists.List
  Exp.

From Equations Require Import Equations.

Generalizable All Variables.

Section Pat.

Import ListNotations.

Context {A : Type}.
Context `{HostExprs A}.

Open Scope Ty_scope.

Inductive Pat : Env → Ty → Type :=
  | PPair {Γ Γ' τ1 τ2}  : Pat Γ τ1 → Pat Γ' τ2 → Pat (Γ ++ Γ') (TyPair τ1 τ2).

Derive Signature NoConfusion for Pat.

End Pat.
