Require Import
  Pact.Lib
  Pact.Ty
  Pact.Exp.

From Equations Require Import Equations.
Set Equations With UIP.
Generalizable All Variables.


Section Pat.

Import ListNotations.

Context {A : Type}.
Context `{HostExprs A}.

Open Scope Ty_scope.

(* Inductive Pat : Env → Ty → Type := *)
(*   | PPair {Γ Γ' τ1 τ2}  : Pat Γ τ1 → Pat Γ' τ2 → Pat (Γ ++ Γ') (TyPair τ1 τ2). *)

(* Derive Signature NoConfusion for Pat. *)

End Pat.
