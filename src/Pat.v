Require Import
  Pact.Lib
  Pact.Ty
  Pact.Exp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Open Scope Ty_scope.

(* Inductive Pat : Env → Ty → Type := *)
(*   | PPair {Γ Γ' τ1 τ2}  : Pat Γ τ1 → Pat Γ' τ2 → Pat (Γ ++ Γ') (TyPair τ1 τ2). *)

(* Derive Signature NoConfusion for Pat. *)
