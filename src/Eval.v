Require Import
  Coq.ZArith.ZArith
  Hask.Control.Lens
  Hask.Control.Monad
  Pact.Data.Either
  Pact.Data.IList
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Value
  Pact.Lang
  Pact.SemTy
  Pact.SemExp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Definition eval `(e : [] ⊢ τ) : Err + (⟦τ⟧ * PactLog) :=
  match SemExp e tt newPactEnv newPactState with
  | inl err => inl err
  | inr (result, (_finalState, log)) => inr (result, log)
  end.

Definition evalInModule (nm : string) `(e : [] ⊢ τ) : Err + (⟦τ⟧ * PactLog) :=
  match SemExp e tt (newPactEnv &+ context %~ cons (InModule nm))
               newPactState with
  | inl err => inl err
  | inr (result, (_finalState, log)) => inr (result, log)
  end.
