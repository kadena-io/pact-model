Require Import
  Coq.ZArith.ZArith
  Hask.Control.Lens
  Hask.Control.Monad
  Hask.Data.Either
  Pact.ilist
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Value
  Pact.Lang
  Pact.SemExp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Definition eval `(e : Exp [] τ) : Err + (SemTy τ * PactLog) :=
  match SemExp e tt newPactEnv newPactState newPactLog with
  | inl err => inl err
  | inr (result, (_finalState, log)) => inr (result, log)
  end.

Definition evalInModule (modname : string) `(e : Exp [] τ) :
  Err + (SemTy τ * PactLog) :=
  match SemExp e tt (newPactEnv &+ context %~ cons (InModule modname))
               newPactState newPactLog with
  | inl err => inl err
  | inr (result, (_finalState, log)) => inr (result, log)
  end.
