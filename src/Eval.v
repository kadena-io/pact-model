Require Import
  Coq.ZArith.ZArith
  Hask.Control.Monad
  Hask.Data.Either
  Pact.ilist
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Value
  Pact.Ren
  Pact.Sub
  Pact.SemTy
  Pact.Lang
  Pact.SemExp
  Pact.Lang.Capability.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Definition eval `(e : Exp [] τ) : Err + (SemTy (m:=PactM) τ * PactLog) :=
  match SemExp e tt newPactEnv newPactState newPactLog with
  | inl err => inl err
  | inr (result, (_finalState, log)) => inr (result, log)
  end.
