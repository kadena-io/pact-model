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

Record PactLog : Set := MkLog {
  entry : unit
}.

Definition newPactLog : PactLog :=
  MkLog tt.

Definition eval `(e : Exp SemTy τ) : Err + (⟦τ⟧ * PactLog) :=
  match SemExp e newPactState with
  | inl err => inl err
  | inr (result, _finalState) => inr (result, newPactLog)
  end.

Definition evalInModule (nm : string) `(e : Exp SemTy τ) : Err + (⟦τ⟧ * PactLog) :=
  match SemExp e (newPactState &+ context %~ cons (InModule nm)) with
  | inl err => inl err
  | inr (result, _finalState) => inr (result, newPactLog)
  end.
