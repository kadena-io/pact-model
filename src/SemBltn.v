Require Import
  Coq.ZArith.ZArith
  Hask.Control.Monad
  Data.Either
  Pact.Lib
  Pact.Bltn
  Pact.SemTy
  Pact.Lang.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Definition add : Z → Z → Z := Z.add.
Definition sub : Z → Z → Z := Z.sub.

Definition arity1 `(f : ty → ty') : ty → PactM ty' :=
  λ n, pure (f n).

Definition arity2 `(f : ty → ty' → ty'') : ty → PactM (ty' → PactM ty'') :=
  λ n, pure (λ m, pure (f n m)).

Definition SemBltn {τ} (bltn : Builtin τ) : SemTy τ :=
  match bltn with
  | AddInt => arity2 add
  | SubInt => arity2 sub
  end.
