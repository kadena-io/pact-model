Require Import
  Coq.Unicode.Utf8.

From Equations Require Import Equations.
Set Equations With UIP.

Section Ty.

Inductive Ty : Type :=
  | TARR : Ty → Ty → Ty

  .

Derive NoConfusion for Ty.

End Ty.

Arguments TARR _ _.

Infix "⟶" := TARR (at level 30, right associativity).
