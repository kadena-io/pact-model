Require Import
  Coq.Unicode.Utf8.

Inductive Ty :=
  | TUNIT
  | TARR : Ty → Ty → Ty.

Infix "⟶" := TARR (at level 30, right associativity).
