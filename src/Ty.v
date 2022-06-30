Require Import
  Coq.Unicode.Utf8.

From Equations Require Import Equations.
Set Equations With UIP.

Section Ty.

Variable t : Type.

Inductive Ty : Type :=
  | TYP : t → Ty
  | TARR : Ty → Ty → Ty.

Derive NoConfusion Subterm for Ty.

End Ty.

Arguments TYP {t} _.
Arguments TARR {t} _ _.

Infix "⟶" := TARR (at level 30, right associativity).
