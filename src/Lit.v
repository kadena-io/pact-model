Require Export
  Ty
  Coq.Strings.String
  Coq.ZArith.Int
  Coq.QArith.QArith.

From Equations Require Import Equations.
Set Equations With UIP.

Section Lit.

Definition UTCTime : Set := nat.

Inductive Literal : PrimType → Set :=
  | LString  : string → Literal PrimString
  | LInteger : Z → Literal PrimInteger
  | LDecimal : Q → Literal PrimDecimal
  | LBool    : bool → Literal PrimBool
  | LTime    : UTCTime → Literal PrimTime
  | LUnit    : Literal PrimUnit.

Derive NoConfusion for Literal.

End Lit.
