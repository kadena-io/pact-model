Require Export
  Ty
  Coq.Strings.String
  Coq.ZArith.Int
  Coq.QArith.QArith.

From Equations Require Import Equations.
Set Equations With UIP.

Section Lit.

Definition UTCTime : Set := nat.

Inductive Literal : Ty → Set :=
  | LString  : string → Literal (TyPrim PrimString)
  | LInteger : Z → Literal (TyPrim PrimInteger)
  | LDecimal : Q → Literal (TyPrim PrimDecimal)
  | LBool    : bool → Literal (TyPrim PrimBool)
  | LTime    : UTCTime → Literal (TyPrim PrimTime)
  | LUnit    : Literal (TyPrim PrimUnit).

Derive NoConfusion for Literal.

End Lit.
