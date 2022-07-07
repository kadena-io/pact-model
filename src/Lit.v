Require Export
  Ty
  Coq.Strings.String
  Coq.ZArith.Int
  Coq.QArith.QArith.

From Equations Require Import Equations.
Set Equations With UIP.

Definition UTCTime : Set := nat.

Inductive Literal : PrimType → Set :=
  | LString  : string → Literal PrimString
  | LInteger : Z → Literal PrimInteger
  | LDecimal : Q → Literal PrimDecimal
  | LTime    : UTCTime → Literal PrimTime.

Derive NoConfusion for Literal.

Definition SemPrim (p : PrimType) : Type :=
  match p with
  | PrimInteger => Z
  | PrimDecimal => Q
  | PrimTime    => UTCTime
  | PrimString  => string
  end.

Definition SemLit `(l : Literal ty) : SemPrim ty :=
  match l with
  | LString  s => s
  | LInteger z => z
  | LDecimal q => q
  | LTime    t => t
  end.

