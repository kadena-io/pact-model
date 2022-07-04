Require Export
  Coq.Unicode.Utf8.

From Equations Require Import Equations.
Set Equations With UIP.

Inductive PrimType : Type :=
  | PrimInteger
  | PrimDecimal
  | PrimTime
  | PrimBool
  | PrimString
  | PrimUnit.

Derive NoConfusion for PrimType.

(* TODO:
 - Lists
 - Builtins
 - Row-types
 - Modules
 - Schemas
 - Tables
 - Guards
 - Capabilities *)

Inductive Ty : Type :=
  | TyPrim : PrimType → Ty
  | TyList : Ty → Ty

  (* The arrow type is the only type in the base lambda calculus *)
  | TyArrow : Ty → Ty → Ty.

Derive NoConfusion for Ty.

Infix "⟶" := TyArrow (at level 30, right associativity).
