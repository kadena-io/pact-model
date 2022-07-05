Require Export
  Coq.Unicode.Utf8.

From Equations Require Import Equations.
Set Equations With UIP.

Inductive PrimType : Type :=
  | PrimInteger
  | PrimDecimal
  | PrimTime
  | PrimString.

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

  | TyUnit : Ty
  | TyBool : Ty
  | TyPair : Ty → Ty → Ty

  (* The arrow type is the only type in the base lambda calculus *)
  | TyArrow : Ty → Ty → Ty.

Derive NoConfusion Subterm for Ty.

Declare Scope Ty_scope.
Bind Scope Ty_scope with Ty.
Delimit Scope Ty_scope with ty.

Infix "⟶" := TyArrow (at level 30, right associativity) : Ty_scope.
Infix "×"  := TyPair  (at level 40, left associativity) : Ty_scope.

Definition ℤ := TyPrim PrimInteger.
Definition ℝ := TyPrim PrimDecimal.
Definition 𝕋 := TyPrim PrimTime.
Definition 𝕊 := TyPrim PrimString.
Definition 𝔹 := TyBool.
