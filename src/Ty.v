Require Export
  Coq.Unicode.Utf8.

From Equations Require Import Equations.

Section Ty.

Class HostTypes (A : Type) : Type := {
  HostTy : Type;
  HostTySem : HostTy → Type
}.

Context {A : Type}.
Context `{HostTypes A}.

(* TODO:
 - Row-types
 - Modules
 - Schemas
 - Tables
 - Guards
 - Capabilities *)

Inductive Ty : Type :=
  | TyHost : HostTy → Ty

  | TyUnit : Ty
  | TyBool : Ty
  | TyList : Ty → Ty
  | TyPair : Ty → Ty → Ty

  (* The arrow type is the only type in the base lambda calculus *)
  | TyArrow : Ty → Ty → Ty.

Derive NoConfusion NoConfusionHom Subterm for Ty.

End Ty.

Arguments Ty {A H}.
Arguments TyHost {A H} _.
Arguments TyUnit {A H}.
Arguments TyBool {A H}.
Arguments TyList {A H} _.
Arguments TyPair {A H} _ _.
Arguments TyArrow {A H} _ _.

Declare Scope Ty_scope.
Bind Scope Ty_scope with Ty.
Delimit Scope Ty_scope with ty.

Infix "⟶" := TyArrow (at level 51, right associativity) : Ty_scope.
Infix "×"  := TyPair  (at level 40, left associativity) : Ty_scope.
