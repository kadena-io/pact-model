Require Export
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Lists.List
  Coq.Logic.Classical
  Coq.Logic.ProofIrrelevance
  Coq.Relations.Relation_Definitions
  Coq.Sets.Ensembles
  Coq.Sets.Finite_sets
  Coq.Sets.Finite_sets_facts
  Coq.Sets.Powerset_facts
  Coq.Strings.String
  Coq.Unicode.Utf8
  Pact.Ltac.

Require Import
  Coq.ZArith.ZArith.

From Coq Require Export ssreflect ssrfun ssrbool.
Require Export Equations.Prop.DepElim.
From Equations Require Export Equations.
From Hammer Require Export Tactics Hammer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Derive NoConfusion NoConfusionHom Subterm EqDec for Ascii.ascii.
Derive NoConfusion NoConfusionHom Subterm EqDec for string.
Derive NoConfusion NoConfusionHom Subterm EqDec for Z.
Next Obligation. now apply Z.eq_dec. Defined.
Derive NoConfusion NoConfusionHom Subterm EqDec for N.
Next Obligation. now apply N.eq_dec. Defined.
Derive NoConfusion NoConfusionHom Subterm EqDec for nat.
Derive NoConfusion NoConfusionHom Subterm EqDec for bool.

#[export] Hint Resolve Z_EqDec : core.
#[export] Hint Resolve N_EqDec : core.
#[export] Hint Resolve nat_EqDec : core.
#[export] Hint Resolve bool_EqDec : core.
#[export] Hint Resolve string_EqDec : core.
#[export] Hint Resolve list_eqdec : core.

Lemma dec_eq_f1 `{EqDec a} (x y : a) `(f : a → b) :
  dec_eq x y → (∀ x y, f x = f y → x = y) → dec_eq (f x) (f y).
Proof. sauto. Defined.

Lemma dec_eq_f2 `{EqDec a} (x y : a) `{EqDec b} (z w : b) `(f : a → b → c) :
  dec_eq x y →
  dec_eq z w →
  (∀ x y z w, f x z = f y w → x = y ∧ z = w) →
  dec_eq (f x z) (f y w).
Proof. sauto. Defined.
