Require Export
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Lists.List
  Coq.Logic.Classical
  Coq.Logic.ProofIrrelevance
  Coq.Program.Equality
  Coq.Program.Program
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

From Equations Require Export Equations.

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

Lemma dec_eq_f1 `{EqDec a} (x y : a) `(f : a → b) :
  dec_eq x y → (∀ x y, f x = f y → x = y) → dec_eq (f x) (f y).
Proof.
  intros.
  destruct H0; subst.
  - now left.
  - right.
    intro.
    contradiction (H1 _ _ H0).
Defined.

Lemma dec_eq_f2 `{EqDec a} (x y : a) `{EqDec b} (z w : b) `(f : a → b → c) :
  dec_eq x y →
  dec_eq z w →
  (∀ x y z w, f x z = f y w → x = y ∧ z = w) →
  dec_eq (f x z) (f y w).
Proof.
  intros.
  destruct H1, H2; subst.
  - now left.
  - right.
    intro.
    pose proof (H3 _ _ _ _ H1); reduce.
    contradiction.
  - right.
    intro.
    pose proof (H3 _ _ _ _ H1); reduce.
    contradiction.
  - right.
    intro.
    pose proof (H3 _ _ _ _ H1); reduce.
    contradiction.
Defined.

#[export]
Program Instance EqDec_EqDec {a} : EqDec (EqDec a).
Next Obligation.
  left.
  extensionality x0.
  extensionality y0.
  destruct (x x0 y0); subst.
  - destruct (y y0 y0); subst;
    now simpl_eq.
  - destruct (y x0 y0); subst.
    contradiction.
    assert (n = n0) by apply proof_irrelevance.
    now subst.
Defined.

Corollary sum_id {X Y : Type} (e : X + Y) :
  match e with
  | inl x => inl x
  | inr y => inr y
  end = e.
Proof. now destruct e. Qed.
