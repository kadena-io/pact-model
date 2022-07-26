Require Import Hask.Prelude.

Generalizable All Variables.
Set Primitive Projections.

Class Semigroup (m : Type) := {
  mappend : m -> m -> m
}.

Arguments mappend {m _ } _ _.

Infix "⨂" := mappend (at level 40).

Definition Maybe_append `{Semigroup a} (x y : Maybe a) : Maybe a :=
  match x, y with
  | Nothing, x     => x
  | x, Nothing     => x
  | Just x, Just y => Just (x ⨂ y)
  end.

#[global]
Program Instance Semigroup_Maybe `{Semigroup a} : Semigroup (Maybe a) := {
  mappend := Maybe_append
}.

Class SemigroupLaws (m : Type) `{Semigroup m} := {
  mappend_assoc : forall a b c, mappend a (mappend b c) = mappend (mappend a b) c;
}.

#[global]
Program Instance SemigroupLaws_Maybe `{SemigroupLaws a} : SemigroupLaws (Maybe a).
Next Obligation.
  destruct a0, b, c; simpl; try reflexivity.
  now rewrite mappend_assoc.
Qed.
