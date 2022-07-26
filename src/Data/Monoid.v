Require Export Pact.Data.Semigroup.

Generalizable All Variables.
Set Primitive Projections.

Class Monoid (m : Type) := {
  is_semigroup :> Semigroup m;
  mempty : m;
}.

#[global]
Program Instance Monoid_option `{Monoid a} : Monoid (option a) := {
  mempty := None
}.

Class MonoidLaws (m : Type) `{Monoid m} := {
  has_semigroup_laws :> SemigroupLaws m;

  mempty_left  : forall a, mappend mempty a = a;
  mempty_right : forall a, mappend a mempty = a;
}.

#[global]
Program Instance MonoidLaws_option `{MonoidLaws a} : MonoidLaws (option a).
Next Obligation.
  destruct a0; reflexivity.
Qed.
