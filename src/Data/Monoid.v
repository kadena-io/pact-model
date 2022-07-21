Require Import Hask.Prelude.
Require Export Pact.Data.Semigroup.

Generalizable All Variables.
Set Primitive Projections.

Class Monoid (m : Type) := {
  is_semigroup :> Semigroup m;

  mempty : m;

  mempty_left  : forall a, mappend mempty a = a;
  mempty_right : forall a, mappend a mempty = a;
}.

#[global]
Program Instance Monoid_option `{Monoid a} : Monoid (option a) := {
  mempty := None
}.
Next Obligation.
  destruct a0; reflexivity.
Qed.
