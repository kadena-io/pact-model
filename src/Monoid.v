Require Export Hask.Data.Semigroup.
Require Import Hask.Prelude.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Monoid (m : Type) := {
  is_semigroup :> Semigroup m;

  mempty : m;

  mempty_left  : forall a, mappend mempty a ≈ a;
  mempty_right : forall a, mappend a mempty ≈ a;
}.

Program Instance Semigroup_option `{Semigroup a} : Semigroup (option a) := {
  mappend := fun x y =>
   match x, y with
   | None, _ => None
   | _, None => None
   | Some x', Some y' => Some (x' ⨂ y')
   end
}.
Next Obligation.
  repeat intro.

Program Instance Monoid_option `{Monoid a} : Monoid (option a) := {
  mempty := None
}.
Next Obligation. reflexivity. Qed.
Next Obligation. destruct a0; reflexivity. Qed.
