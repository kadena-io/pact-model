Class Magma (e : Type) := {
  op : e → e → e
}.

Infix "⊗" := op (at level 40, left associativity).

Class Semigroup (e : Type) := {
  is_magma :> Magma e;
  op_assoc a b c : a ⊗ (b ⊗ c) = (a ⊗ b) ⊗ c
}.

Class Monoid (e : Type) := {
  is_semigroup :> Magma e;
  ε : e;
  ε_left  a : ε ⊗ a = a;
  ε_right a : a ⊗ ε = a
}.

Class Group (e : Type) := {
  is_monoid :> Monoid e;
  inv : e → e;
  inv_left a : inv a ⊗ a = ε;
  inv_right a : a ⊗ inv a = ε;
}.

Notation "a ⁻¹" := (inv a) (at level 100).

