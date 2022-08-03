Require Import
  Coq.Classes.CRelationClasses
  Coq.micromega.Lia
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.Vectors.Fin
  Coq.Structures.Equalities
  Coq.Structures.DecidableType
  Coq.Sets.Finite_sets
  Coq.Logic.Classical
  Coq.Logic.ClassicalFacts
  Coq.Sets.Ensembles.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(************************************************************************
 ** Types with finite inhabitants.
 ************************************************************************)

Definition Iso (a b : Type) : Type :=
  { h : iffT a b | fst h ∘ snd h = id ∧ snd h ∘ fst h = id }.

(* [a] is a finite type (and thus, enumerable) if there is a bijection from
   that type to the finite naturals for some value of [n]. *)
Class Finite (a : Type) : Type := {
    cardinality : nat;
    (* There is a drawback to this definition, which is that it decides a
       single ordering, when in fact there are combinatorially many witness to
       this proof. What we should really have here is the space of all such
       isomorphisms. *)
    cardinality_witness : Iso a (Fin.t cardinality)
}.

(* We can enumerate all inhabitants of a finite type by induction on the
   cardinality and asking for the witness. *)
Definition enumerate `{F : Finite k} : list k.
Proof.
  destruct F as [n [[_ h] [_ _]]]; simpl in *.
  induction n.
  - exact nil.
  - pose proof (@of_nat_lt 0 (S n) ltac:(lia)) as H.
    apply cons.
    + apply h.
      exact H.
    + apply IHn.
      intros.
      apply h.
      apply FS.
      exact H0.
Defined.

(************************************************************************
 ** Helper tactics used below.
 ************************************************************************)

Ltac breakdown :=
  repeat lazymatch goal with
         | [ H : context[eq_dec ?X ?Y] |- _ ] =>
             destruct (eq_dec X Y); subst; firstorder eauto
         | [ |- context[eq_dec ?X ?Y] ] =>
             destruct (eq_dec X Y); subst; firstorder eauto
         end.

(************************************************************************
 ** Map interface
 ************************************************************************)

Definition remove {k v} (i : k) (m : Ensemble (k * v)) :=
  Setminus _ m (λ '(j, _), i = j).

Definition add {k v} (i : k) (x : v) (m : Ensemble (k * v)) :=
  Add _ m (i, x).

Definition insert {k v} (i : k) (x : v) (m : Ensemble (k * v)) :=
  Add _ (remove i m) (i, x).

Definition find {k v} (i : k) (m : Ensemble (k * v)) :=
  (λ x, In _ m (i, x)) : Ensemble v.

Definition mem {k v} (i : k) (m : Ensemble (k * v)) :=
  ∃ x, In _ m (i, x).

Definition has_val {k v} (i : k) (x : v) (m : Ensemble (k * v)) :=
  In _ m (i, x).

Definition keys {k v} (m : Ensemble (k * v)) := λ i, ∃ x, In _ m (i, x).

Definition elements {k v} (m : Ensemble (k * v)) := m.

Definition map {k v v'} (f : v → Ensemble v') (m : Ensemble (k * v)) :=
  λ '(i, x), ∃ y, In _ m (i, y) ∧ f y = x.

Definition mapi {k v v'} (f : k → v → Ensemble v') (m : Ensemble (k * v)) :=
  λ '(i, x), ∃ y, In _ m (i, y) ∧ f i y = x.

Definition equal {k v} : relation (Ensemble (k * v)) :=
  Same_set _.

Definition equal_f {k v} (f : relation v) : relation (Ensemble (k * v)) :=
  λ m1 m2, ∀ i x y, In _ m1 (i, x) → In _ m2 (i, y) → f x y.

Definition cardinal {k v} (m : Ensemble (k * v)) :=
   Coq.Sets.Finite_sets.cardinal k (keys m).

(************************************************************************
 ** Dependent Map interface
 ************************************************************************)

Definition remove_dep {k v} (i : k) (m : Ensemble { j : k & v j }) :=
  Setminus _ m (λ '(existT _ j _), i = j).

Definition add_dep {k v} (i : k) (x : v i) (m : Ensemble { j : k & v j }) :=
  Add _ m (existT _ i x).

Definition insert_dep {k v} (i : k) (x : v i) (m : Ensemble { j : k & v j }) :=
  Add _ (remove_dep i m) (existT _ i x).

Definition find_dep {k v} (i : k) (m : Ensemble { j : k & v j }) :=
  (λ x, In _ m (existT _ i x)) : Ensemble (v i).

Definition mem_dep {k v} (i : k) (m : Ensemble { j : k & v j }) :=
  ∃ x, In _ m (existT _ i x).

Definition has_val_dep {k v} (i : k) (x : v i) (m : Ensemble { j : k & v j }) :=
  In _ m (existT _ i x).

Definition keys_dep {k v} (m : Ensemble { j : k & v j }) :=
  λ i, ∃ x, In _ m (existT _ i x).

Definition elements_dep {k v} (m : Ensemble { j : k & v j }) := m.

Definition map_dep {k v v'} (f : ∀ j, v j → Ensemble (v' j)) (m : Ensemble { j : k & v j }) :=
  λ '(existT _ i x), ∃ y, In _ m (existT _ i y) ∧ f i y = x.

Definition equal_dep {k v} : relation (Ensemble { j : k & v j }) :=
  Same_set _.

Definition equal_f_dep {k v} (f : ∀ j, relation (v j)) :
  relation (Ensemble { j : k & v j }) :=
  λ m1 m2, ∀ i x y, In _ m1 (existT _ i x) → In _ m2 (existT _ i y) → f i x y.

Definition cardinal_dep {k v} (m : Ensemble { j : k & v j }) :=
   Coq.Sets.Finite_sets.cardinal k (keys_dep m).
