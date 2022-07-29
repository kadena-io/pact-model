Require Export
  Coq.Lists.List
  Coq.Bool.Bool
  Coq.Unicode.Utf8
  Coq.Classes.SetoidClass
  Coq.Classes.Morphisms
  Pact.Data.Eq
  Pact.Data.Ord.

Generalizable All Variables.

(** General utility library providing partial maps, built
    on a foundation isomorphic to association lists. *)

Section Map.

Import ListNotations.

Context {k v : Type}.

Inductive Map (k v : Type) : Type :=
  | Add : k → v → Map k v → Map k v
  | Empty : Map k v.

Arguments Empty {_ _}.
Arguments Add {_ _} _ _ _.

Fixpoint lookup `{Eq k} (i : k) (m : Map k v) : option v :=
  match m with
  | Empty => None
  | Add i' x m =>
      if i == i'
      then Some x
      else lookup i m
  end.

#[export]
Program Instance Map_Typeoid `{Eq k} : Setoid (Map k v) := {|
  equiv := λ m1 m2, ∀ k, lookup k m1 = lookup k m2
|}.
Next Obligation.
  constructor; repeat intro; auto.
  transitivity (lookup k0 y); congruence.
Qed.

Fixpoint member `{Eq k} (i : k) (m : Map k v) : bool :=
  match m with
  | Empty => false
  | Add i' _ m => (i == i') || member i m
  end.

#[export]
Program Instance member_respects `{Eq k} :
  Proper (eq ==> equiv ==> eq) member.
Next Obligation.
  repeat intro; subst.
  specialize (H1 y).
  generalize dependent y.
  induction x0; simpl; intros.
  - destruct (y == k0) eqn:Heqe; simpl.
    + apply eqb_eq in Heqe; subst.
      clear -H1.
      induction y0; simpl in *; auto.
      * destruct (k0 == k1) eqn:Heqe; simpl; auto.
      * congruence.
    + now apply IHx0.
  - induction y0; simpl in *; auto.
    destruct (y == k0) eqn:Heqe; simpl.
    + congruence.
    + now apply IHy0.
Qed.

Fixpoint toList (m : Map k v) : list (k * v) :=
  match m with
  | Empty => []
  | Add i x m => (i, x) :: toList m
  end.

Fixpoint fromList (l : list (k * v)) : Map k v :=
  match l with
  | [] => Empty
  | (i, x) :: xs => Add i x (fromList xs)
  end.

Lemma toList_fromList (l : list (k * v)) : toList (fromList l) = l.
Proof.
  induction l; simpl; auto.
  destruct a; simpl.
  now rewrite IHl.
Qed.

Lemma fromList_toList (m : Map k v) : fromList (toList m) = m.
Proof.
  induction m; simpl; auto.
  now rewrite IHm.
Qed.

Definition null (m : Map k v) : bool :=
  if m then false else true.

#[export]
Program Instance null_respects `{Eq k} : Proper (equiv ==> eq) null.
Next Obligation.
  repeat intro.
  generalize dependent y.
  induction x, y; simpl; intros; auto.
  - specialize (H0 k0).
    rewrite eqb_refl in H0.
    discriminate.
  - specialize (H0 k0).
    rewrite eqb_refl in H0.
    discriminate.
Qed.

Fixpoint size (m : Map k v) : nat :=
  match m with
  | Add _ _ m => 1 + size m
  | Empty => 0
  end.

Fixpoint findWithDefault `{Eq k} (d : v) (i : k) (m : Map k v) : v :=
  match m with
  | Empty => d
  | Add i' x m =>
      if i == i'
      then x
      else findWithDefault d i m
  end.

Definition empty : Map k v := Empty.

Definition singleton (i : k) (x : v) : Map k v := Add i x empty.

Fixpoint insert `{Eq k} (i : k) (x : v) (m : Map k v) : Map k v :=
  match m with
  | Empty => singleton i x
  | Add i' _ m =>
      if i == i'
      then Add i x m
      else insert i x m
  end.

Fixpoint insertWith `{Eq k} (f : v → v → v) (i : k) (x : v) (m : Map k v) : Map k v :=
  match m with
  | Empty => singleton i x
  | Add i' x' m =>
      if i == i'
      then Add i (f x x') m
      else insertWith f i x m
  end.

Fixpoint insertWithKey `{Eq k} (f : k → v → v → v) (i : k) (x : v) (m : Map k v) : Map k v :=
  match m with
  | Empty => singleton i x
  | Add i' x' m =>
      if i == i'
      then Add i (f i x x') m
      else insertWithKey f i x m
  end.

Fixpoint insertLookupWithKey `{Eq k} (f : k → v → v → v) (i : k) (x : v) (m : Map k v) :
  option v * Map k v :=
  match m with
  | Empty => (None, singleton i x)
  | Add i' x' m =>
      if i == i'
      then (Some x', Add i (f i x x') m)
      else insertLookupWithKey f i x m
  end.

Fixpoint delete `{Eq k} (i : k) (m : Map k v) : Map k v :=
  match m with
  | Empty => m
  | Add i' x m =>
      if i == i'
      then delete i m
      else Add i' x (delete i m)
  end.

Fixpoint adjust `{Eq k} (f : v → v) (i : k) (m : Map k v) : Map k v :=
  match m with
  | Empty => Empty
  | Add i' x' m =>
      if i == i'
      then Add i' (f x') m
      else Add i' x' (adjust f i m)
  end.

Fixpoint adjustWithKey `{Eq k} (f : k → v → v) (i : k) (m : Map k v) : Map k v :=
  match m with
  | Empty => Empty
  | Add i' x' m =>
      if i == i'
      then Add i' (f i' x') m
      else Add i' x' (adjustWithKey f i m)
  end.

Fixpoint alter `{Eq k} (f : option v → option v) (i : k) (m : Map k v) : Map k v :=
  match m with
  | Empty =>
      match f None with
      | None => empty
      | Some v => singleton i v
      end
  | Add i' x' m =>
      if i == i'
      then
        match f (Some x') with
        | None => m
        | Some v => Add i' v m
        end
      else Add i' x' (alter f i m)
  end.

Context {b : Type}.

Fixpoint map (f : v → b) (m : Map k v) : Map k b :=
  match m with
  | Empty => Empty
  | Add i x m => Add i (f x) (map f m)
  end.

Fixpoint mapWithKey (f : k → v → b) (m : Map k v) : Map k b :=
  match m with
  | Empty => Empty
  | Add i x m => Add i (f i x) (mapWithKey f m)
  end.

Fixpoint fold (f : v → b → b) (z : b) (m : Map k v) : b :=
  match m with
  | Empty => z
  | Add _ x m => fold f (f x z) m
  end.

Fixpoint foldrWithKey (f : k → v → b → b) (z : b) (m : Map k v) : b :=
  match m with
  | Empty => z
  | Add i x m => f i x (foldrWithKey f z m)
  end.

Fixpoint foldlWithKey (f : k → v → b → b) (z : b) (m : Map k v) : b :=
  match m with
  | Empty => z
  | Add i x m => foldlWithKey f (f i x z) m
  end.

Fixpoint elems (m : Map k v) : list v :=
  match m with
  | Empty => []
  | Add _ x m => x :: elems m
  end.

Fixpoint keys (m : Map k v) : list k :=
  match m with
  | Empty => []
  | Add i _ m => i :: keys m
  end.

Definition assocs (m : Map k v) : list (k * v) := toList m.

Fixpoint filter (f : v → bool) (m : Map k v) : Map k v :=
  match m with
  | Empty => Empty
  | Add i x m =>
      if f x
      then Add i x (filter f m)
      else filter f m
  end.

Fixpoint mapMaybe (f : v → option b) (m : Map k v) : Map k b :=
  match m with
  | Empty => Empty
  | Add i x m =>
      match f x with
      | Some x' => Add i x' (mapMaybe f m)
      | None => mapMaybe f m
      end
  end.

End Map.
