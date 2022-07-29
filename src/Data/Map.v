Require Export
  Coq.Arith.Arith
  Coq.Lists.List
  Coq.Bool.Bool
  Coq.Unicode.Utf8
  Coq.micromega.Lia
  Coq.Classes.SetoidClass
  Coq.Classes.Morphisms
  Pact.Data.Eq
  Pact.Data.Ord.

Require Export Equations.Prop.DepElim.
From Equations Require Export Equations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

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

Inductive MapsTo `{Eq k} (i : k) (x : v) : Map k v -> Prop :=
  | MapsTo_hd i' x' m :
    i == i' = true -> x = x' → MapsTo i x (Add i' x' m)
  | MapsTo_tl i' x' m :
    i == i' = false → MapsTo i x m -> MapsTo i x (Add i' x' m).

Fixpoint lookup `{Eq k} (i : k) (m : Map k v) : option v :=
  match m with
  | Empty => None
  | Add i' x m =>
      if i == i'
      then Some x
      else lookup i m
  end.

Lemma MapsTo_lookup `{Eq k} i x m : MapsTo i x m ↔ lookup i m = Some x.
Proof.
  split; intros.
  - induction H0; simpl; subst;
    now rewrite H0.
  - induction m; simpl in *; [|discriminate].
    destruct (i == k0) eqn:Heqe.
    + inversion H0; subst.
      now constructor.
    + apply MapsTo_tl; auto.
Qed.

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
  specialize (H0 x).
  generalize dependent y.
  induction x0; simpl; intros.
  - destruct (x == k0) eqn:Heqe; simpl.
    + apply eqb_eq in Heqe; subst.
      clear -H0.
      induction y; simpl in *; auto.
      * destruct (k0 == k1) eqn:Heqe; simpl; auto.
      * congruence.
    + now apply IHx0.
  - induction y; simpl in *; auto.
    destruct (x == k0) eqn:Heqe; simpl.
    + congruence.
    + now apply IHy.
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

Fixpoint delete `{Eq k} (i : k) (m : Map k v) : Map k v :=
  match m with
  | Empty => m
  | Add i' x m =>
      if i == i'
      then delete i m
      else Add i' x (delete i m)
  end.

Lemma delete_idem `{Eq k} i m :
  delete i (delete i m) = delete i m.
Proof.
  induction m; simpl; auto.
  destruct (i == k0) eqn:Heqe; auto; simpl.
  rewrite Heqe.
  now rewrite IHm.
Qed.

Lemma delete_comm `{Eq k} i j m :
  delete i (delete j m) = delete j (delete i m).
Proof.
  generalize dependent j.
  generalize dependent i.
  induction m; simpl; intros; auto.
  destruct (i == k0) eqn:Heqe1; auto; simpl.
  - destruct (j == k0) eqn:Heqe2; auto; simpl.
    now rewrite Heqe1.
  - destruct (j == k0) eqn:Heqe2; auto; simpl.
    rewrite Heqe1.
    now rewrite IHm.
Qed.

Fixpoint size (m : Map k v) : nat :=
  match m with
  | Add _ _ m => 1 + size m
  | Empty => 0
  end.

Lemma size_delete `{Eq k} i m : (size (delete i m) <= size m)%nat.
Proof.
  induction m; simpl; auto.
  destruct (i == k0) eqn:Heqe;
  auto; simpl; lia.
Qed.

Equations compress `{Eq k} (m : Map k v) : Map k v by wf (size m) :=
  compress Empty := Empty;
  compress (Add i' x m) := Add i' x (compress (delete i' m)).
Next Obligation.
  specialize (compress H m).
  pose proof (size_delete i' m); lia.
Qed.

Lemma compress_delete `{Eq k} i m :
  compress (delete i m) = delete i (compress m).
Proof.
  generalize dependent i.
  funelim (compress m); simpl; intros; auto.
  simp compress; simpl.
  destruct (i == i') eqn:Heqe.
  - apply eqb_eq in Heqe; subst.
    rewrite <- H0.
    now rewrite delete_idem.
  - simp compress; simpl.
    f_equal.
    rewrite <- H0.
    now rewrite delete_comm.
Qed.

Lemma size_compress `{Eq k} m : (size (compress m) <= size m)%nat.
Proof.
  induction m; auto.
  simp compress; simpl.
  apply le_n_S.
  rewrite compress_delete.
  now rewrite size_delete.
Qed.

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
  | Add i' x' m =>
      if i == i'
      then Add i x m
      else Add i' x' (insert i x m)
  end.

Lemma lookup_insert `{Eq k} i j x m :
  lookup i (insert j x m) = if i == j then Some x else lookup i m.
Proof.
  destruct (i == j) eqn:Heqe1.
  - induction m; simpl; intros.
    + destruct (j == k0) eqn:Heqe2; simpl.
      * now rewrite Heqe1.
      * apply eqb_eq in Heqe1; subst.
        now rewrite Heqe2.
    + now destruct (i == j).
  - induction m; simpl; intros.
    + destruct (j == k0) eqn:Heqe2; simpl.
      * rewrite Heqe1.
        apply eqb_eq in Heqe2; subst.
        now rewrite Heqe1.
      * now rewrite IHm.
    + now destruct (i == j).
Qed.

Lemma lookup_delete `{Eq k} i j m :
  lookup i (delete j m) = if i == j then None else lookup i m.
Proof.
  induction m; simpl.
  - destruct (i == j) eqn:Heqe1.
    + destruct (j == k0) eqn:Heqe2; auto.
      simpl.
      apply eqb_eq in Heqe1; subst.
      now rewrite Heqe2.
    + destruct (j == k0) eqn:Heqe2; simpl; auto.
      * apply eqb_eq in Heqe2; subst.
        now rewrite Heqe1.
      * now destruct (i == k0).
  - now destruct (i == j).
Qed.

Lemma compress_equiv `{Eq k} m :
  m == compress m.
Proof.
  funelim (compress m); repeat intro; auto.
  simp compress; simpl.
  rewrite <- H0.
  rewrite lookup_delete.
  now destruct (k0 == i').
Qed.

Lemma insert_delete `{Eq k } i x m :
  insert i x (delete i m) == insert i x m.
Proof.
  induction m; simpl; intros; auto.
  destruct (i == k0) eqn:Heqe.
  - rewrite IHm; clear IHm.
    now rewrite lookup_insert.
  - simpl.
    rewrite Heqe; simpl.
    now rewrite IHm.
Qed.

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
