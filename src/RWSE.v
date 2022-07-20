Require Import Hask.Prelude.
Require Import Hask.Ltac.
Require Import Hask.Control.Monad.
Require Import Data.Semigroup.
Require Import Data.Monoid.
Require Import Coq.Unicode.Utf8.
Require Import FunctionalExtensionality.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(******************************************************************************
 * The RWSET Monad transformer
 *)

Section RWSE.

Context {r s w e : Type}.

Definition RWSE (a : Type) := r → s → w → e + (a * (s * w)).

Definition ask : RWSE r := λ r s w, inr (r, (s, w)).

Definition local (f : r → r) `(x : RWSE a) : RWSE a :=
  λ r s w, x (f r) s w.

Definition get : RWSE s := λ r s w, inr (s, (s, w)).
Definition gets {a : Type} (f : s → a) : RWSE a := λ r s w, inr (f s, (s, w)).
Definition put (x : s) : RWSE unit := λ _ _ w, inr (tt, (x, w)).
Definition modify (f : s → s) : RWSE unit := λ _ s w, inr (tt, (f s, w)).

Definition tell `{Monoid w} (v : w) : RWSE unit :=
  λ _ s w, inr (tt, (s, w ⨂ v)).

Definition tellf (f : w → w) : RWSE unit := λ _ s w, inr (tt, (s, f w)).

Definition throw {a : Type} (err : e) : RWSE a := λ _ _ _, inl err.

#[export]
Program Instance RWSE_Functor : Functor RWSE := {
  fmap := λ A B f (x : RWSE A), λ r s w, first f <$> x r s w
}.

Definition RWSE_ap {a b : Type} (f : RWSE (a → b)) (x : RWSE a) :
  RWSE b := λ r s w,
  match f r s w with
  | inl e => inl e
  | inr (f', (s', w')) => first f' <$> x r s' w'
  end.

#[export]
Program Instance RWSE_Applicative : Applicative RWSE := {
  pure := λ _ x, λ _ s w, inr (x, (s, w));
  ap   := @RWSE_ap
}.

Definition RWSE_join `(x : RWSE (RWSE a)) :
  RWSE a := λ r s w,
  match x r s w with
  | inl e => inl e
  | inr (y, (s', w')) => y r s' w'
  end.

#[export]
Program Instance RWSE_Monad : Monad RWSE := {
  join := @RWSE_join
}.

End RWSE.

Arguments RWSE : clear implicits.

Module RWSELaws.

Include MonadLaws.

Lemma first_id : forall a z, first (a:=a) (b:=a) (z:=z) id = id.
Proof.
  unfold first.
  intros a z.
  extensionality x.
  destruct x; auto.
Qed.

#[global]
Program Instance RWSE_FunctorLaws {r s w e : Type} :
  FunctorLaws (@RWSE r s w e).
Next Obligation.
  extensionality x.
  extensionality r0.
  extensionality s0.
  extensionality w0.
  rewrite first_id.
  unfold id.
  now destruct (x r0 s0 w0).
Qed.
Next Obligation.
  unfold comp.
  extensionality x.
  extensionality r0.
  extensionality s0.
  extensionality w0.
  unfold Either_map, first.
  destruct (x r0 s0 w0); simpl; auto.
  now destruct p.
Qed.

#[global]
Program Instance RWSE_Applicative {r s w e : Type} :
  ApplicativeLaws (@RWSE r s w e).
Next Obligation.
  extensionality x.
  extensionality r0.
  extensionality s0.
  extensionality w0.
  unfold RWSE_ap.
  rewrite first_id.
  simpl.
  unfold Either_map, id.
  now destruct (x r0 s0 w0).
Qed.
Next Obligation.
  extensionality r1.
  extensionality s1.
  extensionality w1.
  unfold RWSE_ap; simpl.
  destruct (u r1 s1 w1); simpl; auto.
  destruct p; simpl.
  destruct p; simpl.
  destruct (v r1 s0 w2); simpl; auto.
  destruct p; simpl.
  destruct p; simpl.
  destruct (w0 r1 s2 w3); simpl; auto.
  destruct p; simpl.
  destruct p; simpl.
  reflexivity.
Qed.
Next Obligation.
  extensionality r1.
  extensionality s1.
  extensionality w1.
  unfold RWSE_ap; simpl.
  destruct (u r1 s1 w1); simpl; auto.
  destruct p; simpl.
  destruct p; simpl.
  reflexivity.
Qed.

#[global]
Program Instance RWSE_Monad {r s w e : Type} :
  MonadLaws (@RWSE r s w e).
Next Obligation.
  unfold comp.
  extensionality x.
  extensionality r1.
  extensionality s1.
  extensionality w1.
  unfold RWSE_join; simpl.
  destruct (x r1 s1 w1); simpl; auto.
  destruct p; simpl.
  destruct p; simpl.
  reflexivity.
Qed.
Next Obligation.
  unfold comp.
  extensionality x.
  extensionality r1.
  extensionality s1.
  extensionality w1.
  unfold RWSE_join, id; simpl.
  destruct (x r1 s1 w1); simpl; auto.
  destruct p; simpl.
  destruct p; simpl.
  reflexivity.
Qed.
Next Obligation.
  unfold comp.
  extensionality x.
  extensionality r1.
  extensionality s1.
  extensionality w1.
  unfold RWSE_join, id; simpl.
  destruct (x r1 s1 w1); simpl; auto.
  destruct p; simpl.
  destruct p; simpl.
  reflexivity.
Qed.

End RWSELaws.
