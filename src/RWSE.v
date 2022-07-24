Require Import Hask.Prelude.
Require Import Hask.Control.Monad.
Require Import Coq.Unicode.Utf8.
Require Import FunctionalExtensionality.
Require Import Pact.Data.Monoid.

Generalizable All Variables.
Set Primitive Projections.

(******************************************************************************
 * The RWSET Monad transformer
 *)

Ltac rwse :=
  let r := fresh "r" in extensionality r;
  let s := fresh "s" in extensionality s;
  let w := fresh "w" in extensionality w.

Section RWSE.

Context {r s w e : Type}.

Definition RWSE (a : Type) := r → s → w → e + (a * (s * w)).

Definition ask : RWSE r := λ r s w, inr (r, (s, w)).
Definition asks {a : Type} (f : r → a) : RWSE a := λ r s w, inr (f r, (s, w)).

Definition local (f : r → r) `(x : RWSE a) : RWSE a :=
  λ r s w, x (f r) s w.

Definition get : RWSE s := λ _ s w, inr (s, (s, w)).
Definition gets {a : Type} (f : s → a) : RWSE a := λ _ s w, inr (f s, (s, w)).
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

Corollary put_get `(x : s) : (put x >> get) = (put x >> pure x).
Proof. reflexivity. Qed.

End RWSE.

#[export] Hint Unfold RWSE_ap : core.
#[export] Hint Unfold RWSE_join : core.

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
  rwse.
  rewrite first_id.
  unfold id.
  now destruct (x r0 s0 w0).
Qed.
Next Obligation.
  unfold comp.
  extensionality x.
  rwse.
  unfold Either_map, first.
  destruct (x _ _ _); simpl; auto.
  now destruct p.
Qed.

#[global]
Program Instance RWSE_Applicative {r s w e : Type} :
  ApplicativeLaws (@RWSE r s w e).
Next Obligation.
  extensionality x.
  rwse.
  unfold RWSE_ap.
  rewrite first_id.
  unfold Either_map, id. (* jww (2022-07-24): Prove functor laws for Either *)
  now destruct (x _ _ _).
Qed.
Next Obligation.
  rwse.
  unfold RWSE_ap; simpl.
  destruct (u _ _ _); simpl; auto.
  destruct p, p; simpl.
  destruct (v _ _ _); simpl; auto.
  destruct p, p; simpl.
  destruct (w0 _ _ _); simpl; auto.
  destruct p, p; simpl.
  reflexivity.
Qed.
Next Obligation.
  rwse.
  unfold RWSE_ap; simpl.
  destruct (u _ _ _); simpl; auto.
  destruct p, p; simpl.
  reflexivity.
Qed.

#[global]
Program Instance RWSE_Monad {r s w e : Type} :
  MonadLaws (@RWSE r s w e).
Next Obligation.
  unfold comp.
  extensionality x.
  rwse.
  unfold RWSE_join; simpl.
  destruct (x _ _ _); simpl; auto.
  destruct p, p; simpl.
  reflexivity.
Qed.
Next Obligation.
  unfold comp.
  extensionality x.
  rwse.
  unfold RWSE_join, id; simpl.
  destruct (x _ _ _); simpl; auto.
  destruct p, p; simpl.
  reflexivity.
Qed.
Next Obligation.
  unfold comp.
  extensionality x.
  rwse.
  unfold RWSE_join, id; simpl.
  destruct (x _ _ _); simpl; auto.
  destruct p, p; simpl.
  reflexivity.
Qed.

End RWSELaws.
