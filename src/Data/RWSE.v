Require Import Hask.Data.Tuple.
Require Import Hask.Control.Monad.
Require Import Coq.Unicode.Utf8.
Require Import FunctionalExtensionality.
Require Import Pact.Data.Monoid.
Require Import Pact.Data.Either.

Generalizable All Variables.
Set Primitive Projections.

(******************************************************************************
 * The RWSET Monad transformer
 *)

Ltac rwse :=
  let r := fresh "r" in extensionality r;
  let s := fresh "s" in extensionality s.

Section RWSE.

Context {r w s e : Type}.
Context `{Monoid w}.

Definition RWSE (a : Type) := r → s → e + (a * (s * w)).

Definition ask : RWSE r := λ r s, inr (r, (s, mempty)).
Definition asks {a : Type} (f : r → a) : RWSE a :=
  λ r s, inr (f r, (s, mempty)).

Definition local (f : r → r) `(x : RWSE a) : RWSE a :=
  λ r s, x (f r) s.

Definition get : RWSE s := λ _ s, inr (s, (s, mempty)).
Definition gets {a : Type} (f : s → a) : RWSE a :=
  λ _ s, inr (f s, (s, mempty)).
Definition put (x : s) : RWSE unit := λ _ _, inr (tt, (x, mempty)).
Definition modify (f : s → s) : RWSE unit := λ _ s, inr (tt, (f s, mempty)).

Definition tell `{Monoid w} (v : w) : RWSE unit :=
  λ _ s, inr (tt, (s, v)).

Definition throw {a : Type} (err : e) : RWSE a := λ _ _, inl err.

#[export]
Program Instance RWSE_Functor : Functor RWSE := {
  fmap := λ A B f (x : RWSE A), λ r s, first f <$> x r s
}.

Definition RWSE_ap {a b : Type} (f : RWSE (a → b)) (x : RWSE a) :
  RWSE b := λ r s,
  match f r s with
  | inl e => inl e
  | inr (f', (s', w')) =>
      match first f' <$> x r s' with
      | inl e => inl e
      | inr (y, (s'', w'')) =>
          inr (y, (s'', w' ⨂ w''))
      end
  end.

#[export]
Program Instance RWSE_Applicative : Applicative RWSE := {
  pure := λ _ x, λ _ s, inr (x, (s, mempty));
  ap   := @RWSE_ap
}.

Definition RWSE_join `(x : RWSE (RWSE a)) :
  RWSE a := λ r s,
  match x r s with
  | inl e => inl e
  | inr (y, (s', w')) =>
      match y r s' with
      | inl e => inl e
      | inr (z, (s'', w'')) =>
          inr (z, (s'', w' ⨂ w''))
      end
  end.

#[export]
Program Instance RWSE_Monad : Monad RWSE := {
  join := @RWSE_join
}.

Corollary put_get `(x : s) : (put x >> get) = (put x >> pure x).
Proof. reflexivity. Qed.

End RWSE.

Arguments RWSE : clear implicits.

Module RWSELaws.

Include MonadLaws.

#[local] Hint Unfold RWSE_ap : core.
#[local] Hint Unfold RWSE_join : core.
#[local] Hint Unfold Either_map : core.
#[local] Hint Unfold Tuple.first : core.
#[local] Hint Unfold id : core.

Lemma first_id : forall a z, first (a:=a) (b:=a) (z:=z) id = id.
Proof.
  unfold first.
  intros a z.
  extensionality x.
  destruct x; auto.
Qed.

#[global]
Program Instance RWSE_FunctorLaws {r w s e : Type} :
  FunctorLaws (RWSE r w s e).
Next Obligation.
  extensionality x.
  rwse.
  rewrite first_id.
  unfold id.
  now destruct (x r0 s0).
Qed.
Next Obligation.
  unfold comp.
  extensionality x.
  rwse.
  unfold Either_map, first.
  destruct (x _ _); simpl; auto.
  now destruct p.
Qed.

#[global]
Program Instance RWSE_ApplicativeLaws {r w s e : Type} `{MonoidLaws w} :
  ApplicativeLaws (RWSE r w s e).
Next Obligation.
  extensionality x.
  rwse.
  unfold RWSE_ap.
  rewrite first_id; simpl.
  autounfold.
  destruct (x _ _); auto.
  destruct p, p; simpl.
  now rewrite mempty_left.
Qed.
Next Obligation.
  rwse.
  unfold RWSE_ap; simpl.
  destruct (u _ _); simpl; auto.
  destruct p, p; simpl.
  destruct (v _ _); simpl; auto.
  destruct p, p; simpl.
  destruct (w0 _ _); simpl; auto.
  destruct p, p; simpl.
  rewrite mempty_left.
  now rewrite mappend_assoc.
Qed.
Next Obligation.
  rwse.
  unfold RWSE_ap; simpl.
  now rewrite mempty_left.
Qed.
Next Obligation.
  autounfold.
  rwse.
  destruct (u _ _); simpl; auto.
  destruct p, p; simpl.
  now rewrite mempty_left, mempty_right.
Qed.
Next Obligation.
  autounfold.
  extensionality x.
  rwse; simpl.
  autounfold.
  destruct (x _ _); simpl; auto.
  destruct p, p; simpl.
  now rewrite mempty_left.
Qed.

#[global]
Program Instance RWSE_MonadLaws {r w s e : Type} `{MonoidLaws w} :
  MonadLaws (RWSE r w s e) := {|
    has_applicative_laws := RWSE_ApplicativeLaws
|}.
Next Obligation.
  autounfold.
  extensionality x.
  rwse; simpl.
  destruct (x _ _); auto.
  destruct p, p; simpl.
  destruct (r1 _ _); auto.
  destruct p, p; simpl.
  destruct (r2 _ _); auto.
  destruct p, p; simpl.
  now rewrite mappend_assoc.
Qed.
Next Obligation.
  autounfold.
  extensionality x.
  rwse; simpl.
  destruct (x _ _); auto.
  destruct p, p; simpl.
  now rewrite mempty_right.
Qed.
Next Obligation.
  autounfold.
  extensionality x.
  rwse; simpl.
  destruct (x _ _); auto.
  destruct p, p; simpl.
  now rewrite mempty_left.
Qed.
Next Obligation.
  autounfold.
  extensionality x.
  rwse; simpl.
  destruct (x _ _); auto.
  destruct p, p; simpl.
  destruct (r1 _ _); auto.
  destruct p, p; simpl.
  reflexivity.
Qed.

End RWSELaws.
