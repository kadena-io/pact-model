Require Import Hask.Prelude.
Require Import Hask.Ltac.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Monoid.
Require Import Coq.Unicode.Utf8.

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

Definition get                : RWSE s    := λ r s w, inr (s, (s, w)).
Definition gets `(f : s → a)  : RWSE a    := λ r s w, inr (f s, (s, w)).
Definition put (x : s)        : RWSE unit := λ _ _ w, inr (tt, (x, w)).
Definition modify (f : s → s) : RWSE unit := λ _ s w, inr (tt, (f s, w)).

Definition tell `{Monoid w} (v : w) : RWSE unit :=
  λ _ s w, inr (tt, (s, w ⨂ v)).

Definition tellf (f : w → w) : RWSE unit := λ _ s w, inr (tt, (s, f w)).

Definition throw (err : e) : RWSE unit := λ _ _ _, inl err.

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
  | inr (y, (s', w')) => y r s w
  end.

#[export]
Program Instance RWSE_Monad : Monad RWSE := {
  join := @RWSE_join
}.

End RWSE.

Arguments RWSE r s w e a.

Module RWSELaws.

Require Import FunctionalExtensionality.

Include MonadLaws.

Lemma first_id : forall a z, first (a:=a) (b:=a) (z:=z) id = id.
Proof.
  unfold first.
  intros a z.
  extensionality x.
  destruct x; auto.
Qed.

Program Instance RWSE_FunctorLaws {r s w e : Type} :
  FunctorLaws (@RWSE r s w e).
Next Obligation. Admitted.
Next Obligation. Admitted.

Program Instance RWSE_Applicative {r s w e : Type} :
  ApplicativeLaws (@RWSE r s w e).
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Program Instance RWSE_Monad {r s w e : Type} :
  MonadLaws (@RWSE r s w e).
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

End RWSELaws.
