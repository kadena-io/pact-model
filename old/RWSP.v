Require Import Hask.Prelude.
Require Import Hask.Ltac.
Require Import Hask.Control.Monad.
Require Import Data.Semigroup.
Require Import Data.Monoid.
Require Import Hask.Data.Either.
Require Import Coq.Unicode.Utf8.
Require Import Coq.Logic.PropExtensionality.
Require Import Ltac.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(******************************************************************************
 * The RWSET Monad transformer
 *)

Section RWSP.

Context {r s w : Type}.

Definition RWSP (a : Type) := r → s → a → s → w → Prop.

#[export]
Program Instance RWSP_Functor : Functor RWSP := {
  fmap := λ A B f (x : RWSP A), λ r s b s' w,
    ∃ a, x r s a s' w ∧ f a = b
}.

Definition RWSP_ap `{Semigroup w} `(f : RWSP (a → b)) (x : RWSP a) :
  RWSP b := λ r s0 b s2 w2,
    ∃ k s1 w0, f r s0 k s1 w0 ∧
    ∃ a w1, x r s1 a s2 w1 ∧
    k a = b ∧ w2 = w0 ⨂ w1.

#[export]
Program Instance RWSP_Applicative `{Monoid w} : Applicative RWSP := {
  pure := λ _ x, λ r s a s' w, x = a ∧ s = s' ∧ w = mempty;
  ap   := @RWSP_ap _
}.

Definition RWSP_join `{Semigroup w} `(x : RWSP (RWSP a)) :
  RWSP a := λ r s0 a s2 w2,
    ∃ y s1 w0, x r s0 y s1 w0 ∧
    ∃ a' w1, y r s1 a' s2 w1 ∧
    a = a' ∧ w2 = w0 ⨂ w1.

#[export]
Program Instance RWSP_Monad `{Monoid w} : Monad RWSP := {
  join := @RWSP_join _
}.

Context `{Monoid w}.

Definition ask : RWSP r := λ r s a s' w, a = r ∧ s = s' ∧ w = mempty.

Definition local (f : r → r) `(x : RWSP a) : RWSP a := λ r s a s' w,
  x (f r) s a s' w.

Definition get : RWSP s :=
  λ _ s a s' w, a = s ∧ s = s' ∧ w = mempty.
Definition gets `(f : s → a) : RWSP a :=
  λ _ s a s' w, a = f s ∧ s = s' ∧ w = mempty.
Definition put (x : s) : RWSP unit :=
  λ _ _ _ s' w, s' = x ∧ w = mempty.
Definition modify (f : s → s) : RWSP unit :=
  λ _ s _ s' w, s' = f s ∧ w = mempty.

Definition tell (v : w) : RWSP unit :=
  λ _ s _ s' w, s = s' ∧ w = v.

Definition decide `(p : Prop) : RWSP bool :=
  λ _ s b s' w,
    ((p ∧ b = true) ∨ (¬ p ∧ b = false)) ∧ s = s' ∧ w = mempty.

Definition require `(p : Prop) : RWSP unit :=
  λ _ s _ s' w, p ∧ s = s' ∧ w = mempty.

Definition demand `(v : a → Prop) : RWSP a :=
  λ _ s a s' w, v a ∧ s = s' ∧ w = mempty.

Definition partial `(v : a → Prop) : RWSP (option a) :=
  λ _ s ma s' w,
    ((∃ a, v a ∧ ma = Some a) ∨ (∀ a, ¬ v a ∧ ma = None))
      ∧ s = s' ∧ w = mempty.

Definition choose `(v : a → Prop) : RWSP bool :=
  λ _ s b s' w,
    ((∃ a, v a ∧ b = true) ∨ (∀ a, ¬ v a ∧ b = false))
      ∧ s = s' ∧ w = mempty.

End RWSP.

Arguments RWSP r s w a.

Module RWSPLaws.

Require Import FunctionalExtensionality.

Include MonadLaws.

Lemma first_id : forall a z, first (a:=a) (b:=a) (z:=z) id = id.
Proof.
  unfold first.
  intros a z.
  extensionality x.
  destruct x; auto.
Qed.

Program Instance RWSP_FunctorLaws {r s w : Type} :
  FunctorLaws (@RWSP r s w).
Next Obligation.
  extensionality x.
  extensionality r0.
  extensionality s0.
  extensionality b0.
  extensionality s1.
  extensionality w0.
  unfold id.
  apply propositional_extensionality.
  split; intros.
  - now destruct H, H; subst.
  - now exists b0.
Qed.
Next Obligation.
  unfold comp.
  extensionality x.
  extensionality r0.
  extensionality s0.
  extensionality c0.
  extensionality s1.
  extensionality w0.
  apply propositional_extensionality.
  split; intros.
  - reduce.
    now exists x1.
  - reduce.
    exists (g x0).
    split; auto.
    now exists x0.
Qed.

Program Instance RWSP_Applicative {r s w : Type} `{Monoid w} :
  ApplicativeLaws (@RWSP r s w).
Next Obligation.
  unfold RWSP_ap.
  extensionality x.
  extensionality r0.
  extensionality s0.
  extensionality a0.
  extensionality s1.
  extensionality w0.
  apply propositional_extensionality.
  split; intros.
  - reduce.
    rewrite mempty_left.
    exact H0.
  - exists id.
    exists s0.
    exists mempty.
    split; auto.
    exists a0.
    exists w0.
    rewrite mempty_left.
    split; auto.
Qed.
Next Obligation.
  unfold RWSP_ap.
  extensionality r0.
  extensionality s0.
  extensionality b0.
  extensionality s2.
  extensionality w1.
  apply propositional_extensionality.
  split; intros; reduce;
  repeat eexists; eauto.
  - rewrite mempty_left.
    now rewrite mappend_assoc.
  - rewrite mempty_left.
    now rewrite mappend_assoc.
Qed.
Next Obligation.
  unfold RWSP_ap.
  extensionality r0.
  extensionality s0.
  extensionality b0.
  extensionality s2.
  extensionality w1.
  apply propositional_extensionality.
  split; intros; reduce;
  repeat eexists; eauto.
  - now rewrite mempty_left.
  - now rewrite mempty_right.
Qed.
Next Obligation.
  unfold RWSP_ap.
  extensionality r0.
  extensionality s0.
  extensionality b0.
  extensionality s2.
  extensionality w1.
  apply propositional_extensionality.
  split; intros; reduce;
  repeat eexists; eauto.
  - now rewrite mempty_left, mempty_right.
  - now rewrite mempty_left, mempty_right.
Qed.
Next Obligation.
  unfold RWSP_ap.
  extensionality x.
  extensionality r0.
  extensionality s0.
  extensionality b0.
  extensionality s2.
  extensionality w0.
  apply propositional_extensionality.
  split; intros; reduce;
  repeat eexists; eauto.
  - now rewrite mempty_left.
  - now rewrite mempty_left.
Qed.

Program Instance RWSP_Monad {r s w : Type} `{Monoid w} :
  MonadLaws (@RWSP r s w).
Next Obligation.
  unfold RWSP_join.
  extensionality x; simpl.
  extensionality r0.
  extensionality s0.
  extensionality a0.
  extensionality s2.
  extensionality w0.
  apply propositional_extensionality.
  split; intros; reduce;
  repeat eexists; eauto.
  - now rewrite mappend_assoc.
  - now rewrite mappend_assoc.
Qed.
Next Obligation.
  unfold RWSP_join.
  extensionality x; simpl.
  extensionality r0.
  extensionality s0.
  extensionality a0.
  extensionality s2.
  extensionality w0.
  apply propositional_extensionality.
  split; intros; reduce;
  repeat eexists; eauto.
  - now rewrite mempty_right.
  - now rewrite mempty_right.
Qed.
Next Obligation.
  unfold RWSP_join.
  extensionality x; simpl.
  extensionality r0.
  extensionality s0.
  extensionality a0.
  extensionality s2.
  extensionality w0.
  apply propositional_extensionality.
  split; intros; reduce;
  repeat eexists; eauto.
  - now rewrite mempty_left.
  - now rewrite mempty_left.
Qed.
Next Obligation.
  unfold RWSP_join.
  extensionality x; simpl.
  extensionality r0.
  extensionality s0.
  extensionality a0.
  extensionality s2.
  extensionality w1.
  apply propositional_extensionality.
  split; intros; reduce;
  repeat eexists; eauto.
Qed.

End RWSPLaws.
