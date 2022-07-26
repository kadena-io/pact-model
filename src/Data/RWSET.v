Require Import Hask.Data.Tuple.
Require Import Hask.Control.Monad.
Require Import Hask.Data.Functor.Identity.
Require Import Hask.Control.Monad.Cont.
Require Import Coq.Unicode.Utf8.
Require Import FunctionalExtensionality.
Require Import Pact.Data.Monoid.
Require Import Pact.Data.Either.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(******************************************************************************
 * The RWSET Monad transformer
 *)

Ltac rwse :=
  let r := fresh "r" in extensionality r;
  let s := fresh "s" in extensionality s.

Section RWSET.

Context {r w s e : Type}.
Context {m : Type → Type}.

Definition RWSET (a : Type) : Type :=
  r → s → m (e + (a * (s * w)))%type.

Definition ask `{Monoid w} `{Applicative m} : RWSET r :=
  λ r s, pure (inr (r, (s, mempty))).
Definition asks`{Monoid w } `{Applicative m} {a : Type} (f : r → a) : RWSET a :=
  λ r s, pure (inr (f r, (s, mempty))).
Definition local (f : r → r) `(x : RWSET a) : RWSET a :=
  λ r s, x (f r) s.
Definition get `{Monoid w} `{Applicative m} : RWSET s :=
  λ _ s, pure (inr (s, (s, mempty))).
Definition gets `{Monoid w} `{Applicative m} {a : Type} (f : s → a) : RWSET a :=
  λ _ s, pure (inr (f s, (s, mempty))).
Definition put `{Monoid w} `{Applicative m} (x : s) : RWSET unit :=
  λ _ _, pure (inr (tt, (x, mempty))).
Definition modify `{Monoid w} `{Applicative m} (f : s → s) : RWSET unit :=
  λ _ s, pure (inr (tt, (f s, mempty))).
Definition tell `{Applicative m} (v : w) : RWSET unit :=
  λ _ s, pure (inr (tt, (s, v))).
Definition throw `{Applicative m} {a : Type} (err : e) : RWSET a :=
  λ _ _, pure (inl err).

#[export]
Instance RWSET_Functor `{Functor m} : Functor RWSET := {
  fmap := λ a _ f (x : RWSET a), λ r s,
    fmap[m] (fmap (first f)) (x r s)
}.

Definition RWSET_ap `{Semigroup w} `{Monad m}
  `(f : RWSET (a → b)) (x : RWSET a) :
  RWSET b := λ r s,
    f' <- f r s ;
    match f' with
    | inl e => pure (inl e)
    | inr (f'', (s', w')) =>
        x' <- fmap f'' x r s' ;
        pure (match x' with
              | inl e => inl e
              | inr (x'', (s'', w'')) =>
                  inr (x'', (s'', w' ⨂ w''))
              end)
    end.

#[export]
Instance RWSET_Applicative `{Monoid w} `{Monad m} : Applicative RWSET := {
  is_functor := RWSET_Functor;
  pure := λ _ x, λ _ s, pure (inr (x, (s, mempty)));
  ap   := λ _ _, RWSET_ap
}.

Definition RWSET_join `{Semigroup w} `{Monad m} `(x : RWSET (RWSET a)) :
  RWSET a := λ r s,
    x' <- x r s ;
    match x' with
    | inl e => pure (inl e)
    | inr (y, (s', w')) =>
        y' <- y r s' ;
        pure (match y' with
              | inl e => inl e
              | inr (z, (s'', w'')) =>
                  inr (z, (s'', w' ⨂ w''))
              end)
    end.

#[export]
Instance RWSET_Monad `{Monoid w} `{Monad m} : Monad RWSET | 1 := {
  is_applicative := RWSET_Applicative;
  join := λ _, RWSET_join
}.

End RWSET.

Arguments RWSET : clear implicits.

Definition RWSE r w s e := RWSET r w s e Identity.

Definition RWSEP r w s e := RWSET r w s e (Cont Prop).

Module RWSETLaws.

Include MonadLaws.
Module Import EL := EitherLaws.

#[local] Hint Unfold RWSET_ap : core.
#[local] Hint Unfold RWSET_join : core.
#[local] Hint Unfold Either_map : core.
#[local] Hint Unfold Tuple.first : core.
#[local] Hint Unfold id : core.

Lemma first_id a z : first (a:=a) (b:=a) (z:=z) id = id.
Proof.
  unfold first.
  extensionality x.
  now destruct x.
Qed.

Lemma first_comp `(f : b → c) `(g : a → b) z x :
  first f (first g x) = first (z:=z) (f \o g) x.
Proof.
  unfold first.
  now destruct x.
Qed.

#[global]
Program Instance RWSET_FunctorLaws {r w s e : Type} `{FunctorLaws m} :
  FunctorLaws (RWSET r w s e m).
Next Obligation.
  extensionality x.
  rwse.
  rewrite first_id.
  rewrite (fmap_id (FunctorLaws:=Either_FunctorLaws (e:=e))).
  now rewrite fmap_id.
Qed.
Next Obligation.
  extensionality x.
  rwse; simpl.
  rewrite fmap_comp_x.
  pose proof (fmap_comp (FunctorLaws:=Either_FunctorLaws (e:=e))).
  simpl in H1.
  unfold comp in H1.
  rewrite H1.
  repeat f_equal.
  extensionality x0.
  now apply first_comp.
Qed.

#[global]
Program Instance RWSET_ApplicativeLaws {r w s e : Type}
  `{MonoidLaws w} `{MonadLaws m} :
  ApplicativeLaws (RWSET r w s e m).
Next Obligation.
  extensionality x.
  rwse.
  unfold RWSET_ap.
  unfold bind, comp; simpl.
  rewrite fmap_pure_x.
  rewrite join_pure_x.
  rewrite fmap_comp_x.
  rewrite first_id; simpl.
  rewrite (fmap_id (FunctorLaws:=Either_FunctorLaws (e:=e))).
  unfold id.
  rewrite <- fmap_comp_x.
  rewrite join_fmap_pure_x.
  rewrite <- fmap_id_x.
  f_equal.
  extensionality y.
  destruct y; auto.
  destruct p; auto.
  destruct p; auto.
  now rewrite mempty_left.
Qed.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

#[global]
Program Instance RWSET_MonadLaws {r w s e : Type}
  `{MonoidLaws w} `{MonadLaws m} :
  MonadLaws (RWSET r w s e m) := {|
    has_applicative_laws := RWSET_ApplicativeLaws
|}.
Next Obligation.
  unfold comp.
  extensionality x.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Notation "a >>[ H ] b" :=
  (bind (H:=H) (fun _ => b) a) (at level 90, right associativity) : monad_scope.

Lemma put_getM {r w s e : Type} `{Monoid w} `{MonadLaws m} `(x : s) :
  (put x >>[RWSET_Monad (r:=r) (e:=e)] get) =
  (put x >>[RWSET_Monad (r:=r) (e:=e)] pure x).
Proof.
  simpl.
  rwse.
  unfold put, RWSET_join, bind, comp.
  now rewrite !fmap_comp_x, !fmap_pure_x.
Qed.

End RWSETLaws.
