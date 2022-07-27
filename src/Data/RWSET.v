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

(******************************************************************************
 * The RWSET Monad transformer
 *)

Ltac rwse :=
  let r := fresh "r" in extensionality r;
  let s := fresh "s" in extensionality s.

Section RWSET.

Context {r w s e : Type}.
Context {m : Type → Type}.

Definition RWSET `{Monad m} `{Monoid w} (a : Type) : Type :=
  r → s → m (e + (a * (s * w)))%type.

Context `{Monad m}.
Context `{Monoid w}.

Definition ask : RWSET r :=
  λ r s, pure (inr (r, (s, mempty))).
Definition asks {a : Type} (f : r → a) : RWSET a :=
  λ r s, pure (inr (f r, (s, mempty))).
Definition local (f : r → r) `(x : RWSET a) : RWSET a :=
  λ r s, x (f r) s.
Definition get : RWSET s :=
  λ _ s, pure (inr (s, (s, mempty))).
Definition gets {a : Type} (f : s → a) : RWSET a :=
  λ _ s, pure (inr (f s, (s, mempty))).
Definition put (x : s) : RWSET unit :=
  λ _ _, pure (inr (tt, (x, mempty))).
Definition modify (f : s → s) : RWSET unit :=
  λ _ s, pure (inr (tt, (f s, mempty))).
Definition tell (v : w) : RWSET unit :=
  λ _ s, pure (inr (tt, (s, v))).
Definition throw {a : Type} (err : e) : RWSET a :=
  λ _ _, pure (inl err).

#[export]
Instance RWSET_Functor : Functor RWSET := {
  fmap := λ a _ f (x : RWSET a), λ r s,
    fmap[m] (fmap (first f)) (x r s)
}.

Definition RWSET_ap `(f : RWSET (a → b)) (x : RWSET a) :
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
Instance RWSET_Applicative : Applicative RWSET := {
  is_functor := RWSET_Functor;
  pure := λ _ x, λ _ s, pure (inr (x, (s, mempty)));
  ap   := λ _ _, RWSET_ap
}.

Definition RWSET_join `(x : RWSET (RWSET a)) :
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
Instance RWSET_Monad : Monad RWSET | 1 := {
  is_applicative := RWSET_Applicative;
  join := λ _, RWSET_join
}.

End RWSET.

Arguments RWSET r w s e m {_ _}.
Arguments RWSET_ap {r w s e m _ _ a b} f x _ _ /.
Arguments RWSET_join {r w s e m _ _ a} x _ _ /.

#[export] Hint Unfold RWSET_ap : core.
#[export] Hint Unfold RWSET_join : core.
#[export] Hint Unfold Either_map : core.
#[export] Hint Unfold Tuple.first : core.
#[export] Hint Unfold id : core.

Definition RWSE r w s e `{Monoid w} := RWSET r w s e Identity.

Definition RWSEP r w s e `{Monoid w} := RWSET r w s e (Cont Prop).

Module RWSETLaws.

Module Import EL := EitherLaws.
Include MonadLaws.

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

Section RWSETLaws.

Context {r w s e : Type}.
Context `{MonoidLaws w}.
Context `{MonadLaws m}.

#[global]
Program Instance RWSET_FunctorLaws :
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
  simpl in H3.
  unfold comp in H3.
  rewrite H3.
  repeat f_equal.
  extensionality x0.
  now apply first_comp.
Qed.

#[global]
Program Instance RWSET_ApplicativeLaws :
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
Program Instance RWSET_MonadLaws :
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

Lemma put_getM `(x : s) :
  (put x >> get (r:=r) (e:=e)) =
  (put x >> pure x).
Proof.
  simpl.
  rwse.
  unfold put, RWSET_join, bind, comp.
  now rewrite !fmap_comp_x, !fmap_pure_x.
Qed.

End RWSETLaws.

End RWSETLaws.


Require Import Coq.Arith.Arith.

#[export] Program Instance Unit_Semigroup : Semigroup unit.
#[export] Program Instance Unit_Monoid : Monoid unit.
Next Obligation. exact tt. Defined.

Definition sample {m : Type → Type} `{Monad m} :
  RWSET nat unit nat nat m nat :=
  x <- get ;
  put (x + 1) ;;
  if x <? 20
  then throw 100
  else pure 50.
