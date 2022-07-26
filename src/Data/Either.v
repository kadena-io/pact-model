Require Import Hask.Control.Monad.
Require Import FunctionalExtensionality.

Generalizable All Variables.
Set Primitive Projections.

Notation Either := sum (only parsing).
Notation Left   := inl (only parsing).
Notation Right  := inr (only parsing).

Definition isLeft  `(x : a + b) : bool := if x then true else false.
Definition isRight `(x : a + b) : bool := if x then false else true.

Definition either `(f : a -> c) `(g : b -> c) (x : a + b) : c :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Definition mapLeft `(f : a -> c) `(x : a + b) : c + b :=
  match x with
  | inl l => inl (f l)
  | inr r => inr r
  end.

Definition Either_map {E X Y} (f : X -> Y) (x : Either E X) : Either E Y :=
  match x with
  | Left e   => Left e
  | Right x' => Right (f x')
  end.

Definition Either_ap {E X Y} (f : Either E (X -> Y)) (x : Either E X)
  : Either E Y :=
  match f with
  | Left e   => Left e
  | Right f' => match x with
    | Left e   => Left e
    | Right x' => Right (f' x')
    end
  end.

Definition Either_join {E X} (x : Either E (Either E X)) : Either E X :=
  match x with
  | Left e           => Left e
  | Right (Left e)   => Left e
  | Right (Right x') => Right x'
  end.

#[export]
Instance Either_Functor {E} : Functor (Either E) :=
{ fmap := @Either_map E
}.

#[export]
Instance Either_Applicative {E} : Applicative (Either E) :=
{ is_functor := Either_Functor
; pure := @Right E
; ap := @Either_ap E
}.

#[export]
Instance Either_Monad {E} : Monad (Either E) :=
{ is_applicative := Either_Applicative
; join := @Either_join E
}.

Module EitherLaws.

Include MonadLaws.

#[local] Hint Unfold Either_ap : core.
#[local] Hint Unfold Either_join : core.
#[local] Hint Unfold Either_map : core.

#[global]
Program Instance Either_FunctorLaws {e : Type} :
  FunctorLaws (Either e).
Next Obligation.
  extensionality x.
  now destruct x.
Qed.
Next Obligation.
  extensionality x.
  now destruct x.
Qed.

#[global]
Program Instance Either_ApplicativeLaws {e : Type} :
  ApplicativeLaws (Either e).
Next Obligation.
  extensionality x.
  now destruct x.
Qed.
Next Obligation.
  now destruct u, w, v.
Qed.

#[global]
Program Instance Either_MonadLaws {e : Type} :
  MonadLaws (Either e) := {|
    has_applicative_laws := Either_ApplicativeLaws
|}.
Next Obligation.
  extensionality x.
  destruct x; auto.
  destruct s; auto.
  now destruct s.
Qed.
Next Obligation.
  extensionality x.
  now destruct x.
Qed.
Next Obligation.
  extensionality x.
  now destruct x.
Qed.
Next Obligation.
  extensionality x.
  destruct x; auto.
  now destruct s.
Qed.

End EitherLaws.
