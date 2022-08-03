Require Import Coq.Arith.Arith.
Require Import Coq.Unicode.Utf8.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Cont.
Require Import Hask.Control.Monad.State.
Require Import Hask.Control.Monad.Trans.Class.
Require Import Hask.Control.Monad.Trans.State.
Require Import Hask.Control.Monad.Trans.Either.
Require Import Hask.Data.Functor.Identity.
Require Import Pact.Data.Either.
Require Import Coq.Classes.RelationClasses.
Require Import FunctionalExtensionality.

From Hammer Require Export Tactics Hammer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Notation "'∑' x .. y , p" := (sigT (fun x => .. (sigT (fun y => p%type)) ..))
  (at level 200, x binder, right associativity,
   format "'[' '∑'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Notation "( x ; y )" := (@existT _ _ x y).
Notation "( x ; y ; z )" := (x ; ( y ; z)).
Notation "( x ; y ; z ; t )" := (x ; ( y ; (z ; t))).
Notation "( x ; y ; z ; t ; u )" := (x ; ( y ; (z ; (t ; u)))).
Notation "( x ; y ; z ; t ; u ; v )" := (x ; ( y ; (z ; (t ; (u ; v))))).
Notation "x .π1" := (@projT1 _ _ x) (at level 3, format "x '.π1'").
Notation "x .π2" := (@projT2 _ _ x) (at level 3, format "x '.π2'").

Class Order W `{Monad W} := {
  wle : ∀ A, W A → W A → Prop ;
  trans :> ∀ A, Transitive (@wle A)
}.

Arguments Order W {_}.
Arguments wle {_ _ _} {_}.

Notation "x ≤ᵂ y" := (wle x y) (at level 80).

Class MonoSpec W `{Order W} := {
  bind_mono :
    ∀ A B (w w' : W A) (wf wf' : A → W B),
      w ≤ᵂ w' →
      (∀ x, wf x ≤ᵂ wf' x) →
      bind wf w ≤ᵂ bind wf' w'
}.

Definition observation (M W : Type → Type) :=
  ∀ A (c : M A), W A.

Class LaxMorphism {M W} `{Monad M} `{Order W} (θ : observation M W) := {
  θ_ret :
    ∀ A (x : A),
      θ _ (pure x) ≤ᵂ pure x ;
  θ_bind :
    ∀ A B c f,
      θ _ (bind (X:=A) (Y:=B) f c) ≤ᵂ bind (λ x, θ _ (f x)) (θ _ c)
}.

Class DijkstraMonad {W} `{Word : Order W} (D : ∀ A (w : W A), Type) := {
  retᴰ : ∀ A (x : A), D A (pure x) ;
  bindᴰ : ∀ A B w wf (c : D A w) (f : ∀ x, D B (wf x)), D B (bind wf w) ;
  subcompᴰ : ∀ A w w' (c : D A w) (h : w ≤ᵂ w'), D A w'
}.

Arguments retᴰ {_ _ _ _ _} [_].
Arguments bindᴰ {_ _ _ _ _} [_ _ _ _].
Arguments subcompᴰ {_ _ _ _ _} [_ _ _] _ {_}.

Class Morphism `{hM : Monad M} `{hN : Monad N} (f : ∀ A, M A → N A) := {
  morph_ret : ∀ A (x : A), f A (pure x) = pure x ;
  morph_bind :
    ∀ A B (c : M A) (k : A → M B),
      f _ (bind k c) = bind (λ x, f _ (k x)) (f _ c)
}.

Definition Wpure (a : Type) := (a → Prop) → Prop.

#[export]
Program Instance Wpure_Order : Order Wpure := {|
  wle := λ _ w₁ w₂, ∀ p, w₂ p → w₁ p
|}.

(*************************************************************************
 * Example
 *)

Ltac calculate :=
  cbv [
    Cont
    Cont_Applicative
    Cont_Functor
    Cont_Monad
    Cont_join
    Cont_map
    Datatypes.id
    EitherT_Applicative
    EitherT_Functor
    EitherT_Monad
    EitherT_MonadTrans
    EitherT_join
    EitherT_map
    EitherT_pure
    Either_Applicative
    Either_Functor
    Either_Monad
    Either_join
    Either_map
    Hask.Data.Either.Either_Applicative
    Hask.Data.Either.Either_Functor
    Hask.Data.Either.Either_Monad
    Hask.Data.Either.Either_join
    Hask.Data.Either.Either_map
    Identity_Applicative
    Identity_Functor
    Identity_Monad
    Prelude.apply
    Prelude.compose
    Prelude.flip
    State.get
    State.modify
    State.put
    StateT_Applicative
    StateT_Functor
    StateT_Monad
    StateT_MonadTrans
    StateT_join
    State_Applicative
    State_Functor
    State_Monad
    Tuple.curry
    Tuple.first
    bind
    comp
    fmap
    getT
    is_applicative
    is_functor
    join
    lift
    modifyT
    pure
    putT
  ] in *.

Module DijkstraSt.

Section DijkstraExample.

Variable s : Type.

Definition M := State s.
Definition W := StateT s (Cont Prop).

#[export]
Program Instance id_Functor : Functor id := {|
  fmap := λ _ _ f x, f x
|}.
#[export]
Program Instance id_Applicative : Applicative id := {|
  pure := λ _ x, x;
  ap := λ _ _ f x, f x
|}.
#[export]
Program Instance id_Monad : Monad id.

#[export]
Instance M_Functor : Functor M := State_Functor.
#[export]
Instance M_Applicative : Applicative M := State_Applicative.
#[export]
Instance M_Monad : Monad M := State_Monad.

#[export]
Program Instance W_Order : Order W := {|
  wle := λ _ w₁ w₂, ∀ p s, w₂ p s → w₁ p s
|}.

Definition θ : observation M W := λ _ c s p, p (c s).

#[export]
Program Instance θ_LaxMorphism : LaxMorphism θ.
Next Obligation.
  unfold θ in *.
  calculate; sauto.
Qed.

#[export]
Program Instance θ_Morphism : Morphism θ.
Next Obligation.
  unfold θ in *.
  calculate.
  extensionality s0.
  extensionality p.
  sauto.
Qed.

Definition ST (A : Type) (w : W A) := ∑ c : M A, θ c ≤ᵂ w.

#[export]
Program Instance ST_Dijkstra : DijkstraMonad ST := {|
  retᴰ := λ _ x, (pure[M] x; _);
  bindᴰ := λ A B w wf (c : ST w) (f : ∀ x, ST (wf x)),
    (bind (m:=M) (λ x, projT1 (f x)) (projT1 c); _);
  subcompᴰ := λ A w w' (c : ST w) (h : w ≤ᵂ w'), _
|}.
Next Obligation.
  unfold θ in *.
  calculate.
  destruct c; simpl in *.
  apply w0 in H.
  unfold θ in *.
  destruct (x p).
  destruct (f a);
  sauto.
Defined.
Next Obligation.
  sauto.
Defined.

Program Definition liftST0 `(f : M a) : ST (θ f) := (f; _).
Program Definition liftST1 `(f : a → M b) (x : a) : ST (θ (f x)) := (f x; _).

Definition getST := liftST0 State.get.
Definition putST := liftST1 State.put.

Definition modify' := liftST1 State.modify.

Definition modifyST `(f : s → s) := bindᴰ getST (λ x, putST (f x)).

End DijkstraExample.

Goal True.
  pose getST.
  pose putST.
  pose modify'.
  pose modifyST.
  unfold θ in *.
  calculate.

  auto.
Qed.

Definition algorithm : M nat nat :=
  n <- getT ;
  if n <? 10
  then
    putT (n + 1) ;;
    pure (n + 100)
  else pure 0.

Definition algorithmST := liftST0 algorithm.

Goal True.
  pose algorithmST.
  unfold θ, algorithm in s.
  calculate.

  auto.
Qed.

End DijkstraSt.

Module DijkstraSte.

Section DijkstraExample.

Variable s : Type.
Variable e : Type.

Definition M := StateT s (Either e).
Definition W := StateT s (EitherT e (Cont Prop)).

#[export]
Program Instance id_Functor : Functor id := {|
  fmap := λ _ _ f x, f x
|}.
#[export]
Program Instance id_Applicative : Applicative id := {|
  pure := λ _ x, x;
  ap := λ _ _ f x, f x
|}.
#[export]
Program Instance id_Monad : Monad id.

#[export]
Instance M_Functor : Functor M := StateT_Functor.
#[export]
Instance M_Applicative : Applicative M := StateT_Applicative.
#[export]
Instance M_Monad : Monad M := StateT_Monad.

#[export]
Program Instance W_Order : Order W := {|
  wle := λ _ w₁ w₂, ∀ p s, w₂ p s → w₁ p s
|}.

Definition θbot : observation M W := λ _ c s p,
  match c s with
  | inl _ => False
  | inr x => p (inr x)
  end.

#[export]
Program Instance θbot_LaxMorphism : LaxMorphism θbot.
Next Obligation.
  unfold θbot in *.
  calculate; sauto.
Qed.

#[export]
Program Instance θbot_Morphism : Morphism θbot.
Next Obligation.
  unfold θbot in *.
  calculate.
  extensionality s0.
  extensionality p.
  sauto.
Qed.

Definition θtop : observation M W := λ _ c s p,
  match c s with
  | inl _ => True
  | inr x => p (inr x)
  end.

#[export]
Program Instance θtop_LaxMorphism : LaxMorphism θtop.
Next Obligation.
  unfold θtop in *.
  calculate; sauto.
Qed.

#[export]
Program Instance θtop_Morphism : Morphism θtop.
Next Obligation.
  unfold θtop in *.
  calculate.
  extensionality s0.
  extensionality p.
  sauto.
Qed.

Definition STbot (A : Type) (w : W A) := ∑ c : M A, θbot c ≤ᵂ w.
Definition STtop (A : Type) (w : W A) := ∑ c : M A, θtop c ≤ᵂ w.

#[export]
Program Instance STbot_Dijkstra : DijkstraMonad STbot := {|
  retᴰ := λ _ x, (pure[M] x; _);
  bindᴰ := λ A B w wf (c : STbot w) (f : ∀ x, STbot (wf x)),
    (bind (m:=M) (λ x, projT1 (f x)) (projT1 c); _);
  subcompᴰ := λ A w w' (c : STbot w) (h : w ≤ᵂ w'), _
|}.
Next Obligation.
  unfold θbot in *.
  simpl in *.
  unfold Datatypes.id.
  destruct c; simpl in *.
  apply w0 in H.
  unfold θbot in *.
  destruct (x p).
  - calculate; sauto.
  - calculate.
    destruct p0.
    destruct (f a).
    unfold θbot in *.
    sauto.
Defined.
Next Obligation.
  sauto.
Defined.

#[export]
Program Instance STtop_Dijkstra : DijkstraMonad STtop := {|
  retᴰ := λ _ x, (pure[M] x; _);
  bindᴰ := λ A B w wf (c : STtop w) (f : ∀ x, STtop (wf x)),
    (bind (m:=M) (λ x, projT1 (f x)) (projT1 c); _);
  subcompᴰ := λ A w w' (c : STtop w) (h : w ≤ᵂ w'), _
|}.
Next Obligation.
  unfold θtop in *.
  simpl in *.
  unfold Datatypes.id.
  destruct c; simpl in *.
  apply w0 in H.
  unfold θtop in *.
  destruct (x p).
  - calculate; sauto.
  - calculate.
    destruct p0.
    destruct (f a).
    unfold θtop in *.
    sauto.
Defined.
Next Obligation.
  sauto.
Defined.

Program Definition liftSTbot0 `(f : M a) : STbot (θbot f) := (f; _).
Program Definition liftSTbot1 `(f : a → M b) (x : a) :
  STbot (θbot (f x)) := (f x; _).

Program Definition liftSTtop0 `(f : M a) : STtop (θtop f) := (f; _).
Program Definition liftSTtop1 `(f : a → M b) (x : a) :
  STtop (θtop (f x)) := (f x; _).

Definition getSTbot    := liftSTbot0 State.getT.
Definition putSTbot    := liftSTbot1 State.putT.
Definition modifySTbot := liftSTbot1 State.modifyT.

Definition getSTtop    := liftSTtop0 State.getT.
Definition putSTtop    := liftSTtop1 State.putT.
Definition modifySTtop := liftSTtop1 State.modifyT.

End DijkstraExample.

Goal True.
  pose getSTbot.
  pose putSTbot.
  pose modifySTbot.
  pose getSTtop.
  pose putSTtop.
  pose modifySTtop.
  unfold θbot, θtop in *.
  calculate.

  auto.
Qed.

Definition assert {s e : Type} (b : bool) (err : e) : M s e unit :=
  if b
  then
    pure tt
  else
    lift (inl err).

Arguments assert _ _ /.

Definition algorithm (x : nat) : M nat unit nat :=
  n <- getT ;
  assert (n <? 10) tt ;;
  putT (n + x) ;;
  assert (x =? 100) tt ;;
  r <- getT ;
  assert (Nat.even r) tt ;;
  pure (n + 100).

Definition algorithmST := liftSTbot1 algorithm.

Lemma if_fun {A B : Type} (b : bool) (P Q : A → B) (x : A) :
  (if b then λ x, P x else λ x, Q x) x = if b then P x else Q x.
Proof. sauto. Qed.

Lemma match_if {A B C : Type} (b : bool) (P Q : A + B) (F : A → C) (G : B → C) :
  match (if b then P else Q) with
  | inl x => F x
  | inr x => G x
  end =
  if b
  then
    match P with
    | inl x => F x
    | inr x => G x
    end
  else
    match Q with
    | inl x => F x
    | inr x => G x
    end.
Proof. sauto. Qed.

Lemma in_ST {A B C : Type} {P Q : W A B C} : forall H : P = Q,
  STbot P = STbot Q.
Proof. sauto. Qed.

Lemma in_STx {A B C D : Type} {P Q : D → W A B C} : forall H : P = Q,
  (∀ x : D, STbot (P x)) = (∀ x : D, STbot (Q x)).
Proof. sauto. Qed.

Ltac calc :=
  repeat
    (calculate;
     cbv [ θbot algorithm assert M_Functor M_Applicative M_Monad ] in *
    ).

Goal True.
  pose algorithmST.
  calc.
  unshelve erewrite (in_STx _) in s. {
    extensionality s0.
    extensionality p.
    extensionality x.
    repeat rewrite !if_fun, !match_if.
    reflexivity.
  }
  simpl in s.

  auto.
Qed.

End DijkstraSte.
