Require Import Pact.Lib.
Require Import Hask.Control.Monad.
Require Import Hask.Control.Monad.Cont.
Require Import Hask.Control.Monad.Trans.State.
Require Import Hask.Data.Functor.Identity.
Require Import Coq.Classes.RelationClasses.

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

Definition M (s : Type)   := StateT s id.
Definition Wst (s : Type) := StateT s (Cont Prop).

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
Instance M_Functor {s} : Functor (M s) := StateT_Functor.
#[export]
Instance M_Applicative {s} : Applicative (M s) := StateT_Applicative.
#[export]
Instance M_Monad {s} : Monad (M s) := StateT_Monad.

#[export]
Program Instance Wst_Order {s : Type} : Order (Wst s) := {|
  wle := λ _ w₁ w₂, ∀ p s, w₂ p s → w₁ p s
|}.

Definition θst {s : Type} : observation (M s) (Wst s) :=
  λ _ c s p, p (c s).

#[export]
Program Instance θst_LaxMorphism {s : Type} : LaxMorphism (θst (s:=s)).
Next Obligation. sauto. Qed.

#[export]
Program Instance θst_Morphism {s : Type} : Morphism (θst (s:=s)).
Next Obligation.
  unfold Cont_map, Prelude.flip, Prelude.compose,
    comp, Tuple.first, θst in *.
  sauto.
Qed.

Definition ST {s : Type} (A : Type) (w : Wst s A) :=
  ∑ c : M s A, θst _ c ≤ᵂ w.

#[export]
Program Instance ST_Dijkstra {s : Type} : DijkstraMonad (ST (s:=s)) := {|
  retᴰ := λ _ x, (pure[M s] x; _);
  bindᴰ := λ A B w wf (c : ST A w) (f : ∀ x, ST B (wf x)),
    (bind (m:=M s) (λ x, projT1 (f x)) (projT1 c); _);
  subcompᴰ := λ A w w' (c : ST A w) (h : w ≤ᵂ w'), _
|}.
Next Obligation.
  unfold Cont_join, Cont_map, Prelude.flip, Prelude.compose,
    comp, Tuple.first, θst, Datatypes.id, StateT_join, comp,
    curry, Prelude.apply in *.
  simpl in *.
  unfold Datatypes.id.
  destruct c; simpl in *.
  apply w0 in H.
  unfold θst in *.
  destruct (x p).
  destruct (f a); simpl.
  sauto.
Qed.
Next Obligation.
  sauto.
Qed.
Next Obligation.
  unfold Cont_join, Cont_map, Prelude.flip, Prelude.compose,
    comp, Tuple.first, θst, Datatypes.id, StateT_join, comp,
    curry, Prelude.apply in *.
  extensionality s0; simpl.
  sauto.
Qed.

Program Definition getST {s : Type} : ST s (θst _ State.get) :=
  (State.get; _).

Program Definition putST {s : Type} (x : s) : ST () (θst _ (State.put x)) :=
  (State.put x; _).

Definition modify `(f : s → s) :=
  bindᴰ getST (λ x, putST (f x)).

Goal True.
  pose proof Type.
  pose (@getST X).
  unfold θst in s.
  unfold State.get in s.
  unfold getST in s.

  pose (@putST X).
  unfold θst in *.
  unfold State.put in *.
  unfold getST in s.

  pose (@modify).
  unfold θst in *.
  unfold State.get, State.put in *.
  unfold bind in s1.
  simpl in s1.
  unfold StateT_join in s1.
  simpl in s1.
  unfold Cont_join, Cont_map, Prelude.flip, Prelude.compose,
    comp, Tuple.first, θst, Datatypes.id, StateT_join, comp,
    curry, Prelude.apply in s1.
Abort.
