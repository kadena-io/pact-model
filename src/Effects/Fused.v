Require Export Hask.Control.Monad.
Require Import Hask.Control.Monad.Trans.Reader.
Require Import Hask.Control.Monad.State.
Require Import Hask.Control.Monad.Trans.State.
Require Import Pact.Data.Either.
Require Import Hask.Control.Compose.

Require Export Equations.Prop.DepElim.
From Equations Require Export Equations.

Set Universe Polymorphism.
Generalizable All Variables.

#[export]
Program Instance id_Functor : Functor id := {|
  fmap := fun _ _ f x => f x
|}.
#[export]
Program Instance id_Applicative : Applicative id := {|
  pure := fun _ x => x;
  ap := fun _ _ f x => f x
|}.
#[export]
Program Instance id_Monad : Monad id.

#[export]
Program Instance arrow_Functor {r} : Functor (fun a => r -> a) := {|
  fmap := fun _ _ f x r => f (x r)
|}.
#[export]
Program Instance arrow_Applicative {r} : Applicative (fun a => r -> a) := {|
  pure := fun _ x _ => x;
  ap := fun _ _ f x r => f r (x r)
|}.
#[export]
Program Instance arrow_Monad {r} : Monad (fun a => r -> a) := {|
  join := fun _ x r => x r r
|}.

Definition Handler ctx (m n : Type -> Type) :=
  forall x, ctx (m x) -> n (ctx x).

Definition hcomp `{Functor n} `{Functor ctx1} {ctx2 l m}
  (hdl1 : Handler ctx1 m n) (hdl2 : Handler ctx2 l m) :
  Handler (ctx1 \o ctx2) l n :=
  fun _ => hdl1 _ \o fmap (hdl2 _).

Infix "~<~" := hcomp (at level 51, right associativity).

Definition Sig : Type := (Type -> Type) -> (Type -> Type).

Inductive Sum (f g : Sig) (m : Type -> Type) : Type -> Type :=
  | L {k} : f m k -> Sum f g m k
  | R {k} : g m k -> Sum f g m k.

Infix ":+:" := Sum (at level 51, right associativity).

Arguments L {_ _ _ k} _.
Arguments R {_ _ _ k} _.

Equations reassociateSumL `(s : (l1 :+: l2 :+: r) m a) :
  ((l1 :+: l2) :+: r) m a :=
  reassociateSumL (L l)     := L (L l);
  reassociateSumL (R (L l)) := L (R l);
  reassociateSumL (R (R x)) := R x.

Class Algebra (sg : Sig) (m : Type -> Type) `{Monad m} := {
  alg `{Functor ctx} {n a}
    : Handler ctx n m
    -> sg n a
    -> ctx unit
    -> m (ctx a)
}.

Close Scope nat_scope.

Class Member (sub sup : Sig) := {
  inj {m a} : sub m a -> sup m a
}.

#[export]
Instance Member_assoc {t l1 l2 r} :
  Member t (l1 :+: l2 :+: r) -> Member t ((l1 :+: l2) :+: r) | 9 := fun _ => {|
  inj := fun _ _ => reassociateSumL \o inj
|}.

#[export]
Instance Member_tl {l l' r} : Member l r -> Member l (l' :+: r) | 3 := fun _ => {|
  inj := fun _ _ => R \o inj
|}.

#[export]
Instance Member_hd {l r} : Member l (l :+: r) | 2 := {|
  inj := fun _ _ => L
|}.

#[export]
Instance Member_refl {t} : Member t t | 1 := {|
  inj := fun _ _ => id
|}.

Class Members (sub sup : Sig) := {
  membership : Member sub sup
}.

#[export] Program Instance is_Member {t u} : Member t u -> Members t u | 2.

#[export] Program Instance sum_Members {l r u} :
  Members l u -> Members r u -> Members (l :+: r) u | 1.
Next Obligation.
  constructor; intros.
  destruct X.
  - now apply H.
  - now apply H0.
Defined.

(* Definition Has eff sig m `{Monad m} : Type := Members eff sig * Algebra sig m. *)

Definition Has (eff sg : Sig) (m : Type -> Type)
  `{M : Monad m} `{U : Members eff sg} `{A : Algebra sg m (H:=M)} := True.

Definition send `{Member eff sg} `{A : Algebra sg m} `(f : eff m a) : m a :=
  alg (Algebra:=A) (H0:=id_Functor) (fun _ x => ltac:(eexact x)) (inj f) tt.

Inductive Throw e (m : Type -> Type) (a : Type) : Type :=
  | Raise : e -> Throw e m a.

Arguments Raise {_ _ _} _.

Inductive Catch e (m : Type -> Type) (a : Type) : Type :=
  | Handle : m a -> (e -> m a) -> Catch e m a.

Arguments Handle {_ _ _} _ _.

Definition Error e := Throw e :+: Catch e.

Definition errorAlg {e} `{Functor ctx} {n a}
  (hdl : Handler ctx n (Either e))
  (s : Error e n a)
  (u : ctx unit) : Either e (ctx a) :=
  match s with
  | L (Raise e)    => Left e
  | R (Handle m h) =>
      either (hdl _ \o (fun x => x <$ u) \o h) pure (hdl _ (m <$ u))
  end.

#[export]
Instance Error_Algebra {e} : Algebra (Error e) (Either e) := {|
  alg := @errorAlg e
|}.

Inductive Reader r (m : Type -> Type) : Type -> Type :=
  | Ask       :                    Reader r m r
  | Local {a} : (r -> r) -> m a -> Reader r m a.

Arguments Ask {_ _}.
Arguments Local {_ _ _} _ _.

Definition readerAlg {r} `{Functor ctx} {n a}
  (hdl : Handler ctx n (fun a => r -> a))
  (s : Reader r n a)
  (u : ctx unit) : r -> ctx a :=
  match s with
  | Ask       => fun x => x <$ u
  | Local f m => hdl _ (m <$ u) \o f
  end.

#[export]
Program Instance Reader_Algebra {r} : Algebra (Reader r) (fun a => r -> a) := {|
  alg := @readerAlg r
|}.

Definition asksT `(f : r -> a) `{Monad m} : ReaderT r m a :=
  fun r => pure (f r).

Definition localT `(f : r -> r) `(x : ReaderT r m a) : ReaderT r m a :=
  fun r => x (f r).

Equations readerTAlg {r sig m} `{Monad m} `{Algebra sig m} `{Functor ctx} {n a}
  (hdl : Handler ctx n (ReaderT r m))
  (s : (Reader r :+: sig) n a)
  (u : ctx unit) : ReaderT r m (ctx a) :=
  readerTAlg hdl (L Ask) u :=
    asksT (fun x => x <$ u);
  readerTAlg hdl (L (Local f mo)) u :=
    localT f (hdl _ (mo <$ u));
  readerTAlg hdl (R other) u :=
    fun r => alg (fun x => (fun f => f r) \o hdl x) other u.

#[export]
Instance ReaderT_Algebra {r sig m} `{Monad m} :
  Algebra sig m -> Algebra (Reader r :+: sig) (ReaderT r m) := fun H => {|
  alg := @readerTAlg r _ _ _ _ H
|}.

Section Reader.

Context `{Member (Reader r) sg}.
Context `{Algebra sg m}.

Definition ask : m r := send Ask.

Definition local (f : r -> r) `(x : m a) : m a :=
  send (Local f x).

End Reader.

(************************************************************************)

Inductive State s (m : Type -> Type) : Type -> Type :=
  | Get :      State s m s
  | Put : s -> State s m unit.

Arguments Get {_ _}.
Arguments Put {_ _} _.

Definition stateAlg {s} `{Functor ctx} {n a}
  (hdl : Handler ctx n (State.State s))
  (sg : State s n a)
  (u : ctx unit) : State.State s (ctx a) :=
  match sg with
  | Get   => fun s => (s <$ u, s)
  | Put m => fun _ => (u, m)
  end.

#[export]
Instance State_Algebra {s} : Algebra (State s) (State.State s) := {|
  alg := @stateAlg s
|}.

Definition getsT `(f : s -> a) `{Monad m} : StateT s m a :=
  fun s => pure (f s, s).

Definition putT `(x : s) `{Monad m} : StateT s m unit :=
  fun _ => pure (tt, x).

Definition thread `{Functor ctx1} `{Functor ctx2}
  `{Algebra sg m} {n a} :
     Handler (ctx1 \o ctx2) n m
  -> sg n a
  -> ctx1 (ctx2 unit)
  -> m (ctx1 (ctx2 a)) :=
  fun hdl s => alg hdl s.

#[local] Remove Hints Compose_Alternative : typeclass_instances.

#[export]
Instance Tuple_Functor {S} : Functor (fun a => (a * S)%type) | 9 := {
  fmap := fun _ _ f p => (f (fst p), snd p)
}.

Equations stateTAlg {s sig m} `{Monad m} `{Algebra sig m} `{Functor ctx} {n a}
  (hdl : Handler ctx n (StateT s m))
  (sg : (State s :+: sig) n a)
  (u : ctx unit) : StateT s m (ctx a) :=
  stateTAlg hdl (L Get) u     := getsT (fun x => x <$ u);
  stateTAlg hdl (L (Put x)) u := u <$ putT x;
  stateTAlg hdl (R other) u   :=
    fun st => thread (ctx1:=fun a => a * s)
                ((fun _ '(f, s') => f s') ~<~ hdl) other (u, st).

#[export]
Instance StateT_Algebra {s sig m} `{Monad m} :
  Algebra sig m -> Algebra (State s :+: sig) (StateT s m) := fun H => {|
  alg := @stateTAlg s _ _ _ _ H
|}.

Section State.

Context `{Member (State s) sg}.
Context `{Algebra sg m}.

Definition get : m s := send Get.

Definition gets `(f : s -> a) : m a := f <$> get.

Definition put : s -> m unit := send \o Put.

Definition modify (f : s -> s) : m unit := get >>= (put \o f).

Definition state `(f : s -> (s * a)) : m a :=
  p <- gets f ;
  let '(s', a) := p in
  a <$ put s'.

End State.

Definition sample
  `{Member (State nat) sg}
  `{Member (Reader bool) sg}
  `{Algebra sg m} : m unit :=
  b <- ask ;
  if b : bool
  then
    n <- get ;
    put (n + 10)%nat
  else
    put 100%nat.

Definition runReader `(env : r) `(x : r -> a) : a := x env.
Definition runReaderT `(env : r) `(x : ReaderT r m a) : m a := x env.

Definition runState `(st : s) `(x : State.State s a) : a * s := x st.
Definition runStateT `(st : s) `(x : StateT s m a) : m (a * s) := x st.

(* This uses the StateT carrier. *)
Definition example1 `{Algebra sg m} : m (unit * nat) :=
  runReaderT true (runStateT 0%nat sample).

(* This uses the State carrier. No final [run] is needed, because in Coq the
  Identity monad is the [id] function, so [run x = x]. *)
Definition example2 : unit * nat :=
  runReader true (runStateT 0%nat sample).

(************************************************************************)

Require Import Hask.Control.Lens.
Require Import Pact.Data.Monoid.

Program Definition focus `(l : Lens' s s')
  `{Member (State s) sg} `{A : Algebra sg m}
  `(f : forall `{Member (State s') sg}, m a) : m a :=
  @f _.
Next Obligation.
  constructor; intros.
  induction X.
  - apply inj.
  - pose (st <- get ;
           modify X0 ;;
           res <- X1 ;
           put st ;;
           pure res).

Program Definition readonly `(l : Lens' s r)
  `{Member (State Foo) sg} `{A : Algebra sg m}
  `(f : forall `{Member (Reader Foo) sg}, m a) : m a :=
  @f _.
Next Obligation.
  constructor; intros.
  apply inj.
  inversion X; subst.
  - exact (Get (m:=m0)).
  - pose (st <- get ;
           modify X0 ;;
           res <- X1 ;
           put st ;;
           pure res).

(*

Definition appendonly `(l : Lens' s w) `{Monoid w} {effs} :
  Eff (Writer w :: effs) ~> Eff (State s :: effs) :=
  reinterpret (fun _ f =>
    let '(a, w) := writerAlg f in
    modify (over l (mappend w)) ;;
    pure a).
*)

Definition overM `(l : Lens s t a b) `{Functor f} : (a -> f b) -> s -> f t := l f _.
Notation "l %%~ f" := (overM l f) (at level 40).

Polymorphic Inductive Foo : Type := mkFoo.
Polymorphic Inductive Bar : Type := mkBar.
Polymorphic Inductive Baz : Type := mkBaz.

Record SomeState : Type := {
  _foo : Foo;
  _bar : Bar;
  _baz : Baz;
}.

Definition foo : Lens' SomeState Foo :=
  fun _ _ f env =>
    f (_foo env) <&> fun g =>
      {| _foo := g
       ; _bar := _bar env
       ; _baz := _baz env |}.

Definition bar : Lens' SomeState Bar :=
  fun _ _ f env =>
    f (_bar env) <&> fun g =>
      {| _foo := _foo env
       ; _bar := g
       ; _baz := _baz env |}.

Definition baz : Lens' SomeState Baz :=
  fun _ _ f env =>
    f (_baz env) <&> fun g =>
      {| _foo := _foo env
       ; _bar := _bar env
       ; _baz := g |}.

Declare Instance Baz_Monoid : Monoid Baz.

Definition sample3 `{Member (Reader Foo) sg} `{Algebra sg m} : m unit :=
  pure tt.

Definition sample4 `{Member (State Foo) sg} `{A : Algebra sg m} : m unit :=
  @sample3 sg _ m _ A.

Definition example3 : Eff [State SomeState] unit :=
  subsume _
    (focus baz _
        (appendonly (fun _ _ => id) _
           (subsume _
              (focus bar _
                 (subsume _
                    (focus foo _
                       (readonly (fun _ _ => id) _ sample))))))).
