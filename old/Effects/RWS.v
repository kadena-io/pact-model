Require Import
  Coq.Lists.List
  Pact.Data.Monoid
  Pact.Data.IList
  Hask.Control.Monad.

Require Export
  Eff.

Require Export Equations.Prop.DepElim.
From Equations Require Export Equations.

Import ListNotations.

Generalizable All Variables.
Set Primitive Projections.

(************************************************************************)

Polymorphic Inductive Reader (r : Type) : Type -> Type :=
  | Ask : Reader r r.

Arguments Ask {r}.

Fixpoint runReader' `(x : e) `(f : Freer (Reader e) a) : a :=
  match f with
  | Pure v => v
  | Impure Ask k => runReader' x (k x)
  end.

Definition ask {r effs} `{Member (Reader r) effs} : Eff effs r :=
  send Ask.

Definition asks {r effs a} `{Member (Reader r) effs} (f : r -> a) : Eff effs a :=
  f <$> ask.

Definition readerAlg `(x : r) `(f : Reader r a) : a :=
  match f with Ask => x end.

Definition local {r effs a} `{Member (Reader r) effs} (f : r -> r) (m : Eff effs a) :
  Eff effs a :=
  r <- asks f ;
  interpose (fun _ => Pure \o readerAlg r) _ m.

Definition runReader `(x : e) {r} : Eff (Reader e :: r) ~> Eff r :=
  interpret (fun _ => Pure \o readerAlg x).

(************************************************************************)

Inductive Writer (w : Type) : Type -> Type :=
  | Tell : w -> Writer w unit.

Arguments Tell {w} _.

Fixpoint runWriter' `{Monoid w} `(f : Freer (Writer w) a) : a * w :=
  match f with
  | Pure v => (v, mempty)
  | Impure (Tell x) k =>
      let '(v, l) := runWriter' (k tt) in (v, x ⨂ l)
  end.

Definition tell {w effs} `{Member (Writer w) effs} : w -> Eff effs unit :=
  send \o Tell.

Definition writerAlg `{Monoid w} `(f : Writer w a) : a * w :=
  match f with Tell x => (tt, x) end.

Definition second {A B C} (f : B -> C) (p : A * B) : A * C :=
  (fst p, f (snd p)).

Definition runWriter {w effs a} `{Monoid w} :
  Eff (Writer w :: effs) a -> Eff effs (a * w) :=
  handleRelay (fun x => Pure (x, mempty))
    (fun _ w k => let '(a, w') := writerAlg w in second (mappend w') <$> k a).

(************************************************************************)

Inductive State (s : Type) : Type -> Type :=
  | Get : State s s
  | Put : s -> State s unit.

Arguments Get {s}.
Arguments Put {s} _.

Fixpoint runState' `(f : Freer (State s) a) (st : s) : (a * s) :=
  match f with
  | Pure v => (v, st)
  | Impure Get k =>
      let '(v, s') := runState' (k st) st in (v, s')
  | Impure (Put s) k =>
      let '(v, s') := runState' (k tt) s in (v, s')
  end.

Definition get {s effs} `{Member (State s) effs} : Eff effs s :=
  send Get.

Definition put {s effs} `{Member (State s) effs} : s -> Eff effs unit :=
  send \o Put.

Definition modify {s effs} `{Member (State s) effs} (f : s -> s) : Eff effs unit :=
  fmap f get >>= put.

Definition gets {s a effs} `{Member (State s) effs} (f : s -> a) : Eff effs a :=
  f <$> get.

Definition stateAlg {s : Type} `(f : State s a) (st : s) : a * s :=
  match f with
  | Get   => (st, st)
  | Put s => (tt, s)
  end.

Definition runState {s r a} (st : s) : Eff (State s :: r) a -> Eff r (a * s) :=
  handleRelayS st (fun s x => Pure (x, s))
    (fun _ s x k => let '(a, s') := stateAlg x s in k s' a).

(************************************************************************)

Require Import Hask.Control.Lens.

Definition readonly {s effs} :
  Eff (Reader s :: effs) ~> Eff (State s :: effs) :=
  reinterpret (fun _ f =>
    s <- get ;
    pure (readerAlg s f)).

Definition focus `(l : Lens' s s') {effs} :
  Eff (State s' :: effs) ~> Eff (State s :: effs) :=
  reinterpret (fun _ f =>
    s' <- get ;
    let '(a, t) := stateAlg f (view l s') in
    put (set l t s') ;;
    pure a).

Definition appendonly `{Monoid s} {effs} :
  Eff (Writer s :: effs) ~> Eff (State s :: effs) :=
  reinterpret (fun _ f =>
    let '(a, w) := writerAlg f in
    a <$ modify (mappend w)).

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

#[local]
Declare Instance Baz_Monoid : Monoid Baz.

Definition sample {effs} :
  Eff (Reader Foo :: State Bar :: Writer Baz :: effs) unit :=
  Pure tt.

Definition example : Eff [State SomeState] unit :=
  subsume _
    (focus baz _
        (appendonly _
           (subsume _
              (focus bar _
                 (subsume _
                    (focus foo _
                       (readonly _ sample))))))).
