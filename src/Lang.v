Require Import
  Hask.Control.Monad
  Hask.Control.Monad.Trans.State
  Hask.Control.Lens
  Pact.Data.Monoid
  Pact.Data.Either
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Value
  Pact.Lang.CapabilityType.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Inductive Err : Type :=
  | Err_Expr
  | Err_CarOfNil
  | Err_CdrOfNil
  | Err_Capability {s} : Cap s → CapError → Err
  | Err_CannotReify : Ty → Err.

Derive NoConfusion NoConfusionHom Subterm EqDec for Err.

Inductive EvalContext : Set :=
  | RegularEvaluation
  | InWithCapability
  | InModule : string → EvalContext.

Derive NoConfusion NoConfusionHom Subterm EqDec for EvalContext.

Record PactState : Type := {
  (* Read-only part of the state. *)
  _granted : list ACap;
  _context : list EvalContext;

  (* We cannot refer to capability tokens by their type here, because
     capability predicates execute in a state monad that reference this
     record type. *)
  _resources  : list ACap;
  _to_compose : list ACap;
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactState.

Definition newPactState : PactState :=
  {| _granted    := []
   ; _context    := []
   ; _resources  := []
   ; _to_compose := []
   |}.

Definition granted : Lens' PactState (list ACap) :=
  λ _ _ f env,
    f (_granted env) <&> λ g,
      {| _granted    := g
       ; _context    := _context env
       ; _resources  := _resources env
       ; _to_compose := _to_compose env
       |}.

Definition context : Lens' PactState (list EvalContext) :=
  λ _ _ f env,
    f (_context env) <&> λ c,
      {| _granted    := _granted env
       ; _context    := c
       ; _resources  := _resources env
       ; _to_compose := _to_compose env
       |}.

Definition resources : Lens' PactState (list ACap) :=
  λ _ _ f env,
    f (_resources env) <&> λ r,
      {| _granted    := _granted env
       ; _context    := _context env
       ; _resources  := r
       ; _to_compose := _to_compose env |}.

Definition to_compose : Lens' PactState (list ACap) :=
  λ _ _ f env,
    f (_to_compose env) <&> λ tc,
      {| _granted    := _granted env
       ; _context    := _context env
       ; _resources  := _resources env
       ; _to_compose := tc |}.

Definition PactM : Type → Type := @StateT PactState (Either Err).

#[export] Instance PactM_Functor     : Functor PactM     := StateT_Functor.
#[export] Instance PactM_Applicative : Applicative PactM := StateT_Applicative.
#[export] Instance PactM_Monad       : Monad PactM       := StateT_Monad.

Definition throw {a : Type} (err : Err) : PactM a := λ _, inl err.

Definition localize `(l : Lens' PactState s) (f : s → s)
  `(x : PactM a) : PactM a :=
  s <- getsT (view l) ;
  modifyT (set l (f s)) ;;
  res <- x ;
  modifyT (set l s) ;;
  pure res.

Definition exchange `(l : Lens' PactState s) (st : s) : PactM s :=
  s <- getsT (view l) ;
  modifyT (set l st) ;;
  pure s.

Definition uncurryM `(f : a → PactM (b → PactM c)) : (a * b) → PactM c :=
  λ '(a, b), f' <- f a ; f' b.

(* This is not a valid definition. *)
Definition curryM `(f : (a * b) → PactM c) : a → PactM (b → PactM c) :=
  pure \o curry f.

Lemma uncurryM_curryM `(f : (a * b) → PactM c) :
  uncurryM (curryM f) = f.
Proof.
  extensionality p.
  destruct p; simpl.
  unfold StateT_join, Ltac.comp, Tuple.curry, Prelude.apply.
  extensionality x.
  sauto lq: on.
Qed.

Lemma curryM_uncurryM `(f : a → PactM (b → PactM c)) :
  curryM (uncurryM f) = f.
Proof.
  unfold curryM, uncurryM.
  extensionality p; simpl.
  unfold StateT_join, Ltac.comp, Tuple.curry, Prelude.apply.
  extensionality x.
  simpl.
  unfold Either_join, Either_map, curry, Tuple.first.
Abort.

Ltac unravel :=
  repeat (cbv [
    Datatypes.id
    Either.Either_map
    Lens.over
    Lens.view
    Lens.set
    StateT_join
    Either_join
    Either_map
    Tuple.first
    Tuple.curry
    granted
    localize
    Prelude.apply
    exchange
    getT
    getsT
    modifyT
    putT
    stepdownl'
    Ltac.comp
  ] in *; simpl in * ).
