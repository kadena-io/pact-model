Require Export
  Hask.Control.Monad
  Hask.Control.Lens
  Pact.RWSE
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.SemTy
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
  | Err_Exp : Exp.Err → Err
  | Err_Capability {s} : Cap s → CapError → Err
  | Err_CannotReify : Ty → Err.

Derive NoConfusion NoConfusionHom Subterm EqDec for Err.

Inductive EvalContext : Set :=
  | RegularEvaluation
  | InWithCapability
  | InModule : string → EvalContext.

Derive NoConfusion NoConfusionHom Subterm EqDec for EvalContext.

Record PactEnv : Type := {
  (* We cannot refer to capability tokens by their type here, because
     capability predicates execute in a state monad that reference this
     record type. *)
  _granted : list ACap;
  _context : list EvalContext;
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactEnv.

Definition newPactEnv : PactEnv :=
  {| _granted := []
   ; _context := []
   |}.

Definition granted : Lens' PactEnv (list ACap) :=
  λ _ _ f env,
    f (_granted env) <&> λ g,
      {| _granted := g
       ; _context := _context env |}.

Definition context : Lens' PactEnv (list EvalContext) :=
  λ _ _ f env,
    f (_context env) <&> λ c,
      {| _granted := _granted env
       ; _context := c |}.

Record PactState : Type := {
  (* We cannot refer to capability tokens by their type here, because
     capability predicates execute in a state monad that reference this
     record type. *)
  _resources  : list ACap;
  _to_compose : list ACap;
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactState.

Definition newPactState : PactState :=
  {| _resources  := []
   ; _to_compose := []
   |}.

Definition resources : Lens' PactState (list ACap) :=
  λ _ _ f env,
    f (_resources env) <&> λ r,
      {| _resources  := r
       ; _to_compose := _to_compose env |}.

Definition to_compose : Lens' PactState (list ACap) :=
  λ _ _ f env,
    f (_to_compose env) <&> λ tc,
      {| _resources  := _resources env
       ; _to_compose := tc |}.

Record PactLog : Set := MkLog {
  entry : unit
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactLog.

Definition newPactLog : PactLog :=
  MkLog tt.

Definition PactM : Type → Type := @RWSE PactEnv PactState PactLog Err.

#[export] Instance PactM_Functor     : Functor PactM     := RWSE_Functor.
#[export] Instance PactM_Applicative : Applicative PactM := RWSE_Applicative.
#[export] Instance PactM_Monad       : Monad PactM       := RWSE_Monad.

Definition uncurryM `(f : a → PactM (b → PactM c)) : (a * b) → PactM c :=
  λ '(a, b), f' <- f a ; f' b.

(* This is not a valid definition. *)
Definition curryM `(f : (a * b) → PactM c) : a → PactM (b → PactM c) :=
  pure ∘ curry f.

Lemma uncurryM_curryM `(f : (a * b) → PactM c) :
  uncurryM (curryM f) = f.
Proof.
  extensionality p.
  destruct p.
  unfold uncurryM, curryM.
  simpl.
  unfold RWSE_join.
  extensionality r.
  extensionality s.
  extensionality w.
  f_equal.
  destruct w.
  reflexivity.
Qed.

Lemma curryM_uncurryM `(f : a → PactM (b → PactM c)) :
  curryM (uncurryM f) = f.
Proof.
  extensionality x.
  unfold uncurryM, curryM.
  simpl.
  unfold RWSE_join.
  extensionality r.
  extensionality s.
  extensionality w.
  unfold Basics.compose.
  unfold curry.
  unfold Tuple.first.
  unfold Either.Either_map.
Abort.
