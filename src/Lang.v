Require Export
  Hask.Control.Monad
  Hask.Control.Lens
  Pact.Data.Monoid
  Pact.Data.RWSE
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

#[export]
Program Instance PactLog_Semigroup : Semigroup PactLog := {|
  mappend := λ '(MkLog _) '(MkLog _), MkLog tt
|}.

#[export]
Program Instance PactLog_SemigroupLaws : SemigroupLaws PactLog.

#[export]
Program Instance PactLog_Monoid : Monoid PactLog := {|
  mempty := MkLog tt
|}.

#[export]
Program Instance PactLog_MonoidLaws : MonoidLaws PactLog.
Next Obligation. sauto. Qed.
Next Obligation. sauto. Qed.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactLog.

Definition newPactLog : PactLog :=
  MkLog tt.

Definition PactM : Type → Type := @RWSE PactEnv PactLog PactState Err.

#[export] Instance PactM_Functor     : Functor PactM     := RWSE_Functor.
#[export] Instance PactM_Applicative : Applicative PactM := RWSE_Applicative.
#[export] Instance PactM_Monad       : Monad PactM       := RWSE_Monad.

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
  unfold RWSE_join.
  rwse.
  sauto lq: on.
Qed.

Lemma curryM_uncurryM `(f : a → PactM (b → PactM c)) :
  curryM (uncurryM f) = f.
Proof.
Abort.
