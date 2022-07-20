Require Export
  Hask.Control.Monad
  Lib
  Exp
  SemTy
  Value
  RWSE.

(* Set Universe Polymorphism. *)

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Pact.

Inductive CapError : Set :=
  | CapErr_CapabilityNotAvailable
  | CapErr_NoResourceAvailable
  | CapErr_CannotInstallDuringWith.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapError.

Inductive Err : Set :=
  | Err_Exp : Exp.Err → Err
  | Err_Capability {s} : Cap s → CapError → Err.

Derive NoConfusion NoConfusionHom Subterm EqDec for Err.

Inductive EvalContext : Set :=
  | RegularEvaluation
  | InWithCapability.

Derive NoConfusion NoConfusionHom Subterm EqDec for EvalContext.

Record PactEnv : Set := {
  (* We cannot refer to capability tokens by their type here, because
     capability predicates execute in a state monad that reference this
     record type. *)
  granted : list ACap;
  context : list EvalContext;
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactEnv.

Record PactState : Set := {
  (* We cannot refer to capability tokens by their type here, because
     capability predicates execute in a state monad that reference this
     record type. *)
  resources : list ACap;
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactState.

Record PactLog : Set := {}.

Derive NoConfusion NoConfusionHom Subterm EqDec for PactLog.

Definition PactM : Type → Type := @RWSE PactEnv PactState PactLog Err.

#[export] Instance PactM_Functor     : Functor PactM     := RWSE_Functor.
#[export] Instance PactM_Applicative : Applicative PactM := RWSE_Applicative.
#[export] Instance PactM_Monad       : Monad PactM       := RWSE_Monad.

End Pact.
