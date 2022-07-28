Require Import
  Pact.Lib
  Pact.Value
  Pact.Data.RWSE.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

(*************************************************************************
 * Capability values
 *)

Record CapSig : Set := {
  paramTy : ValueTy;
  valueTy : ValueTy;
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapSig.

(* jww (2022-07-21): Capabilities need to match also on the module name *)
Inductive Cap (s : CapSig) : Type :=
  | Token (name : string) :
    reflectTy (paramTy s) → reflectTy (valueTy s) → Cap s.

Derive NoConfusion NoConfusionHom Subterm for Cap.

#[export]
Program Instance Cap_EqDec {s} : EqDec (Cap s).
Next Obligation.
  destruct x as [n1 p1 v1], y as [n2 p2 v2].
  destruct (string_EqDec n1 n2); [subst|sauto].
  destruct (reflectTy_EqDec p1 p2); [subst|sauto].
  destruct (reflectTy_EqDec v1 v2); sauto.
Defined.

Arguments Token {s} name arg val.

Definition nameOf `(c : Cap s) : string :=
  match c with Token n _ _ => n end.

Definition paramOf `(c : Cap s) : reflectTy (paramTy s) :=
  match c with Token _ p _ => p end.

Definition valueOf `(c : Cap s) : reflectTy (valueTy s) :=
  match c with Token _ _ v => v end.

Inductive ACap : Type :=
  | AToken (s : CapSig) : Cap s → ACap.

Derive NoConfusion NoConfusionHom Subterm for ACap.

#[export]
Program Instance ACap_EqDec : EqDec ACap.
Next Obligation.
  destruct x, y.
  destruct (CapSig_EqDec s s0); [subst|right; congruence].
  apply dec_eq_f1.
  - apply Cap_EqDec.
  - now intros ? ? H; inv H.
Defined.

Inductive CapError : Set :=
  | CapErr_CapabilityNotAvailable
  | CapErr_NoResourceAvailable
  | CapErr_CannotInstallInDefcap
  | CapErr_CannotWithInDefcap
  | CapErr_CannotWithOutsideDefcapModule
  | CapErr_CannotComposeOutsideDefcap
  | CapErr_CannotComposeOutsideDefcapModule.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapError.
