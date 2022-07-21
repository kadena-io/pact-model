Require Export
  Lib
  Value
  RWSE.

(* Set Universe Polymorphism. *)

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(*************************************************************************
 * Capability values
 *)

Record CapSig : Set := {
  paramTy : ValueTy;
  valueTy : ValueTy;
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapSig.

Inductive Cap (s : CapSig) : Type :=
  | Token (name : string) :
    reflectTy (paramTy s) → reflectTy (valueTy s) → Cap s.

Derive NoConfusion NoConfusionHom Subterm for Cap.

#[export]
Program Instance Cap_EqDec {s} : EqDec (Cap s).
Next Obligation.
  destruct x, y.
  destruct (string_EqDec name name0); subst;
  [|right; intro; congruence].
  destruct (reflectTy_EqDec r r1); subst.
  - destruct (reflectTy_EqDec r0 r2); subst.
    + now left.
    + right; intro; congruence.
  - right; intro; congruence.
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
  destruct (CapSig_EqDec s s0); subst; [|right; congruence].
  apply dec_eq_f1.
  - apply Cap_EqDec.
  - intros.
    now inv H.
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
