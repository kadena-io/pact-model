Require Import
  Lib
  Ltac
  Ty
  Exp
  Log
  Sub
  Sem
  Step
  Lang.

From Equations Require Import Equations.
Set Equations With UIP.

Section Sound.

Generalizable All Variables.

Import ListNotations.

Context {A : Type}.
Context `{S : HostLang A}.

Definition denoted {Γ τ} (e e' : Exp Γ τ) :=
  e ---> e' ∧ SemExp e = SemExp e'.

Definition Sound {Γ τ} := ExpR (Γ:=Γ) (τ:=τ) (@denoted Γ).

Definition Sound_Sub {Γ Γ'} : Sub Γ' Γ → Prop := SubR (@denoted Γ').
Arguments Sound_Sub {Γ Γ'} /.

Theorem Step_sound {Γ Γ' τ} (env : Sub Γ' Γ) {e e' : Exp Γ τ} :
  Sound_Sub env →
  e ---> e' →
  Sound (SubExp env e) (SubExp env e').
Proof.
  generalize dependent env.
  induction e; intros; simpl; try solve [ inv H0 ].
  dependent induction H0.
  simpl.
Admitted.

Theorem Exp_sound {τ} (e e' : Exp [] τ) : e ---> e' → Sound e e'.
Proof.
  intros.
  replace e with (SubExp (Γ:=[]) NoSub e).
  - replace e' with (SubExp (Γ:=[]) NoSub e').
    + apply Step_sound; auto.
      now constructor.
    + rewrite NoSub_idSub.
      now rewrite SubExp_idSub.
  - rewrite NoSub_idSub.
    now rewrite SubExp_idSub.
Qed.

Theorem soundness {τ} {e e' : Exp [] τ} :
  e ---> e' → SemExp e = SemExp e'.
Proof.
  intros.
  pose proof (Exp_sound e e') as H1.
  apply (ExpR_R (@denoted [])).
  now apply H1.
Qed.

(*
    (* rewrite <- SemExp_SubSem. *)
    (* f_equal; simpl. *)
    (* simp SubSem. *)
    (* now rewrite SubSem_idSub. *)
  (* - destruct (SemExp_ValueP _ se X) as [? H1]. *)
  (*   now rewrite H1. *)
*)

End Sound.
