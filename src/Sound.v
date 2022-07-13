Require Import
  Lib
  Ltac
  Ty
  Exp
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

Theorem Step_sound {Γ τ} (e : Exp Γ τ) v :
  e ---> v → SemExp e = SemExp v.
Proof.
  intros.
  induction H; simpl; auto;
  extensionality se;
  rewrite ?IHStep, ?sum_id; auto.
  (* - destruct (SemExp_ValueP _ se X) as [? H]. *)
  (*   simpl; rewrite H; simpl. *)
  (*   now rewrite sum_id. *)
  (* - now erewrite <- Reduce_sound. *)
  (* - destruct (SemExp_ValueP _ se X) as [? H]. *)
  (*   now simpl; rewrite H. *)
  (* - destruct (SemExp_ValueP _ se X) as [? H1]. *)
  (*   destruct (SemExp_ValueP _ se X0) as [? H2]. *)
  (*   now simpl; rewrite H1, H2. *)
  (* - destruct (SemExp_ValueP _ se X) as [? H1]. *)
  (*   destruct (SemExp_ValueP _ se X0) as [? H2]. *)
  (*   now simpl; rewrite H1, H2. *)
  (* - destruct (SemExp_ValueP _ se X) as [? H]. *)
  (*   now simpl; rewrite H. *)
  (* - destruct (SemExp_ValueP _ se X) as [? H1]. *)
  (*   destruct (SemExp_ValueP _ se X0) as [? H2]. *)
  (*   now simpl; rewrite H1, H2. *)
  (* - destruct (SemExp_ValueP _ se X) as [? H1]. *)
  (*   destruct (SemExp_ValueP _ se X0) as [? H2]. *)
  (*   now simpl; rewrite H1, H2. *)
  (* - destruct (SemExp_ValueP _ se X) as [? H1]. *)
  (*   destruct (SemExp_ValueP _ se X0) as [? H2]. *)
  (*   now simpl; rewrite H1, H2. *)
  (* - now apply CallHost_sound. *)
  (* - destruct (SemExp_ValueP _ se X) as [? H1]. *)
  (*   rewrite H1; simpl. *)
  (*   rewrite sum_id. *)
  (*   now erewrite <- SemExp_SubExp. *)
  - admit.
    (* rewrite <- SemExp_SubSem. *)
    (* f_equal; simpl. *)
    (* simp SubSem. *)
    (* now rewrite SubSem_idSub. *)
  (* - destruct (SemExp_ValueP _ se X) as [? H1]. *)
  (*   now rewrite H1. *)
Abort.

(*
Lemma If_loop_true {Γ τ} b {x : Exp Γ τ} {y : Exp Γ τ} :
  ¬ (If b x y = x).
Proof.
  induction x; intro; inv H.
  now eapply IHx2; eauto.
Qed.

Lemma If_loop_false {Γ τ} b {x : Exp Γ τ} {y : Exp Γ τ} :
  ¬ (If b x y = y).
Proof.
  induction y; intro; inv H.
  now eapply IHy3; eauto.
Qed.

Lemma Seq_loop {Γ τ ty} {x : Exp Γ ty} {y : Exp Γ τ} :
  ¬ (Seq x y = y).
Proof.
  induction y; intro; inv H.
  now eapply IHy2; eauto.
Qed.
*)

End Sound.
