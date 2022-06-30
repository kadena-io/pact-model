Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List
  Ty
  Exp
  Sub
  Sem.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Inductive Ev : ∀ {τ}, Exp [] τ → Exp [] τ → Prop :=
  | EvAbs t1 t2 (e : Exp [t1] t2) :
    Ev (LAM e) (LAM e)

  | EvApp t1 t2 e v w (e1 : Exp [] (t1 ⟶ t2)) e2 :
    Ev e1 (LAM e) → Ev e2 w → Ev (STmExp {| w |} e) v →
    Ev (APP e1 e2) v.

Theorem Soundness τ (e : Exp [] τ) v :
  Ev e v → SemExp e = SemExp v.
Proof.
  intros.
  induction H; simpl; auto.
  extensionality se.
  destruct se.
  rewrite IHEv1.
  rewrite IHEv2.
  rewrite <- IHEv3.
  simpl.
  rewrite <- SemSubComm.
  simpl.
  unfold hdSub.
  rewrite consSub_equation_1.
  reflexivity.
Qed.
