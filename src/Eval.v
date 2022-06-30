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

Section Eval.

Inductive Eval : ∀ {τ}, Exp [] τ → Exp [] τ → Prop :=
  | EvLam t1 t2 (e : Exp [t1] t2) :
    Eval (LAM e) (LAM e)

  | EvApp t1 t2 e v w (e1 : Exp [] (t1 ⟶ t2)) e2 :
    Eval e1 (LAM e) →
    Eval e2 w →
    Eval (STmExp {| w |} e) v →
    Eval (APP e1 e2) v.

Theorem soundness τ (e : Exp [] τ) v :
  Eval e v → SemExp e = SemExp v.
Proof.
  intros.
  induction H; simpl; auto.
  - extensionality E.
    destruct E.
    rewrite IHEval1.
    rewrite IHEval2.
    rewrite <- IHEval3.
    simpl.
    rewrite <- SemSubComm.
    + simpl.
      unfold hdSub.
      now rewrite consSub_equation_1.
Qed.

End Eval.
