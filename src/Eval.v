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

Context {t : Type}.
Context {x : Ty t → Type}.
Context `{Sem t x}.

Inductive Eval : ∀ {τ}, Exp t x [] τ → Exp t x [] τ → Prop :=
  | EvAbs t1 t2 (e : Exp t x [t1] t2) :
    Eval (LAM e) (LAM e)

  | EvApp t1 t2 e v w (e1 : Exp t x [] (t1 ⟶ t2)) e2 :
    Eval e1 (LAM e) → Eval e2 w → Eval (STmExp {| w |} e) v →
    Eval (APP e1 e2) v.

Theorem Soundness τ (e : Exp t x [] τ) v :
  Eval e v → SemExp SemT SemX e = SemExp SemT SemX v.
Proof.
  intros.
  induction H0; simpl; auto.
  extensionality E.
  destruct E.
  rewrite IHEval1.
  rewrite IHEval2.
  rewrite <- IHEval3.
  simpl.
  rewrite <- SemSubComm.
  - simpl.
    unfold hdSub.
    now rewrite consSub_equation_1.
  - now apply SemX_SemRen.
  - now apply SemX_SemSub.
Qed.

End Eval.
