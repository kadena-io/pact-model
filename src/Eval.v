Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List
  Ty
  Exp
  Sub
  Sem
  Lang.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Section Eval.

Context {t : Type}.
Context {x : Env t → Ty t → Type}.
Context `{Lang t x}.

Inductive Eval : ∀ {τ}, Exp t x [] τ → Exp t x [] τ → Prop :=
  | EvTerm t1 (e1 : x [] t1) (e2 : Exp t x [] t1) :
    eval e1 e2 →
    Eval (TERM e1) e2

  | EvLam t1 t2 (e : Exp t x [t1] t2) :
    Eval (LAM e) (LAM e)

  | EvApp t1 t2 e v w (e1 : Exp t x [] (t1 ⟶ t2)) e2 :
    Eval e1 (LAM e) →
    Eval e2 w →
    Eval (STmExp (ren:=@ren _ _ _) (sub:=@sub _ _ _) {| w |} e) v →
    Eval (APP e1 e2) v.

Theorem soundness τ (e : Exp t x [] τ) v :
  Eval e v → SemExp SemT (@SemX _ _ _) e = SemExp SemT (@SemX _ _ _) v.
Proof.
  intros.
  induction H0; simpl; auto.
  - now apply (eval_sound _ e1 e2).
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
    + now intros; apply SemX_SemRen.
    + now intros; apply SemX_SemSub.
Qed.

End Eval.
