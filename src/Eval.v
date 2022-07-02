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
  | EvConstant τ (c : Literal τ) :
    Eval (Constant c) (Constant c)
  | EvSeq τ τ' (e1 : Exp [] τ') (e2 : Exp [] τ) v :
    Eval e2 v → Eval (Seq e1 e2) v
  | EvNil τ :
    Eval (@Nil _ τ) Nil
  | EvCons τ (x : Exp [] τ) (xs : Exp [] (TyList τ)) :
    Eval (Cons x xs) (Cons x xs)
  | EvLet τ ty (x : Exp [] ty) w (body : Exp [ty] τ) v :
    Eval x w →
    Eval (STmExp {| w |} body) v →
    Eval (Let x body) v

  | EvLam dom cod (e : Exp [dom] cod) :
    Eval (LAM e) (LAM e)
  | EvApp dom cod e v w (e1 : Exp [] (dom ⟶ cod)) (e2 : Exp [] dom) :
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
    rewrite <- IHEval2.
    rewrite <- SemSubComm.
    simpl.
    unfold hdSub.
    now rewrite consSub_equation_1.
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
