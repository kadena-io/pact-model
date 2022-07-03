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

Reserved Notation " t '--->' t' " (at level 40).

(************************************************************************
 * Small-step operational semantics
 *)

Inductive Step : ∀ {τ}, Exp [] τ → Exp [] τ → Prop :=
  | ST_Seq τ τ' (e1 : Exp [] τ') (e2 : Exp [] τ) :
    Seq e1 e2 ---> e2

  | ST_ListElem τ (l : list (Exp [] τ)) l' pre post x x' :
    l  = pre ++ x :: post →
    l' = pre ++ x' :: post →
    x ---> x' →
    List l ---> List l'

  | ST_Let τ ty (x : Exp [] ty) (body : Exp [ty] τ) :
    Let x body ---> APP (LAM body) x

  | ST_AppAbs dom cod (e : Exp [dom] cod) (v : Exp [] dom) :
    ValueP [] dom v ->
    APP (LAM e) v ---> STmExp {| v |} e

  | ST_App1 dom cod (e1 : Exp [] (dom ⟶ cod)) e1' (e2 : Exp [] dom) :
    e1 ---> e1' →
    APP e1 e2 ---> APP e1' e2

  | ST_App dom cod (e1 : Exp [] (dom ⟶ cod)) (e2 : Exp [] dom) e2' :
    e2 ---> e2' →
    APP e1 e2 ---> APP e1 e2'

  where " t '--->' t' " := (Step t t').

Theorem soundness τ (e : Exp [] τ) v :
  Step e v → SemExp e = SemExp v.
Proof.
  intros.
  induction H; simpl; auto;
  extensionality E;
  destruct E.
  - subst.
    rewrite !map_app.
    f_equal.
    rewrite !map_cons.
    f_equal.
    now rewrite IHStep.
  - now rewrite <- SemSubComm.
  - now rewrite IHStep.
  - now rewrite IHStep.
Qed.

End Eval.
