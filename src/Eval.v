Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List
  Coq.Logic.Classical
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
    l  = pre ++ x  :: post →
    l' = pre ++ x' :: post →
    x ---> x' →
    List l ---> List l'

  | ST_Let τ ty (x : Exp [] ty) (body : Exp [ty] τ) :
    Let x body ---> APP (LAM body) x

  | ST_AppAbs dom cod (e : Exp [dom] cod) (v : Exp [] dom) :
    ValueP v ->
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

Definition normal_form {X : Type}
           (R : relation X) (t : X) : Prop :=
  ¬ ∃ t', R t t'.

Lemma app_cons A (y : A) (xs ys : list A) :
  xs ++ y :: ys = (xs ++ [y]) ++ ys.
Proof.
  induction xs; simpl; auto.
  now rewrite IHxs.
Qed.

Lemma value_is_nf {τ} (v : Exp [] τ) :
  ValueP v → normal_form Step v.
Proof.
  intros.
  induction H; intro.
  - destruct H.
    now inversion H.
  - destruct H0.
    generalize dependent x.
    induction H; intros.
    + inversion H0.
      apply inj_pair2 in H1, H2; subst.
      apply app_eq_nil in H1.
      destruct H1.
      now inversion H1.
    + inversion H1.
      apply inj_pair2 in H3, H4; subst.
      destruct pre.
      * simpl in *.
        inversion H3; subst.
        admit.
      * admit.
  - destruct H.
    now inversion H.
Abort.

Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e ∨ ∃ e', e ---> e'.
Proof.
  dependent elimination e.
  - now left; constructor.
  - right.
    eexists e0.
    now constructor.
  - induction l0; simpl.
    + now left; constructor.
    + destruct IHl0.
      * destruct (classic (ValueP a)).
        ** left.
           constructor.
           *** constructor; auto.
               inversion H; subst.
               apply inj_pair2 in H2.
               now subst.
        ** right.
           admit.
      * destruct H.
        inversion H; subst.
        apply inj_pair2 in H1; subst.
        apply inj_pair2 in H2; subst.
        right.
        exists (List (a :: pre ++ x' :: post)).
        rewrite !app_comm_cons.
        now eapply ST_ListElem; eauto.
Abort.

Definition deterministic {X : Type} (R : relation X) :=
  ∀ x y1 y2 : X, R x y1 → R x y2 → y1 = y2.

Theorem step_deterministic τ :
  deterministic (@Step τ).
Abort.

Lemma nf_is_value τ (v : Exp [] τ) :
  normal_form Step v → ValueP v.
Abort.

Corollary nf_same_as_value τ (v : Exp [] τ) :
  normal_form Step v ↔ ValueP v.
Abort.

End Eval.
