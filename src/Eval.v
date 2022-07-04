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

Reserved Notation " t '--->' t' " (at level 40).

(************************************************************************
 * Small-step operational semantics
 *)

Inductive Step : ∀ {τ}, Exp [] τ → Exp [] τ → Prop :=
  | ST_Seq τ τ' (e1 : Exp [] τ') (e2 : Exp [] τ) :
    Seq e1 e2 ---> e2

  | ST_ListElem τ (pre post : list (Exp [] τ)) x x' :
    Forall ValueP pre →
    x ---> x' →
    List (pre ++ x :: post) ---> List (pre ++ x' :: post)

  | ST_Let τ ty (x : Exp [] ty) (body : Exp [ty] τ) :
    Let x body ---> APP (LAM body) x

  | ST_AppAbs dom cod (e : Exp [dom] cod) (v : Exp [] dom) :
    ValueP v ->
    APP (LAM e) v ---> STmExp {| v |} e

  | ST_App1 dom cod (e1 : Exp [] (dom ⟶ cod)) e1' (e2 : Exp [] dom) :
    e1 ---> e1' →
    APP e1 e2 ---> APP e1' e2

  | ST_App2 dom cod (v1 : Exp [] (dom ⟶ cod)) (e2 : Exp [] dom) e2' :
    ValueP v1 →
    e2 ---> e2' →
    APP v1 e2 ---> APP v1 e2'

  where " t '--->' t' " := (Step t t').

Ltac reduce :=
  repeat lazymatch goal with
         | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
             apply inj_pair2 in H; subst
         | [ H : _ ∧ _ |- _ ] => destruct H
         | [ H : _ * _ |- _ ] => destruct H
         | [ H : ∃ _, _ |- _ ] => destruct H
         end.

Ltac inv H := inversion H; subst; clear H; reduce.

Theorem Step_sound τ (e : Exp [] τ) v :
  e ---> v → SemExp e = SemExp v.
Proof.
  intros.
  induction H; simpl; auto;
  extensionality E;
  destruct E.
  - subst.
    rewrite !map_app; f_equal.
    rewrite !map_cons; f_equal.
    now rewrite !IHStep.
  - now rewrite <- SemSubComm.
  - now rewrite IHStep.
  - now rewrite IHStep.
Qed.

Theorem Step_List_length τ (l1 l2 : list (Exp [] τ)) :
  List l1 ---> List l2 → length l1 = length l2.
Proof.
  intros.
  inv H.
  now rewrite !app_length.
Qed.

Theorem Step_List_inv {τ pre} {x x' : Exp [] τ} {post l} :
  List (pre ++ x :: post) ---> l →
  x ---> x' →
  l = List (pre ++ x' :: post).
Proof.
  intros.
  inv H.
Admitted.
