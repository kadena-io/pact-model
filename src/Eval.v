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

  | ST_IfTrue τ (t e : Exp [] τ) :
    If ETrue t e ---> t
  | ST_IfFalse τ (t e : Exp [] τ) :
    If EFalse t e ---> e
  | ST_If b b' τ (t e : Exp [] τ) :
    b ---> b' →
    If b t e ---> If b' t e

  | ST_Pair1 τ1 τ2 (x x' : Exp [] τ1) (y : Exp [] τ2) :
    x ---> x' →
    Pair x y ---> Pair x' y
  | ST_Pair2 τ1 τ2 (x : Exp [] τ1) (y y' : Exp [] τ2) :
    y ---> y' →
    Pair x y ---> Pair x y'
  | ST_Fst1 τ1 τ2 (p p' : Exp [] (TyPair τ1 τ2)) :
    p ---> p' →
    Fst p ---> Fst p'
  | ST_FstPair τ1 τ2 (v1 : Exp [] τ1) (v2 : Exp [] τ2) :
    ValueP v1 →
    ValueP v2 →
    Fst (Pair v1 v2) ---> v1
  | ST_Snd1 τ1 τ2 (p p' : Exp [] (TyPair τ1 τ2)) :
    p ---> p' →
    Snd p ---> Snd p'
  | ST_SndPair τ1 τ2 (v1 : Exp [] τ1) (v2 : Exp [] τ2) :
    ValueP v1 →
    ValueP v2 →
    Snd (Pair v1 v2) ---> v2

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

Derive Signature for Step.

Ltac reduce :=
  repeat (lazymatch goal with
          | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
              apply inj_pair2 in H; subst
          | [ H : _ ∧ _ |- _ ] => destruct H
          | [ H : _ * _ |- _ ] => destruct H
          | [ H : ∃ _, _ |- _ ] => destruct H
          end; subst).

Ltac inv H := inversion H; subst; clear H; reduce.

Theorem Step_sound τ (e : Exp [] τ) v :
  e ---> v → SemExp e = SemExp v.
Proof.
  intros.
  induction H; simpl; auto;
  extensionality E;
  destruct E;
  try now rewrite IHStep.
  now rewrite <- SemSubComm.
Qed.
