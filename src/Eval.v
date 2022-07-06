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

Inductive Step : ∀ {Γ τ}, Exp Γ τ → Exp Γ τ → Prop :=
  | ST_Seq Γ τ τ' (e1 : Exp Γ τ') (e2 : Exp Γ τ) :
    Seq e1 e2 ---> e2

  | ST_IfTrue Γ τ (t e : Exp Γ τ) :
    If ETrue t e ---> t
  | ST_IfFalse Γ τ (t e : Exp Γ τ) :
    If EFalse t e ---> e
  | ST_If Γ b b' τ (t e : Exp Γ τ) :
    b ---> b' →
    If b t e ---> If b' t e

  | ST_Pair1 Γ τ1 τ2 (x x' : Exp Γ τ1) (y : Exp Γ τ2) :
    x ---> x' →
    Pair x y ---> Pair x' y
  | ST_Pair2 Γ τ1 τ2 (x : Exp Γ τ1) (y y' : Exp Γ τ2) :
    ValueP x →
    y ---> y' →
    Pair x y ---> Pair x y'
  | ST_Fst1 Γ τ1 τ2 (p p' : Exp Γ (TyPair τ1 τ2)) :
    p ---> p' →
    Fst p ---> Fst p'
  | ST_FstPair Γ τ1 τ2 (v1 : Exp Γ τ1) (v2 : Exp Γ τ2) :
    ValueP v1 →
    ValueP v2 →
    Fst (Pair v1 v2) ---> v1
  | ST_Snd1 Γ τ1 τ2 (p p' : Exp Γ (TyPair τ1 τ2)) :
    p ---> p' →
    Snd p ---> Snd p'
  | ST_SndPair Γ τ1 τ2 (v1 : Exp Γ τ1) (v2 : Exp Γ τ2) :
    ValueP v1 →
    ValueP v2 →
    Snd (Pair v1 v2) ---> v2

  | ST_Let1 Γ τ ty (x : Exp Γ ty) x' (body : Exp (ty :: Γ) τ) :
    x ---> x' →
    Let x body ---> Let x' body
  | ST_Let2 Γ τ ty (x : Exp Γ ty) (body : Exp (ty :: Γ) τ) :
    ValueP x →
    Let x body ---> SubExp {|| x ||} body

  | ST_AppAbs Γ dom cod (e : Exp (dom :: Γ) cod) (v : Exp Γ dom) :
    ValueP v →
    APP (LAM e) v ---> SubExp {|| v ||} e

  | ST_App1 Γ dom cod (e1 : Exp Γ (dom ⟶ cod)) e1' (e2 : Exp Γ dom) :
    e1 ---> e1' →
    APP e1 e2 ---> APP e1' e2

  | ST_App2 Γ dom cod (v1 : Exp Γ (dom ⟶ cod)) (e2 : Exp Γ dom) e2' :
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

Theorem Step_sound {Γ τ} (e : Exp Γ τ) v :
  e ---> v → SemExp e = SemExp v.
Proof.
  intros.
  induction H; simpl; auto;
  extensionality E;
  try now rewrite IHStep.
  - rewrite <- SemExp_SubSem.
    f_equal; simpl.
    simp SubSem.
    now rewrite SubSem_idSub.
  - rewrite <- SemExp_SubSem.
    f_equal; simpl.
    simp SubSem.
    now rewrite SubSem_idSub.
Qed.
