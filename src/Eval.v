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

Section Eval.

Generalizable All Variables.

Import ListNotations.

Context {A : Type}.
Context `{S : HostExprsSem A}.

Reserved Notation " t '--->' t' " (at level 40).

(************************************************************************
 * Small-step operational semantics
 *)

Inductive Step : ∀ {Γ τ}, Exp Γ τ → Exp Γ τ → Prop :=
  | ST_Seq Γ τ τ' (e1 : Exp Γ τ') (e2 : Exp Γ τ) :
    Seq e1 e2 ---> e2

  | ST_Host Γ τ (h : HostExp τ) :
    HostedExp h ---> projT1 (Reduce (Γ:=Γ) h)

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

  | ST_Cons1 Γ τ (x : Exp Γ τ) x' (xs : Exp Γ (TyList τ)) :
    x ---> x' →
    Cons x xs ---> Cons x' xs
  | ST_Cons2 Γ τ (x : Exp Γ τ) (xs : Exp Γ (TyList τ)) xs' :
    ValueP x →
    xs ---> xs' →
    Cons x xs ---> Cons x xs'

  | ST_AppHost Γ dom cod (f : HostExp (dom ⟶ cod)) (v : Exp Γ dom) :
    ∀ H : ValueP v,
    APP (HostedFun f) v ---> CallHost f v H

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

End Eval.

Notation " t '--->' t' " := (Step t t') (at level 40).

Class HostLang (A : Type) : Type := {
  has_host_exprs_sem :> HostExprsSem A;


  CallHost_sound {Γ dom cod} (f : HostExp (dom ⟶ cod))
                 (v : Exp Γ dom) (H : ValueP v) se :
    HostExpSem f (SemExp v se) = SemExp (CallHost f v H) se;

  CallHost_irr {Γ dom cod} (f : HostExp (dom ⟶ cod))
               (v : Exp Γ dom) (H : ValueP v) :
    ¬ (CallHost f v H = APP (HostedFun f) v);

  CallHost_preserves_renaming {Γ Γ' dom cod} (f : HostExp (dom ⟶ cod))
               (v : Exp Γ dom) (H : ValueP v) (σ : Ren Γ' Γ) :
    APP (HostedFun f) (RenExp σ v) ---> RenExp σ (CallHost f v H);

  CallHost_preserves_substitution {Γ Γ' dom cod} (f : HostExp (dom ⟶ cod))
               (v : Exp Γ dom) (H : ValueP v) (σ : Sub Γ' Γ) :
    APP (HostedFun f) (SubExp σ v) ---> SubExp σ (CallHost f v H);


  Reduce_sound {Γ τ} (h : HostExp τ) se :
    HostExpSem h = SemExp (projT1 (Reduce (Γ:=Γ) h)) se;

  Reduce_irr {Γ τ} (h : HostExp τ) :
    ¬ (projT1 (Reduce (Γ:=Γ) h) = HostedExp h);

  Reduce_preserves_renaming {Γ Γ' τ} (h : HostExp τ) (σ : Ren Γ Γ') :
    RenExp σ (HostedExp h) ---> RenExp σ (projT1 (Reduce h));

  Reduce_preserves_substitution {Γ Γ' τ} (h : HostExp τ) (σ : Sub Γ Γ') :
    SubExp σ (HostedExp h) ---> SubExp σ (projT1 (Reduce h));
}.

Section Sound.

Context {A : Type}.
Context `{L : HostLang A}.

Theorem Step_sound {Γ τ} (e : Exp Γ τ) v :
  e ---> v → SemExp e = SemExp v.
Proof.
  intros.
  dependent induction H; simpl; auto;
  extensionality se;
  try now rewrite IHStep.
  - now erewrite Reduce_sound; eauto.
  - now apply CallHost_sound.
  - rewrite <- SemExp_SubSem.
    f_equal; simpl.
    simp SubSem.
    now rewrite SubSem_idSub.
Qed.

End Sound.
