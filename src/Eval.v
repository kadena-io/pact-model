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

  | ST_HostUnit Γ (u : HostExp TyUnit) :
    Hosted u ---> EUnit (Γ:=Γ)
  | ST_HostBool Γ (b : HostExp TyBool) :
    Hosted b ---> projT1 (GetBool (Γ:=Γ) b)
  | ST_HostPair Γ τ1 τ2 (p : HostExp (TyPair τ1 τ2)) :
    Hosted p ---> projT1 (GetPair (Γ:=Γ) p)

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

  | ST_ConsHead Γ τ (x : Exp Γ τ) x' (xs : Exp Γ (TyList τ)) :
    x ---> x' →
    Cons x xs ---> Cons x' xs
  | ST_ConsTail Γ τ (x : Exp Γ τ) (xs : Exp Γ (TyList τ)) xs' :
    ValueP x →
    xs ---> xs' →
    Cons x xs ---> Cons x xs'

  | ST_AppHost Γ dom cod (f : HostExp (dom ⟶ cod)) (v : Exp Γ dom) :
    ∀ H : ValueP v,
    APP (Hosted f) v ---> CallHost f v H

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
    ¬ (CallHost f v H = APP (Hosted f) v);

  CallHost_preserves_renaming {Γ Γ' dom cod} (f : HostExp (dom ⟶ cod))
               (v : Exp Γ dom) (H : ValueP v) (σ : Ren Γ' Γ) :
    APP (Hosted f) (RenExp σ v) ---> RenExp σ (CallHost f v H);

  CallHost_preserves_substitution {Γ Γ' dom cod} (f : HostExp (dom ⟶ cod))
               (v : Exp Γ dom) (H : ValueP v) (σ : Sub Γ' Γ) :
    APP (Hosted f) (SubExp σ v) ---> SubExp σ (CallHost f v H);


  Unit_sound (u : HostExp TyUnit) :
    HostExpSem u = ();


  GetBool_sound {Γ} (b : HostExp TyBool) se :
    HostExpSem b = SemExp (projT1 (GetBool (Γ:=Γ) b)) se;

  GetBool_irr {Γ} (b : HostExp TyBool) :
    ¬ (projT1 (GetBool (Γ:=Γ) b) = Hosted b);

  GetBool_preserves_renaming {Γ Γ'} (b : HostExp TyBool) (σ : Ren Γ Γ') :
    RenExp σ (Hosted b) ---> RenExp σ (projT1 (GetBool b));

  GetBool_preserves_substitution {Γ Γ'} (b : HostExp TyBool) (σ : Sub Γ Γ') :
    SubExp σ (Hosted b) ---> SubExp σ (projT1 (GetBool b));


  GetPair_sound {Γ τ1 τ2} (p : HostExp (TyPair τ1 τ2)) se :
    HostExpSem p = SemExp (projT1 (GetPair (Γ:=Γ) p)) se;

  GetPair_irr {Γ τ1 τ2} (p : HostExp (TyPair τ1 τ2)) :
    ¬ (projT1 (GetPair (Γ:=Γ) p) = Hosted p);

  GetPair_preserves_renaming {Γ Γ' τ1 τ2} (p : HostExp (TyPair τ1 τ2))
                             (σ : Ren Γ Γ') :
    RenExp σ (Hosted p) ---> RenExp σ (projT1 (GetPair p));

  GetPair_preserves_substitution {Γ Γ' τ1 τ2} (p : HostExp (TyPair τ1 τ2))
                                 (σ : Sub Γ Γ') :
    SubExp σ (Hosted p) ---> SubExp σ (projT1 (GetPair p));
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
  - now erewrite Unit_sound; eauto.
  - now erewrite GetBool_sound; eauto.
  - now erewrite GetPair_sound; eauto.
  - now apply CallHost_sound.
  - rewrite <- SemExp_SubSem.
    f_equal; simpl.
    simp SubSem.
    now rewrite SubSem_idSub.
Qed.

End Sound.
