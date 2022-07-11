Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List
  Coq.Classes.RelationClasses
  Coq.Classes.Morphisms
  Ty
  Exp
  Sub
  Sem.

From Equations Require Import Equations.

Section Step.

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

  | ST_Car1 Γ τ (d d' : Exp Γ τ) (l : Exp Γ (TyList τ)) :
    d ---> d' →
    Car d l ---> Car d' l
  | ST_Car2 Γ τ (d : Exp Γ τ) (l l' : Exp Γ (TyList τ)) :
    ValueP d →
    l ---> l' →
    Car d l ---> Car d l'
  | ST_CarNil Γ τ (d : Exp Γ τ) :
    ValueP d →
    Car d Nil ---> d
  | ST_CarCons Γ τ (d x : Exp Γ τ) (xs : Exp Γ (TyList τ)) :
    ValueP d →
    ValueP x →
    ValueP xs →
    Car d (Cons x xs) ---> x

  | ST_Cdr1 Γ τ (l l' : Exp Γ (TyList τ)) :
    l ---> l' →
    Cdr l ---> Cdr l'
  | ST_CdrNil Γ τ :
    Cdr (Nil (Γ:=Γ) (τ:=τ)) ---> Nil
  | ST_CdrCons Γ τ (x : Exp Γ τ) (xs : Exp Γ (TyList τ)) :
    ValueP x →
    ValueP xs →
    Cdr (Cons x xs) ---> xs

  | ST_IsNil1 Γ τ (l l' : Exp Γ (TyList τ)) :
    l ---> l' →
    IsNil l ---> IsNil l'
  | ST_IsNilNil Γ τ :
    IsNil (Nil (Γ:=Γ) (τ:=τ)) ---> ETrue
  | ST_IsNilCons Γ τ (x : Exp Γ τ) (xs : Exp Γ (TyList τ)) :
    ValueP x →
    ValueP xs →
    IsNil (Cons x xs) ---> EFalse

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

End Step.

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

Lemma If_loop_true {Γ τ} b {x : Exp Γ τ} {y : Exp Γ τ} :
  ¬ (If b x y = x).
Proof.
  induction x; intro; inv H.
  now eapply IHx2; eauto.
Qed.

Lemma If_loop_false {Γ τ} b {x : Exp Γ τ} {y : Exp Γ τ} :
  ¬ (If b x y = y).
Proof.
  induction y; intro; inv H.
  now eapply IHy3; eauto.
Qed.

Lemma Seq_loop {Γ τ ty} {x : Exp Γ ty} {y : Exp Γ τ} :
  ¬ (Seq x y = y).
Proof.
  induction y; intro; inv H.
  now eapply IHy2; eauto.
Qed.

Lemma App_Lam_loop {Γ τ ty} {v : Exp Γ ty} {e : Exp (ty :: Γ) τ} :
  ¬ (SubExp {||v||} e = APP (LAM e) v).
Proof.
  dependent induction e; repeat intro; inv H.
  - dependent induction v0; simp consSub in *.
    + simp SubVar in H1.
      now induction v; inv H1; intuition.
    + simp SubVar in H1.
      rewrite SubVar_idSub in H1.
      now induction v0; inv H1; intuition.
  - admit.
Admitted.

(* A term never reduces to itself. *)
#[export]
Program Instance Step_Irreflexive {Γ τ} :
  Irreflexive (Step (Γ:=Γ) (τ:=τ)).
Next Obligation.
  dependent induction x; try solve [ now inv H ].
  - inv H.
    + now apply Reduce_irr in H4.
  - inv H.
    + now eapply If_loop_true; eauto.
    + now eapply If_loop_false; eauto.
    + now firstorder.
  - inv H.
    now eapply Seq_loop; eauto.
  - inv H.
    + now eapply CallHost_irr; eauto.
    + now eapply App_Lam_loop; eauto.
    + now eapply IHx1; eauto.
    + now eapply IHx2; eauto.
Qed.

#[export]
Program Instance RenExp_Step {Γ Γ' τ} (σ : Ren Γ' Γ) :
  Proper (Step (Γ:=Γ) (τ:=τ) ==> Step) (RenExp σ).
Next Obligation.
  intros.
  induction H; simpl;
  try solve [ now constructor; intuition idtac
            | now constructor; intuition; apply RenExp_ValueP ].
  - now apply Reduce_preserves_renaming.
  - now apply CallHost_preserves_renaming.
  - rewrite <- SubExp_ScR.
    simp ScR.
    rewrite <- RcS_idSub.
    pose proof (SubExp_RcS (Keep σ) (Push (RenExp σ v) idSub) e).
    simp RcS in H.
    rewrite H.
    constructor.
    now apply RenExp_ValueP.
Qed.

#[export]
Program Instance SubExp_Step {Γ Γ' τ} (σ : Sub Γ' Γ) :
  Proper (Step (Γ:=Γ) (τ:=τ) ==> Step) (SubExp σ).
Next Obligation.
  intros.
  induction H; simpl;
  try solve [ now constructor; intuition idtac
            | now constructor; intuition; apply SubExp_ValueP ].
  - now apply Reduce_preserves_substitution.
  - now apply CallHost_preserves_substitution.
  - rewrite <- SubExp_ScS.
    simpl ScS.
    rewrite ScS_idSub_left.
    pose proof (SubExp_ScS (Keepₛ σ) (Push (SubExp σ v) idSub) e).
    simpl in H.
    simp SubVar in H.
    unfold Dropₛ in H.
    rewrite ScS_ScR in H.
    rewrite RcS_skip1 in H.
    rewrite ScS_idSub_right in H.
    rewrite H.
    constructor.
    now apply SubExp_ValueP.
Qed.

Corollary Step_productive {Γ τ} {x x' : Exp Γ τ} : x ---> x' → x ≠ x'.
Proof.
  repeat intro; subst.
  now eapply Step_Irreflexive; eauto.
Qed.

Import ListNotations.

Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e + { e' | e ---> e' }.
Proof.
  dependent induction e; reduce.
  - destruct τ;
    right; now exists (projT1 (Reduce h)); constructor.
  - now left; constructor.
  - now left; constructor.
  - now left; constructor.
  - now left; constructor.
  - now left; constructor.
  - right.
    destruct IHe1; reduce.
    + inv v.
      * now exists e2; constructor.
      * now exists e3; constructor.
    + reduce.
      now exists (If x e2 e3); constructor.
  - destruct IHe1; reduce.
    + destruct IHe2; reduce.
      * left.
        now constructor.
      * right; reduce.
        now exists (Pair e1 x); constructor.
    + destruct IHe2; reduce.
      * right; reduce.
        now exists (Pair x e2); constructor.
      * right; reduce.
        now exists (Pair x e2); constructor.
  - destruct IHe; reduce.
    + right.
      inv v; reduce.
      * now exists x; constructor.
    + right; reduce.
      now exists (Fst x); constructor.
  - destruct IHe; reduce.
    + right.
      inv v.
      * now exists y; constructor.
    + right; reduce.
      now exists (Snd x); constructor.
  - now left; constructor.
  - destruct IHe1.
    + destruct IHe2.
      * now left; constructor.
      * right; reduce.
        now exists (Cons e1 x); constructor.
    + destruct IHe2.
      * right; reduce.
        now exists (Cons x e2); constructor.
      * right; reduce.
        now exists (Cons x0 e2); constructor.
  - destruct IHe1.
    + destruct IHe2.
      * right.
        inv v0.
        ** now eexists; constructor.
        ** now eexists; constructor.
      * right; reduce.
        now exists (Car e1 x); constructor.
    + destruct IHe2.
      * right; reduce.
        now exists (Car x e2); constructor.
      * right; reduce.
        now exists (Car x0 e2); constructor.
  - destruct IHe.
    + right.
      inv v; now eexists; constructor.
    + right; reduce.
      now exists (Cdr x); constructor.
  - right.
    destruct IHe.
    + inv v.
      * now exists ETrue; constructor.
      * now exists EFalse; constructor.
    + reduce.
      exists (IsNil x).
      now constructor.
  - right.
    now exists e2; constructor.
  - now inversion v.
  - left.
    now constructor.
  - right.
    destruct IHe1.
    + destruct IHe2.
      * dependent elimination e1; inv v.
        ** now exists (CallHost h1 e2 v0); constructor.
        ** now eexists (SubExp {|| e2 ||} _); constructor.
      * dependent elimination e1; inv v.
        ** exists (APP (HostedFun h1) x); constructor; auto.
           now constructor.
        ** eexists (APP (LAM _) x); constructor; eauto.
           now constructor.
    + reduce.
      destruct IHe2.
      * exists (APP x e2).
        now constructor.
      * reduce.
        exists (APP x e2).
        now constructor.
Qed.

End Sound.
