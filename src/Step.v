Require Import
  Lib
  Ltac
  Ty
  Exp
  Value
  Ren
  Sub
  Sem.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** Evaluation contexts *)

Section Step.

Import ListNotations.

Context {A : Type}.
Context `{HostExprs A}.

Open Scope Ty_scope.

(* A context defines a hole which, after substitution, yields an expression of
   the index type. *)
Inductive Ctxt Γ τ' : Ty → Type :=
  | C_Hole : Ctxt Γ τ' τ'

  (* | C_If1 {τ} : Ctxt Γ τ' TyBool → Exp Γ τ → Exp Γ τ → Ctxt Γ τ' TyBool *)
  (* | C_If2 {τ} : Exp Γ TyBool → Ctxt Γ τ → Exp Γ τ → Ctxt Γ τ *)
  (* | C_If3 {τ} : Exp Γ TyBool → Exp Γ τ → Ctxt Γ τ → Ctxt Γ τ *)

  | C_App1 {dom cod} : Ctxt Γ τ' (dom ⟶ cod) → Exp Γ dom → Ctxt Γ τ' cod
  | C_App2 {dom cod} : Exp Γ (dom ⟶ cod) → Ctxt Γ τ' dom → Ctxt Γ τ' cod.

Derive Signature NoConfusion for Ctxt.

(* [Ctxt] forms a category with objects = types and morphisms = contexts. *)

Definition Ctxt_id {Γ τ} : Ctxt Γ τ τ := C_Hole _ _.
Arguments Ctxt_id {_ _} /.

Equations Ctxt_comp {Γ τ τ' τ''} (C : Ctxt Γ τ' τ) (C' : Ctxt Γ τ'' τ') :
  Ctxt Γ τ'' τ :=
  Ctxt_comp (C_Hole _ _)     c' := c';
  Ctxt_comp (C_App1 _ _ c _) c' := C_App1 _ _ (Ctxt_comp c c') _;
  Ctxt_comp (C_App2 _ _ _ c) c' := C_App2 _ _ _ (Ctxt_comp c c').

Theorem Ctxt_id_left {Γ τ τ'} {C : Ctxt Γ τ' τ} :
  Ctxt_comp Ctxt_id C = C.
Proof. induction C; simp Ctxt_comp; auto; now f_equal. Qed.

Theorem Ctxt_id_right {Γ τ τ'} {C : Ctxt Γ τ' τ} :
  Ctxt_comp C Ctxt_id = C.
Proof. induction C; simp Ctxt_comp; auto; now f_equal. Qed.

Theorem Ctxt_comp_assoc {Γ τ τ' τ'' τ'''}
        {C : Ctxt Γ τ' τ} {C' : Ctxt Γ τ'' τ'} {C'' : Ctxt Γ τ''' τ''} :
  Ctxt_comp C (Ctxt_comp C' C'') = Ctxt_comp (Ctxt_comp C C') C''.
Proof. induction C; simp Ctxt_comp; auto; now f_equal. Qed.

(*
Equations Plug {Γ τ' τ} (e : Exp Γ τ') (c : Ctxt Γ τ' τ) : Exp Γ τ :=
  Plug e (C_Hole _ _)      := e;
  Plug e (C_App1 _ _ C e1) := APP (Plug e C) e1;
  Plug e (C_App2 _ _ e1 C) := APP e1 (Plug e C).
*)

Unset Elimination Schemes.

Inductive Plug {Γ τ'} (e : Exp Γ τ') : nat → ∀ {τ}, Ctxt Γ τ' τ → Exp Γ τ → Prop :=
  | Plug_Hole : Plug e 0 (C_Hole _ _) e

  (* | Plug_If1 {Γ τ} (C : Ctxt Γ TyBool) (e e' : Exp Γ TyBool) (e1 e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If1 _ C e1 e2) e (If e' e1 e2) *)
  (* | Plug_If2 {Γ τ} (C : Ctxt Γ τ) (e e' : Exp Γ τ) e1 (e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If2 _ e1 C e2) e (If e1 e' e2) *)
  (* | Plug_If3 {Γ τ} (C : Ctxt Γ τ) (e e' : Exp Γ τ) e1 (e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If3 _ e1 e2 C) e (If e1 e2 e') *)

  | Plug_App1 {n dom cod} {C : Ctxt Γ τ' (dom ⟶ cod)}
              {e' : Exp Γ (dom ⟶ cod)} {e1 : Exp Γ dom} :
    Plug e n C e' →
    Plug e (S n) (C_App1 _ _ C e1) (APP e' e1)
  | Plug_App2 {n dom cod} {C : Ctxt Γ τ' dom}
              {e' : Exp Γ dom} {e1 : Exp Γ (dom ⟶ cod)} :
    ValueP e1 →
    Plug e n C e' →
    Plug e (S n) (C_App2 _ _ e1 C) (APP e1 e').

Derive Signature for Plug.

Set Elimination Schemes.

Scheme Plug_ind := Induction for Plug Sort Prop.

(* [Plug] forms a category with objects = expressions and morphisms = plugs
   over existential contexts. *)

Definition Plug_id {Γ τ} {x : Exp Γ τ} : Plug x 0 (C_Hole Γ τ) x := Plug_Hole _.
Arguments Plug_id {_ _ _} /.

Equations Plug_comp {Γ τ τ' τ'' n m}
          {x : Exp Γ τ''} {y : Exp Γ τ'} {z : Exp Γ τ}
          {C : Ctxt Γ τ' τ} {C' : Ctxt Γ τ'' τ'}
          (P : Plug x n C' y) (P' : Plug y m C z) :
  Plug x (m + n) (Ctxt_comp C C') z :=
  Plug_comp p (Plug_Hole _)    := p;
  Plug_comp p (Plug_App1 _ p')   := Plug_App1 _ (Plug_comp p p');
  Plug_comp p (Plug_App2 _ H p') := Plug_App2 _ H (Plug_comp p p').

(* This should be provable, but the dependent types get in the way. *)
Theorem Plug_id_left {Γ τ τ' n} {C : Ctxt Γ τ' τ} {x : Exp Γ τ'} {y : Exp Γ τ}
        (P : Plug x n C y) :
  Plug_comp Plug_id P ~= P.
Proof.
  dependent induction P; auto.
  - rewrite (Plug_comp_equation_2 _ _ _ _ _ _ _ _ _ _ _ _ _ Plug_id P).
    unfold Ctxt_comp_obligations_obligation_1.
    pose proof (@Ctxt_id_right _ _ _ C).
    simpl in *.
    Fail rewrite H0 in IHP.
    Fail now rewrite IHP.
Abort.
(*
  - rewrite (Plug_comp_equation_3 _ _ _ _ _ _ _ _ _ _ _ Plug_id _ P).
    pose proof (@Ctxt_id_right _ _ _ C).
    simpl in *.
    Fail now rewrite IHP.
*)

Inductive Redex {Γ} : ∀ {τ}, Exp Γ τ → Exp Γ τ → Prop :=
  | ST_AppAbs0 {dom cod} (e : Exp (dom :: Γ) cod) v :
    ValueP v →
    Redex (APP (LAM e) v) (SubExp {|| v ||} e).

Derive Signature for Redex.

Reserved Notation " t '--->' t' " (at level 40).

Inductive Step {Γ τ} : Exp Γ τ → Exp Γ τ → Prop :=
  | StepRule {τ' n} {C : Ctxt Γ τ' τ} {e1 e2 : Exp Γ τ'} {e1' e2' : Exp Γ τ} :
    Plug e1 n C e1' →
    Plug e2 n C e2' →
    Redex e1 e2 →
    e1' ---> e2'

  | StepError {τ' n} {C : Ctxt Γ τ' τ} {m : Err} {e1' : Exp Γ τ} :
    Plug (Error m) (S n) C e1' →
    e1' ---> Error m

  where " t '--->' t' " := (Step t t').

Derive Signature for Step.

#[local] Hint Constructors ValueP Plug Redex Step : core.

Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e ∨ ErrorP e ∨ ∃ e', e ---> e'.
Proof.
  dependent induction e; reduce.
  - right.
    now left; eexists.
  - now inv v.
  - now left; constructor.
  - right.
    destruct IHe1 as [V1|[E1|[e1' H1']]];
    destruct IHe2 as [V2|[E2|[e2' H2']]].
    + dependent elimination V1.
      now eauto 6.
    + dependent elimination V1.
      dependent elimination E2.
      right.
      now eexists; eapply StepError; eauto.
    + dependent elimination H2'.
      * now eauto 6.
      * now right; eexists; eapply StepError; eauto.
    + dependent elimination V2.
      dependent elimination E1.
      right.
      now eexists; eapply StepError; eauto.
    + dependent elimination E1.
      right.
      now eexists; eapply StepError; eauto.
    + dependent elimination E1.
      right.
      now eexists; eapply StepError; eauto.
    + dependent elimination H1'.
      * now eauto 6.
      * right.
        now eexists; eapply StepError; eauto.
    + dependent elimination H1'.
      * eauto 6.
      * right.
        now eexists; eapply StepError; eauto.
    + dependent elimination H1'.
      dependent elimination H2'.
      * now eauto 6.
      * now eauto 6.
      * right.
        now eexists; eapply StepError; eauto.
Qed.

Lemma Plug_not_ValueP {Γ τ} {C : Ctxt Γ τ τ} (e v : Exp Γ τ) :
  ValueP v → Plug e 0 C v → C = C_Hole _ _ ∧ e = v.
Proof.
  intros.
  dependent elimination H0.
  now inv H1.
Qed.

Lemma Redex_ValueP {Γ τ} (e v : Exp Γ τ) :
  ValueP v → ¬ Redex v e.
Proof.
  repeat intro.
  dependent elimination H0.
  now inv H1.
Qed.

Lemma Plug_deterministic {Γ τ τ' n} {C : Ctxt Γ τ' τ} e2 :
  ∀ e1 e1', Redex e1 e1' →
  ∀ τ'' f1 f1', Redex f1 f1' →
  Plug e1 n C e2 →
  ∀ m (C' : Ctxt Γ τ'' τ),
  Plug f1 m C' e2 →
    τ' = τ'' ∧ n = m ∧ C ~= C' ∧ e1 ~= f1.
Proof.
  intros.
  generalize dependent C'.
  generalize dependent m.
  induction H2; intros; subst.
  inv H3; auto.
  - exfalso.
    dependent elimination H0.
    dependent elimination H1.
    now inv H7.
  - exfalso.
    dependent elimination H0.
    dependent elimination H1.
    now inv H8.
  - dependent elimination H3.
    + exfalso.
      dependent elimination H0.
      dependent elimination H1.
      now inv H2.
    + intuition.
      now destruct (IHPlug _ _ p); reduce.
    + exfalso.
      dependent elimination H0.
      dependent elimination H1.
      now inv H2.
  - dependent elimination H3.
    + exfalso.
      dependent elimination H0.
      dependent elimination H1.
      now inv H2.
    + exfalso.
      dependent elimination H0.
      dependent elimination H1.
      now inv p.
    + intuition.
      now destruct (IHPlug _ _ p0); reduce.
Qed.

Lemma Plug_functional {Γ τ τ' n} {C : Ctxt Γ τ' τ} e e1 :
  Plug e n C e1 → ∀ e2, Plug e n C e2 → e1 = e2.
Proof.
  intros.
  dependent induction H0.
  - now inv H1.
  - dependent destruction H1.
    now f_equal; auto.
  - dependent destruction H1.
    now f_equal; auto.
Qed.

Lemma Plug_injective {Γ τ τ' n} {C : Ctxt Γ τ' τ} e e1 :
  Plug e1 n C e → ∀ e2, Plug e2 n C e → e1 = e2.
Proof.
  intros.
  dependent induction H0.
  - now inv H1.
  - dependent destruction H1.
    now f_equal; auto.
  - dependent destruction H1.
    now f_equal; auto.
Qed.

Lemma Redex_deterministic : ∀ Γ τ (e e' : Exp Γ τ),
  Redex e e' → ∀ e'', Redex e e'' → e' = e''.
Proof.
  intros.
  dependent elimination H0.
  dependent elimination H1.
  reflexivity.
Qed.

Lemma App_Lam_loop {Γ τ ty} {v : Exp Γ ty} {e : Exp (ty :: Γ) τ} :
  ¬ (SubExp {||v||} e = APP (LAM e) v).
Admitted.
(*
Proof.
  dependent induction e; repeat intro; inv H.
  - dependent induction v0; simp consSub in *.
    + simp SubVar in H1.
  (*     now induction v; inv H1; intuition. *)
  (*   + simp SubVar in H1. *)
  (*     rewrite SubVar_idSub in H1. *)
  (*     now induction v0; inv H1; intuition. *)
Admitted.
*)

(*
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
*)

(* A term never reduces to itself. *)
#[export]
Program Instance Step_Irreflexive {Γ τ} :
  Irreflexive (Step (Γ:=Γ) (τ:=τ)).
Next Obligation.
  inv H0.
  - pose proof (Plug_injective _ _ H1 _ H2); subst.
    inv H3.
    now eapply App_Lam_loop; eauto.
  - now inv H1.
Qed.

Corollary Step_productive {Γ τ} {x x' : Exp Γ τ} : x ---> x' → x ≠ x'.
Proof.
  repeat intro; subst.
  now eapply Step_Irreflexive; eauto.
Qed.

#[export]
Program Instance RenExp_Step {Γ Γ' τ} (σ : Ren Γ' Γ) :
  Proper (Step (Γ:=Γ) (τ:=τ) ==> Step) (RenExp σ).
Next Obligation.
  intros.
  induction H0; simpl;
  try solve [ now constructor; intuition idtac
            | now constructor; intuition; apply RenExp_ValueP ].
  (* - now apply Reduce_preserves_renaming. *)
  (* - now apply CallHost_preserves_renaming. *)
Admitted.
(*
  - dependent elimination H2.
    (* epose proof (StepRule (Plug_App2 _ H0) *)
    (*                       (Plug_App2 _ H1) H3). *)
    dependent induction H2.
    + inv H1; simpl.
      rewrite <- SubExp_ScR.
      simp ScR.
      rewrite <- RcS_idSub.
      pose proof (SubExp_RcS (Keep σ) (Push (RenExp σ v) idSub) e) as H1.
      simp RcS in H1.
      rewrite H1.
      repeat econstructor.
      now apply RenExp_ValueP.
    + specialize (IHPlug _ _ _ _ _ eq_refl H1 v0).
      apply IHPlug.
      dependent destruction H1; simpl.

      repeat econstructor.
      epose proof (StepRule (Plug_App1 p)
                            (Plug_App1 H1)).

Qed.
*)

#[export]
Program Instance SubExp_Step {Γ Γ' τ} (σ : Sub Γ' Γ) :
  Proper (Step (Γ:=Γ) (τ:=τ) ==> Step) (SubExp σ).
Next Obligation.
  intros.
Admitted.
(*
  induction H; simpl;
  try solve [ now constructor; intuition idtac
            | now constructor; intuition; apply SubExp_ValueP ].
  (* - now apply Reduce_preserves_substitution. *)
  (* - now apply CallHost_preserves_substitution. *)
  - rewrite <- SubExp_ScS.
    simpl ScS.
    rewrite ScS_idSub_left.
    pose proof (SubExp_ScS (Keepₛ σ) (Push (SubExp σ v) idSub) e) as H1.
    simpl in H1.
    simp SubVar in H1.
    unfold Dropₛ in H1.
    rewrite ScS_ScR in H1.
    rewrite RcS_skip1 in H1.
    rewrite ScS_idSub_right in H1.
    rewrite H1.
    constructor.
    now apply SubExp_ValueP.
Qed.
*)

Lemma pluggable {Γ τ n} {e1 e2 : Exp Γ τ} {τ'}
      {C : Ctxt Γ τ' τ} {f1 f2 : Exp Γ τ'} :
  ¬ ErrorP f2 →
  f1 ---> f2 →
  Plug f1 n C e1 →
  Plug f2 n C e2 →
  e1 ---> e2.
Proof.
  intros.
  dependent elimination H1.
  - exact (StepRule (Plug_comp p H2) (Plug_comp p0 H3) r).
  - exfalso.
    now apply H0.
Qed.

Lemma APP_LAM_2 {Γ dom cod} (e : Exp (dom :: Γ) cod) (x x' : Exp Γ dom) :
  ¬ ErrorP x' →
  x ---> x' →
  APP (LAM e) x ---> APP (LAM e) x'.
Proof.
  intros.
  now eapply (pluggable H0 H1); eauto.
Qed.

End Step.

Notation " t '--->' t' " := (Step t t') (at level 40).