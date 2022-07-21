Require Import
  TList
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

Unset Elimination Schemes.

Inductive Redex {Γ} : ∀ {τ}, Exp Γ τ → Exp Γ τ → Prop :=
  | R_Beta {dom cod} (e : Exp (dom :: Γ) cod) v :
    ValueP v →
    Redex (APP (LAM e) v) (SubExp {|| v ||} e).

Derive Signature for Redex.

Scheme Redex_ind := Induction for Redex Sort Prop.

(* A context defines a hole which, after substitution, yields an expression of
   the index type. *)
Inductive Ctxt1 Γ : ∀ {τ τ'}, (Exp Γ τ' → Exp Γ τ) → Prop :=
  | C_AppL {dom cod} (x : Exp Γ dom) :
    Ctxt1 Γ (λ f : Exp Γ (dom ⟶ cod), APP f x)
  | C_AppR {dom cod} (f : Exp Γ (dom ⟶ cod)) :
    Ctxt1 Γ (λ x : Exp Γ dom, APP f x).

Derive Signature for Ctxt1.

Scheme Ctxt1_ind := Induction for Ctxt1 Sort Prop.

Arguments C_AppL {_ _ _} x.
Arguments C_AppR {_ _ _} f.

Inductive Ctxt Γ : nat → ∀ {τ τ'}, (Exp Γ τ' → Exp Γ τ) → Prop :=
  | Ctxt_nil {τ} : Ctxt Γ 0 (λ x : Exp Γ τ, x)
  | Ctxt_cons {n τ τ' τ''} {f : Exp Γ τ' → Exp Γ τ} {g : Exp Γ τ'' → Exp Γ τ'} :
    Ctxt1 Γ f → Ctxt Γ n g → Ctxt Γ (S n) (f ∘ g).

Derive Signature for Ctxt.

Scheme Ctxt_ind := Induction for Ctxt Sort Prop.

Arguments Ctxt_nil {_ _}.
Arguments Ctxt_cons {_ _ _ _ _ _ _} _ _.

Notation "⦉ e ; .. ; f ⦊" := (Ctxt_cons e .. (Ctxt_cons f Ctxt_nil) ..).

Notation "x ∷ xs" := (Ctxt_cons x xs) (at level 70).

(* [Ctxt] forms a category with objects = types and morphisms = contexts. *)

Definition Ctxt_id {Γ τ} : Ctxt Γ 0 id := @Ctxt_nil Γ τ.
Arguments Ctxt_id {Γ τ} /.

Equations Ctxt_comp {Γ τ τ' τ'' n m}
          {f : Exp Γ τ' → Exp Γ τ}
          {g : Exp Γ τ'' → Exp Γ τ'}
          (Cf : Ctxt Γ n f) (Cg : Ctxt Γ m g) : Ctxt Γ (n + m) (f ∘ g) :=
  Ctxt_comp Ctxt_nil gs := gs;
  Ctxt_comp (f ∷ fs) gs := f ∷ Ctxt_comp fs gs.

Theorem Ctxt_id_left {Γ τ τ' n} {f : Exp Γ τ' → Exp Γ τ} {C : Ctxt Γ n f} :
  Ctxt_comp Ctxt_id C = C.
Proof.
  simpl.
  pose proof (Ctxt_comp_equation_1 _ _ _ _ f C).
  unfold compose in H0.
  now apply H0.
Qed.

Theorem Ctxt_id_right {Γ τ τ' n} {f : Exp Γ τ' → Exp Γ τ} {C : Ctxt Γ n f} :
  Ctxt_comp C Ctxt_id ~= C.
Proof.
  simpl.
  dependent induction C; simp Ctxt_comp; auto.
  pose proof (Ctxt_comp_equation_2 Γ _ _ _ n 0 _ _ _ _ c C Ctxt_id).
  simpl in *.
  unfold compose in H0.
  rewrite H0; clear H0.
Abort.

Theorem Ctxt_comp_assoc {Γ τ τ' τ'' τ''' n m o}
        {f : Exp Γ τ' → Exp Γ τ}
        {g : Exp Γ τ'' → Exp Γ τ'}
        {h : Exp Γ τ''' → Exp Γ τ''}
        (Cf : Ctxt Γ n f) (Cg : Ctxt Γ m g) (Ch : Ctxt Γ o h) :
  Ctxt_comp Cf (Ctxt_comp Cg Ch) ~= Ctxt_comp (Ctxt_comp Cf Cg) Ch.
Proof.
  simpl.
  dependent induction Cf; simp Ctxt_comp; auto.
  pose proof (Ctxt_comp_equation_2 Γ _ _ _ n _ _ _ _ _ c Cf (Ctxt_comp Cg Ch)).
  simpl in *.
  rewrite H0; clear H0.
  pose proof (Ctxt_comp_equation_2 Γ _ _ _ n _ _ _ _ _ c Cf Cg).
  simpl in *.
  rewrite H0; clear H0.
  pose proof (Ctxt_comp_equation_2 Γ _ _ _ _ _ _ _ _ _ c (Ctxt_comp Cf Cg) Ch).
  simpl in *.
  rewrite H0; clear H0.
  Fail rewrite PeanoNat.Nat.add_assoc.
  Fail rewrite IHCf.
Abort.

(*
Equations Plug {Γ τ' τ} (e : Exp Γ τ') (c : Ctxt Γ τ' τ) : Exp Γ τ :=
  Plug e (C_Hole _ _)      := e;
  Plug e (C_App1 _ _ C e1) := APP (Plug e C) e1;
  Plug e (C_App2 _ _ e1 C) := APP e1 (Plug e C).
*)

(*
Unset Elimination Schemes.

Inductive Plug {Γ τ'} (e : Exp Γ τ') : ∀ {τ}, Ctxt Γ τ' τ → Exp Γ τ → Prop :=
  | Plug_Hole : Plug e (C_Hole _ _) e

  (* | Plug_If1 {Γ τ} (C : Ctxt Γ TyBool) (e e' : Exp Γ TyBool) (e1 e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If1 _ C e1 e2) e (If e' e1 e2) *)
  (* | Plug_If2 {Γ τ} (C : Ctxt Γ τ) (e e' : Exp Γ τ) e1 (e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If2 _ e1 C e2) e (If e1 e' e2) *)
  (* | Plug_If3 {Γ τ} (C : Ctxt Γ τ) (e e' : Exp Γ τ) e1 (e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If3 _ e1 e2 C) e (If e1 e2 e') *)

  | Plug_App1 {dom cod} {C : Ctxt Γ τ' (dom ⟶ cod)}
              {e' : Exp Γ (dom ⟶ cod)} {e1 : Exp Γ dom} :
    Plug e C e' →
    Plug e (C_App1 _ _ C e1) (APP e' e1)
  | Plug_App2 {dom cod} {C : Ctxt Γ τ' dom}
              {e' : Exp Γ dom} {e1 : Exp Γ (dom ⟶ cod)} :
    ValueP e1 →
    Plug e C e' →
    Plug e (C_App2 _ _ e1 C) (APP e1 e').

Derive Signature for Plug.

Set Elimination Schemes.

Scheme Plug_ind := Induction for Plug Sort Prop.

(* [Plug] forms a category with objects = expressions and morphisms = plugs
   over existential contexts. *)

Definition Plug_id {Γ τ} {x : Exp Γ τ} : Plug x (C_Hole Γ τ) x := Plug_Hole _.
Arguments Plug_id {_ _ _} /.

Equations Plug_comp {Γ τ τ' τ''}
          {x : Exp Γ τ''} {y : Exp Γ τ'} {z : Exp Γ τ}
          {C : Ctxt Γ τ' τ} {C' : Ctxt Γ τ'' τ'}
          (P : Plug x C' y) (P' : Plug y C z) : Plug x (Ctxt_comp C C') z :=
  Plug_comp p (Plug_Hole _)    := p;
  Plug_comp p (Plug_App1 _ p')   := Plug_App1 _ (Plug_comp p p');
  Plug_comp p (Plug_App2 _ H p') := Plug_App2 _ H (Plug_comp p p').

(* This should be provable, but the dependent types get in the way. *)
Theorem Plug_id_left {Γ τ τ'} {C : Ctxt Γ τ' τ} {x : Exp Γ τ'} {y : Exp Γ τ}
        (P : Plug x C y) :
  Plug_comp Plug_id P ~= P.
Proof.
  dependent induction P; auto.
  - rewrite (Plug_comp_equation_2 _ _ _ _ _ _ _ _ _ _ _ Plug_id P).
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
*)

Reserved Notation " t '--->' t' " (at level 40).

Inductive Step {Γ τ} : Exp Γ τ → Exp Γ τ → Prop :=
  | StepRule {n τ' C} {e1 e2 : Exp Γ τ'} :
    Ctxt Γ n C →
    Redex e1 e2 →
    C e1 ---> C e2

  | StepError {n τ'} {C : Exp Γ τ' → Exp Γ τ} {m : Err} :
    Ctxt Γ (S n) C →
    C (Error m) ---> Error m

  where " t '--->' t' " := (Step t t').

Derive Signature for Step.

(* #[local] Hint Constructors ValueP Plug Redex Step : core. *)
#[local] Hint Constructors ValueP Redex Ctxt1 Ctxt Step : core.

Ltac step :=
  first [ now eapply (StepRule Ctxt_nil); eauto
        | now eapply (StepError Ctxt_nil); eauto
        | now eapply (StepRule ⦉ C_AppL _ ⦊); eauto
        | now eapply (StepError ⦉ C_AppL _ ⦊); eauto
        | now match goal with
              | [ H : Ctxt [] _ _ |- _ ] =>
                  eapply (StepRule (C_AppL _ ∷ H)); eauto
              end
        | now match goal with
              | [ H : Ctxt [] _ _ |- _ ] =>
                  eapply (StepError (C_AppL _ ∷ H)); eauto
              end
        | now eapply (StepRule ⦉ C_AppR _ ⦊); eauto
        | now eapply (StepError ⦉ C_AppR _ ⦊); eauto
        | now match goal with
              | [ H : Ctxt [] _ _ |- _ ] =>
                  eapply (StepRule (C_AppR _ ∷ H)); eauto
              end
        | now match goal with
              | [ H : Ctxt [] _ _ |- _ ] =>
                  eapply (StepError (C_AppR _ ∷ H)); eauto
              end ].

Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e ∨ ErrorP e ∨ ∃ e', e ---> e'.
Proof.
  dependent induction e.
  - now right; left.
  - now inv v.
  - now left; constructor.
  - reduce.
    right; right.
    destruct IHe1 as [V1|[E1|[e1' H1']]];
    destruct IHe2 as [V2|[E2|[e2' H2']]].
    + dependent elimination V1.
      now eexists; step.
    + dependent elimination V1.
      dependent elimination E2.
      now eexists; step.
    + dependent elimination H2'.
      * now eexists; step.
      * now eexists; step.
    + dependent elimination V2.
      dependent elimination E1.
      now eexists; step.
    + dependent elimination E1.
      now eexists; step.
    + dependent elimination E1.
      now eexists; step.
    + dependent elimination H1'.
      * now eexists; step.
      * now eexists; step.
    + dependent elimination H1'.
      * now eexists; step.
      * now eexists; step.
    + dependent elimination H1'.
      * dependent elimination H2'.
        ** now eexists; step.
        ** now eexists; step.
      * now eexists; step.
Qed.

Lemma Redex_ValueP {Γ τ} (e v : Exp Γ τ) :
  ValueP v → ¬ Redex v e.
Proof.
  repeat intro.
  dependent elimination H0.
  now inv H1.
Qed.

Lemma Plug_deterministic {Γ τ} :
  ∀  τ' n {Ce : Exp Γ τ' → Exp Γ τ} e1 e1',
    Ctxt Γ n Ce →
    Redex e1 e1' →
  ∀ τ'' m {Cf : Exp Γ τ'' → Exp Γ τ} f1 f1',
    Ctxt Γ m Cf →
    Redex f1 f1' →

    Ce e1 = Cf f1 →
      τ' = τ'' ∧ Ce ~= Cf ∧ e1 ~= f1.
Proof.
  intros.
  generalize dependent Cf.
  dependent induction H1; intros; subst.
  inv H3; auto.
  - exfalso.
    dependent elimination H0.
    dependent elimination H2.
    now inv H6.
  - exfalso.
    dependent elimination H0.
    dependent elimination H1.
    now inv H7.
  - dependent elimination H3.
    + exfalso.
      dependent elimination H0.
      dependent elimination H1.
      now inv H2.
    + intuition.
      now destruct (IHPlug _ p); reduce.
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
      now destruct (IHPlug _ p0); reduce.
Qed.

Lemma Plug_functional {Γ τ τ'} {C : Ctxt Γ τ' τ} e e1 :
  Plug e C e1
    → ∀ e2, Plug e C e2 → e1 = e2.
Proof.
  intros.
  dependent induction H0.
  - now inv H1.
  - dependent destruction H1.
    now f_equal; auto.
  - dependent destruction H1.
    now f_equal; auto.
Qed.
*)

Theorem Ctxt1_injective {Γ τ τ'} {C : Exp Γ τ' → Exp Γ τ} {e1 e2 : Exp Γ τ'} :
  Ctxt1 Γ C →
  C e1 = C e2 → e1 = e2.
Proof.
  intros.
  generalize dependent e2.
  generalize dependent e1.
  induction H0; simpl; intros; auto.
  - now inv H1.
  - now inv H1.
Qed.

Theorem Ctxt_injective {Γ τ τ' n} {C : Exp Γ τ' → Exp Γ τ} {e1 e2 : Exp Γ τ'} :
  Ctxt Γ n C →
  C e1 = C e2 → e1 = e2.
Proof.
  intros.
  generalize dependent e2.
  generalize dependent e1.
  induction H0; simpl; intros; auto.
  now eapply Ctxt1_injective in c; eauto.
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
  dependent induction H0.
  - eapply Ctxt_injective in H0; eauto; subst.
    dependent destruction H1.
    now eapply App_Lam_loop; eauto.
  - inv H0.
    inv H3;
    now inv x.
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
  dependent elimination H0; simpl.
  - dependent induction r;
    induction c; simpl.
    + rewrite <- SubExp_ScR.
      simp ScR.
      rewrite <- RcS_idSub.
      pose proof (SubExp_RcS (Keep σ) (Push (RenExp σ v) idSub) e) as H1.
      simp RcS in H1.
      rewrite H1.
      apply (StepRule Ctxt_nil).
      repeat econstructor.
      now apply RenExp_ValueP.
    + specialize (IHc e).
      admit.
  - inv c0.
    admit.
Admitted.

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

Lemma pluggable {Γ τ τ' n} {e e' : Exp Γ τ'} {C : Exp Γ τ' → Exp Γ τ} :
  ¬ ErrorP e' →
  e ---> e' →
  Ctxt Γ n C →
  C e ---> C e'.
Proof.
  intros.
  dependent elimination H1.
  - exact (StepRule (Ctxt_comp H2 c) r).
  - exfalso.
    now apply H0.
Qed.

Lemma APP_LAM_R {Γ dom cod} {f : Exp Γ (dom ⟶ cod)} {x x' : Exp Γ dom} :
  ¬ ErrorP x' →
  x ---> x' →
  APP f x ---> APP f x'.
Proof.
  intros.
  now eapply (pluggable H0 H1 ⦉ C_AppR _ ⦊); eauto.
Qed.

End Step.

Arguments C_AppL [A]%type_scope [H Γ] [dom]%Ty_scope [cod]%Ty_scope x.
Arguments C_AppR : default implicits.

Arguments Ctxt_nil {A}%type_scope {H Γ} {τ}%Ty_scope.
Arguments Ctxt_cons : default implicits.

Notation "⦉ e ; .. ; f ⦊" := (Ctxt_cons e .. (Ctxt_cons f Ctxt_nil) ..).

Notation "x ∷ xs" := (Ctxt_cons x xs) (at level 70).

Notation " t '--->' t' " := (Step t t') (at level 40).
