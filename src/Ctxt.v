Require Export
  Ty
  Coq.Lists.List
  Exp
  Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

(** Evaluation contexts *)

Section Ctxt.

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

(*
Equations Plug {Γ τ' τ} (e : Exp Γ τ') (c : Ctxt Γ τ' τ) : Exp Γ τ :=
  Plug e (C_Hole _ _)      := e;
  Plug e (C_App1 _ _ C e1) := APP (Plug e C) e1;
  Plug e (C_App2 _ _ e1 C) := APP e1 (Plug e C).
*)

Inductive Plug {Γ τ'} : ∀ {τ}, Exp Γ τ' → Ctxt Γ τ' τ → Exp Γ τ → Prop :=
  | Plug_Hole (e : Exp Γ τ') : Plug e (C_Hole _ _) e

  (* | Plug_If1 {Γ τ} (C : Ctxt Γ TyBool) (e e' : Exp Γ TyBool) (e1 e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If1 _ C e1 e2) e (If e' e1 e2) *)
  (* | Plug_If2 {Γ τ} (C : Ctxt Γ τ) (e e' : Exp Γ τ) e1 (e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If2 _ e1 C e2) e (If e1 e' e2) *)
  (* | Plug_If3 {Γ τ} (C : Ctxt Γ τ) (e e' : Exp Γ τ) e1 (e2 : Exp Γ τ) : *)
  (*   Plug C e e' → Plug (C_If3 _ e1 e2 C) e (If e1 e2 e') *)

  | Plug_App1 {dom cod} {C : Ctxt Γ τ' (dom ⟶ cod)}
              {e : Exp Γ τ'} {e' : Exp Γ (dom ⟶ cod)}
              {e1 : Exp Γ dom} :
    Plug e C e' →
    Plug e (C_App1 _ _ C e1) (APP e' e1)
  | Plug_App2 {dom cod} {C : Ctxt Γ τ' dom}
              {e : Exp Γ τ'} {e' : Exp Γ dom}
              {e1 : Exp Γ (dom ⟶ cod)} :
    ValueP e1 →
    Plug e C e' →
    Plug e (C_App2 _ _ e1 C) (APP e1 e').

Derive Signature for Plug.

Inductive Redex {Γ} : ∀ {τ}, Exp Γ τ → Exp Γ τ → Prop :=
  | ST_AppAbs0 {dom cod} (e : Exp (dom :: Γ) cod) v :
    ValueP v →
    Redex (APP (LAM e) v) (SubExp {|| v ||} e).

Derive Signature for Redex.

Reserved Notation " t '--->' t' " (at level 40).

Inductive Step : ∀ {Γ τ}, Exp Γ τ → Exp Γ τ → Prop :=
  | StepRule {Γ τ' τ} {C : Ctxt Γ τ' τ}
             {e1 e2 : Exp Γ τ'} {e1' e2' : Exp Γ τ} :
    Plug e1 C e1' →
    Plug e2 C e2' →
    Redex e1 e2 →
    e1' ---> e2'

  where " t '--->' t' " := (Step t t').

Derive Signature for Step.

#[local] Hint Constructors ValueP Plug Redex Step : core.

Theorem strong_progress {τ} (e : Exp [] τ) :
  ValueP e ∨ ∃ e', e ---> e'.
Proof.
  dependent induction e; reduce.
  - now inv v.
  - now left; constructor.
  - right.
    destruct IHe1 as [V1|[e1' H1']];
    destruct IHe2 as [V2|[e2' H2']].
    + dependent elimination V1.
      now eauto 6.
    + dependent elimination H2'.
      now eauto 6.
    + dependent elimination H1'.
      now eauto 6.
    + dependent elimination H1'.
      dependent elimination H2'.
      now eauto 6.
Qed.

Lemma Plug_not_ValueP {Γ τ} {C : Ctxt Γ τ τ} (e v : Exp Γ τ) :
  ValueP v →
  Plug e C v →
    C = C_Hole _ _ ∧ e = v.
Proof.
  intros.
  dependent elimination H0.
  now inv H1.
Qed.

Lemma Redex_ValueP {Γ τ} (e v : Exp Γ τ) :
  ValueP v →
    ¬ Redex v e.
Proof.
  repeat intro.
  dependent elimination H0.
  now inv H1.
Qed.

Lemma Plug_deterministic {Γ τ τ'} {C : Ctxt Γ τ' τ} e2 :
  ∀ e1 e1', Redex e1 e1' →
  ∀ τ'' f1 f1', Redex f1 f1' →
  Plug e1 C e2 →
    ∀ (C' : Ctxt Γ τ'' τ),
      Plug f1 C' e2 →
      τ' = τ'' ∧ C ~= C' ∧ e1 ~= f1.
Proof.
  intros.
  generalize dependent C'.
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
      now destruct (H3 _ p); reduce.
    + exfalso.
      dependent elimination H0.
      dependent elimination H1.
      now inv H2.
  - dependent elimination H4.
    + exfalso.
      dependent elimination H0.
      dependent elimination H1.
      now inv H3.
    + exfalso.
      dependent elimination H0.
      dependent elimination H1.
      now inv p.
    + intuition.
      now destruct (H4 _ p0); reduce.
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
  - dependent destruction H2.
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

End Ctxt.

Notation " t '--->' t' " := (Step t t') (at level 40).
