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

Inductive Ctxt Γ : Ty → Type :=
  | C_Hole {τ} : Ctxt Γ τ

  (* | C_If1 {τ} : Ctxt Γ TyBool → Exp Γ τ → Exp Γ τ → Ctxt Γ TyBool *)
  (* | C_If2 {τ} : Exp Γ TyBool → Ctxt Γ τ → Exp Γ τ → Ctxt Γ τ *)
  (* | C_If3 {τ} : Exp Γ TyBool → Exp Γ τ → Ctxt Γ τ → Ctxt Γ τ *)

  | C_App1 {dom cod} : Ctxt Γ (dom ⟶ cod) -> Exp Γ dom -> Ctxt Γ (dom ⟶ cod)
  | C_App2 {dom cod} : Exp Γ (dom ⟶ cod) -> Ctxt Γ dom -> Ctxt Γ dom.

Derive Signature NoConfusion NoConfusionHom for Ctxt.

Inductive Plug : ∀ {Γ τ τ'}, Ctxt Γ τ → Exp Γ τ → Exp Γ τ' → Prop :=
  | Plug_Hole {Γ τ} (e : Exp Γ τ) : Plug (C_Hole _) e e

  (* | Plug_If1 {Γ τ} (C : Ctxt Γ TyBool) (e e' : Exp Γ TyBool) (e1 e2 : Exp Γ τ) : *)
  (*   Plug C e e' -> Plug (C_If1 _ C e1 e2) e (If e' e1 e2) *)
  (* | Plug_If2 {Γ τ} (C : Ctxt Γ τ) (e e' : Exp Γ τ) e1 (e2 : Exp Γ τ) : *)
  (*   Plug C e e' -> Plug (C_If2 _ e1 C e2) e (If e1 e' e2) *)
  (* | Plug_If3 {Γ τ} (C : Ctxt Γ τ) (e e' : Exp Γ τ) e1 (e2 : Exp Γ τ) : *)
  (*   Plug C e e' -> Plug (C_If3 _ e1 e2 C) e (If e1 e2 e') *)

  | Plug_App1 {Γ dom cod} (C : Ctxt Γ (dom ⟶ cod)) (e e' : Exp Γ (dom ⟶ cod))
              (e1 : Exp Γ dom) :
    Plug C e e' -> Plug (C_App1 _ C e1) e (APP e' e1)
  | Plug_App2 {Γ dom cod} (C : Ctxt Γ dom) (e e' : Exp Γ dom)
              (e1 : Exp Γ (dom ⟶ cod)) :
    Plug C e e' -> Plug (C_App2 _ e1 C) e (APP e1 e').

Derive Signature for Plug.

Inductive Step0 : ∀ {Γ τ}, Exp Γ τ -> Exp Γ τ -> Prop :=
  | ST_AppAbs0 {Γ dom cod} (e : Exp (dom :: Γ) cod) v :
    ValueP v -> Step0 (APP (LAM e) v) (SubExp {|| v ||} e).

Derive Signature for Step0.

Inductive Step : ∀ {Γ τ}, Exp Γ τ -> Exp Γ τ -> Prop :=
  | StepRule {Γ τ} (C : Ctxt Γ τ) (e1 e1' e2 e2' : Exp Γ τ) :
    Plug C e1 e1' ->
    Plug C e2 e2' ->
    Step0 e1 e2 ->
    Step e1' e2'.

Derive Signature for Step.

End Ctxt.
