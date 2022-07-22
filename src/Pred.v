Require Import
  Coq.ZArith.ZArith
  Hask.Control.Monad
  Hask.Data.Either
  Pact.ilist
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Value
  Pact.Ren
  Pact.Sub
  Pact.SemTy
  Pact.Lang
  Pact.Lang.Capability
  Pact.SemExp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

(* This encodes a boolean predicate in positive normal form. *)
Inductive Pred Γ : ∀ {τ}, Γ ⊢ τ → Set :=
  | P_True : Pred (Γ:=Γ) (Lit (LitBool true))
  | P_Or {τ} {x y : Γ ⊢ τ} : Pred x → Pred y → Pred (Pair x y)
  | P_And {τ} {x y : Γ ⊢ τ} : Pred x → Pred y → Pred (Pair x y)

  | P_Car {τ} {xs : Γ ⊢ (TyList τ)} :
    Pred xs → Pred (Car xs)
.

#[export] Hint Constructors Pred : core.

Theorem total `(e : Γ ⊢ τ) (se : SemEnv Γ) :
  ∃ P : Pred e, ∃ x, ⟦ se ⊨ e ⟧ = pure x.
Proof.
  induction e.
Abort.
(*
  - kick.
      sauto.
    reflexivity.
  - kick.
      sauto.
    reflexivity.
  - kick.
    rewrite H H0 /=.
*)
