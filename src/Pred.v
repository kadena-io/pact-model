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

Section Pred.

Definition env   : Type := PactEnv.
Definition state : Type := PactState.
Definition log   : Type := PactLog.

(* Definition EvalP (r : env) (s : state) `(e : Exp [] τ) *)
(*   (s' : state) (v : SemTy τ) (er : Err) : Prop := *)

Implicit Type G : env → Prop.
Implicit Type H : state → Prop.
Implicit Type Z : Err → Prop.

Definition hoare
  (G : env → Prop)
  (H : state → Prop)
  `(e : Exp [] τ)
  (Q : ⟦τ⟧ → state → Prop)
  (Y : log → Prop)
  (Z : Err → Prop) : Prop :=
  ∀ (r : env), G r →
  ∀ (s : state), H s ->
  match ⟦e⟧ r s : Err + ⟦τ⟧ * (state * log) with
  | inr (v, (s', w)) => Q v s' ∧ Y w
  | inl err => Z err
  end.

Notation "{ G & H } x ← e { Q & Y | Z }" :=
  (hoare G H e (λ x, Q) Y Z) (at level 1, e at next level).

#[local] Hint Unfold hoare : core.

Theorem hoare_post_true G H `(Q : ⟦τ⟧ → state → Prop) (Y : log → Prop) Z e :
  (∀ v s, Q v s) →
  (∀ l, Y l) →
  (∀ err, Z err) →
  { G & H } x ← e { Q x & Y | Z }.
Proof.
  unfold hoare; sauto.
Qed.

Theorem hoare_pre_false G H `(Q : ⟦τ⟧ → state → Prop) (Y : log → Prop) Z e :
  (∀ r, ¬ (G r)) ∨ (∀ s, ¬ (H s)) →
  { G & H } x ← e { Q x & Y | Z }.
Proof.
  unfold hoare; sauto.
Qed.

Definition hprop_conj `(Q : state → Prop) (H : state → Prop) : state → Prop :=
  λ st, Q st ∧ H st.

Notation "Q \∧ H" := (hprop_conj Q H) (at level 10).

Definition quadruple
  (G : env → Prop)
  (H : state → Prop)
  `(e : Exp [] τ)
  (Q : ⟦τ⟧ → state → Prop)
  (Y : log → Prop)
  (Z : Err → Prop) : Prop :=
  ∀ H', { G & H \∧ H' } x ← e { Q x \∧ H' & Y | Z }.

(* This encodes a boolean predicate in positive normal form. *)
Inductive Pred Γ : ∀ {τ}, Γ ⊢ τ → Set :=
  | P_True : Pred (Γ:=Γ) (Lit (LitBool true))
  | P_Or {τ} {x y : Γ ⊢ τ} : Pred x → Pred y → Pred (Pair x y)
  | P_And {τ} {x y : Γ ⊢ τ} : Pred x → Pred y → Pred (Pair x y)

  | P_APP {dom cod} {e1 : Γ ⊢ (dom ⟶ cod)} {e2 : Γ ⊢ dom} :
    Pred e1 → Pred e2 → Pred (APP e1 e2)

  | P_Car {τ} {xs : Γ ⊢ (TyList τ)} :
    Pred xs → Pred (Car xs).

#[local] Hint Constructors Pred : core.

Inductive EnvPred : ∀ {Γ}, SemEnv Γ → Type :=
  | Empty : EnvPred (Γ:=[]) tt
  | Add {Γ τ} {e : Γ ⊢ τ} v se :
    Pred e → ⟦ se ⊨ e⟧ = pure v → EnvPred se →
    EnvPred (Γ:=τ :: Γ) (v, se).

End Pred.
