Require Import
  Lib
  Ty
  Exp.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Value.

Import ListNotations.

Context {A : Type}.
Context `{HostExprs A}.

Open Scope Ty_scope.

(* [ValueP] is an inductive proposition that indicates whether an expression
   represents a value, i.e., that it does reduce any further. *)
Inductive ValueP Γ : ∀ {τ}, Exp Γ τ → Prop :=
  (* | HostedValP {ty} (x : HostExp (TyHost ty)) : ValueP Γ (HostedVal x) *)
  (* | HostedFunP {dom cod} (f : HostExp (dom ⟶ cod)) : ValueP Γ (HostedFun f) *)
  (* | ErrorP {τ} m : ValueP Γ (Error (τ:=τ) m) *)
  (* | UnitP        : ValueP Γ EUnit *)
  (* | TrueP        : ValueP Γ ETrue *)
  (* | FalseP       : ValueP Γ EFalse *)
  (* | PairP {τ1 τ2} {x : Exp Γ τ1} {y : Exp Γ τ2} : *)
  (*   ValueP Γ x → ValueP Γ y → ValueP Γ (Pair x y) *)
  (* | NilP {τ} : ValueP Γ (Nil (τ:=τ)) *)
  (* | ConsP {τ} (x : Exp Γ τ) xs : *)
  (*   ValueP Γ x → ValueP Γ xs → ValueP Γ (Cons x xs) *)
  | LambdaP {dom cod} (e : Exp (dom :: Γ) cod) : ValueP Γ (LAM e).

Derive Signature for ValueP.

Lemma ValueP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ValueP _ v) :
  H1 = H2.
Proof.
  dependent elimination H1.
  dependent elimination H2.
  reflexivity.
Qed.

Inductive ErrorP Γ : ∀ {τ}, Exp Γ τ → Prop :=
  | IsError {τ} m : ErrorP Γ (Error (τ:=τ) m).

Derive Signature for ErrorP.

Lemma ErrorP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ErrorP _ v) :
  H1 = H2.
Proof.
  dependent elimination H1.
  dependent elimination H2.
  reflexivity.
Qed.

End Value.

Arguments ValueP {A H Γ τ} _.
(* Arguments HostedValP {A H Γ ty} _. *)
(* Arguments HostedFunP {A H Γ dom cod} _. *)
(* Arguments ErrorP {A H Γ τ} _. *)
(* Arguments TrueP {A H Γ}. *)
(* Arguments FalseP {A H Γ}. *)
(* Arguments PairP {A H Γ τ1 τ2 x y} _ _. *)
(* Arguments NilP {A H Γ τ}. *)
(* Arguments ConsP {A H Γ τ _ _} _ _. *)
Arguments LambdaP {A H Γ dom cod} _.

Arguments ErrorP {A H Γ τ} _.
