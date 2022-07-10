Require Export
  Ty
  Exp.

From Equations Require Import Equations.

Generalizable All Variables.

Section Value.

Import ListNotations.

Context {A : Type}.
Context `{HostExprs A}.

Open Scope Ty_scope.

(* [ValueP] is an inductive proposition that indicates whether an expression
   represents a value, i.e., that it does reduce any further. *)
Inductive ValueP Γ : ∀ {τ}, Exp Γ τ → Type :=
  | HostedValP {ty} (x : HostExp (TyHost ty)) : ValueP Γ (HostedVal x)
  | HostedFunP {dom cod} (f : HostExp (dom ⟶ cod)) : ValueP Γ (HostedFun f)
  | UnitP : ValueP Γ EUnit
  | TrueP : ValueP Γ ETrue
  | FalseP : ValueP Γ EFalse
  | PairP {τ1 τ2} {x : Exp Γ τ1} {y : Exp Γ τ2} :
    ValueP Γ x → ValueP Γ y → ValueP Γ (Pair x y)
  | NilP {τ} : ValueP Γ (Nil (τ:=τ))
  | ConsP {τ} (x : Exp Γ τ) xs :
    ValueP Γ x → ValueP Γ xs → ValueP Γ (Cons x xs)
  | LambdaP {dom cod} (e : Exp (dom :: Γ) cod) : ValueP Γ (LAM e).

Derive Signature NoConfusion NoConfusionHom for ValueP.

Lemma ValueP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ValueP _ v) :
  H1 = H2.
Proof.
  induction H1; dependent elimination H2; auto.
  - now erewrite IHValueP1, IHValueP2; eauto.
  - now erewrite IHValueP1, IHValueP2; eauto.
Qed.

Inductive Value : Ty → Type :=
  | HostValue {ty}         : HostExp (TyHost ty) → Value (TyHost ty)
  | VUnit                  : Value TyUnit
  | VTrue                  : Value TyBool
  | VFalse                 : Value TyBool
  | VPair {τ1 τ2}          : Value τ1 → Value τ2 → Value (TyPair τ1 τ2)
  | VNil {τ}               : Value (TyList τ)
  | VCons {τ}              : Value τ → Value (TyList τ) → Value (TyList τ)
  | ClosureExp {dom cod}   : Closure dom cod → Value (dom ⟶ cod)

with Closure : Ty → Ty → Type :=
  | Lambda {dom cod}   : Exp [dom] cod → Closure dom cod
  | Func {dom cod}     : HostExp (dom ⟶ cod) → Closure dom cod.

Derive Signature NoConfusion NoConfusionHom for Value.
Derive Signature NoConfusion NoConfusionHom Subterm for Closure.

Inductive ValEnv : Env → Type :=
  | Empty : ValEnv []
  | Val {Γ τ} : Value τ → ValEnv Γ → ValEnv (τ :: Γ).

Derive Signature NoConfusion NoConfusionHom for ValEnv.

Equations get_value `(s : ValEnv Γ) `(v : Var Γ τ) : Value τ :=
  get_value (Val x _)  ZV     := x;
  get_value (Val _ xs) (SV v) := get_value xs v.

End Value.

Arguments ValueP {A H Γ τ} _.
Arguments HostedValP {A H Γ ty} _.
Arguments HostedFunP {A H Γ dom cod} _.
Arguments TrueP {A H Γ}.
Arguments FalseP {A H Γ}.
Arguments PairP {A H Γ τ1 τ2 x y} _ _.
Arguments NilP {A H Γ τ}.
Arguments ConsP {A H Γ τ _ _} _ _.
Arguments LambdaP {A H Γ dom cod} _.
