Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List
  Ty
  Exp
  Sub
  Sem.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Section Pact.

Inductive PactTy : Type :=
  | TUnit : PactTy
  | TList : Ty PactTy → PactTy.

Inductive PactExpr : Ty PactTy → Type :=
  | Unit : PactExpr (TYP TUnit)
  | Nil {τ} : PactExpr (TYP (TList τ))
  | Cons {τ} : PactExpr τ → PactExpr (TYP (TList τ)) → PactExpr (TYP (TList τ)).

Fixpoint SemPactTy (t : PactTy) : Type :=
  match t with
  | TUnit => unit
  | TList y => list (SemTy SemPactTy y)
  end.

Fixpoint SemPactExpr {Γ τ} (r : PactExpr τ)
         (E : SemEnv SemPactTy Γ) : SemTy SemPactTy τ :=
  match r with
  | Unit => tt
  | Nil => []
  | Cons x xs => SemPactExpr x E :: SemPactExpr xs E
  end.

#[export]
Program Instance Pact_Sem : Sem PactTy PactExpr := {
  SemT := SemPactTy;
  SemX := @SemPactExpr
}.
Next Obligation.
  induction z; simpl; auto.
  now rewrite IHz1, IHz2.
Qed.
Next Obligation.
  induction z; simpl; auto.
  now rewrite IHz1, IHz2.
Qed.

End Pact.
