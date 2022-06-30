Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List
  Ty
  Exp
  Ren
  Sub
  Sem
  Lang.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Section Pact.

(** Pact syntax *)

Inductive PactTy : Type :=
  | TUnit : PactTy
  | TList : Ty PactTy → PactTy.

Inductive PactExpr Γ : Ty PactTy → Type :=
  | Unit : PactExpr Γ (TYP TUnit)
  | Nil {τ} : PactExpr Γ (TYP (TList τ))
  | Cons {τ} : Exp PactTy PactExpr Γ τ →
               Exp PactTy PactExpr Γ (TYP (TList τ)) →
               PactExpr Γ (TYP (TList τ)).

Arguments Unit {Γ}.
Arguments Nil {Γ τ}.
Arguments Cons {Γ τ} _ _.

Fixpoint PactRen {Γ Γ' τ} (r : Ren Γ Γ') (p : PactExpr Γ τ) : PactExpr Γ' τ :=
  match p with
  | Unit => Unit
  | Nil => Nil
  | @Cons _ τ x xs =>
    Cons (@RTmExp _ _ (@PactRen) Γ Γ' _ r x)
         (RTmExp (ren:=@PactRen) r xs)
  end.

Fixpoint PactSub {Γ Γ' τ} (r : Sub Γ Γ') (p : PactExpr Γ τ) : PactExpr Γ' τ :=
  match p with
  | Unit => Unit
  | Nil => Nil
  | @Cons _ τ x xs =>
    Cons (@STmExp _ _ (@PactRen) (@PactSub) Γ Γ' _ r x)
         (STmExp (ren:=@PactRen) (sub:=@PactSub) r xs)
  end.

(** Pact evaluation *)

Inductive PactEval : ∀ {τ}, PactExpr [] τ → Exp PactTy PactExpr [] τ → Prop :=
  | EvUnit : PactEval (@Unit []) (TERM (@Unit []))
  | EvNil {τ} : PactEval (@Nil _ τ) (TERM (@Nil _ τ))
  | EvCons {τ} (x : PactExpr [] τ) x' (xs : PactExpr [] (TYP (TList τ))) xs' :
    PactEval x x' →
    PactEval xs xs' →
    PactEval (Cons (TERM x) (TERM xs)) (TERM (Cons x' xs')).

(** Pact semantics *)

Fixpoint SemPactTy (t : PactTy) : Type :=
  match t with
  | TUnit => unit
  | TList y => list (SemTy SemPactTy y)
  end.

Fixpoint SemPactExpr {Γ τ} (r : PactExpr Γ τ)
         (E : SemEnv SemPactTy Γ) : SemTy SemPactTy τ :=
  match r with
  | Unit => tt
  | Nil => []
  | Cons x xs =>
    SemExp SemPactTy (@SemPactExpr) x E :: SemExp SemPactTy (@SemPactExpr) xs E
  end.

#[export]
Program Instance Pact_Lang : Lang PactTy PactExpr := {
  ren  := @PactRen;
  sub  := @PactSub;
  eval := @PactEval;
  SemT := SemPactTy;
  SemX := @SemPactExpr;
}.
Next Obligation.
  induction z; simpl; auto.
  now rewrite !H.
Qed.
Next Obligation.
  induction z; simpl; auto.
  now rewrite !H.
Qed.
Next Obligation.
  induction H; simpl; auto.
  extensionality E.
  now rewrite IHPactEval1, IHPactEval2.
Qed.

End Pact.
