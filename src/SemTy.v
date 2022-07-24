Require Import
  Coq.ZArith.ZArith
  Hask.Control.Monad
  Hask.Data.Either
  Hask.Data.Maybe
  Pact.ilist
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Value
  Pact.Ren
  Pact.Sub
  Pact.Lang.CapabilityType.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Definition SemPrimTy (ty : PrimType) : Type :=
  match ty with
  | PrimUnit    => unit
  | PrimInteger => Z
  | PrimDecimal => N
  | PrimTime    => nat
  | PrimBool    => bool
  | PrimString  => string
  end.

#[export]
Program Instance SemPrimTy_EqDec {ty} : EqDec (SemPrimTy ty).
Next Obligation.
  induction ty; auto; sauto.
Defined.

Section SemTy.

Context {m : Type → Type}.

Fixpoint SemTy (τ : Ty) : Type :=
  match τ with
  | TyArrow dom cod => SemTy dom → m (SemTy cod)

  | TyPrim p        => SemPrimTy p
  | TySym           => string

  | TyList t        => list (SemTy t)
  | TyPair t1 t2    => SemTy t1 * SemTy t2

  (** Capabilities *)
  | TyCap p v       => Cap {| paramTy := reifyTy p; valueTy := reifyTy v |}
  end.

Lemma reflectTy_reifyTy {τ} :
  ConcreteP τ → reflectTy (reifyTy τ) = SemTy τ.
Proof.
  induction τ; sauto.
Qed.

#[export]
Program Instance Concrete_EqDec {t} (H : ConcreteP t) : EqDec (SemTy t).
Next Obligation.
  generalize dependent y.
  generalize dependent x.
  induction t; simpl; intros; auto.
  - sauto.
  - apply SemPrimTy_EqDec.
  - apply list_eqdec.
    unfold EqDec.
    apply IHt; sauto.
  - reduce.
    assert (ConcreteP t1 ∧ ConcreteP t2) as H0 by sauto.
    destruct (IHt1 (proj1 H0) s1 s).
    + destruct (IHt2 (proj2 H0) s2 s0); sauto.
    + sauto.
  - sauto.
Defined.

End SemTy.

Notation "⟦ t ⟧" := (SemTy t) (at level 9) : type_scope.
