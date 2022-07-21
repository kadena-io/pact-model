Require Import
  Coq.ZArith.ZArith
  Hask.Control.Monad
  Hask.Data.Either
  Hask.Data.Maybe
  ilist
  Lib
  Ty
  Exp
  Value
  Ren
  Sub
  Pact.CapabilityType.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section SemTy.

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

Context `{Monad m}.

Fixpoint SemTy (τ : Ty) : Type :=
  match τ with
  | TyArrow dom cod => SemTy dom → m (SemTy cod)

  | TyPrim p        => SemPrimTy p
  | TySym           => string

  | TyList t        => list (SemTy t)
  | TyPair t1 t2    => SemTy t1 * SemTy t2

  (* These types are used by capabilities. *)
  | TyCap p v       => Cap {| paramTy := reifyTy p; valueTy := reifyTy v |}
  end.

Notation "⟦ t ⟧" := (SemTy t) (at level 9) : type_scope.

Lemma reflectTy_reifyTy {τ} :
  ConcreteP τ → reflectTy (reifyTy τ) = ⟦τ⟧.
Proof.
  induction τ; simpl in *; intros; auto.
  - inv H0.
  - now destruct p.
  - inv H0.
    f_equal.
    now apply IHτ.
  - inv H0.
    f_equal.
    + now apply IHτ1.
    + now apply IHτ2.
  - inv H0.
Qed.

#[export]
Program Instance SemPrimTy_EqDec {ty} : EqDec (SemPrimTy ty).
Next Obligation.
  induction ty; simpl in x, y.
  - destruct x, y.
    now left.
  - apply Z_EqDec.
  - apply N_EqDec.
  - apply nat_EqDec.
  - apply bool_EqDec.
  - apply string_EqDec.
Defined.

#[export]
Program Instance Concrete_EqDec {t} (H : ConcreteP t) : EqDec ⟦t⟧.
Next Obligation.
  induction H0;
  try first [ now inv H0 | now apply Value_EqDec ];
  simpl in x, y.
  - apply SemPrimTy_EqDec.
  - apply string_EqDec.
  - apply list_eqdec.
    fold SemTy.
    unfold EqDec.
    apply IHConcreteP.
  - destruct x, y.
    destruct (IHConcreteP1 s s1); subst.
    + destruct (IHConcreteP2 s0 s2); subst.
      * now left.
      * right; intro; now inv H0.
    + right; intro; now inv H0.
Defined.

End SemTy.

Arguments Token {s} name arg val.

Notation "⟦ t ⟧" := (SemTy t) (at level 9) : type_scope.
