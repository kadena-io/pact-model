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

Equations reify `(v : ⟦ t ⟧) (C : ConcreteP t) : Value t :=
  reify (t:=𝕌)     v _ := VUnit;
  reify (t:=ℤ)     v _ := VInteger v;
  reify (t:=𝔻)     v _ := VDecimal v;
  reify (t:=𝕋)     v _ := VTime v;
  reify (t:=𝔹)     v _ := VBool v;
  reify (t:=𝕊)     v _ := VString v;
  reify (t:=TySym) v _  := VSymbol v;

  reify (t:=TyList _) [] _ := VList [];
  reify (t:=TyList _) xs _ := VList (map (λ x, reify x _) xs);

  reify (t:=TyPair _ _) (x, y) _ :=
    VPair (reify x _) (reify y _).
Next Obligation. now inv C. Qed.
Next Obligation. now inv C. Qed.
Next Obligation. now inv C. Qed.

Equations reflect `(v : Value t) : ⟦ t ⟧ :=
  reflect (t:=TyPrim PrimUnit)    VUnit        := tt;
  reflect (t:=TyPrim PrimInteger) (VInteger v) := v;
  reflect (t:=TyPrim PrimDecimal) (VDecimal v) := v;
  reflect (t:=TyPrim PrimTime)    (VTime v)    := v;
  reflect (t:=TyPrim PrimBool)    (VBool v)    := v;
  reflect (t:=TyPrim PrimString)  (VString v)  := v;
  reflect (t:=TySym)              (VSymbol v)  := v;
  reflect (t:=TyList _)           (VList vs)   := map reflect vs;
  reflect (t:=TyPair _ _)         (VPair x y)  := (reflect x, reflect y).

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

End SemTy.

Arguments Token {s} name arg val.

Notation "⟦ t ⟧" := (SemTy t) (at level 9) : type_scope.
