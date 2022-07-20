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
  Sub.

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
  | TyACapList      => list ACap
  | TyCap p v       => Cap {| paramTy := concreteTy p; valueTy := concreteTy v |}
  end.

Notation "⟦ t ⟧" := (SemTy t) (at level 9) : type_scope.

Equations concrete `(v : ⟦ t ⟧) (C : ConcreteP t) : Value (concreteTy t) :=
  concrete (t:=𝕌)     v PrimDecP := VUnit;
  concrete (t:=ℤ)     v PrimDecP := VInteger v;
  concrete (t:=𝔻)     v PrimDecP := VDecimal v;
  concrete (t:=𝕋)     v PrimDecP := VTime v;
  concrete (t:=𝔹)     v PrimDecP := VBool v;
  concrete (t:=𝕊)     v PrimDecP := VString v;
  concrete (t:=TySym) v SymDecP  := VSymbol v;

  concrete (t:=TyList _) [] (ListDecP H) := VList [];
  concrete (t:=TyList _) xs (ListDecP H) := VList (map (λ x, concrete x H) xs);

  concrete (t:=TyPair _ _) (x, y) (PairDecP Hx Hy) :=
    VPair (concrete x Hx) (concrete y Hy).

Equations reflect `(v : Value (concreteTy t)) : ⟦ t ⟧ :=
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
