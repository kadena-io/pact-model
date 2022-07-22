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

Section SemTy.

Context {m : Type → Type}.

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
  induction τ; sauto.
Qed.

Equations reify `(v : ⟦ t ⟧) (C : ConcreteP t) : Value t :=
  reify (t:=𝕌)     v _ := VUnit;
  reify (t:=ℤ)     v _ := VInteger v;
  reify (t:=𝔻)     v _ := VDecimal v;
  reify (t:=𝕋)     v _ := VTime v;
  reify (t:=𝔹)     v _ := VBool v;
  reify (t:=𝕊)     v _ := VString v;
  reify (t:=TySym) v _ := VSymbol v;

  reify (t:=TyList _) [] _ := VList [];
  reify (t:=TyList _) xs _ :=
    VList (map (λ x, reify x ltac:(inversion C)) xs);

  reify (t:=TyPair _ _) (x, y) C :=
    VPair (reify x ltac:(inversion C))
          (reify y ltac:(inversion C)).

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
  induction ty; auto; sauto.
Defined.

End SemTy.

Notation "⟦ t ⟧" := (SemTy t) (at level 9) : type_scope.
