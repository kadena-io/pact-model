Require Import
  Coq.ZArith.ZArith
  Hask.Control.Monad
  Hask.Data.Either
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

Definition SemPrimType (ty : PrimType) : Set :=
  match ty with
  | PrimInteger => Z
  | PrimDecimal => N
  | PrimTime    => nat
  | PrimBool    => bool
  | PrimString  => string
  | PrimUnit    => unit
  end.

Record CapSig : Set := {
  paramTy : ValueTy;
  valueTy : ValueTy;
}.

Derive NoConfusion NoConfusionHom Subterm EqDec for CapSig.

Inductive Cap (s : CapSig) : Set :=
  | Token (name : string) : Value (paramTy s) → Value (valueTy s) → Cap s.

Derive NoConfusion NoConfusionHom Subterm EqDec for Cap.

Arguments Token {s} name arg val.

Definition nameOf `(c : Cap s) : string :=
  match c with Token n _ _ => n end.

Definition paramOf `(c : Cap s) : Value (paramTy s) :=
  match c with Token _ p _ => p end.

Definition valueOf `(c : Cap s) : Value (valueTy s) :=
  match c with Token _ _ v => v end.

Context `{Monad m}.

Fixpoint SemTy (τ : Ty) : Type :=
  match τ with
  | TyArrow dom cod => SemTy dom → m (SemTy cod)

  | TyPrim ty       => SemPrimType ty
  | TySym           => string
  | TyList τ        => list (SemTy τ)
  | TyPair t1 t2    => SemTy t1 * SemTy t2

  | TyCap p v       => Cap {| paramTy := concreteTy p
                            ; valueTy := concreteTy v |}
  end.

Notation "⟦ t ⟧" := (SemTy t) (at level 9) : type_scope.

Equations concrete {τ} (H : ConcreteP τ) (e : ⟦τ⟧) : Value (concreteTy τ) :=
  concrete (τ:=ℤ)        PrimDecP     lit := VInteger lit;
  concrete (τ:=𝔻)        PrimDecP     lit := VDecimal lit;
  concrete (τ:=𝕋)        PrimDecP     lit := VTime lit;
  concrete (τ:=𝔹)        PrimDecP     lit := VBool lit;
  concrete (τ:=𝕊)        PrimDecP     lit := VString lit;
  concrete (τ:=𝕌)        PrimDecP     tt  := VUnit;
  concrete (τ:=TySym)    SymDecP      sym := VSymbol sym;
  concrete (τ:=TyList t) (ListDecP H) xs  := VList (map (concrete H) xs);
  concrete (τ:=TyPair t1 t2) (PairDecP Hx Hy) (x, y) :=
    VPair (concrete Hx x) (concrete Hy y).

Equations Concrete_EqDec {t} (H : ConcreteP t) : EqDec ⟦t⟧ :=
  Concrete_EqDec (t:=TyPrim PrimUnit) _ tt tt := left _;
  Concrete_EqDec (t:=TyPrim PrimString) _ s1 s2
    with eq_dec s1 s2 := {
      | left _  => left _
      | right _ => right _
    };
  Concrete_EqDec (t:=TyPrim PrimInteger) _ i1 i2
    with eq_dec i1 i2 := {
      | left _  => left _
      | right _ => right _
    };
  Concrete_EqDec (t:=TyPrim PrimDecimal) _ d1 d2
    with eq_dec d1 d2 := {
      | left _  => left _
      | right _ => right _
    };
  Concrete_EqDec (t:=TyPrim PrimBool) _ b1 b2
    with eq_dec b1 b2 := {
      | left _  => left _
      | right _ => right _
    };
  Concrete_EqDec (t:=TyPrim PrimTime) _ t1 t2
    with eq_dec t1 t2 := {
      | left _  => left _
      | right _ => right _
    };

  Concrete_EqDec (t:=TySym) _ n1 n2 := eq_dec n1 n2;

  Concrete_EqDec (t:=TyList _)  _ ([]) ([]) := left _;
  Concrete_EqDec (t:=TyList _)  _ (_ :: _) ([]) := right _;
  Concrete_EqDec (t:=TyList _)  _ ([]) (_ :: _) := right _;
  Concrete_EqDec (t:=TyList ty) (ListDecP H) (x1 :: xs1) (x2 :: xs2)
    with @eq_dec _ (Concrete_EqDec (t:=ty) H) x1 x2 := {
      | left _
        with @eq_dec _ (list_eqdec (Concrete_EqDec (t:=ty) H)) xs1 xs2 := {
        | left _  => left _
        | right _ => right _
      }
      | right _ => right _
    };

  Concrete_EqDec (t:=TyPair t1 t2) (PairDecP H1 H2) (x1, y1) (x2, y2)
    with @eq_dec _ (Concrete_EqDec (t:=t1) H1) x1 x2 := {
      | left  _ with @eq_dec _ (Concrete_EqDec (t:=t2) H2) y1 y2 := {
        | left _  => left _
        | right _ => right _
      }
      | right _ => right _
    }.

#[export]
Instance Concrete_EqDec' {t} : ConcreteP t → EqDec ⟦t⟧ :=
  Concrete_EqDec (t:=t).

Inductive Value t : Type :=
  | Bundle : ConcreteP t → ⟦t⟧ → Value t.

Derive NoConfusion NoConfusionHom Subterm EqDec for Value.
Next Obligation.
  destruct x, y.
  destruct (eq_dec c c0); subst.
  - destruct (@eq_dec _ (Concrete_EqDec c0) s s0); subst.
    + now left.
    + right; intro.
      now inv H0.
  - pose proof (ConcreteP_irrelevance c c0).
    contradiction.
Defined.

End SemTy.

Arguments Token {s} name arg val.

Notation "⟦ t ⟧" := (SemTy t) (at level 9) : type_scope.
