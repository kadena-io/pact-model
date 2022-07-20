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

Definition SemPrimType (ty : PrimType) : Type :=
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

Inductive ACap : Set :=
  | AToken (s : CapSig) : Cap s → ACap.

Derive NoConfusion NoConfusionHom Subterm EqDec for ACap.

Definition ACap_ext (ac : ACap) : { s : CapSig & Cap s } :=
  match ac with AToken s c => existT _ s c end.

Arguments Token {s} name arg val.

Context `{Monad m}.

Fixpoint concreteTy (τ : Ty) : ValueTy :=
  match τ with
  | ℤ            => TInteger
  | 𝔻            => TDecimal
  | 𝕋            => TTime
  | 𝔹            => TBool
  | 𝕊            => TString
  | 𝕌            => TUnit
  | TySym        => TSymbol
  | TyList t     => TList (concreteTy t)
  | TyPair t1 t2 => TPair (concreteTy t1) (concreteTy t2)
  | _            => TVoid
  end.

Arguments concreteTy τ /.

Fixpoint SemTy (τ : Ty) : Type :=
  match τ with
  | TyArrow dom cod => SemTy dom → m (SemTy cod)

  | TyCap p v =>
      Cap {| paramTy := concreteTy p; valueTy := concreteTy v |}

  (* Disallow functions and capabilities from appearing inside data
     structures. They may only be passed as arguments to functions, or
     returned from functions. *)
  | ty              => Value (concreteTy ty)
  end.

Notation "⟦ t ⟧" := (SemTy t) (at level 9) : type_scope.

#[export]
Program Instance Concrete_EqDec {t} (H : ConcreteP t) : EqDec ⟦t⟧.
Next Obligation.
  induction t;
  first [ now inv H0 | now apply Value_EqDec ].
Defined.

Equations concrete `(v : ⟦ t ⟧) : option (Value (concreteTy t)) :=
  concrete (t:=TyArrow _ _) v := None;
  concrete (t:=TyACap)      v := None;
  concrete (t:=TyCap _ _)   v := None;
  concrete                  v := Some v.

Equations concreteH `(v : ⟦ t ⟧) (C : ConcreteP t) : Value (concreteTy t) :=
  concreteH v PrimDecP       := v;
  concreteH v SymDecP        := v;
  concreteH v (ListDecP _)   := v;
  concreteH v (PairDecP _ _) := v.

Equations reflect `(v : Value (concreteTy t)) : ⟦ t ⟧ :=
  reflect (t:=TyPrim PrimInteger) v := v;
  reflect (t:=TyPrim PrimDecimal) v := v;
  reflect (t:=TyPrim PrimTime)    v := v;
  reflect (t:=TyPrim PrimBool)    v := v;
  reflect (t:=TyPrim PrimString)  v := v;
  reflect (t:=TyPrim PrimUnit)    v := v;
  reflect (t:=TySym)              v := v;
  reflect (t:=TyList _)           v := v;
  reflect (t:=TyPair _ _)         v := v.

Definition concreteH1 `{M :Monad m} `(f : ⟦ dom ⟶ cod ⟧) (CC : ConcreteP cod) :
  Value (concreteTy dom) → m (Value (concreteTy cod)) :=
  λ x, r <- f (reflect x) ;
       pure (concreteH r CC).

End SemTy.

Arguments Token {s} name arg val.

Notation "⟦ t ⟧" := (SemTy t) (at level 9) : type_scope.
