Require Import
  Coq.ZArith.ZArith
  Pact.Lib
  Pact.Ty
  Pact.Exp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Open Scope Ty_scope.

Unset Elimination Schemes.

(* [ValueP] is an inductive proposition that indicates whether an expression
   represents a value, i.e., that it does reduce any further. *)
Inductive ValueP Γ : ∀ {τ}, Exp Γ τ → Prop :=
  | LambdaP {dom cod} (e : Exp (dom :: Γ) cod) : ValueP (LAM e)
  | LiteralP {ty l} : ValueP (Lit (ty:=ty) l)
  | BuiltinP {τ b} : ValueP (Bltn (τ:=τ) b)
  | SymbolP {n} : ValueP (Symbol n)
  | PairP {τ1 τ2} {x : Exp Γ τ1} {y : Exp Γ τ2} :
    ValueP x → ValueP y → ValueP (Pair x y)
  | NilP {τ} : ValueP (Nil (τ:=τ))
  | ConsP {τ} (x : Exp Γ τ) xs :
    ValueP x → ValueP xs → ValueP (Cons x xs)
  | CapabilityP {tp tv} (s : Exp Γ TySym)
                (Hp : ConcreteP tp) (Hv : ConcreteP tv)
                {p : Exp Γ tp} {v : Exp Γ tv} :
    ValueP s → ValueP p → ValueP v →
    ValueP (Capability Hp Hv s p v).

Derive Signature for ValueP.

Inductive ErrorP Γ : ∀ {τ}, Exp Γ τ → Prop :=
  | IsError {τ} m : ErrorP (Error (τ:=τ) m).

Derive Signature for ErrorP.

Set Elimination Schemes.

Scheme ValueP_ind := Induction for ValueP Sort Prop.
Scheme ErrorP_ind := Induction for ErrorP Sort Prop.

#[local] Hint Constructors ValueP ErrorP : core.

Lemma ValueP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ValueP v) :
  H1 = H2.
Proof.
  dependent induction H1;
  dependent elimination H2; sauto.
Qed.

Lemma ErrorP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ErrorP v) :
  H1 = H2.
Proof.
  dependent induction H1;
  dependent elimination H2; sauto.
Qed.

Lemma ValueP_dec {Γ τ} (e : Exp Γ τ) :
  ValueP e ∨ ¬ ValueP e.
Proof.
  induction e; branch; sauto lq: on dep: on.
Qed.

Lemma ErrorP_dec {Γ τ} (e : Exp Γ τ) :
  ErrorP e ∨ ¬ ErrorP e.
Proof.
  induction e; sauto.
Qed.

Inductive ValueTy : Set :=
  | TVoid
  | TUnit
  | TSymbol
  | TInteger
  | TDecimal
  | TTime
  | TBool
  | TString
  | TList : ValueTy → ValueTy
  | TPair : ValueTy → ValueTy → ValueTy.

Derive NoConfusion NoConfusionHom Subterm EqDec for ValueTy.

Fixpoint reifyTy (τ : Ty) : ValueTy :=
  match τ with
  | TySym        => TSymbol
  | ℤ            => TInteger
  | 𝔻            => TDecimal
  | 𝕋            => TTime
  | 𝔹            => TBool
  | 𝕊            => TString
  | 𝕌            => TUnit
  | TyList t     => TList (reifyTy t)
  | TyPair t1 t2 => TPair (reifyTy t1) (reifyTy t2)
  | _            => TVoid
  end.

Fixpoint reflectTy (t : ValueTy) : Type :=
  match t with
  | TVoid       => False
  | TUnit       => unit
  | TSymbol     => string
  | TInteger    => Z
  | TDecimal    => N
  | TTime       => nat
  | TBool       => bool
  | TString     => string
  | TList l     => list (reflectTy l)
  | TPair t1 t2 => reflectTy t1 * reflectTy t2
  end.

#[export]
Program Instance reflectTy_EqDec {t} : EqDec (reflectTy t).
Next Obligation.
  induction t; auto.
  - sauto.
  - apply list_eqdec.
    unfold EqDec.
    apply IHt.
  - destruct x as [x1 x2], y as [y1 y2].
    destruct (IHt1 x1 y1), (IHt2 x2 y2); sauto.
Defined.
