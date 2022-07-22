Require Import
  Coq.ZArith.ZArith
  Pact.Lib
  Pact.Ty
  Pact.Exp.

Set Equations With UIP.

Generalizable All Variables.

Section Value.

Import ListNotations.

Open Scope Ty_scope.

Unset Elimination Schemes.

(* [ValueP] is an inductive proposition that indicates whether an expression
   represents a value, i.e., that it does reduce any further. *)
Inductive ValueP Γ : ∀ {τ}, Exp Γ τ → Prop :=
  | LambdaP {dom cod} (e : Exp (dom :: Γ) cod) : ValueP Γ (LAM e)
  | LiteralP {ty l} : ValueP Γ (Lit (ty:=ty) l)
  | BuiltinP {τ b} : ValueP Γ (Bltn (τ:=τ) b)
  | SymbolP {n} : ValueP Γ (Symbol n)
  | PairP {τ1 τ2} {x : Exp Γ τ1} {y : Exp Γ τ2} :
    ValueP Γ x → ValueP Γ y → ValueP Γ (Pair x y)
  | NilP {τ} : ValueP Γ (Nil (τ:=τ))
  | ConsP {τ} (x : Exp Γ τ) xs :
    ValueP Γ x → ValueP Γ xs → ValueP Γ (Cons x xs)
  | CapabilityP {tp tv} (s : Exp Γ TySym)
                (Hp : ConcreteP tp) (Hv : ConcreteP tv)
                {p : Exp Γ tp} {v : Exp Γ tv} :
    ValueP Γ s → ValueP Γ p → ValueP Γ v →
    ValueP Γ (Capability Hp Hv s p v).

Derive Signature for ValueP.

Inductive ErrorP Γ : ∀ {τ}, Exp Γ τ → Prop :=
  | IsError {τ} m : ErrorP Γ (Error (τ:=τ) m).

Derive Signature for ErrorP.

Set Elimination Schemes.

Scheme ValueP_ind := Induction for ValueP Sort Prop.
Scheme ErrorP_ind := Induction for ErrorP Sort Prop.

#[local] Hint Constructors ValueP ErrorP : core.

Lemma ValueP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ValueP _ v) :
  H1 = H2.
Proof.
  dependent induction H1;
  dependent elimination H2; auto;
  f_equal; congruence.
Qed.

Lemma ErrorP_irrelevance {Γ τ} (v : Exp Γ τ) (H1 H2 : ErrorP _ v) :
  H1 = H2.
Proof.
  dependent induction H1;
  dependent elimination H2; auto;
  f_equal; congruence.
Qed.

Lemma ValueP_dec {Γ τ} (e : Exp Γ τ) :
  ValueP Γ e ∨ ¬ ValueP Γ e.
Proof.
  induction e; try solve [now left|now right].
  - destruct IHe1, IHe2;
    try (now left; constructor);
    right; intro; inv H1; contradiction.
  - destruct IHe1, IHe2;
    try (now left; constructor);
    right; intro; inv H1; contradiction.
  - destruct IHe1, IHe2, IHe3;
    try (now left; constructor);
    right; intro; inv H2; contradiction.
Qed.

Lemma ErrorP_dec {Γ τ} (e : Exp Γ τ) :
  ErrorP Γ e ∨ ¬ ErrorP Γ e.
Proof.
  induction e; solve [now left|now right].
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
  induction t; simpl in x, y; auto.
  - destruct x, y.
    now left.
  - apply string_EqDec.
  - apply Z_EqDec.
  - apply N_EqDec.
  - apply nat_EqDec.
  - apply bool_EqDec.
  - apply string_EqDec.
  - apply list_eqdec.
    unfold EqDec.
    apply IHt.
  - destruct x, y.
    destruct (IHt1 r r1); subst.
    + destruct (IHt2 r0 r2); subst.
      * now left.
      * right; congruence.
    + right; congruence.
Defined.

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

Inductive Value : Ty → Set :=
  | VUnit         : Value 𝕌
  | VSymbol       : string → Value TySym
  | VInteger      : Z      → Value ℤ
  | VDecimal      : N      → Value 𝔻
  | VTime         : nat    → Value 𝕋
  | VBool         : bool   → Value 𝔹
  | VString       : string → Value 𝕊
  | VList {t}     : list (Value t) → Value (TyList t)
  | VPair {t1 t2} : Value t1 → Value t2 → Value (TyPair t1 t2).

Derive Signature NoConfusion NoConfusionHom Subterm for Value.

Section Value_rect.

Inductive ForallT `(P : A → Type) : list A → Type :=
    ForallT_nil : ForallT P []
  | ForallT_cons (x : A) (l : list A) :
    P x → ForallT P l → ForallT P (x :: l).

Variable P : ∀ {t}, Value t → Type.

Variable Pinteger : ∀ (num : Z), P (VInteger num).
Variable Pdecimal : ∀ (num : N), P (VDecimal num).
Variable Ptime    : ∀ (num : nat), P (VTime num).
Variable Pbool    : ∀ (b : bool), P (VBool b).
Variable Pstring  : ∀ (s : string), P (VString s).
Variable Punit    : P VUnit.
Variable Psym     : ∀ (sym : string), P (VSymbol sym).
Variable Plist    : ∀ t (l : list (Value t)), ForallT P l → P (VList l).
Variable Ppair    : ∀ t1 (x : Value t1) t2 (y : Value t2),
                      P x → P y → P (VPair x y).

Fixpoint Value_rect' `(e : Value t) : P e.
Proof.
  induction e.
  - now apply Punit.
  - now apply Psym.
  - now apply Pinteger.
  - now apply Pdecimal.
  - now apply Ptime.
  - now apply Pbool.
  - now apply Pstring.
  - apply Plist.
    induction l.
    * constructor.
    * constructor.
      ** now apply Value_rect'.
      ** exact IHl.
  - now apply Ppair.
Qed.

End Value_rect.

#[export]
Program Instance Value_EqDec {t} : EqDec (Value t).
Next Obligation.
  generalize dependent y.
  dependent induction x using Value_rect'; intros;
  dependent destruction y; subst;
  try solve [ now left | right; congruence ];
  try apply dec_eq_f1;
  try (intros; now inv H).
  - apply Z_EqDec.
  - apply N_EqDec.
  - apply nat_EqDec.
  - apply bool_EqDec.
  - apply string_EqDec.
  - apply string_EqDec.
  - generalize dependent l0.
    induction l, l0; intros;
    simpl in X.
    + now left.
    + right; intro; now inv H.
    + right; intro; now inv H.
    + inv X.
      intuition.
      destruct (H0 v); subst.
      * destruct (H l0).
        ** inv e.
           now left.
        ** right; intro.
           now inv H1.
      * right; intro.
        now inv H1.
  - destruct (IHx1 y1); subst.
    + destruct (IHx2 y2); subst.
      * now left.
      * right; intro.
        now inv H.
    + right; intro.
      now inv H.
Defined.

End Value.

Arguments ValueP {Γ τ} _.
Arguments LambdaP {Γ dom cod} _.
Arguments LiteralP {Γ}.
Arguments BuiltinP {Γ}.
Arguments SymbolP {Γ}.
Arguments PairP {Γ τ1 τ2 x y} _ _.
Arguments NilP {Γ τ}.
Arguments ConsP {Γ τ _ _} _ _.
Arguments CapabilityP {Γ tp tv s} Hp Hv {p v} _ _ _.

Arguments ErrorP {Γ τ} _.
