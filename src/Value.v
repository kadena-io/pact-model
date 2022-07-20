Require Import
  Coq.ZArith.ZArith
  Lib
  Ty
  Exp.

From Equations Require Import Equations.
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
  | TInteger
  | TDecimal
  | TTime
  | TBool
  | TString
  | TUnit
  | TVoid
  | TSymbol
  | TList : ValueTy → ValueTy
  | TPair : ValueTy → ValueTy → ValueTy.

Derive NoConfusion NoConfusionHom Subterm EqDec for ValueTy.

Inductive Value : ValueTy → Set :=
  | VInteger      : Z → Value TInteger
  | VDecimal      : N → Value TDecimal
  | VTime         : nat → Value TTime
  | VBool         : bool → Value TBool
  | VString       : string → Value TString
  | VUnit         : Value TUnit
  | VSymbol       : string → Value TSymbol
  | VList {t}     : list (Value t) → Value (TList t)
  | VPair {t1 t2} : Value t1 → Value t2 → Value (TPair t1 t2).

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
  - now apply Pinteger.
  - now apply Pdecimal.
  - now apply Ptime.
  - now apply Pbool.
  - now apply Pstring.
  - now apply Punit.
  - now apply Psym.
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
