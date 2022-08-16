Require Import
  Coq.ZArith.ZArith
  Pact.Lib
  Pact.Ty
  Pact.Bltn
  Pact.Ren
  Pact.Exp
  Pact.Value.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Open Scope Ty_scope.

Inductive Simp Γ : Ty → Set :=
  | SVAR {τ}       : Var Γ τ → Simp Γ τ
  | SLAM {dom cod} : ANF (dom :: Γ) cod → Simp Γ (dom ⟶ cod)

  | SLit {ty}       : Literal ty → Simp Γ (TyPrim ty)
  | SBltn {τ}       : Builtin τ → Simp Γ τ

  | SSymbol         : string → Simp Γ TySym

  | SPair {τ1 τ2}   : Simp Γ τ1 → Simp Γ τ2 → Simp Γ (TyPair τ1 τ2)
  | SFst {τ1 τ2}    : Simp Γ (TyPair τ1 τ2) → Simp Γ τ1
  | SSnd {τ1 τ2}    : Simp Γ (TyPair τ1 τ2) → Simp Γ τ2

  | SInl {τ1 τ2}    : Simp Γ τ1 → Simp Γ (TySum τ1 τ2)
  | SInr {τ1 τ2}    : Simp Γ τ2 → Simp Γ (TySum τ1 τ2)
  | SCase {τ1 τ2 τ} : Simp Γ (TySum τ1 τ2) →
                      Simp Γ (τ1 ⟶ τ) → Simp Γ (τ2 ⟶ τ) → Simp Γ τ

  | SNil {τ}        : Simp Γ (TyList τ)
  | SCons {τ}       : Simp Γ τ → Simp Γ (TyList τ) → Simp Γ (TyList τ)
  | SCar {τ}        : Simp Γ (TyList τ) → Simp Γ τ
  | SCdr {τ}        : Simp Γ (TyList τ) → Simp Γ (TyList τ)
  | SIsNil {τ}      : Simp Γ (TyList τ) → Simp Γ 𝔹

with ANF Γ : Ty → Set :=
  | AReturn {τ} : Simp Γ τ → ANF Γ τ
  | ALetApp {τ dom cod} :
      Simp Γ (dom ⟶ cod) →
      Simp Γ dom →
      ANF (cod :: Γ) τ →
      ANF Γ τ
  | ATailApp {dom cod} :
      Simp Γ (dom ⟶ cod) →
      Simp Γ dom →
      ANF Γ cod
(*
  | ALet {τ τ'} :
      ANF (𝕌 :: Γ) τ' →
      ANF (𝕌 ⟶ τ' :: Γ) τ →
      ANF Γ τ

  | AError {τ} : ANF Γ τ
  | ACatch {τ} : ANF Γ τ → ANF Γ (TySum 𝕌 τ)

  | AIf {τ} :
      Simp Γ 𝔹 →
      ANF Γ τ →
      ANF Γ τ →
      ANF Γ τ.

  (** Capabilities *)

  | AWithCapability {Γ p v τ}
      {Hv : ConcreteP v}
      {n : Exp Γ TySym}
      {prd : Exp Γ (TyCap p v ⟶ 𝕌)}
      {mng : Exp Γ (v × v ⟶ v)}
      {cap : Exp Γ (TyCap p v)}
      {e : Exp Γ τ} :
    ANF n →
    ANF prd →
    ANF mng →
    ANF cap →
    ANF e →
    ANF (WithCapability Hv n prd mng cap e)
  | AComposeCapability {Γ p v}
      {Hv : ConcreteP v}
      {n : Exp Γ TySym}
      {prd : Exp Γ (TyCap p v ⟶ 𝕌)}
      {mng : Exp Γ (v × v ⟶ v)}
      {cap : Exp Γ (TyCap p v)} :
    ANF n →
    ANF prd →
    ANF mng →
    ANF cap →
    ANF (ComposeCapability Hv n prd mng cap)
  | AInstallCapability {Γ p v} {cap : Exp Γ (TyCap p v)} :
    ANF cap →
    ANF (InstallCapability cap)
  | ARequireCapability {Γ p v} {cap : Exp Γ (TyCap p v)} :
    ANF cap →
    ANF (RequireCapability cap).
*).


Derive Signature NoConfusionHom Subterm for Simp ANF.

Notation "( x ';T' y )" := (@existT _ _ x y).
Notation "( x ; y )" := (@exist _ _ x y).

Arguments SLit {Γ ty} _.
Arguments SBltn {Γ τ} _.
Arguments SSymbol {Γ} _.
Arguments SNil {Γ τ}.

Definition WalkSimp
  (R : Env → Env → Set)
  `(r : R Γ Γ')
  (l : ∀ {τ Γ Γ'}, R Γ Γ' → R (τ :: Γ) (τ :: Γ'))
  (f : ∀ {Γ Γ' : Env} {τ : Ty}, R Γ Γ' → Var Γ' τ → Simp Γ τ)
  (k : ∀ {Γ Γ' : Env} {τ : Ty}, R Γ Γ' → ANF Γ' τ → ANF Γ τ)
  {τ} : Simp Γ' τ → Simp Γ τ :=
  let fix go {Γ Γ' τ} (r : R Γ Γ') (e : Simp Γ' τ) : Simp Γ τ :=
    match e with
    | SVAR v      => f r v
    | SLAM e      => SLAM (k (l r) e)

    | SLit v      => SLit v
    | SBltn b     => SBltn b
    | SSymbol s   => SSymbol s

    | SPair x y   => SPair (go r x) (go r y)
    | SFst p      => SFst (go r p)
    | SSnd p      => SSnd (go r p)

    | SInl x      => SInl (go r x)
    | SInr y      => SInr (go r y)
    | SCase e g h => SCase (go r e) (go r g) (go r h)

    | SNil        => SNil
    | SCons x xs  => SCons (go r x) (go r xs)
    | SCar xs     => SCar (go r xs)
    | SCdr xs     => SCdr (go r xs)
    | SIsNil xs   => SIsNil (go r xs)
    end in go r.

Definition WalkANF
  (R : Env → Env → Set)
  `(r : R Γ Γ')
  (l : ∀ {τ Γ Γ'}, R Γ Γ' → R (τ :: Γ) (τ :: Γ'))
  (f : ∀ {Γ Γ' : Env} {τ : Ty}, R Γ Γ' → Var Γ' τ → Simp Γ τ)
  {τ} : ANF Γ' τ → ANF Γ τ :=
  let fix go {Γ Γ' τ} (r : R Γ Γ') (e : ANF Γ' τ) : ANF Γ τ :=
    match e with
    | AReturn s       => AReturn (WalkSimp r (@l) (@f) (@go) s)
    | ALetApp f' x' e => ALetApp (WalkSimp r (@l) (@f) (@go) f')
                           (WalkSimp r (@l) (@f) (@go) x') (go (l r) e)
    | ATailApp f' x'  => ATailApp (WalkSimp r (@l) (@f) (@go) f')
                           (WalkSimp r (@l) (@f) (@go) x')
    end in go r.

Definition RenSimp {Γ Γ' τ} (r : Ren Γ Γ') (e : Simp Γ' τ) : Simp Γ τ :=
  WalkSimp r (@Keep) (λ _ _ _ r v, SVAR (RenVar r v))
    (λ _ _ _ r, WalkANF r (@Keep) (λ _ _ _ r v, SVAR (RenVar r v))) e.

Definition RenANF {Γ Γ' τ} (r : Ren Γ Γ') (e : ANF Γ' τ) : ANF Γ τ :=
  WalkANF r (@Keep) (λ _ _ _ r v, SVAR (RenVar r v)) e.

Equations anf `(e : Exp Γ τ) : ANF Γ τ := {
  anf (VAR v) := AReturn (SVAR v);
  anf (LAM e) := AReturn (SLAM (anf e));
  anf (APP f x) :=
    anfk f (λ _ f',
      anfk (RenExp lifted x) (λ _ x',
        ATailApp (RenSimp lifted f') x'));

  anf _ := _
}
with anfk `(e : Exp Γ τ) {r} (k : ∀ Γ', Simp (Γ' ++ Γ) τ → r) : r := {
  anfk (VAR v) k := k (SVAR v);
  anfk (LAM e) k := k (SLAM (anf e));
  anfk (APP f x) k :=
    anfk f (λ f',
      anfk x (λ x',
        ALetApp f' x' (k (SVAR ZV))));

  anfk _ _ := _
}.

Equations anf `(e : Exp Γ τ) : { e' : Exp Γ τ | ANF e' } := {
  anf (VAR v) := (VAR v; AReturn (AVAR v));
  anf (LAM e) :=
    let '(e'; He') := anf e in
    (LAM e'; AReturn (ALAM He'));
  anf (APP f x) :=
    _ (projT2 (projT2 (anfk f (λ f' Hf',
      (anfk x (λ x' Hx',
        (_ ;T (_ ;T (APP f' x'; AAPP Hf' Hx')))))))));

  anf _ := _
}
with anfk `(e : Exp Γ τ)
  (k : ∀ (e' : Exp Γ τ), Simp e' → { Γ' & { τ' & { e'' : Exp Γ' τ' | ANF e'' }}}) :
  { Γ' & { τ' & { e'' : Exp Γ' τ' | ANF e'' }}} := {
  anfk (VAR v) k := k _ (AVAR v);
  anfk (LAM e) k :=
    let '(e'; He') := anf e in
    k _ (ALAM He');
  anfk (APP f x) k :=
    let '(f'; Hf') := anf f in
    let '(x'; Hx') := anf x in
    (_ ;T
    (_ ;T
    (Let f' (Let (RenExp skip1 x') (APP (VAR (SV ZV)) (VAR ZV)));
     _)));

  anfk _ _ := _
}.
Next Obligation.
  simpl in *.

  anf (Let x body) := _;

  anf Error       := (Error; AError);
  anf (Catch e)   :=
    let '(e'; _) := anf e in
    (Catch e'; _);

  anf (Lit l)     := (Lit l;    AValue (LiteralP _));
  anf (Bltn b)    := (Bltn b;   AValue (BuiltinP _));
  anf (Symbol s)  := (Symbol s; AValue (SymbolP _));

  anf (If b t e)  :=
    let '(b'; _) := anf b in
    let '(t'; _) := anf t in
    let '(e'; _) := anf e in
    (If b' t' e'; _);
    
  anf (Pair x y)  :=
    let '(x'; _) := anf x in
    let '(y'; _) := anf y in
    (Pair x' y'; AValue (PairP _ _));
  anf (Fst p)     := _;
  anf (Snd p)     := _;

  anf (Inl p)      := _;
  anf (Inr p)      := _;
  anf (Case p l r) := _;

  anf Nil         := _;
  anf (Cons x xs) := _;
  anf (Car xs)    := _;
  anf (Cdr xs)    := _;
  anf (IsNil xs)  := _;
  anf (Seq x y)   := _;

  anf (Capability _ _ n p v)         := _;
  anf (WithCapability _ nm p m c e)  := _;
  anf (ComposeCapability _ nm p m c) := _;
  anf (InstallCapability c)          := _;
  anf (RequireCapability c)          := _.

Print anf.
