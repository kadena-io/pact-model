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

Inductive Simp Γ Γ' : Ty → Set :=
  | EVAR {τ}        : Var Γ τ → Simp Γ Γ' τ
  | SVAR {τ}        : Var Γ' τ → Simp Γ Γ' τ
  | SLAM {dom cod}  : ANF (dom :: Γ) Γ' cod → Simp Γ Γ' (dom ⟶ cod)

  | SLit {ty}       : Literal ty → Simp Γ Γ' (TyPrim ty)
  | SBltn {τ}       : Builtin τ → Simp Γ Γ' τ

  | SSymbol         : string → Simp Γ Γ' TySym

  | SPair {τ1 τ2}   : Simp Γ Γ' τ1 → Simp Γ Γ' τ2 → Simp Γ Γ' (TyPair τ1 τ2)
  | SFst {τ1 τ2}    : Simp Γ Γ' (TyPair τ1 τ2) → Simp Γ Γ' τ1
  | SSnd {τ1 τ2}    : Simp Γ Γ' (TyPair τ1 τ2) → Simp Γ Γ' τ2

  | SInl {τ1 τ2}    : Simp Γ Γ' τ1 → Simp Γ Γ' (TySum τ1 τ2)
  | SInr {τ1 τ2}    : Simp Γ Γ' τ2 → Simp Γ Γ' (TySum τ1 τ2)
  | SCase {τ1 τ2 τ} : Simp Γ Γ' (TySum τ1 τ2) →
                      Simp Γ Γ' (τ1 ⟶ τ) → Simp Γ Γ' (τ2 ⟶ τ) → Simp Γ Γ' τ

  | SNil {τ}        : Simp Γ Γ' (TyList τ)
  | SCons {τ}       : Simp Γ Γ' τ → Simp Γ Γ' (TyList τ) → Simp Γ Γ' (TyList τ)
  | SCar {τ}        : Simp Γ Γ' (TyList τ) → Simp Γ Γ' τ
  | SCdr {τ}        : Simp Γ Γ' (TyList τ) → Simp Γ Γ' (TyList τ)
  | SIsNil {τ}      : Simp Γ Γ' (TyList τ) → Simp Γ Γ' 𝔹

with ANF Γ Γ' : Ty → Set :=
  | AReturn {τ} : Simp Γ Γ' τ → ANF Γ Γ' τ
  | ALetApp {τ dom cod} :
      Simp Γ Γ' (dom ⟶ cod) →
      Simp Γ Γ' dom →
      ANF Γ (cod :: Γ') τ →
      ANF Γ Γ' τ
  | ATailApp {dom cod} :
      Simp Γ Γ' (dom ⟶ cod) →
      Simp Γ Γ' dom →
      ANF Γ Γ' cod
  | ALet {τ τ'} :
      ANF Γ (𝕌 :: Γ') τ' →
      ANF Γ (𝕌 ⟶ τ' :: Γ') τ →
      ANF Γ Γ' τ

  | AError {τ} : ANF Γ Γ' τ
(*
  | ACatch {τ} : ANF Γ Γ' τ → ANF Γ Γ' (TySum 𝕌 τ)

  | AIf {τ} :
      Simp Γ Γ' 𝔹 →
      ANF Γ Γ' τ →
      ANF Γ Γ' τ →
      ANF Γ Γ' τ.

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
Notation "( x ';T' y ';T' z )" := (@existT _ _ x (@existT _ _ y z)).
Notation "( x ; y )" := (@exist _ _ x y).
Notation "( x ; y ; z )" := (@exist _ _ x (@exist _ _ y z)).

Arguments EVAR {Γ Γ' τ} _.
Arguments SVAR {Γ Γ' τ} _.
Arguments SLit {Γ Γ' ty} _.
Arguments SBltn {Γ Γ' τ} _.
Arguments SSymbol {Γ Γ'} _.
Arguments SNil {Γ Γ' τ}.

Definition WalkSimp
  (R : Env → Env → Set)
  `(r1 : R Γ Γ') `(r2 : R Δ Δ')
  (l : ∀ {Γ Γ' τ}, R Γ Γ' → R (τ :: Γ) (τ :: Γ'))
  (f : ∀ {Γ Γ' Δ : Env} {τ : Ty}, R Γ Γ' → Var Γ' τ → Simp Γ Δ τ)
  (g : ∀ {Γ Δ Δ' : Env} {τ : Ty}, R Δ Δ' → Var Δ' τ → Simp Γ Δ τ)
  (k : ∀ {Γ Γ' Δ Δ' : Env} {τ : Ty}, R Γ Γ' → R Δ Δ' → ANF Γ' Δ' τ → ANF Γ Δ τ)
  {τ} : Simp Γ' Δ' τ → Simp Γ Δ τ :=
  let fix go {Γ Γ' Δ Δ' τ} (r1 : R Γ Γ') (r2 : R Δ Δ')
        (e : Simp Γ' Δ' τ) : Simp Γ Δ τ :=
    match e with
    | EVAR v      => f r1 v
    | SVAR v      => g r2 v
    | SLAM e      => SLAM (k (l r1) r2 e)

    | SLit v      => SLit v
    | SBltn b     => SBltn b
    | SSymbol s   => SSymbol s

    | SPair x y   => SPair (go r1 r2 x) (go r1 r2 y)
    | SFst p      => SFst (go r1 r2 p)
    | SSnd p      => SSnd (go r1 r2 p)

    | SInl x      => SInl (go r1 r2 x)
    | SInr y      => SInr (go r1 r2 y)
    | SCase e x y => SCase (go r1 r2 e) (go r1 r2 x) (go r1 r2 y)

    | SNil        => SNil
    | SCons x xs  => SCons (go r1 r2 x) (go r1 r2 xs)
    | SCar xs     => SCar (go r1 r2 xs)
    | SCdr xs     => SCdr (go r1 r2 xs)
    | SIsNil xs   => SIsNil (go r1 r2 xs)
    end in go r1 r2.

Definition WalkANF
  (R : Env → Env → Set)
  `(r1 : R Γ Γ') `(r2 : R Δ Δ')
  (l : ∀ {Γ Γ' τ}, R Γ Γ' → R (τ :: Γ) (τ :: Γ'))
  (f : ∀ {Γ Γ' Δ : Env} {τ : Ty}, R Γ Γ' → Var Γ' τ → Simp Γ Δ τ)
  (g : ∀ {Γ Δ Δ' : Env} {τ : Ty}, R Δ Δ' → Var Δ' τ → Simp Γ Δ τ)
  {τ} : ANF Γ' Δ' τ → ANF Γ Δ τ :=
  let fix go {Γ Γ' Δ Δ' τ} (r1 : R Γ Γ') (r2 : R Δ Δ')
        (e : ANF Γ' Δ' τ) : ANF Γ Δ τ :=
    let go' {Γ Γ' Δ Δ' τ} (r1 : R Γ Γ') (r2 : R Δ Δ') :=
      WalkSimp r1 r2 (@l) (@f) (@g) (@go) in
    match e with
    | AReturn s       => AReturn (go' r1 r2 s)
    | ALetApp f' x' e => ALetApp (go' r1 r2 f') (go' r1 r2 x') (go r1 (l r2) e)
    | ATailApp f' x'  => ATailApp (go' r1 r2 f') (go' r1 r2 x')
    | ALet x' e       => ALet (go r1 (l r2) x') (go r1 (l r2) e)
    | AError _ _      => AError _ _
    end in go r1 r2.

Definition RenEVar {Γ Γ' Δ : Env} {τ : Ty} (r : Ren Γ Γ') (v : Var Γ' τ) :
  Simp Γ Δ τ := EVAR (RenVar r v).

Definition RenSVar {Γ Δ Δ' : Env} {τ : Ty} (r : Ren Δ Δ') (v : Var Δ' τ) :
  Simp Γ Δ τ := SVAR (RenVar r v).

Definition RenSimp {Γ Γ' Δ Δ' τ} (r1 : Ren Γ Γ') (r2 : Ren Δ Δ')
  (e : Simp Γ' Δ' τ) : Simp Γ Δ τ :=
  WalkSimp r1 r2 (@Keep) (@RenEVar) (@RenSVar)
    (λ _ _ _ _ _ r1 r2,
      WalkANF r1 r2 (@Keep) (@RenEVar) (@RenSVar)) e.

Definition RenANF {Γ Γ' Δ Δ' τ} (r1 : Ren Γ Γ') (r2 : Ren Δ Δ')
  (e : ANF Γ' Δ' τ) : ANF Γ Δ τ :=
  WalkANF r1 r2 (@Keep) (@RenEVar) (@RenSVar) e.

Equations anf `(e : Exp Γ τ) : { Γ'' & ANF Γ Γ'' τ } := {
  anf (VAR v) := ([] ;T AReturn (EVAR v));
  anf (LAM e) :=
    let '(Γ' ;T e') := anf e in
    (Γ' ;T AReturn (SLAM e'));
  anf (APP f x) :=
    anfk f (λ e f',
      anfk x (λ e0 x',
        (e0 ++ e ;T
         ATailApp (RenSimp idRen liftedL f')
                  (RenSimp idRen liftedR x'))));

  anf _ := _
}
with anfk `(e : Exp Γ τ)
     {τ'} (k : ∀ Γ', Simp Γ Γ' τ → { Γ'' & ANF Γ Γ'' τ' }) :
  { Γ'' & ANF Γ Γ'' τ' } := {
  anfk (VAR v) k := k [] (EVAR v);
  anfk (LAM e) k :=
    let '(Γ' ;T e') := anf e in
    k Γ' (SLAM e');
  anfk (APP f x) k :=
    anfk f (λ e f',
      anfk x (λ e0 x',
        (e0 ++ e ;T
         ALetApp (RenSimp idRen liftedL f')
                 (RenSimp idRen liftedR x')
                 (k (_ :: e0 ++ e) (SVAR ZV)))));

  anfk _ k := (_ ;T AError _ _)
}.
Next Obligation.

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
