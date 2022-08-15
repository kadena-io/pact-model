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

Inductive Simp : ∀ Γ τ, Exp Γ τ → Prop :=
  | AVal {Γ τ} {e : Exp Γ τ} : ValueP e → Simp e
  | AVAR {Γ τ} {v : Var Γ τ} : Simp (VAR v)
  | ALAM {Γ dom cod} {e : Exp (dom :: Γ) cod} : ANF e → Simp (LAM e)

with ANF : ∀ Γ τ, Exp Γ τ → Prop :=
  | AReturn {Γ τ} {e : Exp Γ τ} : Simp e → ANF e
  | ABind {Γ τ dom cod}
      {f : Exp Γ (dom ⟶ cod)}
      {x : Exp Γ dom}
      (body : Exp (cod :: Γ) τ) :
    Simp f →
    Simp x →
    ANF body →
    ANF (Let (APP f x) body)
  | AAPP {Γ dom cod}
      {f : Exp Γ (dom ⟶ cod)}
      {x : Exp Γ dom} :
    Simp f →
    Simp x →
    ANF (APP f x)
        
  | ALet {Γ τ τ'}
      {x : Exp Γ τ'}
      (body : Exp (τ' :: Γ) τ) :
    ANF x →
    ANF body →
    ANF (Let x body)

  | AError {Γ τ} : ANF (Error (Γ:=Γ) (τ:=τ))
  | ACatch {Γ τ} {e : Exp Γ τ} : ANF e → ANF (Catch e)

  | AIf {Γ τ} b {e1 e2 : Exp Γ τ} :
    ANF b → ANF e1 → ANF e2 → ANF (If b e1 e2)

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

Derive Signature for ANF.

Notation "( x ; y )" := (@exist _ _ x y).

Equations anf `(e : Exp Γ τ) : { e' : Exp Γ τ | ANF e' } :=
  anf (VAR v)     k := k (VAR v) AVAR;
  anf (LAM e)     k := k (LAM e) (AValue (LambdaP _));
  anf (APP e1 e2) k :=
    anf e1 (λ e1' _,
        anf e2 (λ e2' _,
            k (APP e1' e2') _));

  anf (Let x body) k := _;

  anf Error       k := (Error; AError);
  anf (Catch e)   k :=
    let '(e'; _) := anf e in
    (Catch e'; _);

  anf (Lit l)     k := (Lit l;    AValue (LiteralP _));
  anf (Bltn b)    k := (Bltn b;   AValue (BuiltinP _));
  anf (Symbol s)  k := (Symbol s; AValue (SymbolP _));

  anf (If b t e)  k :=
    let '(b'; _) := anf b in
    let '(t'; _) := anf t in
    let '(e'; _) := anf e in
    (If b' t' e'; _);
    
  anf (Pair x y)  k :=
    let '(x'; _) := anf x in
    let '(y'; _) := anf y in
    (Pair x' y'; AValue (PairP _ _));
  anf (Fst p)     k := _;
  anf (Snd p)     k := _;

  anf (Inl p)      k := _;
  anf (Inr p)      k := _;
  anf (Case p l r) k := _;

  anf Nil         k := _;
  anf (Cons x xs) k := _;
  anf (Car xs)    k := _;
  anf (Cdr xs)    k := _;
  anf (IsNil xs)  k := _;
  anf (Seq x y)   k := _;

  anf (Capability _ _ n p v)         k := _;
  anf (WithCapability _ nm p m c e)  k := _;
  anf (ComposeCapability _ nm p m c) k := _;
  anf (InstallCapability c)          k := _;
  anf (RequireCapability c)          k := _.

Print anf.
