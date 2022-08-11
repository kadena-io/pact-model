Require Import
  Coq.ZArith.ZArith
  Pact.Lib
  Pact.Ty
  Pact.Bltn
  Pact.Ren
  Pact.Exp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Open Scope Ty_scope.

Inductive AVal Γ : Ty → Set :=
  | AVAR {τ}        : Var Γ τ → AVal Γ τ
  | AApp {dom cod}  : AVal Γ (dom ⟶ cod) → AVal Γ dom → AVal Γ cod
  | ALAM {dom cod}  : Exp (dom :: Γ) cod → AVal Γ (dom ⟶ cod)

  | ALit {ty}       : Literal ty → AVal Γ (TyPrim ty)
  | ABltn {τ}       : Builtin τ → AVal Γ τ

  | ASymbol         : string → AVal Γ TySym

  | APair {τ1 τ2}   : AVal Γ τ1 → AVal Γ τ2 → AVal Γ (TyPair τ1 τ2)
  | AFst {τ1 τ2}    : AVal Γ (TyPair τ1 τ2) → AVal Γ τ1
  | ASnd {τ1 τ2}    : AVal Γ (TyPair τ1 τ2) → AVal Γ τ2

  | AInl {τ1 τ2}    : AVal Γ τ1 → AVal Γ (TySum τ1 τ2)
  | AInr {τ1 τ2}    : AVal Γ τ2 → AVal Γ (TySum τ1 τ2)
  | ACase {τ1 τ2 τ} : AVal Γ (TySum τ1 τ2) →
                         AVal Γ (τ1 ⟶ τ) → AVal Γ (τ2 ⟶ τ) → AVal Γ τ

  | ANil {τ}        : AVal Γ (TyList τ)
  | ACons {τ}       : AVal Γ τ → AVal Γ (TyList τ) → AVal Γ (TyList τ)
  | ACar {τ}        : AVal Γ (TyList τ) → AVal Γ τ
  | ACdr {τ}        : AVal Γ (TyList τ) → AVal Γ (TyList τ)
  | AIsNil {τ}      : AVal Γ (TyList τ) → AVal Γ 𝔹

with AExp Γ         : Ty → Set :=
  | AValue {τ}      : AVal Γ τ → AExp Γ τ

  (* a; b = let _   := a in b *)
  | ALet {τ τ'}     : AVal Γ τ' → AExp (τ' :: Γ) τ → AExp Γ τ
  | ALetApp {τ τ' τ''} : AVal Γ (τ'' ⟶ τ') → AVal Γ τ'' → AExp (τ' :: Γ) τ → AExp Γ τ

  (* The following terms represent Pact beyond lambda calculus. *)
  | AError {τ}      : AExp Γ τ
  | ACatch {τ}      : AExp Γ τ → AExp Γ (TySum 𝕌 τ)

  | AIf {τ}         : AVal Γ 𝔹 → AExp Γ τ → AExp Γ τ → AExp Γ τ

  (** Capabilities *)

  | ACapability {p v} :
    ConcreteP p →
    ConcreteP v →
    AExp Γ TySym →
    AExp Γ p →
    AExp Γ v →
    AExp Γ (TyCap p v)

  | AWithCapability {p v τ} :
    ConcreteP v →
    AExp Γ TySym →                (* name of the defining module *)
    AExp Γ (TyCap p v ⟶ 𝕌) →     (* throws exception on failure *)
    AExp Γ (v × v ⟶ v) →         (* throws exception on failure *)
    AExp Γ (TyCap p v) → AExp Γ τ → AExp Γ τ

  | AComposeCapability {p v} :
    ConcreteP v →
    AExp Γ TySym →                (* name of the defining module *)
    AExp Γ (TyCap p v ⟶ 𝕌) →     (* throws exception on failure *)
    AExp Γ (v × v ⟶ v) →         (* throws exception on failure *)
    AExp Γ (TyCap p v) → AExp Γ 𝕌

  | AInstallCapability {p v} : AExp Γ (TyCap p v) → AExp Γ 𝕌
  | ARequireCapability {p v} : AExp Γ (TyCap p v) → AExp Γ 𝕌.

(* Derive Signature NoConfusionHom Subterm for AExp. *)

Arguments ALit {Γ ty} _.
Arguments ABltn {Γ τ} _.
Arguments AError {Γ τ}.
Arguments ASymbol {Γ} _.
Arguments ANil {Γ τ}.

Reserved Notation "⟦ x ⟧ k" (at level 90, k at next level).

Equations transform `(e : Exp Γ τ)
  (k : ∀ Γ' τ', AVal (Γ' ++ Γ) τ → AExp (Γ' ++ Γ) τ') {τ'} : AExp Γ τ' := {
  ⟦VAR v⟧ k := k [] _ (AVAR v);
  ⟦LAM e⟧ k := k [] _ (ALAM e);
  ⟦Lit x⟧ k := k [] _ (ALit x);
  ⟦APP (VAR f) (VAR x)⟧ k :=
    k [] _ (AApp (AVAR f) (AVAR x));
  ⟦APP (VAR f) x⟧ k :=
    ⟦x⟧ (λ l _ x',
        ALet x'
          (k (_ :: l) _
             (AApp (AVAR (RenVar lifted f)) (AVAR (Γ:=(_ :: l) ++ Γ) ZV))));
  ⟦APP f x⟧ k :=
    ⟦f⟧ (λ fl _ f',
        (⟦x⟧ (λ xl _ x',
             ALet f'
               (ALet x'
                  (k (_ :: _ :: fl ++ xl) _
                     (AApp
                        (AVAR (Γ:=(_ :: _ :: fl ++ xl) ++ Γ) (SV ZV))
                        (AVAR (Γ:=(_ :: _ :: fl ++ xl) ++ Γ) ZV)))))));
  ⟦Error⟧ _ := λ _, AError;
  ⟦Catch x⟧ k := _;
  ⟦Bltn x⟧ k := _;
  ⟦Symbol x⟧ k := _;
  ⟦If x x0 x1⟧ k := _;
  ⟦Pair x y⟧ k := _;
  ⟦Fst p⟧ k := _;
  ⟦Snd p⟧ k := _;
  ⟦Inl x⟧ k := _;
  ⟦Inr x⟧ k := _;
  ⟦Case x f g⟧ k := _;
  ⟦Nil⟧ k := _;
  ⟦Cons x xs⟧ k := _;
  ⟦Car xs⟧ k := _;
  ⟦Cdr xs⟧ k := _;
  ⟦IsNil xs⟧ k := _;
  ⟦Seq e1 e2⟧ k := _;
  ⟦Capability x x0 x1 x2 x3⟧ k := _;
  ⟦WithCapability x x0 x1 x2 x3 x4⟧ k := _;
  ⟦ComposeCapability x x0 x1 x2 x3⟧ k := _;
  ⟦InstallCapability x⟧ k := _;
  ⟦RequireCapability x⟧ k := _
} where "⟦ x ⟧ k" := (transform x k).

Declare Scope Var_scope.
Bind Scope Var_scope with Var.
Delimit Scope Var_scope with var.

Declare Scope AExp_scope.
Bind Scope AExp_scope with AExp.
Delimit Scope AExp_scope with exp.

Notation "Γ ∋ τ" :=
  (Var Γ τ%ty) (at level 10, τ at next level) : type_scope.
Notation "Γ ⊢ τ" :=
  (AExp Γ τ%ty) (at level 10, τ at next level) : type_scope.
