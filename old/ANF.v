Require Import
  Coq.ZArith.ZArith
  Pact.Lib
  Pact.Ty
  Pact.Bltn
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

Section Exp.

Open Scope Ty_scope.

Variable Γ : Ty → Type.

Inductive Exp : Ty → Type :=
  | VAR {τ}        : Γ τ → Exp τ
  | LAM {dom cod}  : (Γ dom → Exp cod) → Exp (dom ⟶ cod)
  | APP {dom cod}  : Exp (dom ⟶ cod) → Exp dom → Exp cod

  | Lit {ty}       : Literal ty → Exp (TyPrim ty)

  | If {τ}         : Exp 𝔹 → Exp τ → Exp τ → Exp τ

  | Pair {τ1 τ2}   : Exp τ1 → Exp τ2 → Exp (TyPair τ1 τ2)
  | Fst {τ1 τ2}    : Exp (TyPair τ1 τ2) → Exp τ1
  | Snd {τ1 τ2}    : Exp (TyPair τ1 τ2) → Exp τ2

  | Seq {τ τ'}     : Exp τ' → Exp τ → Exp τ.

Derive Signature NoConfusionHom Subterm for Exp.

End Exp.

Inductive Simp (Γ : Ty → Type) : Ty → Type :=
  | SVAR {τ}        : Γ τ → Simp Γ τ
  | SLAM {dom cod}  : (Γ dom → ANF Γ cod) → Simp Γ (dom ⟶ cod)

  | SLit {ty}       : Literal ty → Simp Γ (TyPrim ty)
  (* | SBltn {τ}       : Builtin τ → Simp Γ τ *)

  (* | SSymbol         : string → Simp Γ TySym *)

  | SPair {τ1 τ2}   : Simp Γ τ1 → Simp Γ τ2 → Simp Γ (TyPair τ1 τ2)
  | SFst {τ1 τ2}    : Simp Γ (TyPair τ1 τ2) → Simp Γ τ1
  | SSnd {τ1 τ2}    : Simp Γ (TyPair τ1 τ2) → Simp Γ τ2

  (* | SInl {τ1 τ2}    : Simp Γ τ1 → Simp Γ (TySum τ1 τ2) *)
  (* | SInr {τ1 τ2}    : Simp Γ τ2 → Simp Γ (TySum τ1 τ2) *)
  (* | SCase {τ1 τ2 τ} : Simp Γ (TySum τ1 τ2) → *)
  (*                     Simp Γ (τ1 ⟶ τ) → Simp Γ (τ2 ⟶ τ) → Simp Γ τ *)

  (* | SNil {τ}        : Simp Γ (TyList τ) *)
  (* | SCons {τ}       : Simp Γ τ → Simp Γ (TyList τ) → Simp Γ (TyList τ) *)
  (* | SCar {τ}        : Simp Γ (TyList τ) → Simp Γ τ *)
  (* | SCdr {τ}        : Simp Γ (TyList τ) → Simp Γ (TyList τ) *)
  (* | SIsNil {τ}      : Simp Γ (TyList τ) → Simp Γ 𝔹 *)

  (* | SCapability {p v} : *)
  (*     ConcreteP p → *)
  (*     ConcreteP v → *)
  (*     Simp Γ TySym → *)
  (*     Simp Γ p → *)
  (*     Simp Γ v → *)
  (*     Simp Γ (TyCap p v) *)

with ANF (Γ : Ty → Type) : Ty → Type :=
  | AReturn {τ} : Simp Γ τ → ANF Γ τ
  | ALetApp {τ dom cod} :
      Simp Γ (dom ⟶ cod) →
      Simp Γ dom →
      (Γ cod → ANF Γ τ) →
      ANF Γ τ
  | ATailApp {dom cod} :
      Simp Γ (dom ⟶ cod) →
      Simp Γ dom →
      ANF Γ cod
  | AThunk {τ τ'} :
      (Γ 𝕌 → ANF Γ τ') →
      (Γ (𝕌 ⟶ τ') → ANF Γ τ) →
      ANF Γ τ
  | ALet {τ τ'} :
      ANF Γ τ' →
      (Γ τ' → ANF Γ τ) →
      ANF Γ τ
  | ALetCont {τ τ' τ''} :
      ANF Γ τ' →
      (Γ τ' → ANF Γ τ) →
      (Γ τ → ANF Γ τ'') →
      ANF Γ τ''

  (* | AError {τ} : ANF Γ τ *)
  (* | ACatch {τ} : ANF Γ τ → ANF Γ (TySum 𝕌 τ) *)

  | AIf {τ} :
      Simp Γ 𝔹 →
      ANF Γ τ →
      ANF Γ τ →
      ANF Γ τ

  (* | ACase {τ1 τ2 τ} : *)
  (*     Simp Γ (TySum τ1 τ2) → *)
  (*     ANF Γ (τ1 ⟶ τ) → *)
  (*     ANF Γ (τ2 ⟶ τ) → *)
  (*     ANF Γ τ *)

  (** Capabilities *)

  (* | AWithCapability {p v τ} : *)
  (*     ConcreteP v → *)
  (*     Simp Γ TySym → *)
  (*     Simp Γ (TyCap p v ⟶ 𝕌) → *)
  (*     Simp Γ (v × v ⟶ v) → *)
  (*     Simp Γ (TyCap p v) → *)
  (*     ANF Γ τ → *)
  (*     ANF Γ τ *)
  (* | AComposeCapability {p v} : *)
  (*     ConcreteP v → *)
  (*     Simp Γ TySym → *)
  (*     Simp Γ (TyCap p v ⟶ 𝕌) → *)
  (*     Simp Γ (v × v ⟶ v) → *)
  (*     Simp Γ (TyCap p v) → *)
  (*   ANF Γ 𝕌 *)
  (* | AInstallCapability {p v} : *)
  (*     Simp Γ (TyCap p v) → *)
  (*     ANF Γ 𝕌 *)
  (* | ARequireCapability {p v} : *)
  (*     Simp Γ (TyCap p v) → *)
  (*     ANF Γ 𝕌 *)
.

Derive Signature NoConfusionHom Subterm for Simp ANF.

Notation "( x ';T' y )" := (@existT _ _ x y).
Notation "( x ';T' y ';T' z )" := (@existT _ _ x (@existT _ _ y z)).
Notation "( x ; y )" := (@exist _ _ x y).
Notation "( x ; y ; z )" := (@exist _ _ x (@exist _ _ y z)).

Arguments SVAR {Γ τ} _.
Arguments Lit {Γ ty} _.
Arguments SLit {Γ ty} _.
(* Arguments SBltn {Γ τ} _. *)
(* Arguments SSymbol {Γ} _. *)
(* Arguments SNil {Γ τ}. *)

#[local] Obligation Tactic := auto.

Equations anf `(e : Exp Γ τ) : ANF Γ τ := {
  anf (VAR v)      := AReturn (SVAR v);
  anf (LAM e)      := AReturn (SLAM (λ x, anf (e x)));
  anf (APP f x)    := anfk f (λ f', anfk x (λ x', ATailApp f' x'));

  (* anf (Let x body) := ALet (anf x) (λ x, anf (body x)); *)

  anf (Lit l)      := AReturn (SLit l);
  (* anf (Bltn b)     := AReturn (SBltn b); *)

  (* anf Error        := AError _; *)
  (* anf (Catch e)    := ACatch (anf e); *)

  (* anf (Symbol s)   := AReturn (SSymbol s); *)

  anf (If b t e)   := anfk b (λ b', AIf b' (anf t) (anf e));

  anf (Pair x y)   := anfk x (λ x', anfk y (λ y', AReturn (SPair x' y')));
  anf (Fst p)      := anfk p (λ p', AReturn (SFst p'));
  anf (Snd p)      := anfk p (λ p', AReturn (SSnd p'));

  (* anf (Inl x)      := anfk x (λ x', AReturn (SInl x')); *)
  (* anf (Inr y)      := anfk y (λ y', AReturn (SInr y')); *)
  (* anf (Case p g h) := anfk p (λ p', ACase p' (anf g) (anf h)); *)

  (* anf Nil          := AReturn SNil; *)

  (* anf (Cons x xs)  := anfk x (λ x', anfk xs (λ xs', AReturn (SCons x' xs'))); *)
  (* anf (Car xs)     := anfk xs (λ xs', AReturn (SCar xs')); *)
  (* anf (Cdr xs)     := anfk xs (λ xs', AReturn (SCdr xs')); *)
  (* anf (IsNil xs)   := anfk xs (λ xs', AReturn (SIsNil xs')); *)

  anf (Seq e1 e2)  := ALet (anf e1) (λ _, anf e2);

  (* anf (Capability (p:=tp) (v:=tv) Hp Hv nm arg val) := *)
  (*   anfk nm (λ nm', *)
  (*     anfk arg (λ arg', *)
  (*       anfk val (λ val', *)
  (*         AReturn (SCapability Hp Hv nm' arg' val')))); *)

  (* anf (WithCapability (p:=tp) (v:=tv) Hv modname prd mng c e) := *)
  (*   anfk modname (λ modname', *)
  (*     anfk prd (λ prd', *)
  (*       anfk mng (λ mng', *)
  (*         anfk c (λ c', *)
  (*           AWithCapability Hv modname' prd' mng' c' (anf e))))); *)
    
  (* anf (ComposeCapability (p:=tp) (v:=tv) Hv modname prd mng c) := *)
  (*   anfk modname (λ modname', *)
  (*     anfk prd (λ prd', *)
  (*       anfk mng (λ mng', *)
  (*         anfk c (λ c', *)
  (*           AComposeCapability Hv modname' prd' mng' c')))); *)

  (* anf (InstallCapability c) := anfk c (λ c', AInstallCapability c'); *)
  (* anf (RequireCapability c) := anfk c (λ c', ARequireCapability c'); *)
}
with anfk `(e : Exp Γ τ) {τ'} (k : Simp Γ τ → ANF Γ τ') : ANF Γ τ' := {
  anfk (VAR v)      k := k (SVAR v);
  anfk (LAM e)      k := k (SLAM (λ x, anf (e x)));
  anfk (APP f x)    k :=
    anfk f (λ f', anfk x (λ x', ALetApp f' x' (λ x, k (SVAR x))));

  (* anfk (Let x body) k := *)
  (*   ALetCont (anf x) (λ x, anf (body x)) (λ x, k (SVAR x)); *)

  anfk (Lit l)      k := k (SLit l);
  (* anfk (Bltn b)     k := k (SBltn b); *)

  (* anfk Error        k := AError _; *)
  (* anfk (Catch e)    k := ACatch (anf e); *)

  (* anfk (Symbol s)   k := k (SSymbol s); *)

  (* anfk (If (Lit (LitBool true)) t e) k := anfk t k; *)

  anfk (If b t e)   k :=
    anfk b (λ b',
      AThunk (λ _, anf t) (λ t', 
        AThunk (λ _, anf e) (λ e', 
          AIf b'
            (ALetApp (SVAR t') (SLit LitUnit) (λ x, k (SVAR x)))
            (ALetApp (SVAR e') (SLit LitUnit) (λ x, k (SVAR x))))));

  anfk (Pair x y)   k := anfk x (λ x', anfk y (λ y', k (SPair x' y')));
  anfk (Fst p)      k := anfk p (λ p', k (SFst p'));
  anfk (Snd p)      k := anfk p (λ p', k (SSnd p'));

  (* anfk (Inl x)      k := anfk x (λ x', k (SInl x')); *)
  (* anfk (Inr y)      k := anfk y (λ y', k (SInr y')); *)
  (* anfk (Case p g h) k := _; *)

  (* anfk Nil          k := k SNil; *)

  (* anfk (Cons x xs)  k := anfk x (λ x', anfk xs (λ xs', k (SCons x' xs'))); *)
  (* anfk (Car xs)     k := anfk xs (λ xs', k (SCar xs')); *)
  (* anfk (Cdr xs)     k := anfk xs (λ xs', k (SCdr xs')); *)
  (* anfk (IsNil xs)   k := anfk xs (λ xs', k (SIsNil xs')); *)

  anfk (Seq e1 e2)  k := ALetCont (anf e1) (λ _, anf e2) (λ x, k (SVAR x));

  (* anfk (Capability (p:=tp) (v:=tv) Hp Hv nm arg val) k := *)
  (*   anfk nm (λ nm', *)
  (*     anfk arg (λ arg', *)
  (*       anfk val (λ val', *)
  (*         k (SCapability Hp Hv nm' arg' val')))); *)

  (* anfk (WithCapability (p:=tp) (v:=tv) Hv modname prd mng c e) k := _; *)
  (* anfk (ComposeCapability (p:=tp) (v:=tv) Hv modname prd mng c) k := _; *)
  (* anfk (InstallCapability c) k := _; *)
  (* anfk (RequireCapability c) k := _; *)
}.

Definition sample Γ (add : Exp Γ (ℤ ⟶ ℤ ⟶ ℤ)) : Exp Γ (ℤ × ℤ) :=
  Pair (APP (APP add (Lit (LitInteger 2))) (Lit (LitInteger 3)))
       (APP (APP add (Lit (LitInteger 7))) (Lit (LitInteger 8))).

Compute sample.
Goal True.
  enough (Exp (λ _, nat) (ℤ ⟶ ℤ ⟶ ℤ)) as add.
    pose (f := anf (sample add)).
    cbv [ anf anfk sample anf_functional anfk_functional ] in f.
