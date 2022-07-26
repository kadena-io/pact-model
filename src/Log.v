Set Warnings "-cannot-remove-as-expected".

Require Import
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Sub.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Section Log.

Context {Γ : Env}.
Variable P : ∀ {τ}, Exp Γ τ → Prop.

(** [ExpP] is a logical predicate that permits type-directed induction on
    expressions. *)
Equations ExpP `(e : Exp Γ τ) : Prop := {
  ExpP e := P e ∧ ExpP' e
}
where ExpP' `(e : Exp Γ τ) : Prop := {
  ExpP' (τ:=_ ⟶ _) e := (∀ x, ExpP x → ExpP (APP e x));
  ExpP' e := True
}.

Lemma ExpP_P {τ} {e : Γ ⊢ τ} : ExpP e → P e.
Proof.
  induction τ; sauto.
Qed.

Inductive SubP : ∀ {Γ'}, Sub Γ Γ' → Prop :=
  | NoSubP : SubP (NoSub (Γ:=Γ))
  | PushP {Γ' τ} (e : Exp Γ τ) (s : Sub Γ Γ') :
    ExpP e → SubP s → SubP (Push e s).

Derive Signature for SubP.

Variable R : ∀ {τ}, Exp Γ τ → Exp Γ τ → Prop.

(** [ExpR] is a logical predicate that permits type-directed induction on
    expressions. *)
Equations ExpR {τ} (e1 e2 : Exp Γ τ) : Prop := {
  ExpR f1 f2 := R f1 f2 ∧ ExpR' f1 f2
}
where ExpR' {τ} (e1 e2 : Exp Γ τ) : Prop := {
  ExpR' (τ:=_ ⟶ _) f1 f2 :=
    (∀ x1 x2, ExpR x1 x2 → ExpR (APP f1 x1) (APP f1 x2));
  ExpR' e1 e2 := True
}.

Lemma ExpR_R {τ} {e1 e2 : Γ ⊢ τ} : ExpR e1 e2 → R e1 e2.
Proof.
  induction τ; sauto.
Qed.

Inductive SubR : ∀ {Γ'}, Sub Γ Γ' → Prop :=
  | NoSubR : SubR (NoSub (Γ:=Γ))
  | PushR {Γ' τ} (e e' : Exp Γ τ) (s : Sub Γ Γ') :
    ExpR e e' → SubR s → SubR (Push e s).

Derive Signature for SubR.

End Log.
