Set Warnings "-cannot-remove-as-expected".

Require Import
  Coq.Unicode.Utf8
  Coq.Program.Program
  Coq.Classes.CRelationClasses
  Coq.Classes.Morphisms
  Ty
  Exp
  Sub.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Log.

Context {A : Type}.
Context `{L : HostExprs A}.
Context {Γ : Env}.

Variable P : ∀ {τ}, Exp Γ τ → Prop.

(** [ExpP] is a logical predicate that permits type-directed induction on
    expressions. *)
Equations ExpP `(e : Exp Γ τ) : Prop :=
  ExpP (τ:=_ ⟶ _)   f := P f ∧ (∀ x, ExpP x → ExpP (APP f x)).
  (* ExpP (τ:=_ × _)    p := P p ∧ ExpP (Fst p) ∧ ExpP (Snd p); *)
  (* ExpP (τ:=TyList _) l := P l ∧ (∀ d, ExpP d → ExpP (Car d l)); *)
  (* ExpP e := P e. *)

Inductive SubP : ∀ {Γ'}, Sub Γ Γ' → Prop :=
  | NoSubP : SubP (NoSub (Γ:=Γ))
  | PushP {Γ' τ} (e : Exp Γ τ) (s : Sub Γ Γ') :
    ExpP e → SubP s → SubP (Push e s).

Derive Signature for SubP.

Lemma ExpP_P {τ} {e : Γ ⊢ τ} : ExpP e → P e.
Proof. intros; induction τ; simpl in *; simp ExpP in H; now reduce. Qed.

End Log.
