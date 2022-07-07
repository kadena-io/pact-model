Require Export
  Coq.Program.Equality
  Ty
  Exp.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Ren.

Import ListNotations.

Context {A : Type}.
Context `{HostExprs A}.

Inductive Ren : Env → Env → Type :=
  | NoRen : Ren [] []
  | Drop {τ Γ Γ'} : Ren Γ Γ' → Ren (τ :: Γ) Γ'
  | Keep {τ Γ Γ'} : Ren Γ Γ' → Ren (τ :: Γ) (τ :: Γ').

Derive Signature NoConfusion for Ren.

Fixpoint idRen {Γ} : Ren Γ Γ :=
  match Γ with
  | []     => NoRen
  | τ :: Γ => Keep idRen
  end.

Lemma Keep_idRen {Γ τ} : Keep (τ:=τ) (@idRen Γ) = idRen.
Proof. now induction Γ. Qed.

Corollary NoRen_idRen : NoRen = idRen.
Proof. reflexivity. Qed.

Definition skip1 {Γ τ} : Ren (τ :: Γ) Γ := Drop idRen.

Equations RcR {Γ Γ' Γ''} (r : Ren Γ' Γ'') (r' : Ren Γ Γ') : Ren Γ Γ'' :=
  RcR σ        NoRen    := σ;
  RcR σ        (Drop δ) := Drop (RcR σ δ);
  RcR (Drop σ) (Keep δ) := Drop (RcR σ δ);
  RcR (Keep σ) (Keep δ) := Keep (RcR σ δ).

Lemma RcR_idRen_left {Γ Γ'} (σ : Ren Γ Γ') :
  RcR idRen σ = σ.
Proof.
  induction σ; simp RcR; simpl; simp RcR; auto;
  now rewrite IHσ.
Qed.

Lemma RcR_idRen_right {Γ Γ'} (σ : Ren Γ Γ') :
  RcR σ idRen = σ.
Proof.
  induction σ; simp RcR; simpl; simp RcR; auto;
  now rewrite IHσ.
Qed.

Lemma RcR_assoc {Γ Γ' Γ'' Γ'''}
      (σ : Ren Γ'' Γ''') (δ : Ren Γ' Γ'') (ν : Ren Γ Γ') :
  RcR (RcR σ δ) ν = RcR σ (RcR δ ν).
Proof.
  generalize dependent Γ'''.
  generalize dependent Γ''.
  induction ν; simp RcR; simpl; intros; auto.
  - simp RcR.
    now rewrite IHν.
  - dependent elimination δ; simp RcR; simpl.
    + now rewrite IHν.
    + dependent elimination σ; simp RcR; simpl;
      now rewrite IHν.
Qed.

Equations RenVar {τ Γ Γ'} (r : Ren Γ Γ') (v : Var Γ' τ) : Var Γ τ :=
  RenVar NoRen    v      := v;
  RenVar (Drop σ) v      := SV (RenVar σ v);
  RenVar (Keep σ) ZV     := ZV;
  RenVar (Keep σ) (SV v) := SV (RenVar σ v).

Lemma RenVar_idRen {τ Γ} (v : Var Γ τ) :
  RenVar idRen v = v.
Proof.
  induction v; simpl; simp RenVar; intros; auto.
  now rewrite IHv.
Qed.

Lemma RenVar_skip1 {τ τ' Γ} (v : Var Γ τ) :
  RenVar (skip1 (τ:=τ')) v = SV v.
Proof.
  unfold skip1; simp RenVar.
  now rewrite RenVar_idRen.
Qed.

Lemma RenVar_RcR {τ Γ Γ' Γ''} (σ : Ren Γ' Γ'') (δ : Ren Γ Γ') (v : Var Γ'' τ) :
  RenVar (RcR σ δ) v = RenVar δ (RenVar σ v).
Proof.
  generalize dependent Γ''.
  induction δ; simpl; simp RcR; intros; auto.
  - simp RenVar.
    now rewrite <- IHδ.
  - dependent elimination σ; simpl; simp RcR; simp RenVar.
    + now rewrite IHδ.
    + dependent elimination v; simp RenVar; auto.
      now rewrite IHδ.
Qed.

Lemma Keep_RcR Γ Γ' Γ'' τ (r : Ren Γ' Γ'') (r' : Ren Γ Γ') :
  Keep (τ := τ) (RcR r r') = RcR (Keep r) (Keep r').
Proof.
  generalize dependent Γ''.
  now induction r'.
Qed.

Fixpoint RenExp {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ' τ) : Exp Γ τ :=
  match e with
  | Hosted x      => Hosted x
  | EUnit         => EUnit
  | ETrue         => ETrue
  | EFalse        => EFalse
  | If b t e      => If (RenExp r b) (RenExp r t) (RenExp r e)
  | Pair x y      => Pair (RenExp r x) (RenExp r y)
  | Fst p         => Fst (RenExp r p)
  | Snd p         => Snd (RenExp r p)
  | Nil           => Nil
  | Cons x xs     => Cons (RenExp r x) (RenExp r xs)
  | Seq exp1 exp2 => Seq (RenExp r exp1) (RenExp r exp2)

  | VAR v         => VAR (RenVar r v)
  | APP e1 e2     => APP (RenExp r e1) (RenExp r e2)
  | LAM e         => LAM (RenExp (Keep r) e)
  end.

Lemma RenExp_preserves_size {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ' τ) :
  Exp_size (RenExp r e) = Exp_size e.
Proof.
  generalize dependent r.
  generalize dependent Γ.
  now induction e; simpl; simp RcR; simpl; intros; auto.
Qed.

Lemma RenExp_idRen {τ Γ} (e : Exp Γ τ) :
  RenExp idRen e = e.
Proof.
  induction e; simpl; simp RenVar; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto.
  - now rewrite RenVar_idRen.
  - now rewrite Keep_idRen, IHe.
Qed.

Lemma RenExp_RcR {τ Γ Γ' Γ''} (σ : Ren Γ' Γ'') (δ : Ren Γ Γ') (e : Exp Γ'' τ) :
  RenExp (RcR σ δ) e = RenExp δ (RenExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto.
  - now rewrite RenVar_RcR.
  - now rewrite <- IHe; simp RcR.
Qed.

Definition wk {Γ τ τ'} : Exp Γ τ → Exp (τ' :: Γ) τ := RenExp skip1.

Definition identity Γ τ : Exp Γ (τ ⟶ τ) := LAM (VAR ZV).

(** Now that we have weakening, we can define composition. *)

Definition composition {Γ τ τ' τ''}
           (f : Exp Γ (τ' ⟶ τ''))
           (g : Exp Γ (τ ⟶ τ')) : Exp Γ (τ ⟶ τ'') :=
  LAM (APP (wk f) (APP (wk g) (VAR ZV))).

End Ren.
