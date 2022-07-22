Require Import
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Value.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Inductive Ren : Env → Env → Set :=
  | NoRen : Ren [] []
  | Drop {τ Γ Γ'} : Ren Γ Γ' → Ren (τ :: Γ) Γ'
  | Keep {τ Γ Γ'} : Ren Γ Γ' → Ren (τ :: Γ) (τ :: Γ').

Derive Signature NoConfusion NoConfusionHom Subterm EqDec for Ren.

Fixpoint idRen {Γ} : Ren Γ Γ :=
  match Γ with
  | []     => NoRen
  | τ :: Γ => Keep idRen
  end.

Lemma Keep_idRen {Γ τ} : Keep (τ:=τ) (@idRen Γ) = idRen.
Proof. now induction Γ. Qed.

Equations DropAll {Γ} : Ren Γ [] :=
  DropAll (Γ:=[])      := NoRen;
  DropAll (Γ:=_ :: xs) := Drop (DropAll (Γ:=xs)).

Corollary NoRen_idRen : NoRen = idRen.
Proof. reflexivity. Qed.

Corollary DropAll_nil_idRen : DropAll (Γ:=[]) = idRen.
Proof. reflexivity. Qed.

Definition skip1 {Γ τ} : Ren (τ :: Γ) Γ := Drop idRen.

Equations RcR {Γ Γ' Γ''} (r : Ren Γ' Γ'') (r' : Ren Γ Γ') : Ren Γ Γ'' :=
  RcR σ        NoRen    := σ;
  RcR σ        (Drop δ) := Drop (RcR σ δ);
  RcR (Drop σ) (Keep δ) := Drop (RcR σ δ);
  RcR (Keep σ) (Keep δ) := Keep (RcR σ δ).

Lemma RcR_idRen_left {Γ Γ'} (σ : Ren Γ Γ') :
  RcR idRen σ = σ.
Proof. induction σ; simp RcR; simpl; simp RcR; sauto. Qed.

Lemma RcR_idRen_right {Γ Γ'} (σ : Ren Γ Γ') :
  RcR σ idRen = σ.
Proof. induction σ; simp RcR; simpl; simp RcR; sauto. Qed.

Lemma RcR_assoc {Γ Γ' Γ'' Γ'''}
      (σ : Ren Γ'' Γ''') (δ : Ren Γ' Γ'') (ν : Ren Γ Γ') :
  RcR (RcR σ δ) ν = RcR σ (RcR δ ν).
Proof.
  generalize dependent Γ'''.
  generalize dependent Γ''.
  induction ν; simp RcR; simpl; intros; auto.
  - simp RcR; sauto.
  - dependent elimination δ; simp RcR; simpl.
    + sauto.
    + dependent elimination σ; simp RcR; simpl; sauto.
Qed.

Equations RenVar {τ Γ Γ'} (r : Ren Γ Γ') (v : Var Γ' τ) : Var Γ τ :=
  RenVar NoRen    v      := v;
  RenVar (Drop σ) v      := SV (RenVar σ v);
  RenVar (Keep σ) ZV     := ZV;
  RenVar (Keep σ) (SV v) := SV (RenVar σ v).

Lemma RenVar_idRen {τ Γ} (v : Var Γ τ) :
  RenVar idRen v = v.
Proof. induction v; simpl; simp RenVar; intros; sauto. Qed.

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
  - simp RenVar; sauto.
  - dependent elimination σ; simpl; simp RcR; simp RenVar.
    + sauto.
    + dependent elimination v; simp RenVar; sauto.
Qed.

Lemma Keep_RcR Γ Γ' Γ'' τ (r : Ren Γ' Γ'') (r' : Ren Γ Γ') :
  Keep (τ := τ) (RcR r r') = RcR (Keep r) (Keep r').
Proof.
  generalize dependent Γ''.
  now induction r'.
Qed.

Fixpoint RenExp {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ' τ) : Exp Γ τ :=
  match e with
  | VAR v         => VAR (RenVar r v)
  | APP e1 e2     => APP (RenExp r e1) (RenExp r e2)
  | LAM e         => LAM (RenExp (Keep r) e)

  | Error e       => Error e
  | Lit l         => Lit l
  | Bltn b        => Bltn b
  | Symbol s      => Symbol s
  | If b t e      => If (RenExp r b) (RenExp r t) (RenExp r e)
  | Pair x y      => Pair (RenExp r x) (RenExp r y)
  | Fst p         => Fst (RenExp r p)
  | Snd p         => Snd (RenExp r p)
  | Nil           => Nil
  | Cons x xs     => Cons (RenExp r x) (RenExp r xs)
  | Car xs        => Car (RenExp r xs)
  | Cdr xs        => Cdr (RenExp r xs)
  | IsNil xs      => IsNil (RenExp r xs)
  | Seq exp1 exp2 => Seq (RenExp r exp1) (RenExp r exp2)

  | Capability Hp Hv n p v =>
      Capability Hp Hv (RenExp r n) (RenExp r p) (RenExp r v)
  | WithCapability Hv mn p m c e =>
      WithCapability Hv (RenExp r mn) (RenExp r p) (RenExp r m)
                     (RenExp r c) (RenExp r e)
  | ComposeCapability Hv mn p m c =>
      ComposeCapability Hv (RenExp r mn) (RenExp r p) (RenExp r m)
                        (RenExp r c)
  | InstallCapability c    => InstallCapability (RenExp r c)
  | RequireCapability c    => RequireCapability (RenExp r c)
  end.

Lemma RenExp_preserves_size {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ' τ) :
  Exp_size (RenExp r e) = Exp_size e.
Proof.
  generalize dependent r.
  generalize dependent Γ.
  induction e; simp RcR; sauto.
Qed.

Lemma RenExp_idRen {τ Γ} (e : Exp Γ τ) :
  RenExp idRen e = e.
Proof.
  induction e;
  rewrite /= ?RenVar_idRen //; sauto.
Qed.

Lemma RenExp_DropAll {τ} (e : Exp [] τ) :
  RenExp DropAll e = e.
Proof. rewrite DropAll_nil_idRen RenExp_idRen //. Qed.

Lemma RenExp_RcR {τ Γ Γ' Γ''} (σ : Ren Γ' Γ'') (δ : Ren Γ Γ') (e : Exp Γ'' τ) :
  RenExp (RcR σ δ) e = RenExp δ (RenExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; intros;
  rewrite /= ?RenVar_RcR //;
  simp RcR; sauto.
Qed.

Lemma RenExp_ValueP {Γ Γ' τ} {v : Exp Γ τ} (σ : Ren Γ' Γ) :
  ValueP v → ValueP (RenExp σ v).
Proof. induction 1; sauto. Qed.

Definition wk {Γ τ τ'} : Exp Γ τ → Exp (τ' :: Γ) τ := RenExp skip1.
