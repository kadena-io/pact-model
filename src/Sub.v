Require Import
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Value
  Pact.Ren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Inductive Sub (Γ : Env) : Env → Set :=
  | NoSub : Sub Γ []
  | Push {Γ' τ} : Exp Γ τ → Sub Γ Γ' → Sub Γ (τ :: Γ').

#[global] Arguments NoSub {Γ}.
#[global] Arguments Push {Γ Γ' τ} _ _.

Derive Signature NoConfusion NoConfusionHom Subterm for Sub.

Equations get `(s : Sub Γ' Γ) `(v : Var Γ τ) : Exp Γ' τ :=
  get (Push x _)   ZV    := x;
  get (Push _ xs) (SV v) := get xs v.

Equations ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') : Sub Γ Γ'' :=
  ScR NoSub      δ := NoSub;
  ScR (Push t σ) δ := Push (RenExp δ t) (ScR σ δ).

Lemma ScR_idRen {Γ Γ'} (s : Sub Γ Γ') :
  ScR s idRen = s.
Proof.
  induction s; simp ScR;
  rewrite ?RenExp_idRen; sauto.
Qed.

Fixpoint idSub {Γ} : Sub Γ Γ :=
  match Γ with
  | []     => NoSub
  | τ :: Γ => Push (VAR ZV) (ScR (@idSub Γ) skip1)
  end.

Corollary NoSub_idSub : NoSub (Γ:=[]) = idSub.
Proof. reflexivity. Qed.

Equations RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') : Sub Γ Γ'' :=
  RcS NoRen    δ          := δ;
  RcS (Drop σ) (Push t δ) := RcS σ δ;
  RcS (Keep σ) (Push t δ) := Push t (RcS σ δ).

Definition Dropₛ {Γ Γ' τ} (s : Sub Γ Γ') : Sub (τ :: Γ) Γ' :=
  ScR s skip1.

Definition Keepₛ {Γ Γ' τ} (s : Sub Γ Γ') : Sub (τ :: Γ) (τ :: Γ') :=
  Push (VAR ZV) (Dropₛ s).

Corollary Keepₛ_idSub {Γ τ} :
  Keepₛ (Γ:=Γ) (Γ':=Γ) (τ:=τ) idSub = idSub.
Proof. reflexivity. Qed.

Equations SubVar {Γ Γ' τ} (s : Sub Γ Γ') (v : Var Γ' τ) : Exp Γ τ :=
  SubVar (Push t σ) ZV     := t;
  SubVar (Push t σ) (SV v) := SubVar σ v.

Fixpoint SubExp {Γ Γ' τ} (s : Sub Γ Γ') (e : Exp Γ' τ) : Exp Γ τ :=
  match e with
  | VAR v         => SubVar s v
  | APP e1 e2     => APP (SubExp s e1) (SubExp s e2)
  | LAM e         => LAM (SubExp (Keepₛ s) e)

  | Error e       => Error e
  | Lit l         => Lit l
  | Bltn b        => Bltn b
  | Symbol s      => Symbol s
  | If b t e      => If (SubExp s b) (SubExp s t) (SubExp s e)
  | Pair x y      => Pair (SubExp s x) (SubExp s y)
  | Fst p         => Fst (SubExp s p)
  | Snd p         => Snd (SubExp s p)
  | Nil           => Nil
  | Cons x xs     => Cons (SubExp s x) (SubExp s xs)
  | Car xs        => Car (SubExp s xs)
  | Cdr xs        => Cdr (SubExp s xs)
  | IsNil xs      => IsNil (SubExp s xs)
  | Seq exp1 exp2 => Seq (SubExp s exp1) (SubExp s exp2)

  | Capability Hp Hv n p v =>
      Capability Hp Hv (SubExp s n) (SubExp s p) (SubExp s v)
  | WithCapability Hv mn p m c e =>
      WithCapability Hv (SubExp s mn) (SubExp s p) (SubExp s m)
                     (SubExp s c) (SubExp s e)
  | ComposeCapability Hv mn p m c =>
      ComposeCapability Hv (SubExp s mn) (SubExp s p) (SubExp s m)
                        (SubExp s c)
  | InstallCapability c => InstallCapability (SubExp s c)
  | RequireCapability c => RequireCapability (SubExp s c)
  end.

Fixpoint ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (δ : Sub Γ Γ') : Sub Γ Γ'' :=
  match s with
  | NoSub    => NoSub
  | Push e σ => Push (SubExp δ e) (ScS σ δ)
  end.

Lemma ScR_ScR {Γ Γ' Γ'' Γ'''} (σ : Sub Γ'' Γ''') (δ : Ren Γ' Γ'') (ν : Ren Γ Γ') :
  ScR (ScR σ δ) ν = ScR σ (RcR δ ν).
Proof.
  induction σ; simp ScR;
  rewrite ?RenExp_RcR; sauto.
Qed.

Lemma ScR_RcS {Γ Γ' Γ'' Γ'''} (σ : Ren Γ'' Γ''') (δ : Sub Γ' Γ'') (ν : Ren Γ Γ') :
  ScR (RcS σ δ) ν = RcS σ (ScR δ ν).
Proof.
  induction σ;
  dependent elimination δ;
  simp RcS; simp ScR; sauto.
Qed.

Lemma RcS_idRen {Γ Γ'} (σ : Sub Γ Γ') :
  RcS idRen σ = σ.
Proof.
  induction σ; simp RcS; simpl; simp RcS; sauto.
Qed.

Lemma RcS_idSub {Γ Γ'} (σ : Ren Γ Γ') :
  RcS σ idSub = ScR idSub σ.
Proof.
  induction σ; simp RcS; simpl; simp RcS; simp ScR; auto.
  - rewrite -ScR_RcS IHσ ScR_ScR /skip1.
    simp RcR.
    rewrite RcR_idRen_right //.
  - rewrite -ScR_RcS IHσ !ScR_ScR /skip1.
    simp RcR.
    rewrite RcR_idRen_left RcR_idRen_right //.
Qed.

Corollary RcS_skip1 {Γ Γ' τ} (e : Exp Γ τ) (σ : Sub Γ Γ') :
  RcS skip1 (Push e σ) = σ.
Proof.
  rewrite /skip1.
  simp RcS.
  rewrite RcS_idRen //.
Qed.

Lemma RcS_DropAll {Γ Γ'} (σ : Sub Γ' Γ) :
  RcS DropAll σ = NoSub.
Proof.
  now induction σ; simp RcS.
Qed.

Lemma SubVar_RcS {Γ Γ' Γ'' τ} (σ : Ren Γ' Γ'') (δ : Sub Γ Γ') (v : Var Γ'' τ) :
  SubVar (RcS σ δ) v = SubVar δ (RenVar σ v).
Proof.
  induction σ; simp RenVar; auto.
  - dependent elimination δ.
    now simp RcS.
  - dependent elimination δ.
    dependent elimination v;
    now simp RcS; simp RenVar; simp SubVar.
Qed.

Lemma SubExp_RcS {Γ Γ' Γ'' τ} (σ : Ren Γ' Γ'') (δ : Sub Γ Γ') (e : Exp Γ'' τ) :
  SubExp (RcS σ δ) e = SubExp δ (RenExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto.
  1: now rewrite SubVar_RcS.
  1: {
    specialize (IHe _ _ (Keep σ) (Keepₛ δ)).
    rewrite <- IHe.
    unfold Keepₛ.
    simp RcS.
    repeat f_equal.
    unfold Dropₛ.
    now apply ScR_RcS.
  }
  all: sauto.
Qed.

Lemma SubVar_ScR {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Ren Γ Γ') (v : Var Γ'' τ) :
  SubVar (ScR σ δ) v = RenExp δ (SubVar σ v).
Proof.
  induction σ; simp SubVar; simp ScR.
  - sauto.
  - now dependent elimination v; simp SubVar.
Qed.

Lemma SubExp_ScR {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Ren Γ Γ') (e : Exp Γ'' τ) :
  SubExp (ScR σ δ) e = RenExp δ (SubExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto.
  1: now rewrite SubVar_ScR.
  1: {
    rewrite <- IHe.
    unfold Keepₛ.
    simp ScR.
    simpl.
    repeat f_equal.
    unfold Dropₛ.
    rewrite !ScR_ScR.
    unfold skip1; simp RcR.
    rewrite RcR_idRen_left.
    now rewrite RcR_idRen_right.
  }
  all: sauto.
Qed.

Lemma ScS_ScR {Γ Γ' Γ'' Γ'''} (σ : Sub Γ'' Γ''') (δ : Ren Γ' Γ'') (ν : Sub Γ Γ') :
  ScS (ScR σ δ) ν = ScS σ (RcS δ ν).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction σ; simp ScR; simp ScS;
  simpl; intros; auto; simp ScR.
  rewrite /= -SubExp_RcS; sauto.
Qed.

Lemma ScR_ScS {Γ Γ' Γ'' Γ'''} (σ : Sub Γ'' Γ''') (δ : Sub Γ' Γ'') (ν : Ren Γ Γ') :
  ScR (ScS σ δ) ν = ScS σ (ScR δ ν).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction σ; simp ScR; simp ScS;
  simpl; intros; auto; simp ScR.
  rewrite /= -SubExp_ScR; sauto.
Qed.

Lemma SubVar_idSub {Γ τ} (v : Var Γ τ) :
  SubVar idSub v = VAR v.
Proof.
  induction v; simpl; simp SubVar; auto.
  rewrite SubVar_ScR IHv /= RenVar_skip1 //.
Qed.

Lemma SubVar_ScS {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Sub Γ Γ') (v : Var Γ'' τ) :
  SubVar (ScS σ δ) v = SubExp δ (SubVar σ v).
Proof.
  induction σ; simp SubVar; simp ScR.
  - sauto.
  - now dependent elimination v; simpl; simp SubVar.
Qed.

Lemma SubExp_idSub {Γ τ} (e : Exp Γ τ) :
  SubExp idSub e = e.
Proof.
  induction e; simpl;
  rewrite ?SubVar_idSub; sauto.
Qed.

Lemma SubExp_ScS {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Sub Γ Γ') (e : Exp Γ'' τ) :
  SubExp (ScS σ δ) e = SubExp δ (SubExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto.
  1: now rewrite SubVar_ScS.
  1: {
    rewrite <- IHe; clear.
    unfold Keepₛ.
    unfold Dropₛ.
    simpl; simp SubVar.
    rewrite ScR_ScS.
    remember (ScR δ skip1) as g; clear.
    unfold skip1.
    generalize dependent g.
    generalize dependent Γ0.
    induction σ; simpl; simp ScR;
    simpl; intros; auto.
    rewrite <- SubExp_RcS.
    simp RcS.
    rewrite RcS_idRen.
    rewrite ScS_ScR.
    simp RcS.
    now rewrite RcS_idRen.
  }
  all: sauto.
Qed.

Lemma ScS_idSub_right {Γ Γ'} (σ : Sub Γ Γ') :
  ScS σ idSub = σ.
Proof.
  induction σ; simpl; rewrite ?SubExp_idSub; sauto.
Qed.

Lemma ScS_idSub_left {Γ Γ'} (σ : Sub Γ Γ') :
  ScS idSub σ = σ.
Proof.
  induction σ; rewrite //= ScS_ScR RcS_skip1 IHσ //.
Qed.

Lemma ScS_Keepₛ {Γ Γ' Γ'' τ} (f : Sub Γ' Γ'') (g : Sub Γ Γ') :
  ScS (Keepₛ (τ:=τ) f) (Keepₛ g) = Keepₛ (ScS f g).
Proof.
  unfold Keepₛ, Dropₛ.
  rewrite /= ScS_ScR ScR_ScS RcS_skip1 //.
Qed.

Notation "{|| e ; .. ; f ||}" := (Push e%exp .. (Push f%exp idSub) ..).

Lemma SubExp_Push {Γ Γ' τ ty} (x : Exp Γ' ty) (s : Sub Γ' Γ) (e : Exp (ty :: Γ) τ) :
  SubExp (Push x s) e = SubExp {|| x ||} (SubExp (Keepₛ s) e).
Proof.
  rewrite -SubExp_ScS /= ScS_ScR RcS_skip1 ScS_idSub_right //.
Qed.

Corollary SubExp_closed `(s : Sub [] []) `(e : [] ⊢ τ) :
  SubExp s e = e.
Proof.
  dependent elimination s.
  rewrite NoSub_idSub SubExp_idSub //.
Qed.

Lemma SubExp_SubExp `(s : Sub [] Γ) (s' : Sub Γ []) `(e : [] ⊢ τ) :
  SubExp s (SubExp s' e) = e.
Proof.
  simpl; induction s; dependent elimination s'.
  - rewrite NoSub_idSub !SubExp_idSub //.
  - rewrite -SubExp_ScS /= NoSub_idSub SubExp_idSub //.
Qed.

Lemma SubExp_RenExp `(s : Sub [] Γ) (r' : Ren Γ []) `(e : [] ⊢ τ) :
  SubExp s (RenExp r' e) = e.
Proof.
  simpl; induction s; dependent destruction r'.
  - rewrite NoSub_idSub SubExp_idSub NoRen_idRen RenExp_idRen //.
  - rewrite -SubExp_RcS.
    simp RcS.
    now rewrite SubExp_RcS.
Qed.

Lemma SubExp_VAR_ZV {Γ τ} (s : Sub [] Γ) (x : Exp [] τ) :
  SubExp (Push x s) (VAR ZV) = x.
Proof.
  now simpl; simp SubVar.
Qed.

Lemma SubExp_VAR_SV {Γ τ τ'} (s : Sub [] Γ) (x : Exp [] τ') (v : Var Γ τ) :
  SubExp (Push x s) (VAR (SV v)) = SubExp s (VAR v).
Proof.
  now simpl; simp SubVar.
Qed.

Lemma SubExp_ValueP {Γ Γ' τ} {v : Exp Γ τ} (σ : Sub Γ' Γ) :
  ValueP v → ValueP (SubExp σ v).
Proof.
  induction 1; sauto.
Qed.
