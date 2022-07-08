Require Export
  Coq.Program.Equality
  Coq.Program.Program
  Ty
  Exp
  Ren.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Ltac reduce :=
  repeat (lazymatch goal with
          | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
              apply inj_pair2 in H; subst
          | [ H : _ ∧ _ |- _ ] => destruct H
          | [ H : _ * _ |- _ ] => destruct H
          | [ H : ∃ _, _ |- _ ] => destruct H
          | [ H : { _ : _ | _ } |- _ ] => destruct H
          | [ H : { _ : _ & _ } |- _ ] => destruct H
          end; subst).

Ltac inv H := inversion H; subst; clear H; reduce.

Section Sub.

Import ListNotations.

Context {A : Type}.
Context `{HostExprs A}.

Inductive Sub (Γ : Env) : Env → Type :=
  | NoSub : Sub Γ []
  | Push {Γ' τ} : Exp Γ τ → Sub Γ Γ' → Sub Γ (τ :: Γ').

#[global] Arguments NoSub {Γ}.
#[global] Arguments Push {Γ Γ' τ} _ _.

Derive Signature NoConfusion for Sub.

Equations get `(s : Sub Γ' Γ) `(v : Var Γ τ) : Exp Γ' τ :=
  get (Push x _)   ZV    := x;
  get (Push _ xs) (SV v) := get xs v.

Equations ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') : Sub Γ Γ'' :=
  ScR NoSub      δ := NoSub;
  ScR (Push t σ) δ := Push (RenExp δ t) (ScR σ δ).

Fixpoint idSub {Γ} : Sub Γ Γ :=
  match Γ with
  | []     => NoSub
  | τ :: Γ => Push (VAR ZV) (ScR (@idSub Γ) skip1)
  end.

Corollary NoSub_idSub : NoSub = @idSub [].
Proof. reflexivity. Qed.

Equations RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') : Sub Γ Γ'' :=
  RcS NoRen    δ          := δ;
  RcS (Drop σ) (Push t δ) := RcS σ δ;
  RcS (Keep σ) (Push t δ) := Push t (RcS σ δ).

Definition Dropₛ {Γ Γ' τ} (s : Sub Γ Γ') : Sub (τ :: Γ) Γ' :=
  ScR s skip1.

Definition Keepₛ {Γ Γ' τ} (s : Sub Γ Γ') : Sub (τ :: Γ) (τ :: Γ') :=
  Push (VAR ZV) (Dropₛ s).

Equations SubVar {Γ Γ' τ} (s : Sub Γ Γ') (v : Var Γ' τ) : Exp Γ τ :=
  SubVar (Push t σ) ZV     := t;
  SubVar (Push t σ) (SV v) := SubVar σ v.

Fixpoint SubExp {Γ Γ' τ} (s : Sub Γ Γ') (e : Exp Γ' τ) : Exp Γ τ :=
  match e with
  | HostedExp x   => HostedExp x
  | HostedVal x   => HostedVal x
  | HostedFun x   => HostedFun x
  | EUnit         => EUnit
  | ETrue         => ETrue
  | EFalse        => EFalse
  | If b t e      => If (SubExp s b) (SubExp s t) (SubExp s e)
  | Pair x y      => Pair (SubExp s x) (SubExp s y)
  | Fst p         => Fst (SubExp s p)
  | Snd p         => Snd (SubExp s p)
  | Nil           => Nil
  | Cons x xs     => Cons (SubExp s x) (SubExp s xs)
  | Seq exp1 exp2 => Seq (SubExp s exp1) (SubExp s exp2)

  | VAR v         => SubVar s v
  | APP e1 e2     => APP (SubExp s e1) (SubExp s e2)
  | LAM e         => LAM (SubExp (Keepₛ s) e)
  end.

Fixpoint ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (δ : Sub Γ Γ') : Sub Γ Γ'' :=
  match s with
  | NoSub    => NoSub
  | Push e σ => Push (SubExp δ e) (ScS σ δ)
  end.

Lemma ScR_ScR {Γ Γ' Γ'' Γ'''} (σ : Sub Γ'' Γ''') (δ : Ren Γ' Γ'') (ν : Ren Γ Γ') :
  ScR (ScR σ δ) ν = ScR σ (RcR δ ν).
Proof.
  induction σ; simp ScR; auto.
  now rewrite RenExp_RcR, IHσ.
Qed.

Lemma ScR_RcS {Γ Γ' Γ'' Γ'''} (σ : Ren Γ'' Γ''') (δ : Sub Γ' Γ'') (ν : Ren Γ Γ') :
  ScR (RcS σ δ) ν = RcS σ (ScR δ ν).
Proof.
  induction σ; dependent elimination δ; auto.
  - simp RcS.
    now simp ScR.
  - simp RcS.
    simp ScR.
    simp RcS.
    now rewrite IHσ.
Qed.

Lemma RcS_idRen {Γ Γ'} (σ : Sub Γ Γ') :
  RcS idRen σ = σ.
Proof.
  induction σ; simp RcS; simpl; simp RcS; auto.
  now rewrite IHσ.
Qed.

Lemma RcS_idSub {Γ Γ'} (σ : Ren Γ Γ') :
  RcS σ idSub = ScR idSub σ.
Proof.
  induction σ; simp RcS; simpl; simp RcS; simp ScR; auto.
  - rewrite <- ScR_RcS.
    rewrite IHσ.
    rewrite ScR_ScR.
    unfold skip1.
    simp RcR.
    now rewrite RcR_idRen_right.
  - simpl.
    f_equal.
    rewrite <- ScR_RcS.
    rewrite IHσ.
    rewrite ScR_ScR.
    unfold skip1.
    rewrite ScR_ScR.
    simp RcR.
    rewrite RcR_idRen_left.
    now rewrite RcR_idRen_right.
Qed.

Lemma RcS_skip1 {Γ Γ' τ} (e : Exp Γ τ) (σ : Sub Γ Γ') :
  RcS skip1 (Push e σ) = σ.
Proof.
  unfold skip1.
  simp RcS.
  now rewrite RcS_idRen.
Qed.

Lemma SubVar_RcS {Γ Γ' Γ'' τ} (σ : Ren Γ' Γ'') (δ : Sub Γ Γ') (v : Var Γ'' τ) :
  SubVar (RcS σ δ) v = SubVar δ (RenVar σ v).
Proof.
  induction σ; simp RenVar; auto.
  - dependent elimination δ.
    now simp RcS.
  - dependent elimination δ.
    simp RcS.
    dependent elimination v.
    + now simp RenVar.
    + simp RenVar.
      now simp SubVar.
Qed.

Lemma SubExp_RcS {Γ Γ' Γ'' τ} (σ : Ren Γ' Γ'') (δ : Sub Γ Γ') (e : Exp Γ'' τ) :
  SubExp (RcS σ δ) e = SubExp δ (RenExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto; f_equal.
  - now rewrite SubVar_RcS.
  - specialize (IHe _ _ (Keep σ) (Keepₛ δ)).
    rewrite <- IHe.
    unfold Keepₛ.
    simp RcS.
    repeat f_equal.
    unfold Dropₛ.
    now apply ScR_RcS.
Qed.

Lemma SubVar_ScR {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Ren Γ Γ') (v : Var Γ'' τ) :
  SubVar (ScR σ δ) v = RenExp δ (SubVar σ v).
Proof.
  induction σ; simp SubVar; simp ScR.
  - now inversion v.
  - now dependent elimination v; simp SubVar.
Qed.

Lemma SubExp_ScR {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Ren Γ Γ') (e : Exp Γ'' τ) :
  SubExp (ScR σ δ) e = RenExp δ (SubExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto; f_equal.
  - now rewrite SubVar_ScR.
  - rewrite <- IHe.
    unfold Keepₛ.
    simp ScR.
    simpl.
    repeat f_equal.
    unfold Dropₛ.
    rewrite !ScR_ScR.
    unfold skip1; simp RcR.
    rewrite RcR_idRen_left.
    now rewrite RcR_idRen_right.
Qed.

Lemma ScS_ScR {Γ Γ' Γ'' Γ'''} (σ : Sub Γ'' Γ''') (δ : Ren Γ' Γ'') (ν : Sub Γ Γ') :
  ScS (ScR σ δ) ν = ScS σ (RcS δ ν).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction σ; simp ScR; simp ScS; simpl; intros; auto.
  simp ScR.
  simpl.
  rewrite IHσ.
  f_equal.
  now rewrite <- SubExp_RcS.
Qed.

Lemma ScR_ScS {Γ Γ' Γ'' Γ'''} (σ : Sub Γ'' Γ''') (δ : Sub Γ' Γ'') (ν : Ren Γ Γ') :
  ScR (ScS σ δ) ν = ScS σ (ScR δ ν).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction σ; simp ScR; simp ScS; simpl; intros; auto.
  simp ScR.
  rewrite IHσ.
  f_equal.
  now rewrite <- SubExp_ScR.
Qed.

Lemma SubVar_idSub {Γ τ} (v : Var Γ τ) :
  SubVar idSub v = VAR v.
Proof.
  induction v; simpl; simp SubVar; auto.
  rewrite SubVar_ScR.
  rewrite IHv.
  simpl.
  now rewrite RenVar_skip1.
Qed.

Lemma SubVar_ScS {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Sub Γ Γ') (v : Var Γ'' τ) :
  SubVar (ScS σ δ) v = SubExp δ (SubVar σ v).
Proof.
  induction σ; simp SubVar; simp ScR.
  - now inversion v.
  - simpl.
    now dependent elimination v; simp SubVar.
Qed.

Lemma SubExp_idSub {Γ τ} (e : Exp Γ τ) :
  SubExp idSub e = e.
Proof.
  induction e; simpl; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto.
  - now rewrite SubVar_idSub.
  - f_equal.
    rewrite <- IHe at 2.
    now f_equal.
Qed.

Lemma SubExp_ScS {Γ Γ' Γ'' τ} (σ : Sub Γ' Γ'') (δ : Sub Γ Γ') (e : Exp Γ'' τ) :
  SubExp (ScS σ δ) e = SubExp δ (SubExp σ e).
Proof.
  generalize dependent Γ'.
  generalize dependent Γ.
  induction e; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto; f_equal.
  - now rewrite SubVar_ScS.
  - rewrite <- IHe; clear.
    f_equal.
    unfold Keepₛ.
    unfold Dropₛ.
    simpl.
    simp SubVar.
    f_equal.
    rewrite ScR_ScS.
    remember (ScR δ skip1) as g; clear.
    unfold skip1.
    generalize dependent g.
    generalize dependent Γ0.
    induction σ; simpl; simp ScR; simpl; intros; auto.
    f_equal; auto.
    rewrite <- SubExp_RcS.
    simp RcS.
    now rewrite RcS_idRen.
Qed.

Lemma ScS_idSub_right {Γ Γ'} (σ : Sub Γ Γ') :
  ScS σ idSub = σ.
Proof.
  induction σ; simpl; auto.
  rewrite IHσ.
  now rewrite SubExp_idSub.
Qed.

Lemma ScS_idSub_left {Γ Γ'} (σ : Sub Γ Γ') :
  ScS idSub σ = σ.
Proof.
  induction σ; simpl; auto.
  simp SubVar.
  rewrite ScS_ScR.
  unfold skip1.
  simp RcS.
  rewrite RcS_idRen.
  now rewrite IHσ.
Qed.

Notation "{|| e ; .. ; f ||}" := (Push e .. (Push f idSub) ..).

Equations valueToExp `(c : Value τ) : { v : Exp [] τ & ValueP v } := {
  valueToExp (HostValue x)             := existT _ (HostedVal x) (HostedValP x);
  valueToExp VUnit                     := existT _ EUnit (UnitP []);
  valueToExp VTrue                     := existT _ (ETrue) TrueP;
  valueToExp VFalse                    := existT _ (EFalse) FalseP;
  valueToExp (VPair x y)               :=
    let '(existT _ v1 H1) := valueToExp x in
    let '(existT _ v2 H2) := valueToExp y in
    existT _ (Pair v1 v2) (PairP H1 H2);
  valueToExp VNil                      := existT _ Nil NilP;
  valueToExp (VCons x xs)              :=
    let '(existT _ v1 H1) := valueToExp x in
    let '(existT _ v2 H2) := valueToExp xs in
    existT _ (Cons v1 v2) (ConsP H1 H2);
  valueToExp (ClosureExp (Lambda e))   := existT _ (LAM e) (LambdaP _);
  valueToExp (ClosureExp (Func f))     := existT _ (HostedFun f) (HostedFunP f)
}.

Equations msubst {Γ ty τ} (e : Exp (ty :: Γ) τ) (s : ValEnv Γ) : Exp [ty] τ := {
  msubst e Empty      := e;
  msubst e (Val x xs) :=
    let r := DropAll in
    let v := RenExp r (projT1 (valueToExp x)) in
    let s := Keepₛ {|| v ||} in
    msubst (SubExp s e) xs
}.

Equations expToValue `{v : Exp [] τ} (V : ValueP v) : Value τ :=
  expToValue (HostedValP x) := HostValue x;
  expToValue (HostedFunP x) := ClosureExp (Func x);
  expToValue (UnitP _)      := VUnit;
  expToValue TrueP          := VTrue;
  expToValue FalseP         := VFalse;
  expToValue (PairP X Y)    := VPair (expToValue X) (expToValue Y);
  expToValue NilP           := VNil;
  expToValue (ConsP X XS)   := VCons (expToValue X) (expToValue XS);
  expToValue (LambdaP e)    := ClosureExp (Lambda e).

Lemma expToValue_valueToExp `(v : Value τ) :
  let '(existT _ e H) := valueToExp v in
  expToValue H = v.
Proof.
  induction v;
  simp valueToExp; simp expToValue; auto.
  - now destruct (valueToExp v1), (valueToExp v2); subst.
  - now destruct (valueToExp v1), (valueToExp v2); subst.
  - now destruct c; simp valueToExp; simp expToValue.
Qed.

Lemma RenExp_ValueP {Γ Γ' τ} {v : Exp Γ τ} (σ : Ren Γ' Γ) :
  ValueP v → ValueP (RenExp σ v).
Proof.
  intros.
  now induction X; simpl; intros; try constructor.
Defined.

Lemma SubExp_ValueP {Γ Γ' τ} {v : Exp Γ τ} (σ : Sub Γ' Γ) :
  ValueP v → ValueP (SubExp σ v).
Proof.
  intros.
  now induction X; simpl; intros; try constructor.
Defined.

End Sub.

Notation "{|| e ; .. ; f ||}" := (Push e .. (Push f idSub) ..).
