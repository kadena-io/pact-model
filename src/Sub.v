Require Export
  Coq.Program.Equality
  Ty
  Exp
  Ren.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Definition Sub Γ Γ' := ∀ τ, Var Γ τ → Exp Γ' τ.

Definition idSub {Γ} : Sub Γ Γ := @VAR Γ.

Equations consSub {Γ Γ' τ} (e : Exp Γ' τ) (s : Sub Γ Γ')
          (* Sub (τ :: Γ) Γ' *)
          τ' (v : Var (τ :: Γ) τ') : Exp Γ' τ' :=
  consSub e s τ' ZV      := e;
  consSub e s τ' (SV v') := s _ v'.

Definition tlSub {Γ Γ' τ} (s : Sub (τ :: Γ) Γ') : Sub Γ Γ' :=
  fun τ' v => s τ' (SV v).
Definition hdSub {Γ Γ' τ} (s : Sub (τ :: Γ) Γ') : Exp Γ' τ := s τ ZV.

Definition sskip1 {Γ τ} : Sub Γ (τ :: Γ) := λ _ v, VAR (SV v).

Equations STmL {Γ Γ' τ} (s : Sub Γ Γ')
          (* Sub (τ :: Γ) (τ :: Γ') *)
          τ' (v : Var (τ :: Γ) τ') : Exp (τ :: Γ') τ' :=
  STmL _ τ' ZV      := VAR ZV;
  STmL _ τ' (SV v') := wk (s _ v').

Lemma STmL_idSub {Γ τ} : @STmL Γ Γ τ idSub = idSub.
Proof.
  extensionality τ'.
  extensionality v.
  dependent elimination v.
  - now rewrite STmL_equation_1.
  - now rewrite STmL_equation_2.
Qed.

Corollary tlSub_idSub {Γ τ} : @tlSub Γ _ τ idSub = sskip1.
Proof. reflexivity. Qed.

Notation "{|| e ; .. ; f ||}" := (consSub e .. (consSub f idSub) ..).

Lemma tlSub_sing Γ τ (x : Exp Γ τ) : tlSub {|| x ||} = idSub.
Proof.
  unfold tlSub, idSub.
  extensionality τ'.
  extensionality v.
  now induction v; simp consSub.
Qed.

Fixpoint STmExp {Γ Γ' τ} (s : Sub Γ Γ') (e : Exp Γ τ) : Exp Γ' τ :=
  match e with
  | Constant lit  => Constant lit
  | EUnit         => EUnit
  | ETrue         => ETrue
  | EFalse        => EFalse
  | If b t e      => If (STmExp s b) (STmExp s t) (STmExp s e)
  | Pair x y      => Pair (STmExp s x) (STmExp s y)
  | Fst p         => Fst (STmExp s p)
  | Snd p         => Snd (STmExp s p)
  | Seq exp1 exp2 => Seq (STmExp s exp1) (STmExp s exp2)
  | Let x body    => Let (STmExp s x) (STmExp (STmL s) body)

  | VAR v         => s _ v
  | APP e1 e2     => APP (STmExp s e1) (STmExp s e2)
  | LAM e         => LAM (STmExp (STmL s) e)
  end.

Ltac Rewrites E :=
  (intros; simpl; try rewrite E;
   repeat match goal with
          | [H : _ = _ |- _ ] => rewrite H; clear H
          end; auto).

Lemma STmExp_idSub {Γ τ} (e : Exp Γ τ) :
  STmExp idSub e = e.
Proof.
  induction e; simpl; auto;
  now Rewrites (@STmL_idSub Γ).
Qed.

Definition ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (s' : Sub Γ Γ') :=
  (λ τ v, STmExp s (s' τ v)) : Sub Γ Γ''.

Corollary tlSub_sskip1 Γ Γ' τ (f : Sub (τ :: Γ') Γ) :
  tlSub f = ScS f sskip1.
Proof. reflexivity. Qed.

Corollary ScS_idSub_left Γ Γ' (f : Sub Γ' Γ) :
  ScS idSub f = f.
Proof.
  unfold ScS.
  extensionality τ.
  extensionality v.
  now rewrite STmExp_idSub.
Qed.

Corollary ScS_idSub_right Γ Γ' (f : Sub Γ' Γ) :
  ScS f idSub = f.
Proof.
  unfold ScS.
  extensionality τ.
  extensionality v.
  now induction v.
Qed.

Corollary ScS_assoc Γ Γ' Γ'' Γ'''
          (f : Sub Γ' Γ) (g : Sub Γ'' Γ') (h : Sub Γ''' Γ'') :
  ScS f (ScS g h) = ScS (ScS f g) h.
Proof.
  unfold ScS.
  extensionality τ.
  extensionality v.
  induction (h τ v); simpl; auto;
  rewrite ?STmL_idSub, ?IHe1, ?IHe2, ?IHe3, ?IHe; auto.
Abort.

Definition ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') :=
  (λ τ v, s τ (r τ v)) : Sub Γ Γ''.

Definition RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') :=
  (λ τ v, RTmExp r (s τ v)) : Sub Γ Γ''.

Lemma LiftScR {Γ Γ' Γ'' τ} (r : Ren Γ Γ') (s : Sub Γ' Γ'') :
  STmL (τ:=τ) (ScR s r) = ScR (STmL s) (RTmL r).
Proof.
Admitted.

Lemma ActionScR {Γ Γ' Γ'' τ} (r : Ren Γ Γ') (s : Sub Γ' Γ'') (e : Exp Γ τ) :
  STmExp (ScR s r) e = STmExp s (RTmExp r e).
Proof.
Admitted.

Lemma LiftRcS {Γ Γ' Γ'' τ} (r : Ren Γ' Γ'') (s : Sub Γ Γ') :
  STmL (τ:=τ) (RcS r s) = RcS (RTmL r) (STmL s).
Proof.
Admitted.

Lemma ActionRcS {Γ Γ' Γ'' τ} (r : Ren Γ' Γ'') (s : Sub Γ Γ') (e : Exp Γ τ) :
  STmExp (RcS r s) e = RTmExp r (STmExp s e).
Proof.
Admitted.

Lemma LiftScS {Γ Γ' Γ'' τ} (s : Sub Γ' Γ'') (s' : Sub Γ Γ') :
  STmL (τ:=τ) (ScS s s') = ScS (STmL s) (STmL s').
Proof.
  extensionality τ'.
  extensionality v.
  unfold ScS.
  dependent induction v.
  - now simp STmL; simpl; simp STmL.
  - simp STmL; simpl; simp STmL.
    unfold wk.
    now rewrite <- ActionRcS, <- ActionScR.
Qed.

Lemma ActionScS {Γ Γ' Γ'' τ} (s : Sub Γ' Γ'') (s' : Sub Γ Γ') (e : Exp Γ τ) :
  STmExp (ScS s s') e = STmExp s (STmExp s' e).
Proof.
  generalize dependent Γ''.
  generalize dependent Γ'.
  induction e; simpl; intros; auto;
  rewrite ?STmL_idSub, ?IHe1, ?IHe2, ?IHe3, ?IHe; auto.
  - rewrite LiftScS.
    now rewrite IHe2.
  - rewrite LiftScS.
    now rewrite IHe.
Qed.
