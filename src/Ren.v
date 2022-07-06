Require Export
  Ty
  Exp.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Section Ren.

Definition Ren Γ Γ' := ∀ τ, Var Γ τ → Var Γ' τ.

Definition idRen {Γ} : Ren Γ Γ := λ _, id.

Definition tlRen {Γ Γ' τ} (r : Ren (τ :: Γ) Γ') : Ren Γ Γ' :=
  fun τ' v => r τ' (SV v).
Definition hdRen {Γ Γ' τ} (r : Ren (τ :: Γ) Γ') : Var Γ' τ := r τ ZV.

Definition skip1 {Γ τ} : Ren Γ (τ :: Γ) := λ _, SV.

Equations skipn {Γ} Γ' : Ren Γ (Γ' ++ Γ) :=
  skipn []        := λ _, id;
  skipn (x :: xs) := λ τ v, SV (skipn xs τ v).

Equations RTmL {Γ Γ' τ} (r : Ren Γ Γ')
          (* Ren (τ :: Γ) (τ :: Γ') *)
          τ' (v : Var (τ :: Γ) τ') : Var (τ :: Γ') τ' :=
  RTmL r τ' ZV      := ZV;
  RTmL r τ' (SV v') := SV (r _ v').

Lemma RTmL_id {Γ τ} : @RTmL Γ Γ τ (λ _, id) = λ _, id.
Proof.
  extensionality τ'.
  extensionality v.
  dependent elimination v.
  - now rewrite RTmL_equation_1.
  - now rewrite RTmL_equation_2.
Qed.

Definition RcR {Γ Γ' Γ''} (r : Ren Γ' Γ'') (r' : Ren Γ Γ') :=
  (λ τ v, r τ (r' τ v)) : Ren Γ Γ''.

Lemma LiftRcR Γ Γ' Γ'' τ (r : Ren Γ' Γ'') (r' : Ren Γ Γ') :
  RTmL (τ := τ) (RcR r r') = RcR (RTmL r) (RTmL r').
Proof.
  extensionality τ'.
  extensionality v.
  now dependent elimination v.
Qed.

Corollary tlRen_skip1 Γ Γ' τ (f : Ren (τ :: Γ') Γ) :
  tlRen f = RcR f skip1.
Proof. reflexivity. Qed.

Corollary RcR_idRen_left Γ Γ' (f : Ren Γ' Γ) :
  RcR idRen f = f.
Proof. reflexivity. Qed.

Corollary RcR_idRen_right Γ Γ' (f : Ren Γ' Γ) :
  RcR f idRen = f.
Proof. reflexivity. Qed.

Corollary RcR_assoc Γ Γ' Γ'' Γ'''
          (f : Ren Γ' Γ) (g : Ren Γ'' Γ') (h : Ren Γ''' Γ'') :
  RcR f (RcR g h) = RcR (RcR f g) h.
Proof. reflexivity. Qed.

Fixpoint RTmExp {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ τ) : Exp Γ' τ :=
  match e with
  | Constant lit  => Constant lit
  | EUnit         => EUnit
  | ETrue         => ETrue
  | EFalse        => EFalse
  | If b t e      => If (RTmExp r b) (RTmExp r t) (RTmExp r e)
  | Pair x y      => Pair (RTmExp r x) (RTmExp r y)
  | Fst p         => Fst (RTmExp r p)
  | Snd p         => Snd (RTmExp r p)
  | Seq exp1 exp2 => Seq (RTmExp r exp1) (RTmExp r exp2)
  | Let x body    => Let (RTmExp r x) (RTmExp (RTmL r) body)

  | VAR v         => VAR (r _ v)
  | APP e1 e2     => APP (RTmExp r e1) (RTmExp r e2)
  | LAM e         => LAM (RTmExp (RTmL r) e)
  end.

Lemma RTmExp_preserves_size {Γ Γ' τ} (r : Ren Γ Γ') (e : Exp Γ τ) :
  Exp_size (RTmExp r e) = Exp_size e.
Proof.
  generalize dependent r.
  generalize dependent Γ'.
  now induction e; simpl; intros; auto.
Qed.

Definition wk {Γ τ τ'} : Exp Γ τ → Exp (τ' :: Γ) τ := RTmExp (λ _, SV).

Lemma ActionRcR {Γ Γ' Γ''} (r : Ren Γ' Γ'') (r' : Ren Γ Γ') `(e : Exp Γ τ) :
  RTmExp (RcR r r') e = RTmExp r (RTmExp r' e).
Proof.
  generalize dependent r'.
  generalize dependent r.
  generalize dependent Γ''.
  generalize dependent Γ'.
  induction e; simpl; intros; auto;
  rewrite ?IHe, ?IHe1, ?IHe2, ?IHe3; auto.
  - rewrite LiftRcR.
    now rewrite IHe2.
  - rewrite LiftRcR.
    now rewrite IHe.
Qed.

Definition identity Γ τ : Exp Γ (τ ⟶ τ) := LAM (VAR ZV).

(** Now that we have renaming, we can define composition. *)

Definition compose {Γ τ τ' τ''}
           (f : Exp Γ (τ' ⟶ τ''))
           (g : Exp Γ (τ ⟶ τ')) : Exp Γ (τ ⟶ τ'') :=
  LAM (APP (wk f) (APP (wk g) (VAR ZV))).

End Ren.
