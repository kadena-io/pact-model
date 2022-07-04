Require Export
  Coq.micromega.Lia
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

Equations STmL {Γ Γ' τ} (s : Sub Γ Γ')
          (* Sub (τ :: Γ) (τ :: Γ') *)
          τ' (v : Var (τ :: Γ) τ') : Exp (τ :: Γ') τ' :=
  STmL _ τ' ZV      := VAR ZV;
  STmL _ τ' (SV v') := wk (s _ v').

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

Definition ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') :=
  (λ τ v, s τ (r τ v)) : Sub Γ Γ''.

Definition RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') :=
  (λ τ v, RTmExp r (s τ v)) : Sub Γ Γ''.

Definition ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (s' : Sub Γ Γ') :=
  (λ τ v, STmExp s (s' τ v)) : Sub Γ Γ''.

Notation "{| e ; .. ; f |}" := (consSub e .. (consSub f idSub) ..).
