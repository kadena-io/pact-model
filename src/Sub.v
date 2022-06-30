Require Import
  Coq.Unicode.Utf8
  Coq.Lists.List
  Ty
  Exp
  Ren.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Section Sub.

Context {t : Type}.
Context {x : Ty t → Type}.

Definition Sub Γ Γ' := ∀ τ, Var t Γ τ → Exp t x Γ' τ.

Definition idSub {Γ} : Sub Γ Γ := @VAR t x Γ.

Equations consSub {Γ Γ' τ} (e : Exp t x Γ' τ) (s : Sub Γ Γ')
          (* Sub (τ :: Γ) Γ' *)
          τ' (v : Var t (τ :: Γ) τ') : Exp t x Γ' τ' :=
  consSub e s τ' ZV      := e;
  consSub e s τ' (SV v') := s _ v'.

Definition tlSub {Γ Γ' τ} (s : Sub (τ :: Γ) Γ') : Sub Γ Γ' :=
  fun τ' v => s τ' (SV v).
Definition hdSub {Γ Γ' τ} (s : Sub (τ :: Γ) Γ') : Exp t x Γ' τ := s τ ZV.

Equations STmL {Γ Γ' τ} (s : Sub Γ Γ')
          (* Sub (τ :: Γ) (τ :: Γ') *)
          τ' (v : Var t (τ :: Γ) τ') : Exp t x (τ :: Γ') τ' :=
  STmL _ τ' ZV      := VAR ZV;
  STmL _ τ' (SV v') := wk (s _ v').

Fixpoint STmExp {Γ Γ' τ} (s : Sub Γ Γ') (e : Exp t x Γ τ) : Exp t x Γ' τ :=
  match e with
  | TERM r    => TERM r
  | VAR v     => s _ v
  | APP e1 e2 => APP (STmExp s e1) (STmExp s e2)
  | LAM e     => LAM (STmExp (STmL s) e)
  end.

Definition ScR {Γ Γ' Γ''} (s : Sub Γ' Γ'') (r : Ren Γ Γ') :=
  (λ τ v, s τ (r τ v)) : Sub Γ Γ''.

Definition RcS {Γ Γ' Γ''} (r : Ren Γ' Γ'') (s : Sub Γ Γ') :=
  (λ τ v, RTmExp r (s τ v)) : Sub Γ Γ''.

Definition ScS {Γ Γ' Γ''} (s : Sub Γ' Γ'') (s' : Sub Γ Γ') :=
  (λ τ v, STmExp s (s' τ v)) : Sub Γ Γ''.

End Sub.

Notation "{| e ; .. ; f |}" := (consSub e .. (consSub f idSub) ..).
