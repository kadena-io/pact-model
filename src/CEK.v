Require Export
  Ty
  Exp
  Sub
  Sem
  Eval
  Norm.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section CEK.

Import ListNotations.

Context {A : Type}.
Context `{L : HostLang A}.

Inductive Value : Ty → Type :=
  | HostValue {ty}         : HostExp (TyHost ty) → Value (TyHost ty)
  | VUnit                  : Value TyUnit
  | VTrue                  : Value TyBool
  | VFalse                 : Value TyBool
  | VPair {τ1 τ2}          : Value τ1 → Value τ2 → Value (TyPair τ1 τ2)
  | ClosureExp {dom cod}   : Closure dom cod → Value (dom ⟶ cod)

with Closure : Ty → Ty → Type :=
  | Lambda {Γ dom cod} : Exp (dom :: Γ) cod → ValEnv Γ → Closure dom cod
  | Func {dom cod}     : HostExp (dom ⟶ cod) → Closure dom cod

with ValEnv : Env → Type :=
  | Empty : ValEnv []
  | Val {Γ τ} : Value τ → ValEnv Γ → ValEnv (τ :: Γ).

Derive Signature NoConfusion Subterm for Value.
Derive Signature NoConfusion Subterm for Closure.
Derive Signature NoConfusion for ValEnv.

Equations get_value `(s : ValEnv Γ) `(v : Var Γ τ) : Value τ :=
  get_value (Val x _)   ZV    := x;
  get_value (Val _ xs) (SV v) := get_value xs v.

Equations render `(v : Exp Γ τ) {V : ValueP v} (ρ : ValEnv Γ) : Value τ :=
  render (τ:=TyHost _) (Hosted x) ρ := HostValue x;
  render (τ:=_ ⟶ _)   (Hosted x) ρ := ClosureExp (Func x);
  render EUnit                    ρ := VUnit;
  render ETrue                    ρ := VTrue;
  render EFalse                   ρ := VFalse;
  render (Pair x y)               ρ := VPair (render x ρ) (render y ρ);
  render (LAM e)                  ρ := ClosureExp (Lambda e ρ).
Next Obligation. now inv V. Qed.
Next Obligation. now inv V. Qed.

Equations valueToExp `(c : Value τ) {Γ} : Exp Γ τ :=
  valueToExp (HostValue x)             := Hosted x;
  valueToExp VUnit                     := EUnit;
  valueToExp VTrue                     := ETrue;
  valueToExp VFalse                    := EFalse;
  valueToExp (VPair x y)               := Pair (valueToExp x) (valueToExp y);
  valueToExp (ClosureExp (Lambda e ρ)) := LAM e;
  valueToExp (ClosureExp (Func f))     := Hosted f.

Inductive Kont : Ty → Ty → Type :=
  | MT {a}   : Kont a a
  | FN {a b} : (Value a → Σ b) → Kont a b

with Σ : Ty → Type :=
  | MkΣ {Γ    : Env}
        {τ    : Ty}
        {r    : Ty}
        (exp  : Exp Γ r)
        (env  : ValEnv Γ)
        (knt  : Kont r τ) : Σ τ.

Derive Signature NoConfusion Subterm for Kont.
Derive Signature NoConfusion Subterm for Σ.

(* Inject the expression into a [Σ] whose final continuation will receive the
   results of the evaluation. Therefore, the resulting [env] will be a
   singleton list containing that value. *)
Definition inject {τ : Ty} (e : Exp [] τ) : Σ τ := MkΣ e Empty MT.

Equations with_closure `(a : Exp Γ dom) `(ρ : ValEnv Γ)
          `(κ : Kont cod τ) `(f : Value (dom ⟶ cod)) : Σ τ :=
  with_closure a ρ κ (ClosureExp (Lambda e ρ')) :=
    MkΣ a ρ (FN (λ v, MkΣ e (Val v ρ') κ));
  with_closure a ρ κ (ClosureExp (Func f)) :=
    MkΣ a ρ (FN (λ v, MkΣ (CallFunction f v) ρ κ)).

Equations IfBody `(v : Value TyBool) {Γ τ} (t e : Exp Γ τ) : Exp Γ τ :=
  IfBody VTrue  t _ := t;
  IfBody VFalse _ e := e.

Equations VFst `(v : Value (TyPair τ1 τ2)) : Value τ1 :=
  VFst (VPair x _) := x.

Equations VSnd `(v : Value (TyPair τ1 τ2)) : Value τ2 :=
  VSnd (VPair _ y) := y.

Equations step {τ : Ty} (s : Σ τ) : Σ τ :=
  (* Constants *)
  step (MkΣ (r:=TyHost _)   (Hosted x) ρ (FN f)) := f (HostValue x);
  step (MkΣ (r:=TyUnit)     (Hosted x) ρ (FN f)) := f VUnit;
  step (MkΣ (r:=TyBool)     (Hosted x) ρ κ)      := MkΣ (` (GetBool x)) ρ κ;
  step (MkΣ (r:=_ × _)      (Hosted x) ρ κ) := MkΣ (` (GetPair x)) ρ κ;
  step (MkΣ (r:=dom ⟶ cod) (Hosted x) ρ (FN f)) := f (ClosureExp (Func x));

  step (MkΣ EUnit  _ (FN f)) := f VUnit;
  step (MkΣ ETrue  _ (FN f)) := f VTrue;
  step (MkΣ EFalse _ (FN f)) := f VFalse;

  step (MkΣ (If b th el) ρ κ) :=
    MkΣ b ρ (FN (λ v, MkΣ (IfBody v th el) ρ κ));

  step (MkΣ (Pair x y) ρ (FN f)) :=
    MkΣ x ρ (FN (λ v1, MkΣ y ρ (FN (λ v2, f (VPair v1 v2)))));
  step (MkΣ (Fst p) ρ (FN f)) := MkΣ p ρ (FN (f ∘ VFst));
  step (MkΣ (Snd p) ρ (FN f)) := MkΣ p ρ (FN (f ∘ VSnd));

  (* A sequence just evaluates the second, for now *)
  step (MkΣ (Seq e1 e2) ρ κ) := MkΣ e2 ρ κ;

  (* A variable might lookup a lambda, in which case continue evaluating down
     that vein; otherwise, if no continuation, this is as far as we can go. *)
  step (MkΣ (VAR v) ρ κ) with get_value ρ v := {
    | x with κ := {
        | MT   => MkΣ (VAR v) ρ κ
        | FN f => f x
      }
  };

  (* If a lambda is passed, call it with the continuation *)
  step (MkΣ (LAM e) ρ (FN f)) := f (ClosureExp (Lambda e ρ));

  (* Application evaluates the lambda and then the argument *)
  step (MkΣ (APP e1 e2) ρ κ) := MkΣ e1 ρ (FN (with_closure e2 ρ κ));

  step (MkΣ e ρ MT) := MkΣ e ρ MT.

Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ :=
  loop O s := s;
  loop (S gas') s with step s := {
    | MkΣ e ρ MT => MkΣ e ρ MT
    | s' => loop gas' s'
  }.

Definition run (gas : nat) {τ : Ty} (e : Exp [] τ) : Σ τ := loop gas (inject e).

Ltac ceksimp :=
  repeat (simp loop;
          simp step;
          simp IfBody;
          simp VFst;
          simp VSnd;
          simpl).

Ltac is_step := ceksimp; firstorder eauto.

Theorem cek_sound τ (e e' : Exp [] τ) :
  e --->* e' → ValueP e' →      (* evaluation halts at e' *)
  ∃ v, represents e' v ∧ ∃ gas, loop gas (inject e) = MkV v.
Proof.
Abort.

End CEK.
