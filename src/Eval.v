Require Import
  Lib
  Ty
  Exp
  Value
  Sub
  Sem
  Step
  Lang.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Eval.

Import ListNotations.

Context {A : Type}.
Context `{L : HostLang A}.

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
Derive Signature NoConfusion NoConfusionHom Subterm for Σ.

Equations with_closure `(a : Exp Γ dom) `(ρ : ValEnv Γ)
          `(κ : Kont cod τ) `(f : Value (dom ⟶ cod)) : Σ τ :=
  with_closure a ρ κ (ClosureExp (Lambda e)) :=
    MkΣ a ρ (FN (λ v, MkΣ e (Val v Empty) κ));
  (* with_closure a ρ κ (ClosureExp (Func f)) := *)
  (*   MkΣ a ρ (FN (λ v, let '(existT _ x H) := valueToExp v in *)
  (*                     MkΣ (CallHost f x H) Empty κ)) *)
.

(*
Equations IfBody `(v : Value TyBool) {Γ τ} (t e : Exp Γ τ) : Exp Γ τ :=
  IfBody VTrue  t _ := t;
  IfBody VFalse _ e := e.

Equations VFst `(v : Value (TyPair τ1 τ2)) : Value τ1 :=
  VFst (VPair x _) := x.

Equations VSnd `(v : Value (TyPair τ1 τ2)) : Value τ2 :=
  VSnd (VPair _ y) := y.

Equations VCar `(v : Value (TyList r)) {Γ} (d : Exp Γ r) (ρ : ValEnv Γ)
          `(κ : Kont r τ) : Σ τ :=
  VCar VNil        d ρ κ := MkΣ d ρ κ;
  VCar (VCons x _) _ _ κ := MkΣ (projT1 (valueToExp x)) Empty κ.

Equations VCdr `(v : Value (TyList r)) {Γ} (ρ : ValEnv Γ)
          `(κ : Kont (TyList r) τ) : Σ τ :=
  VCdr VNil         ρ κ := MkΣ Nil ρ κ;
  VCdr (VCons _ xs) _ κ := MkΣ (projT1 (valueToExp xs)) Empty κ.

Equations VIsNil `(v : Value (TyList r)) `(κ : Kont TyBool τ) : Σ τ :=
  VIsNil VNil        κ := MkΣ ETrue  Empty κ;
  VIsNil (VCons _ _) κ := MkΣ EFalse Empty κ.
*)

Equations step {τ : Ty} (s : Σ τ) : Σ τ :=
  (* Constants *)
  step (MkΣ (r:=TyHost _)   (HostedVal x) ρ (FN f)) := f (HostValue x);
  step (MkΣ (r:=dom ⟶ cod) (HostedFun x) ρ (FN f)) := f (ClosureExp (Func x));
  step (MkΣ (HostedExp x) ρ κ) := MkΣ (projT1 (Reduce x)) ρ κ;

  step (MkΣ EUnit  _ (FN f)) := f VUnit;
  step (MkΣ ETrue  _ (FN f)) := f VTrue;
  step (MkΣ EFalse _ (FN f)) := f VFalse;

  step (MkΣ (If b th el) ρ κ) :=
    MkΣ b ρ (FN (λ v, MkΣ (IfBody v th el) ρ κ));

  step (MkΣ (Pair x y) ρ (FN f)) :=
    MkΣ x ρ (FN (λ v1, MkΣ y ρ (FN (λ v2, f (VPair v1 v2)))));
  step (MkΣ (Fst p) ρ κ) :=
    MkΣ p ρ (FN (λ p, MkΣ (projT1 (valueToExp (VFst p))) Empty κ));
  step (MkΣ (Snd p) ρ κ) :=
    MkΣ p ρ (FN (λ p, MkΣ (projT1 (valueToExp (VSnd p))) Empty κ));

  step (MkΣ Nil _ (FN f)) := f VNil;
  step (MkΣ (Cons x xs) ρ (FN f)) :=
    MkΣ x ρ (FN (λ v1, MkΣ xs ρ (FN (λ v2, f (VCons v1 v2)))));
  step (MkΣ (Car d xs) ρ κ) :=
    MkΣ xs ρ (FN (λ l, VCar l d ρ κ));
  step (MkΣ (Cdr xs) ρ κ) :=
    MkΣ xs ρ (FN (λ l, VCdr l ρ κ));
  step (MkΣ (IsNil xs) ρ κ) :=
    MkΣ xs ρ (FN (λ l, VIsNil l κ));

  (* A sequence just evaluates the second, for now *)
  step (MkΣ (Seq e1 e2) ρ κ) := MkΣ e2 ρ κ;

  (* A variable might lookup a lambda, in which case continue evaluating down
     that vein; otherwise, if no continuation, this is as far as we can go. *)
  step (MkΣ (VAR v) ρ κ) with get_value ρ v := {
    | x with κ := {
        | MT   => MkΣ (projT1 (valueToExp x)) Empty κ
        | FN f => f x
      }
  };

  (* If a lambda is passed, call it with the continuation *)
  step (MkΣ (LAM e) ρ (FN f)) := f (ClosureExp (Lambda (vsubst e ρ)));

  (* Application evaluates the lambda and then the argument *)
  step (MkΣ (APP e1 e2) ρ κ) := MkΣ e1 ρ (FN (with_closure e2 ρ κ));

  step (MkΣ e ρ MT) := MkΣ e ρ MT.

(*
Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ :=
  loop O s := s;
  loop (S gas') s := loop gas' (step s).

(* Inject the expression into a [Σ] whose final continuation will receive the
   results of the evaluation. Therefore, the resulting [env] will be a
   singleton list containing that value. *)
Definition inject {τ : Ty} (e : Exp [] τ) : Σ τ := MkΣ e Empty MT.

Definition run (gas : nat) {τ : Ty} (e : Exp [] τ) : Σ τ := loop gas (inject e).

Ltac ceksimp :=
  repeat (simp loop;
          simp step;
          simp IfBody;
          simp VFst;
          simp VSnd;
          simpl).

Ltac is_step := ceksimp; firstorder eauto.
*)

(*
Theorem cek_sound τ (e e' : Exp [] τ) :
  e --->* e' → ValueP e' →      (* evaluation halts at e' *)
  ∃ gas, loop gas (inject e) = MkΣ e' Empty MT.
Proof.
Abort.
*)

End Eval.
