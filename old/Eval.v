Require Import
  Lib
  Ty
  Exp
  Log
  Value
  Sub
  Sem
  Step
  Multi
  Lang.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Eval.

Import ListNotations.

Context {A : Type}.
Context `{L : HostLang A}.

Inductive Closed : Ty → Type :=
  | Closure {Γ τ} : Exp Γ τ → ClEnv Γ → Closed τ
  (* | Clapp {dom cod} : Closed (dom ⟶ cod) → Closed dom → Closed cod *)

with ClEnv : Env → Type :=
  | NoCl : ClEnv []
  | AddCl {Γ τ} : Value τ → ClEnv Γ → ClEnv (τ :: Γ)

with Value : Ty → Type :=
  | Val {Γ τ} (x : Exp Γ τ) : ValueP x → ClEnv Γ → Value τ.

Derive Signature NoConfusion NoConfusionHom Subterm for ClEnv Closed Value.

Equations get_val `(s : ClEnv Γ) `(v : Var Γ τ) : Value τ :=
  get_val (AddCl x _)  ZV     := x;
  get_val (AddCl _ xs) (SV v) := get_val xs v.

Inductive EvalContext : Ty → Ty → Type :=
  | MT {τ} : EvalContext τ τ
  | AR {dom cod τ} : Closed dom → EvalContext cod τ → EvalContext (dom ⟶ cod) τ
  | FN {dom cod τ} : Value (dom ⟶ cod) → EvalContext cod τ → EvalContext dom τ.

Derive Signature NoConfusion NoConfusionHom Subterm for EvalContext.

Inductive Σ : Ty → Type :=
  | MkΣ {u    : Ty}
        (exp  : Closed u)
        {τ    : Ty}
        (knt  : EvalContext u τ) : Σ τ.

Derive Signature NoConfusion NoConfusionHom Subterm for Σ.

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
  (* step (MkΣ (r:=TyHost _)   (HostedVal x) ρ (FN f)) := f (HostValue x); *)
  (* step (MkΣ (r:=dom ⟶ cod) (HostedFun x) ρ (FN f)) := f (ClosureExp (Func x)); *)
  (* step (MkΣ (HostedExp x) ρ κ) := MkΣ (projT1 (Reduce x)) ρ κ; *)

  step (MkΣ (Closure EUnit _) (FN f κ)) with f := {
    | Val (LAM e) _ ρ' := MkΣ (Closure e (AddCl (Val EUnit UnitP NoCl) ρ')) κ;
  };
  (* step (MkΣ ETrue  _ (FN f)) := f VTrue; *)
  (* step (MkΣ EFalse _ (FN f)) := f VFalse; *)

  (* step (MkΣ (If b th el) ρ κ) := *)
  (*   MkΣ b ρ (FN (λ v, MkΣ (IfBody v th el) ρ κ)); *)

  (* step (MkΣ (Pair x y) ρ (FN f)) := *)
  (*   MkΣ x ρ (FN (λ v1, MkΣ y ρ (FN (λ v2, f (VPair v1 v2))))); *)
  (* step (MkΣ (Fst p) ρ κ) := *)
  (*   MkΣ p ρ (FN (λ p, MkΣ (projT1 (valueToExp (VFst p))) Empty κ)); *)
  (* step (MkΣ (Snd p) ρ κ) := *)
  (*   MkΣ p ρ (FN (λ p, MkΣ (projT1 (valueToExp (VSnd p))) Empty κ)); *)

  (* step (MkΣ Nil _ (FN f)) := f VNil; *)
  (* step (MkΣ (Cons x xs) ρ (FN f)) := *)
  (*   MkΣ x ρ (FN (λ v1, MkΣ xs ρ (FN (λ v2, f (VCons v1 v2))))); *)
  (* step (MkΣ (Car d xs) ρ κ) := *)
  (*   MkΣ xs ρ (FN (λ l, VCar l d ρ κ)); *)
  (* step (MkΣ (Cdr xs) ρ κ) := *)
  (*   MkΣ xs ρ (FN (λ l, VCdr l ρ κ)); *)
  (* step (MkΣ (IsNil xs) ρ κ) := *)
  (*   MkΣ xs ρ (FN (λ l, VIsNil l κ)); *)

  (* (* A sequence just evaluates the second, for now *) *)
  (* step (MkΣ (Seq e1 e2) ρ κ) := MkΣ e2 ρ κ; *)

  (* A variable might lookup a lambda, in which case continue evaluating down
     that vein; otherwise, if no continuation, this is as far as we can go. *)
  step (MkΣ (Closure (VAR v) ρ) κ) with get_val ρ v := {
    | Val val _ ρ' := MkΣ (Closure val ρ') κ
  };

  (* If a lambda is passed, call it with the continuation *)
  step (MkΣ (Closure (LAM e) ρ) (AR a κ)) :=
    MkΣ a (FN (Val (LAM e) (LambdaP _) ρ) κ);
  step (MkΣ (Closure (LAM e) ρ) (FN (Val (LAM f) _ ρ') κ)) :=
    MkΣ (Closure f (AddCl (Val (LAM e) (LambdaP _) ρ) ρ')) κ;

  (* Application evaluates the lambda and then the argument *)
  step (MkΣ (Closure (APP f x) ρ) κ) :=
    MkΣ (Closure f ρ) (AR (Closure x ρ) κ);

  step (MkΣ (Closure (Error m) _) κ) := MkΣ (Closure (Error m) NoCl) κ;

  step (MkΣ c MT) := MkΣ c MT.

Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ :=
  loop O s := s;
  loop (S gas') s := loop gas' (step s).

(* Inject the expression into a [Σ] whose final continuation will receive the
   results of the evaluation. Therefore, the resulting [env] will be a
   singleton list containing that value. *)
Definition inject {τ : Ty} (e : Exp [] τ) : Σ τ := MkΣ (Closure e NoCl) MT.

Definition run (gas : nat) {τ : Ty} (e : Exp [] τ) : Σ τ := loop gas (inject e).

(*
Definition Completes {τ} :=
  ExpP (Γ:=[]) (τ:=τ) (λ _ e, ∃ e' gas, loop gas (inject e) = inject e').

Definition completes_impl {τ} {e : Exp [] τ} :
  Completes (τ:=τ) e → ∃ e' gas, loop gas (inject e) = inject e' := ExpP_P _.

Theorem all_exprs_complete τ (e e' : Exp [] τ) :
  e --->* e' → Completes e.
Proof.
  intros.
  unfold Completes.
  induction τ.
  now eapply IHτ2; eauto.
Qed.

Theorem cek_sound τ (e e' : Exp [] τ) :
  e --->* e' → ∃ gas, loop gas (inject e) = inject e'.
Proof.
  intros.
  apply all_exprs_complete in H.
  induction τ.
  exact (IHτ1 e e' H).
Qed.
*)

End Eval.
