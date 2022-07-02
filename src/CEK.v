Require Export
  Ty
  Exp
  Sub
  Sem
  Eval.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Section CEK.

Inductive Value : Ty → Type :=
  | VLit {ty} : Literal ty → Value (TyPrim ty)
  | VNil {τ} : Value (TyList τ)
  | VCons {τ} : Value τ → Value (TyList τ) → Value (TyList τ)
  | VClosure {dom cod} : Closure (dom ⟶ cod) → Value (dom ⟶ cod)

with Closure : Ty → Type :=
  | Closed {Γ dom cod} : Exp (dom :: Γ) cod → Env Γ → Closure (dom ⟶ cod)

with Env : Env → Type :=
  | Empty : Env []
  | Val {Γ τ} : Value τ → Env Γ → Env (τ :: Γ).

Derive Signature NoConfusion Subterm for Value.
Derive Signature NoConfusion Subterm for Closure.
Derive Signature NoConfusion for Env.

Equations get `(se : Env Γ) `(v : Var Γ τ) : Value τ :=
  get (Val x _)   ZV    := x;
  get (Val _ xs) (SV v) := get xs v.

Inductive Kont : Ty → Ty → Type :=
  | Mt {u} : Kont u u
  | Ar {Γ u v w} : Exp Γ u → Env Γ → Kont v w → Kont (u ⟶ v) w
  | Fn {a b c} : Closure (a ⟶ b) → Kont b c → Kont a c.

Derive Signature NoConfusion for Kont.

Record Σ := MkΣ {
  Γ   : Exp.Env;
  τ   : Ty;
  exp : Exp Γ τ;
  env : Env Γ;
  r   : Ty;
  knt : Kont τ r
}.

Arguments MkΣ {Γ τ} _ _ {r} _.

Definition inject {τ : Ty} (e : Exp [] τ) : Σ := MkΣ e Empty Mt.

Equations step (gas : nat) {Γ : Exp.Env} {τ : Ty} (e : Exp Γ τ) (ρ : Env Γ)
          {r : Ty} `(κ : Kont τ r) : Σ :=
  step 0 _ _ _ := MkΣ e ρ κ;

  (* A constant is passed as a literal *)
  step (S g) (Constant x) _ (Fn (Closed b ρ') κ) :=
    step g b (Val (VLit x) ρ') κ;

  (* A sequence just evaluates the second, for now *)
  step (S g) (Seq e1 e2) ρ κ :=
    step g e2 ρ κ;

  (* Nil is just a special constant *)
  step (S g) Nil _ (Fn (Closed b ρ') κ) :=
    step g b (Val VNil ρ') κ;
  (* Cons walk down the list evaluating all of the elements *)
  step (S g) (Cons x xs) ρ κ :=
    step g x ρ (Fn (Closed (Cons (VAR ZV) (wk xs)) ρ) κ);

  (* Let is a simple desugaring *)
  step (S g) (Let x body) ρ κ :=
    step g (APP (LAM body) x) ρ κ;

  (* A variable might lookup a lambda, in which case continue evaluating down
     that vein; otherwise, if no continuation, this is as far as we can go. *)
  step (S g) (VAR v) ρ κ with get ρ v := {
    | VClosure (Closed e ρ') => step g (LAM e) ρ' κ
    | x with κ := {
        | Fn (Closed b ρ') κ' => step g b (Val x ρ') κ'
        | Mt => step g (VAR v) ρ Mt
      }
  };

  (* Lambda evaluates its argument, with the lambda as the cont *)
  step (S g) (LAM e) ρ (Ar a ρ' κ) :=
    step g a ρ' (Fn (Closed e ρ) κ);
  (* If a lambda is being passed, call the continuation with it *)
  step (S g) (LAM e) ρ (Fn (Closed b ρ') κ) :=
    step g b (Val (VClosure (Closed e ρ)) ρ') κ;

  (* Application evaluates the lambda and then the argument *)
  step (S g) (APP e1 e2) ρ κ :=
    step g e1 ρ (Ar e2 ρ κ);

  (* Otherwise, there is nothing more than can be done *)
  step _ s ρ Mt := MkΣ s ρ Mt.

Definition run (gas : nat) {τ : Ty} (e : Exp [] τ) : Σ :=
  step gas e Empty Mt.

Theorem cek_sound τ (e : Exp [] τ) v :
  Eval e v → ∃ gas, run gas e = MkΣ v Empty Mt.
Proof.
  unfold run, Basics.compose, inject.
  intros.
  induction H; simpl; intros; auto.
  - exists 1%nat; simpl.
    now rewrite step_equation_2.
  - destruct IHEval as [gas' IHEval'].
    now exists (S gas').
  - exists 1%nat; simpl.
    now rewrite step_equation_5.
  - destruct IHEval1 as [gas1 IHEval1'].
    destruct IHEval2 as [gas2 IHEval2'].
    exists (S (S (S (gas1 + gas2)))).
    rewrite step_equation_7.
    admit.
  - destruct IHEval1 as [gas1 IHEval1].
    destruct IHEval2 as [gas2 IHEval2].
    exists (S (S (S (gas1 + gas2)))).
    rewrite step_equation_8.
    rewrite step_equation_13.
    rewrite step_equation_11.
    admit.
  - admit.
  - admit.
Abort.
