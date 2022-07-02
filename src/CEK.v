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
  (* | VNil {τ} : Value (TyList τ) *)
  (* | VCons {Γ τ} : Exp Γ τ → Exp Γ (TyList τ) → Value (TyList τ) *)
  | VClosure {dom cod} : Closure dom cod → Value (dom ⟶ cod)

with Closure : Ty → Ty → Type :=
  | Lambda {Γ dom cod} : Exp (dom :: Γ) cod → Env Γ → Closure dom cod

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
  | Fn {a b c} : Closure a b → Kont b c → Kont a c.

Derive Signature NoConfusion for Kont.

Record Σ (τ : Ty) := MkΣ {
  Γ   : Exp.Env;
  r   : Ty;
  exp : Exp Γ r;
  env : Env Γ;
  knt : Kont r τ
}.

Derive NoConfusion for Σ.

Arguments MkΣ {τ Γ r} _ _ _.

(* Inject the expression into a [Σ] whose final continuation will receive the
   results of the evaluation. Therefore, the resulting [env] will be a
   singleton list containing that value. *)
Definition inject {τ : Ty} (e : Exp [] τ) : Σ τ := MkΣ e Empty Mt.

Equations step {τ : Ty} (s : Σ τ) : Σ τ :=
  (* A constant is passed as a literal *)
  step (MkΣ (Constant x) _ (Fn (Lambda f ρ') κ)) :=
    MkΣ f (Val (VLit x) ρ') κ;

  (* A sequence just evaluates the second, for now *)
  step (MkΣ (Seq e1 e2) ρ κ) :=
    MkΣ e2 ρ κ;

(*
  (* Nil is a special constant *)
  step (MkΣ Nil _ (Fn (Lambda b ρ') κ)) :=
    MkΣ b (Val VNil ρ') κ;
  (* Cons produces a lazily evaluated list *)
  step (MkΣ (Cons x xs) ρ (Fn (Lambda b ρ') κ)) :=
    MkΣ b (Val (VCons x xs) ρ') κ;
*)

  (* Let is a simple desugaring *)
  step (MkΣ (Let x body) ρ κ) :=
    MkΣ (APP (LAM body) x) ρ κ;

  (* A variable might lookup a lambda, in which case continue evaluating down
     that vein; otherwise, if no continuation, this is as far as we can go. *)
  step (MkΣ (VAR v) ρ κ) with get ρ v := {
    | VClosure (Lambda e ρ') => MkΣ (LAM e) ρ' κ
    | x with κ := {
        | Fn (Lambda f ρ') κ' => MkΣ f (Val x ρ') κ'
        | Mt => MkΣ (VAR v) ρ Mt
      }
  };

  (* Lambda evaluates its argument, with the lambda as the cont *)
  step (MkΣ (LAM e) ρ (Ar a ρ' κ)) :=
    MkΣ a ρ' (Fn (Lambda e ρ) κ);
  (* If a lambda is passed, call it with the continuation *)
  step (MkΣ (LAM e) ρ (Fn (Lambda f ρ') κ)) :=
    MkΣ f (Val (VClosure (Lambda e ρ)) ρ') κ;

  (* Application evaluates the lambda and then the argument *)
  step (MkΣ (APP e1 e2) ρ κ) :=
    MkΣ e1 ρ (Ar e2 ρ κ);

  (* Otherwise, there is nothing more that can be done *)
  step (MkΣ s ρ Mt) := MkΣ s ρ Mt.

Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ + Value τ :=
  loop O s :=
    inl s;
  loop _ (MkΣ (Constant x) _ Mt) :=
    inr (VLit x);
  (* loop _ (MkΣ Nil _ Mt) := *)
  (*   inr VNil; *)
  (* loop _ (MkΣ (Cons x xs) _ Mt) := *)
  (*   inr (VCons x xs); *)
  loop _ (MkΣ (VAR v) ρ Mt) :=
    inr (get ρ v);
  loop (S gas') s :=
    loop gas' (step s).

Definition run (gas : nat) {τ : Ty} (e : Exp [] τ) : Σ τ + Value τ :=
  loop gas (inject e).

Example constant_integer :
  run 10 (Constant (LInteger 123%Z)) = inr (VLit (LInteger 123%Z)).
Proof. reflexivity. Qed.

Example constant_lam_integer :
  run 10 (APP (LAM (VAR ZV)) (Constant (LInteger 123%Z))) =
    inr (VLit (LInteger 123%Z)).
Proof. reflexivity. Qed.

(*
Compute run 20 (Cons (Constant (LInteger 123%Z))
                     (Cons (Constant (LInteger 456%Z)) Nil)).

Example constant_cons :
  run 20 (Cons (Constant (LInteger 123%Z))
               (Cons (Constant (LInteger 456%Z)) Nil)) =
    inr (VCons (Γ:=[]) (Constant (LInteger 123%Z))
               (Cons (Constant (LInteger 456%Z)) Nil)).
Proof. reflexivity. Qed.
*)

(*
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
*)

End CEK.
