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
  | VList {τ} : list (Value τ) → Value (TyList τ)
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

Inductive Accum Γ : ∀ τ : Ty, Exp Γ τ → Type :=
  | ANone {τ e} : Accum Γ τ e
  | AList {τ l} : list (Value τ) → Accum Γ (TyList τ) (List l).

Arguments ANone {Γ τ e}.
Arguments AList {Γ τ l} _.

Derive Signature NoConfusion Subterm for Accum.

Inductive Kont : Ty → Ty → Type :=
  | Mt {a} : Kont a a
  | Ar {Γ a b c} : Exp Γ a → Env Γ → Kont b c → Kont (a ⟶ b) c
  | Fn {a b} : (Value a → Σ b) → Kont a b

with Σ : Ty → Type :=
  | MkΣ (τ   : Ty)
        (Γ   : Exp.Env)
        (r   : Ty)
        (exp : Exp Γ r)
        (env : Env Γ)
        (acc : Accum Γ r exp)
        (knt : Kont r τ) : Σ τ.

Derive Signature NoConfusion for Kont.
Derive Signature NoConfusion Subterm for Σ.

Arguments MkΣ {τ Γ r} _ _ _.

(* Inject the expression into a [Σ] whose final continuation will receive the
   results of the evaluation. Therefore, the resulting [env] will be a
   singleton list containing that value. *)
Definition inject {τ : Ty} {Γ : Exp.Env} (e : Exp Γ τ) (E : Env Γ) : Σ τ :=
  MkΣ e E ANone Mt.

Equations step {τ : Ty} (s : Σ τ) : Σ τ :=
  (* A constant is passed as a literal *)
  step (MkΣ (Constant x) _ ANone (Fn f)) :=
    f (VLit x);

  (* Lists are evaluated step-wise using Ls *)
  step (MkΣ (List []) ρ ANone (Fn f)) :=
    f (VList []);
  step (MkΣ (List []) ρ (AList r) (Fn f)) :=
    f (VList (rev r));

  step (MkΣ (List (x :: xs)) ρ ANone κ) :=
    MkΣ x ρ ANone (Fn (λ v, MkΣ (List xs) ρ (AList [v]) κ));
  step (MkΣ (List (x :: xs)) ρ (AList r) κ) :=
    MkΣ x ρ ANone (Fn (λ v, MkΣ (List xs) ρ (AList (v :: r)) κ));

  (* A sequence just evaluates the second, for now *)
  step (MkΣ (Seq e1 e2) ρ ANone κ) :=
    MkΣ e2 ρ ANone κ;

  (* Let is a simple desugaring *)
  step (MkΣ (Let x body) ρ ANone κ) :=
    MkΣ (APP (LAM body) x) ρ ANone κ;

  (* A variable might lookup a lambda, in which case continue evaluating down
     that vein; otherwise, if no continuation, this is as far as we can go. *)
  step (MkΣ (VAR v) ρ _ κ) with get ρ v := {
    | VClosure (Lambda e ρ') => MkΣ (LAM e) ρ' ANone κ
    | x with κ := {
        | Fn f => f x
        | Mt => MkΣ (VAR v) ρ ANone Mt
      }
  };

  (* Lambda evaluates its argument, with the lambda as the cont *)
  step (MkΣ (LAM e) ρ ANone (Ar a ρ' κ)) :=
    MkΣ a ρ' ANone (Fn (λ v, MkΣ e (Val v ρ) ANone κ));
  (* If a lambda is passed, call it with the continuation *)
  step (MkΣ (LAM e) ρ ANone (Fn f)) :=
    f (VClosure (Lambda e ρ));

  (* Application evaluates the lambda and then the argument *)
  step (MkΣ (APP e1 e2) ρ ANone κ) :=
    MkΣ e1 ρ ANone (Ar e2 ρ κ);

  (* Otherwise, there is nothing more that can be done *)
  step (MkΣ s ρ r Mt) := MkΣ s ρ r Mt.

Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ + Value τ :=
  loop O s :=
    inl s;
  loop _ (MkΣ (Constant x) _ ANone Mt) :=
    inr (VLit x);
  loop _ (MkΣ (List []) _ ANone Mt) :=
    inr (VList []);
  loop _ (MkΣ (List []) _ (AList r) Mt) :=
    inr (VList (rev r));
  loop _ (MkΣ (VAR v) ρ ANone Mt) :=
    inr (get ρ v);
  loop (S gas') s :=
    loop gas' (step s).

Equations loop' (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ :=
  loop' O s := s;
  loop' (S gas') s := loop' gas' (step s).

Definition run (gas : nat) {τ : Ty} {Γ : Exp.Env} (e : Exp Γ τ) (E : Env Γ) :
  Σ τ + Value τ := loop gas (inject e E).

Example exp_constant :
  run 10 (Constant (LInteger 123%Z)) Empty = inr (VLit (LInteger 123%Z)).
Proof. reflexivity. Qed.

Example exp_list :
  run 20 (List (Constant (LInteger 123%Z) ::
                Constant (LInteger 456%Z) ::
                Constant (LInteger 789%Z) :: [])) Empty =
    inr (VList (VLit (LInteger 123%Z) ::
                VLit (LInteger 456%Z) ::
                VLit (LInteger 789%Z) :: [])).
Proof. reflexivity. Qed.

Example exp_let :
  run 10 (Let (Constant (LInteger 123%Z)) (VAR ZV)) Empty =
    inr (VLit (LInteger 123%Z)).
Proof. reflexivity. Qed.

Example exp_var :
  run 10 (VAR ZV) (Val (VLit (LInteger 123%Z)) Empty) =
    inr (VLit (LInteger 123%Z)).
Proof. reflexivity. Qed.

Example exp_lam τ :
  run 10 (LAM (cod:=τ) (VAR ZV)) Empty =
    inl (MkΣ (LAM (VAR ZV)) Empty ANone Mt).
Proof. reflexivity. Qed.

Example exp_app :
  run 10 (APP (LAM (VAR ZV)) (Constant (LInteger 123%Z))) Empty =
    inr (VLit (LInteger 123%Z)).
Proof. reflexivity. Qed.

Theorem cek_sound τ (e : Exp [] τ) v :
  Eval e v → ∃ gas, loop' gas (inject e Empty) = MkΣ v Empty ANone Mt.
Proof.
  unfold run, Basics.compose, inject.
  intros.
  induction H; simpl; intros; auto.
  - exists 1%nat; simpl.
    rewrite loop'_equation_2.
    now rewrite step_equation_1.
  - destruct IHEval as [gas' IHEval'].
    now exists (S gas').
  - destruct IHEval as [gas' IHEval'].
    exists (S gas'); simpl.
    rewrite loop'_equation_2.
    now rewrite step_equation_10.
  - exists 1%nat; simpl.
    rewrite loop'_equation_2.
    rewrite step_equation_12.
    now rewrite loop'_equation_1.
  - destruct IHEval1 as [gas1 IHEval1].
    destruct IHEval2 as [gas2 IHEval2].
    destruct IHEval3 as [gas3 IHEval3].
    exists (S (S (S (gas1 + gas2 + gas3)))).
    rewrite loop'_equation_2.
    rewrite step_equation_15.
    admit.
Abort.

End CEK.
