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

Inductive Kont : Ty → Ty → Type :=
  | Mt {a} : Kont a a
  | Ar {Γ a b c} : Exp Γ a → Env Γ → Kont b c → Kont (a ⟶ b) c
  | Nv {a b} : (Value a → Σ b) → Kont a b

with Σ : Ty → Type :=
  | MkΣ
      (τ   : Ty)
      (Γ   : Exp.Env)
      (r   : Ty)
      (exp : Exp Γ r)
      (env : Env Γ)
      (acc : option (Value r))
      (knt : Kont r τ) : Σ τ.

Derive Signature NoConfusion for Kont.
Derive Signature NoConfusion Subterm for Σ.

Arguments MkΣ {τ Γ r} _ _ _.

(* Inject the expression into a [Σ] whose final continuation will receive the
   results of the evaluation. Therefore, the resulting [env] will be a
   singleton list containing that value. *)
Definition inject {τ : Ty} (e : Exp [] τ) : Σ τ := MkΣ e Empty None Mt.

Equations step {τ : Ty} (s : Σ τ) : Σ τ :=
  (* A constant is passed as a literal *)
  step (MkΣ (Constant x) _ _ (Nv f)) :=
    f (VLit x);

  (* Lists are evaluated step-wise using Ls *)
  step (MkΣ (List []) ρ None (Nv f)) :=
    f (VList []);
  step (MkΣ (List []) ρ (Some (VList r)) (Nv f)) :=
    f (VList (rev r));

  step (MkΣ (List (x :: xs)) ρ None κ) :=
    MkΣ x ρ None (Nv (λ v, MkΣ (List xs) ρ (Some (VList [v])) κ));
  step (MkΣ (List (x :: xs)) ρ (Some (VList r)) κ) :=
    MkΣ x ρ None (Nv (λ v, MkΣ (List xs) ρ (Some (VList (v :: r))) κ));

  (* A sequence just evaluates the second, for now *)
  step (MkΣ (Seq e1 e2) ρ r κ) :=
    MkΣ e2 ρ r κ;

  (* Let is a simple desugaring *)
  step (MkΣ (Let x body) ρ r κ) :=
    MkΣ (APP (LAM body) x) ρ r κ;

  (* A variable might lookup a lambda, in which case continue evaluating down
     that vein; otherwise, if no continuation, this is as far as we can go. *)
  step (MkΣ (VAR v) ρ r κ) with get ρ v := {
    | VClosure (Lambda e ρ') => MkΣ (LAM e) ρ' r κ
    | x with κ := {
        | Nv f => f x
        | Mt => MkΣ (VAR v) ρ r Mt
      }
  };

  (* Lambda evaluates its argument, with the lambda as the cont *)
  step (MkΣ (LAM e) ρ r (Ar a ρ' κ)) :=
    MkΣ a ρ' None (Nv (λ v, MkΣ e (Val v ρ) None κ));
  (* If a lambda is passed, call it with the continuation *)
  step (MkΣ (LAM e) ρ _ (Nv f)) :=
    f (VClosure (Lambda e ρ));

  (* Application evaluates the lambda and then the argument *)
  step (MkΣ (APP e1 e2) ρ r κ) :=
    MkΣ e1 ρ None (Ar e2 ρ κ);

  (* Otherwise, there is nothing more that can be done *)
  step (MkΣ s ρ r Mt) := MkΣ s ρ r Mt.

Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ + Value τ :=
  loop O s :=
    inl s;
  loop _ (MkΣ (Constant x) _ _ Mt) :=
    inr (VLit x);
  loop _ (MkΣ (List []) _ None Mt) :=
    inr (VList []);
  loop _ (MkΣ (List []) _ (Some (VList r)) Mt) :=
    inr (VList (rev r));
  loop _ (MkΣ (VAR v) ρ _ Mt) :=
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

Compute run 20 (List (Constant (LInteger 123%Z) ::
                      Constant (LInteger 456%Z) ::
                      Constant (LInteger 789%Z) :: [])).

Example constant_cons :
  run 20 (List (Constant (LInteger 123%Z) ::
                Constant (LInteger 456%Z) ::
                Constant (LInteger 789%Z) :: [])) =
    inr (VList (VLit (LInteger 123%Z) ::
                VLit (LInteger 456%Z) ::
                VLit (LInteger 789%Z) :: [])).
Proof. reflexivity. Qed.
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
