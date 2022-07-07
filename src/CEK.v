Require Export
  Ty
  Exp
  Sub
  Sem
  Eval
  Norm
  Coq.micromega.Lia.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Import ListNotations.

Section CEK.

Inductive Value : Ty → Type :=
  | VConst {ty}        : Literal ty → Value (TyPrim ty)
  | VUnit              : Value TyUnit
  | VTrue              : Value TyBool
  | VFalse             : Value TyBool
  | VPair {τ1 τ2}      : Value τ1 → Value τ2 → Value (TyPair τ1 τ2)
  | VClosure {dom cod} : Closure dom cod → Value (dom ⟶ cod)

with Closure : Ty → Ty → Type :=
  | Lambda {Γ dom cod} : Exp (dom :: Γ) cod → Env Γ → Closure dom cod

with Env : Env → Type :=
  | Empty : Env []
  | Val {Γ τ} : Value τ → Env Γ → Env (τ :: Γ).

Derive Signature NoConfusion for Value.
Derive Signature NoConfusion Subterm for Closure.
Derive Signature NoConfusion for Env.

Inductive represents {Γ} : ∀ {τ}, Exp Γ τ → Value τ → Prop :=
  | VConst_represents {ty} (l : Literal ty) :
    represents (Constant l) (VConst l)
  | VUnit_represents  : represents EUnit VUnit
  | VTrue_represents  : represents ETrue VTrue
  | VFalse_represents : represents EFalse VFalse
  | VPair_represents {τ1 τ2} (x : Exp Γ τ1) x' (y : Exp Γ τ2) y' :
    represents x x' →
    represents y y' →
    represents (Pair x y) (VPair x' y')
  | VClosure_represents {dom cod} (e : Exp (dom :: Γ) cod) (ρ : Env Γ) :
    represents (LAM e) (VClosure (Lambda e ρ)).

Lemma represents_values Γ {τ : Ty} (v : Exp Γ τ) (v' : Value τ) :
  represents v v' → ValueP v.
Proof.
  intros.
  now induction H; constructor.
Qed.

Equations get `(se : Env Γ) `(v : Var Γ τ) : Value τ :=
  get (Val x _)   ZV    := x;
  get (Val _ xs) (SV v) := get xs v.

Inductive Kont : Ty → Ty → Type :=
  | Fn {a b} : (Value a → Σ b) → Kont a b

with Σ : Ty → Type :=
  | MkV {τ   : Ty}
        (v   : Value τ) : Σ τ
  | MkΣ {τ   : Ty}
        {Γ   : Exp.Env}
        {r   : Ty}
        (exp : Exp Γ r)
        (env : Env Γ)
        (knt : Kont r τ) : Σ τ.

Derive Signature NoConfusion Subterm for Kont.
Derive Signature NoConfusion Subterm for Σ.

(* Inject the expression into a [Σ] whose final continuation will receive the
   results of the evaluation. Therefore, the resulting [env] will be a
   singleton list containing that value. *)
Definition inject {τ : Ty} (e : Exp [] τ) : Σ τ := MkΣ e Empty (Fn MkV).

Equations IfBody (v : Value TyBool) {τ : Ty} {Γ : Exp.Env}
          (t e : Exp Γ τ) : Exp Γ τ :=
  IfBody VTrue t _  := t;
  IfBody VFalse _ e := e.

Equations VFst {τ1 τ2 : Ty} (v : Value (TyPair τ1 τ2)) : Value τ1 :=
  VFst (VPair x _) := x.

Equations VSnd {τ1 τ2 : Ty} (v : Value (TyPair τ1 τ2)) : Value τ2 :=
  VSnd (VPair _ y) := y.

Equations with_closure `(a : Exp Γ dom) (ρ : Env Γ) {τ} `(κ : Kont cod τ)
          `(v : Value (dom ⟶ cod)) : Σ τ :=
  with_closure a ρ κ (VClosure (Lambda e ρ')) :=
    MkΣ a ρ (Fn (λ v, MkΣ e (Val v ρ') κ)).

(*
Equations eval
          {τ : Ty}
          {Γ : Exp.Env}
          (e : Exp Γ τ)
          (ρ : Env Γ) : Value τ :=
  (* Constants *)
  eval (Constant x) _ := VConst x;

  eval EUnit  _ := VUnit;
  eval ETrue  _ := VTrue;
  eval EFalse _ := VFalse;

  eval (If b t e) ρ with eval b ρ := {
    | VTrue  => eval t ρ
    | VFalse => eval e ρ
  };

  eval (Pair x y) ρ := VPair (eval x ρ) (eval y ρ);
  eval (Fst p) ρ    := VFst (eval p ρ);
  eval (Snd p) ρ    := VSnd (eval p ρ);

  (* A sequence just evaluates the second, for now *)
  eval (Seq _ e2) ρ := eval e2 ρ;

  (* Let is a simple desugaring *)
  eval (Let x body) ρ := eval body (Val (eval x ρ) ρ);

  (* A variable might lookup a lambda, in which case continue evaluating down
     that vein; otherwise, if no continuation, this is as far as we can go. *)
  eval (VAR v) ρ := get ρ v;

  (* If a lambda is passed, call it with the continuation *)
  eval (LAM e) ρ := VClosure (Lambda e ρ);

  (* Application evaluates the lambda and then the argument *)
  eval (APP e1 e2) ρ with eval e1 ρ := {
    | VClosure (Lambda e ρ') => eval e (Val (eval e2 ρ) ρ')
  }.
*)

Equations step {τ : Ty} (s : Σ τ) : Σ τ :=
  step (MkV v) := MkV v;

  (* Constants *)
  step (MkΣ (Constant x) _ (Fn f)) := f (VConst x);

  step (MkΣ EUnit  _ (Fn f)) := f VUnit;
  step (MkΣ ETrue  _ (Fn f)) := f VTrue;
  step (MkΣ EFalse _ (Fn f)) := f VFalse;

  step (MkΣ (If b t e) ρ κ) :=
    MkΣ b ρ (Fn (λ v, MkΣ (IfBody v t e) ρ κ));

  step (MkΣ (Pair x y) ρ (Fn f)) :=
    MkΣ x ρ (Fn (λ v1, MkΣ y ρ (Fn (λ v2, f (VPair v1 v2)))));
  step (MkΣ (Fst p) ρ (Fn f)) :=
    MkΣ p ρ (Fn (f ∘ VFst));
  step (MkΣ (Snd p) ρ (Fn f)) :=
    MkΣ p ρ (Fn (f ∘ VSnd));

  (* A sequence just evaluates the second, for now *)
  step (MkΣ (Seq e1 e2) ρ κ) :=
    MkΣ e2 ρ κ;

  (* A variable might lookup a lambda, in which case continue evaluating down
     that vein; otherwise, if no continuation, this is as far as we can go. *)
  step (MkΣ (VAR v) ρ κ) with get ρ v := {
    | VClosure (Lambda e ρ') => MkΣ (LAM e) ρ' κ
    | x with κ := {
        | Fn f => f x
      }
  };

  (* If a lambda is passed, call it with the continuation *)
  step (MkΣ (LAM e) ρ (Fn f)) :=
    f (VClosure (Lambda e ρ));

  (* Application evaluates the lambda and then the argument *)
  step (MkΣ (APP e1 e2) ρ κ) :=
    MkΣ e1 ρ (Fn (with_closure e2 ρ κ)).

Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ :=
  loop O s := s;
  loop (S gas') s with step s := {
    | MkV v  => MkV v
    | s' => loop gas' s'
  }.

Definition run (gas : nat) {τ : Ty} (e : Exp [] τ) : Σ τ := loop gas (inject e).

Example exp_constant :
  run 10 (Constant (LInteger 123%Z)) = MkV (VConst (LInteger 123%Z)).
Proof. reflexivity. Qed.

Example exp_pair :
  run 20 (Pair (Constant (LInteger 123%Z))
               (Constant (LInteger 456%Z))) =
    MkV (VPair (VConst (LInteger 123%Z))
               (VConst (LInteger 456%Z))).
Proof. reflexivity. Qed.

Example exp_lam τ :
  run 10 (LAM (cod:=τ) (VAR ZV)) =
    MkV (VClosure (Lambda (VAR ZV) Empty)).
Proof. reflexivity. Qed.

Example exp_app :
  run 10 (APP (LAM (VAR ZV)) (Constant (LInteger 123%Z))) =
    MkV (VConst (LInteger 123%Z)).
Proof. reflexivity. Qed.

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
