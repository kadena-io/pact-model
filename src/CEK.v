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

Inductive represents Γ : ∀ {τ}, Exp Γ τ → Value τ → Prop :=
  | VConst_represents {ty} (l : Literal ty) :
    represents Γ (Constant l) (VConst l)
  | VUnit_represents  : represents Γ EUnit VUnit
  | VTrue_represents  : represents Γ ETrue VTrue
  | VFalse_represents : represents Γ EFalse VFalse
  | VPair_represents {τ1 τ2} (x : Exp Γ τ1) x' (y : Exp Γ τ2) y' :
    represents Γ x x' →
    represents Γ y y' →
    represents Γ (Pair x y) (VPair x' y')
  | VClosure_represents {dom cod} (e : Exp (dom :: Γ) cod) (ρ : Env Γ) :
    represents Γ (LAM e) (VClosure (Lambda e ρ)).

Lemma represents_values Γ {τ : Ty} (v : Exp Γ τ) (v' : Value τ) :
  represents Γ v v' → ValueP v.
Proof.
  intros.
  now induction H; constructor.
Qed.

Equations get `(se : Env Γ) `(v : Var Γ τ) : Value τ :=
  get (Val x _)   ZV    := x;
  get (Val _ xs) (SV v) := get xs v.

Inductive Kont : Ty → Ty → Type :=
  | Fn {a b} : (Value a → Σ b + Value b) → Kont a b

with Σ : Ty → Type :=
  | MkΣ (τ   : Ty)
        (Γ   : Exp.Env)
        (r   : Ty)
        (exp : Exp Γ r)
        (env : Env Γ)
        (knt : Kont r τ) : Σ τ.

Derive Signature NoConfusion Subterm for Kont.
Derive Signature NoConfusion Subterm for Σ.

Arguments MkΣ {τ Γ r} _ _ _.

(* Inject the expression into a [Σ] whose final continuation will receive the
   results of the evaluation. Therefore, the resulting [env] will be a
   singleton list containing that value. *)
Definition inject {τ : Ty} {Γ : Exp.Env} (e : Exp Γ τ) (E : Env Γ) : Σ τ :=
  MkΣ e E (Fn inr).

Equations IfBody {τ : Ty} {Γ : Exp.Env} (t e : Exp Γ τ)
          (v : Value TyBool) : Exp Γ τ :=
  IfBody t _ VTrue  := t;
  IfBody _ e VFalse := e.

Equations VFst {τ1 τ2 : Ty} (v : Value (TyPair τ1 τ2)) : Value τ1 :=
  VFst (VPair x _) := x.

Equations VSnd {τ1 τ2 : Ty} (v : Value (TyPair τ1 τ2)) : Value τ2 :=
  VSnd (VPair _ y) := y.

Equations with_closure `(a : Exp Γ dom) (ρ : Env Γ) {τ} `(κ : Kont cod τ)
          `(v : Value (dom ⟶ cod)) : Σ τ :=
  with_closure a ρ κ (VClosure (Lambda e ρ')) :=
    MkΣ a ρ (Fn (λ v, inl (MkΣ e (Val v ρ') κ))).

Equations step {τ : Ty} (s : Σ τ) : Σ τ + Value τ :=
  (* Constants *)
  step (MkΣ (Constant x) _ (Fn f)) := f (VConst x);

  step (MkΣ EUnit  _ (Fn f)) := f VUnit;
  step (MkΣ ETrue  _ (Fn f)) := f VTrue;
  step (MkΣ EFalse _ (Fn f)) := f VFalse;
  step (MkΣ (If b t e) ρ κ) :=
    inl (MkΣ b ρ (Fn (λ v, inl (MkΣ (IfBody t e v) ρ κ))));

  step (MkΣ (Pair x y) ρ (Fn f)) :=
    inl (MkΣ x ρ (Fn (λ v1, inl (MkΣ y ρ (Fn (λ v2, f (VPair v1 v2)))))));
  step (MkΣ (Fst p) ρ (Fn f)) :=
    inl (MkΣ p ρ (Fn (f ∘ VFst)));
  step (MkΣ (Snd p) ρ (Fn f)) :=
    inl (MkΣ p ρ (Fn (f ∘ VSnd)));

  (* A sequence just evaluates the second, for now *)
  step (MkΣ (Seq e1 e2) ρ κ) :=
    inl (MkΣ e2 ρ κ);

  (* Let is a simple desugaring *)
  step (MkΣ (Let x body) ρ κ) :=
    inl (MkΣ (APP (LAM body) x) ρ κ);

  (* A variable might lookup a lambda, in which case continue evaluating down
     that vein; otherwise, if no continuation, this is as far as we can go. *)
  step (MkΣ (VAR v) ρ κ) with get ρ v := {
    | VClosure (Lambda e ρ') => inl (MkΣ (LAM e) ρ' κ)
    | x with κ := {
        | Fn f => f x
      }
  };

  (* If a lambda is passed, call it with the continuation *)
  step (MkΣ (LAM e) ρ (Fn f)) :=
    f (VClosure (Lambda e ρ));

  (* Application evaluates the lambda and then the argument *)
  step (MkΣ (APP e1 e2) ρ κ) :=
    inl (MkΣ e1 ρ (Fn (inl ∘ with_closure e2 ρ κ))).

Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ + Value τ :=
  loop O s := inl s;
  loop (S gas') s with step s := {
    | inl s' => loop gas' s'
    | inr r  => inr r
  }.

Definition run (gas : nat) {τ : Ty} {Γ : Exp.Env} (e : Exp Γ τ) (E : Env Γ) :
  Σ τ + Value τ := loop gas (inject e E).

Example exp_constant :
  run 10 (Constant (LInteger 123%Z)) Empty = inr (VConst (LInteger 123%Z)).
Proof. reflexivity. Qed.

Example exp_pair :
  run 20 (Pair (Constant (LInteger 123%Z))
               (Constant (LInteger 456%Z))) Empty =
    inr (VPair (VConst (LInteger 123%Z))
               (VConst (LInteger 456%Z))).
Proof. reflexivity. Qed.

Example exp_let :
  run 10 (Let (Constant (LInteger 123%Z)) (VAR ZV)) Empty =
    inr (VConst (LInteger 123%Z)).
Proof. reflexivity. Qed.

Example exp_var :
  run 10 (VAR ZV) (Val (VConst (LInteger 123%Z)) Empty) =
    inr (VConst (LInteger 123%Z)).
Proof. reflexivity. Qed.

Example exp_lam τ :
  run 10 (LAM (cod:=τ) (VAR ZV)) Empty =
    inr (VClosure (Lambda (VAR ZV) Empty)).
Proof. reflexivity. Qed.

Example exp_app :
  run 10 (APP (LAM (VAR ZV)) (Constant (LInteger 123%Z))) Empty =
    inr (VConst (LInteger 123%Z)).
Proof. reflexivity. Qed.

Theorem cek_sound τ (e : Exp [] τ) v v' :
  e --->* v → represents [] v v' →
  ∃ gas, loop gas (inject e Empty) = inr v'.
Proof.
  intros.
  unfold inject.
  induction H.
  - dependent induction x;
    exists 10%nat;
    simp loop; simp step; simpl;
    inv H0; auto.
    + admit.
    + now dependent elimination ρ.
  - destruct IHmulti; auto.
    induction H;
    try solve [ exists (S x0);
                simp loop; simp step; simpl;
                rewrite <- H1; clear H1 ].
    + exists (S (S x0)).
      simp loop; simp step; simpl.
      now simp loop; simp step; simpl.
    + exists (S (S x0)).
      simp loop; simp step; simpl.
      now simp loop; simp step; simpl.
    + exists x0.
Abort.

End CEK.
