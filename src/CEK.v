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
  | VNil {τ}               : Value (TyList τ)
  | VCons {τ}              : Value τ → Value (TyList τ) → Value (TyList τ)
  | ClosureExp {dom cod}   : Closure dom cod → Value (dom ⟶ cod)

with Closure : Ty → Ty → Type :=
  | Lambda {Γ dom cod} : Exp (dom :: Γ) cod → ValEnv Γ → Closure dom cod
  | Func {dom cod}     : HostExp (dom ⟶ cod) → Closure dom cod

with ValEnv : Env → Type :=
  | Empty : ValEnv []
  | Val {Γ τ} : Value τ → ValEnv Γ → ValEnv (τ :: Γ).

Derive Signature NoConfusion for Value.
Derive Signature NoConfusion Subterm for Closure.
Derive Signature NoConfusion for ValEnv.

Equations get_value `(s : ValEnv Γ) `(v : Var Γ τ) : Value τ :=
  get_value (Val x _)   ZV    := x;
  get_value (Val _ xs) (SV v) := get_value xs v.

Equations keepAll Γ : Ren Γ [] :=
  keepAll []        := NoRen;
  keepAll (x :: xs) := Drop (keepAll xs).

Equations valueToExp `(c : Value τ) : { v : Exp [] τ & ValueP v } := {
  valueToExp (HostValue x)             := existT _ (Hosted x) (HostedP x);
  valueToExp VUnit                     := existT _ EUnit (UnitP []);
  valueToExp VTrue                     := existT _ (ETrue) TrueP;
  valueToExp VFalse                    := existT _ (EFalse) FalseP;
  valueToExp (VPair x y)               :=
    let '(existT _ v1 H1) := valueToExp x in
    let '(existT _ v2 H2) := valueToExp y in
    existT _ (Pair v1 v2) (PairP H1 H2);
  valueToExp VNil                      := existT _ Nil NilP;
  valueToExp (VCons x xs)              :=
    let '(existT _ v1 H1) := valueToExp x in
    let '(existT _ v2 H2) := valueToExp xs in
    existT _ (Cons v1 v2) (ConsP H1 H2);
  valueToExp (ClosureExp (Lambda e ρ)) := existT _ (LAM (msubst e ρ)) (LambdaP _);
  valueToExp (ClosureExp (Func f))     := existT _ (Hosted f) (FunctionP f)
}
where msubst {Γ ty τ} (e : (ty :: Γ) ⊢ τ) (s : ValEnv Γ) : [ty] ⊢ τ := {
  msubst e Empty      := e;
  msubst e (Val x xs) :=
    let r := keepAll _ in
    let v := RenExp r (projT1 (valueToExp x)) in
    let s := Keepₛ {|| v ||} in
    msubst (SubExp s e) xs
}.

Equations render `(v : Exp Γ τ) {V : ValueP v} (ρ : ValEnv Γ) : Value τ :=
  render (τ:=TyHost _) (Hosted x) ρ := HostValue x;
  render (τ:=_ ⟶ _)   (Hosted x) ρ := ClosureExp (Func x);
  render EUnit                    ρ := VUnit;
  render ETrue                    ρ := VTrue;
  render EFalse                   ρ := VFalse;
  render (Pair x y)               ρ := VPair (render x ρ) (render y ρ);
  render Nil                      ρ := VNil;
  render (Cons x xs)              ρ := VCons (render x ρ) (render xs ρ);
  render (LAM e)                  ρ := ClosureExp (Lambda e ρ).
Next Obligation. now inv V. Qed.
Next Obligation. now inv V. Qed.
Next Obligation. now inv V. Qed.
Next Obligation. now inv V. Qed.

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
    MkΣ a ρ (FN (λ v, let '(existT _ x H) := valueToExp v in
                      MkΣ (CallHost f x H) Empty κ)).

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
  step (MkΣ (r:=TyBool)     (Hosted x) ρ κ)      := MkΣ (projT1 (GetBool x)) ρ κ;
  step (MkΣ (r:=_ × _)      (Hosted x) ρ κ)      := MkΣ (projT1 (GetPair x)) ρ κ;
  step (MkΣ (r:=TyList _)   (Hosted x) ρ κ)      := MkΣ (projT1 (GetList x)) ρ κ;
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

  step (MkΣ Nil _ (FN f)) := f VNil;
  step (MkΣ (Cons x xs) ρ (FN f)) :=
    MkΣ x ρ (FN (λ v1, MkΣ xs ρ (FN (λ v2, f (VCons v1 v2)))));

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
  step (MkΣ (LAM e) ρ (FN f)) := f (ClosureExp (Lambda e ρ));

  (* Application evaluates the lambda and then the argument *)
  step (MkΣ (APP e1 e2) ρ κ) := MkΣ e1 ρ (FN (with_closure e2 ρ κ));

  step (MkΣ e ρ MT) := MkΣ e ρ MT.

Equations loop (gas : nat) {τ : Ty} (s : Σ τ) : Σ τ :=
  loop O s := s;
  loop (S gas') s := loop gas' (step s).

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
  ∃ gas, loop gas (inject e) = MkΣ e' Empty MT.
Proof.
Abort.

End CEK.
