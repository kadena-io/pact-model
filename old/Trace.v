Require Import
  Lib
  Ltac
  Ty
  Exp
  Value.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Trace.

Import ListNotations.

Context {A : Type}.
Context `{HostExprs A}.

Open Scope Ty_scope.

Inductive Redex : Ty → Type :=
  | Lookup {Γ τ} : Var Γ τ → ClEnv Γ → Redex τ
  | App {Γ dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → ClEnv Γ → Redex cod
  | Beta {Γ τ ty} : Exp (ty :: Γ) τ → ClEnv Γ → Value ty → Redex τ.

Derive Signature NoConfusion NoConfusionHom Subterm for Redex.

Equations fromRedex {u} (r : Redex u) : Closed u :=
  fromRedex (Lookup v env)  := Closure (VAR v) env;
  fromRedex (App f arg env) := Closure (APP f arg) env;
  fromRedex (Beta e env (Lambda f env'))  :=
    Clapp (Closure (LAM e) env) (Closure (LAM f) env').

Equations contract {u} (r : Redex u) : Closed u :=
  contract (Lookup v env) with get_exp env v := {
    | Lambda e env' => Closure (LAM e) env'
  };
  contract (App f x env)     := Clapp (Closure f env) (Closure x env);
  contract (Beta body env x) := Closure body (AddCl x env).

Equations plug {u v} (e : EvalContext u v) (c : Closed u) : Closed v :=
  plug MT f         := f;
  plug (AR x ctx) f := plug ctx (Clapp f x);
  plug (FN (Lambda f env) ctx) x := plug ctx (Clapp (Closure (LAM f) env) x).

Inductive Decomposition : ∀ {τ}, Closed τ → Type :=
  | DVal {Γ dom cod} (e : Exp (dom :: Γ) cod) (ρ : ClEnv Γ) :
    Decomposition (Closure (LAM e) ρ)
  | RedCtx {τ τ'} (r : Redex τ) (c : EvalContext τ τ') :
    Decomposition (plug c (fromRedex r)).

Derive Signature NoConfusion Subterm for Decomposition.

Definition decompose {u} (c : Closed u) : Decomposition c.

Equations headReduce {u} (c : Closed u) : Closed u :=
  headReduce c with decompose c := {
    headReduce ?(Closure (LAM body) env) (DVal body env) :=
      Closure (LAM body) env;
    headReduce ?(plug ctx (fromRedex redex)) (RedCtx redex ctx) :=
      plug ctx (contract redex)
  }.

Equations snoc {u v w} (e : EvalContext u (v ⟶ w)) (c : Closed v) :
  EvalContext u w :=
  snoc MT c         := AR c MT;
  snoc (FN x ctx) c := FN x (snoc ctx c);
  snoc (AR x ctx) c := AR x (snoc ctx c).

Equations cons {a b c} (e : EvalContext a b) (v : Value (b ⟶ c)) :
  EvalContext a c :=
  cons MT val         := FN val MT;
  cons (FN x ctx) val := FN x (cons ctx val);
  cons (AR x ctx) val := AR x ((cons ctx val)).

Inductive SnocView : ∀ {u v}, EvalContext u v → Type :=
  | SVNil {u} : SnocView (u:=u) MT
  | SVCons {dom cod} (v : Value (dom ⟶ cod)) {τ} (c : EvalContext τ dom) :
    SnocView (cons c v)
  | SVSnoc {dom cod} (v : Closed dom) {τ} (c : EvalContext τ (dom ⟶ cod)) :
    SnocView (snoc c v).

Derive Signature NoConfusion Subterm for SnocView.

Equations viewSnoc {u v} (ctx : EvalContext u v) : SnocView ctx :=
  viewSnoc MT := SVNil;
  viewSnoc (FN x ctx) with viewSnoc ctx := {
    viewSnoc (FN x ?(MT))           SVNil := SVCons x MT;
    viewSnoc (FN x ?(cons ctx val)) (SVCons val ctx) := SVCons val (FN x ctx);
    viewSnoc (FN x ?(snoc ctx z))   (SVSnoc z ctx) := SVSnoc z (FN x ctx)
  };
  viewSnoc (AR x ctx) with viewSnoc ctx := {
    viewSnoc (AR x ?(MT))           SVNil := SVSnoc x MT;
    viewSnoc (AR x ?(cons ctx val)) (SVCons val ctx) := SVCons val (AR x ctx);
    viewSnoc (AR x ?(snoc ctx z))   (SVSnoc z ctx) := SVSnoc z (AR x ctx)
  }.

Inductive isValidClosure : ∀ {u}, Closed u → Type :=
  | ClosureIsValid {Γ u} (x : Exp Γ u) (ρ : ClEnv Γ) :
    isValidEnv ρ →
    isValidClosure (Closure x ρ)

with isValidEnv : ∀ {Γ}, ClEnv Γ → Type :=
  | NoClIsValid : isValidEnv NoCl
  | ClAddIsValidEnv {Γ u} {x : Closed u} {ρ : ClEnv Γ} :
    isValidClosure x → isValidEnv ρ → isValidEnv (AddCl x ρ).

Derive Signature NoConfusion NoConfusionHom Subterm for isValidClosure.
Derive Signature NoConfusion NoConfusionHom for isValidEnv.

Inductive isValidContext : ∀ {u v}, EvalContext u v → Type :=
  | MT_isValidContext {u} : isValidContext (u:=u) MT
  | FN_isValidContext {Γ dom cod} (body : Exp (dom :: Γ) cod)
                      (ρ : ClEnv Γ) {r} (κ : EvalContext cod r) :
    isValidEnv ρ → isValidContext κ →
    isValidContext (FN (Val (Closure (LAM body) ρ)
                            (ClosureVal _ (LambdaP _))) κ)
  | AR_isValidContext {Γ τ} (x : Exp Γ τ)
                       (ρ : ClEnv Γ) {r} (κ : EvalContext τ r) :
    isValidEnv ρ → isValidContext κ →
    isValidContext (AR (Closure x ρ) κ).

Derive Signature for isValidContext.

Definition Σ := @sigT.

Equations getContext {u} (e : Σ (Closed u) isValidClosure) : Env :=
  getContext (existT _ (Closure (Γ:=Γ) _ _) _) := Γ.

Equations getEnv {u} (c : Σ (Closed u) isValidClosure) : ClEnv (getContext c) :=
  getEnv (existT _ (Closure _ env) _) := env.

Equations getTerm {u} (c : Σ (Closed u) isValidClosure) : Exp (getContext c) u :=
  getTerm (existT _ (Closure x _) _) := x.

Equations lookup {u Γ} (e : Var Γ u) (env : ClEnv Γ) (H : isValidEnv env) :
  Σ (Closed u) isValidClosure :=
  lookup ZV (AddCl x _) (ClAddIsValidEnv lft _) := existT _ x lft;
  lookup (SV ref) (AddCl x env) (ClAddIsValidEnv _ rght) :=
    lookup ref env rght.

Inductive Trace : ∀ {Γ τ}, Exp Γ τ → ClEnv Γ → ∀ {r}, EvalContext τ r → Type :=
  | TDone {Γ} {ρ : ClEnv Γ} {dom cod} (e : Exp (dom :: Γ) cod) :
    Trace (LAM e) ρ MT
  | TLookup {Γ τ} (v : Var Γ τ) {ρ : ClEnv Γ} (p : isValidEnv ρ)
            {r} {κ : EvalContext τ r} :
    Trace (getTerm (lookup v ρ p)) (getEnv (lookup v ρ p)) κ →
    Trace (VAR v) ρ κ
  | TLeft {Γ dom cod} (f : Exp Γ (dom ⟶ cod)) (x : Exp Γ dom) {ρ}
          {r} {κ : EvalContext cod r} :
    Trace f ρ (AR (Closure x ρ) κ) →
    Trace (APP f x) ρ κ
  | TRight {Γ Γ' dom cod} (e : Exp (dom :: Γ') cod) (x : Exp Γ dom) {ρ ρ'}
           {r} {κ : EvalContext cod r} :
    Trace x ρ (FN (Val (Closure (LAM e) ρ') (ClosureVal _ (LambdaP _))) κ) →
    Trace (LAM e) ρ' (AR (Closure x ρ) κ)
  | TBeta {Γ Γ' dom cod} (argBody : Exp (dom :: Γ') cod)
          {r} (body : Exp ((dom ⟶ cod) :: Γ) r) {ρ ρ'}
          {r'} (κ : EvalContext r r') :
    Trace body (AddCl (Closure (LAM argBody) ρ') ρ) κ →
    Trace (LAM argBody) ρ' (FN (Val (Closure (LAM body) ρ)
                                      (ClosureVal _ (LambdaP _))) κ).

Derive Signature for Trace.

Equations refocus {Γ u v} (ctx : EvalContext u v) (t : Exp Γ u)
          (env : ClEnv Γ) (tr : Trace t env ctx) : Value v :=
  refocus kont ?(VAR i) env (TLookup i p trace) :=
    let c := lookup i env p in
    refocus kont (getTerm c) (getEnv c) trace;
  refocus ?(MT) ?(LAM body) env (TDone body) :=
    Val (Closure (LAM body) env) (ClosureVal _ (LambdaP _));
  refocus kont ?(APP f x) env (TLeft f x trace) :=
    refocus (AR (Closure x env) kont) f env trace;
  refocus ?(AR (Closure x _) _) ?(LAM body) ?(env)
          (TRight body x (ρ':=env) trace) :=
    refocus (FN (Val (Closure (LAM body) env)
                     (ClosureVal _ (LambdaP _))) _) x _ trace;
  refocus ?(FN (Val (Closure (LAM body) _)
                    (ClosureVal _ (LambdaP _))) ctx)
          ?(LAM argBody) env (TBeta argBody body ctx trace) :=
    refocus ctx body (AddCl (Closure (LAM argBody) env) _) trace.

Definition invariant {Γ u v} (ctx : EvalContext u v) (env : ClEnv Γ) : Type :=
  isValidEnv env * isValidContext ctx.

Definition termination {u} (t : Exp [] u) : Trace t NoCl MT.
Proof.
  dependent induction t.
  (* 18: { *)
  (*   unshelve eapply TLookup; [constructor|]. *)
  (*   now dependent elimination v. *)
  (* } *)
  (* 18: { *)
  (*   now apply TDone. *)
  (* } *)
Abort.

(*
Definition evaluate {u} (e : Exp [] u) : Value u :=
  refocus MT e NoCl (termination e).
*)

End Trace.
