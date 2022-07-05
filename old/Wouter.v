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

Inductive Closed : Ty → Type :=
  | Closure {Γ u} : Exp Γ u → Env Γ → Closed u
  | Clapp {u v} : Closed (u ⟶ v) → Closed u → Closed v
  | Clif {u} : Closed TyBool → Closed u → Closed u → Closed u
  | Clpair {u v} : Closed u → Closed v → Closed (TyPair u v)
  | Clfst {u v} : Closed (TyPair u v) → Closed u
  | Clsnd {u v} : Closed (TyPair u v) → Closed v
  | Clseq {u v} : Closed u → Closed v → Closed v
  | Cllet {u v} : Closed u → Closed (u ⟶ v) → Closed v

with Env : Env → Type :=
  | Nil : Env []
  | Add {Γ u} : Closed u → Env Γ → Env (u :: Γ).

Derive Signature NoConfusion for Closed.
Derive Signature NoConfusion for Env.

Notation "c ∙ e" := (Add c e) (at level 50).

Inductive Redex : Ty → Type :=
  | Return {τ} : Value τ → Redex τ
  | Branch {Γ τ} : Exp Γ TyBool → Exp Γ τ → Exp Γ τ → Env Γ → Redex τ
  | MkPair {Γ τ1 τ2} : Exp Γ τ1 → Exp Γ τ2 → Env Γ → Redex (TyPair τ1 τ2)
  | GetFst {Γ τ1 τ2} : Exp Γ (TyPair τ1 τ2) → Env Γ → Redex τ1
  | GetSnd {Γ τ1 τ2} : Exp Γ (TyPair τ1 τ2) → Env Γ → Redex τ2
  | Progn {Γ τ1 τ2} : Exp Γ τ1 → Exp Γ τ2 → Env Γ → Redex τ2
  | Bind {Γ τ ty} : Exp Γ ty → Exp (ty :: Γ) τ → Env Γ → Redex τ
  | Lookup {Γ τ} : Var Γ τ → Env Γ → Redex τ
  | App {Γ dom cod} : Exp Γ (dom ⟶ cod) → Exp Γ dom → Env Γ → Redex cod
  | Beta {Γ dom cod} : Exp (dom :: Γ) cod → Env Γ → Value dom → Redex cod

with Value : Ty → Type :=
  | Val {τ} (c : Closed τ) : IsValue c → Value τ

with IsValue : ∀ {τ}, Closed τ → Prop :=
  | IsVal {Γ τ} {e : Exp Γ τ} {ρ} : ValueP e → IsValue (Closure e ρ).

Derive Signature NoConfusion Subterm for Redex.
Derive Signature NoConfusion Subterm for Value.

Equations lookup `(se : Env Γ) `(v : Var Γ τ) : Closed τ :=
  lookup (Add x _)   ZV    := x;
  lookup (Add _ xs) (SV v) := lookup xs v.

Equations contract {u} (r : Redex u) : Closed u :=
  contract (Return (Val v _))        := v;
  contract (Branch b t e env)        := Clif (Closure b env) (Closure t env) (Closure e env);
  contract (MkPair x y env)          := Clpair (Closure x env) (Closure y env);
  contract (GetFst p env)            := Clfst (Closure p env);
  contract (GetSnd p env)            := Clsnd (Closure p env);
  contract (Progn e1 e2 env)         := Clseq (Closure e1 env) (Closure e2 env);
  contract (Bind x body env)         := Cllet (Closure x env) (Closure (LAM body) env);
  contract (Lookup i env)            := lookup env i;
  contract (App f x env)             := Clapp (Closure f env) (Closure x env);
  contract (Beta body env (Val c _)) := Closure body (c ∙ env).

Inductive EvalContext : Ty → Ty → Type :=
  | MT {u} : EvalContext u u
  | ARG {u v w} : Closed u → EvalContext v w → EvalContext (u ⟶ v) w
  | FN {Γ a b c} : Exp (a :: Γ) b → Env Γ → EvalContext b c → EvalContext a c.

Derive Signature NoConfusion for EvalContext.

Equations plug {u v} (c : EvalContext u v) (t : Closed u) : Closed v :=
  plug MT f             := f;
  plug (ARG x ctx) f    := plug ctx (Clapp f x);
  plug (FN f env ctx) x := plug ctx (Clapp (Closure (LAM f) env) x).

Equations fromRedex {u} (r : Redex u) : Closed u :=
  fromRedex (Return (Val v _))        := v;
  fromRedex (Branch b t e env)        := Closure (If b t e) env;
  fromRedex (MkPair x y env)          := Closure (Pair x y) env;
  fromRedex (GetFst p env)            := Closure (Fst p) env;
  fromRedex (GetSnd p env)            := Closure (Snd p) env;
  fromRedex (Progn e1 e2 env)         := Closure (Seq e1 e2) env;
  fromRedex (Bind x body env)         := Closure (Let x body) env;
  fromRedex (Lookup x env)            := Closure (VAR x) env;
  fromRedex (App f arg env)           := Closure (APP f arg) env;
  fromRedex (Beta body env (Val c _)) := Clapp (Closure (LAM body) env) c.

Inductive Decomposition : ∀ {u}, Closed u → Type :=
  | DVal {Γ u v} (body : Exp (u :: Γ) v) (env : Env Γ) :
    Decomposition (Closure (LAM body) env)
  | RedexxContext {u v} (r : Redex u) (ctx : EvalContext u v) :
    Decomposition (plug ctx (fromRedex r)).

Equations decompose' {u v} (ctx : EvalContext u v) (c : Closed u) :
  Decomposition (plug ctx c) := {
  decompose' ctx (Closure (Constant x) env) :=
    RedexxContext (Return (Val (Closure (Constant x) env) _)) ctx;

  decompose' ctx (Closure EUnit env)  :=
    RedexxContext (Return (Val (Closure EUnit env) _)) ctx;
  decompose' ctx (Closure ETrue env)  :=
    RedexxContext (Return (Val (Closure ETrue env) _)) ctx;
  decompose' ctx (Closure EFalse env) :=
    RedexxContext (Return (Val (Closure EFalse env) _)) ctx;

  decompose' ctx (Closure (If b t e) env) :=
    RedexxContext (Branch b t e env) ctx;

  decompose' ctx (Closure (Pair x y) env) :=
    RedexxContext (MkPair x y env) ctx;
  decompose' ctx (Closure (Fst p) env)    :=
    RedexxContext (GetFst p env) ctx;
  decompose' ctx (Closure (Snd p) env)    :=
    RedexxContext (GetSnd p env) ctx;

  decompose' ctx (Closure (Seq e1 e2) env) :=
    RedexxContext (Progn e1 e2 env) ctx;

  decompose' ctx (Closure (Let x body) env) :=
    RedexxContext (Bind x body env) ctx;

  decompose' ctx (Closure (VAR i) env) :=
    RedexxContext (Lookup i env) ctx;
  decompose' ctx (Closure (LAM body) env) :=
    decompose'_aux ctx body env;
  decompose' ctx (Closure (APP f x) env) :=
    RedexxContext (App f x env) ctx;

  decompose' ctx (Clapp f x) :=
    decompose' (ARG x ctx) f;

  decompose' ctx (Clif t b e) := _;
  decompose' ctx (Clpair x y) := _;
  decompose' ctx (Clfst p) :=  _;
  decompose' ctx (Clsnd p) := _;
  decompose' ctx (Clseq e1 e2) := _;
  decompose' ctx (Cllet x body) := _
}

where decompose'_aux {a b w Γ}
     (ctx : EvalContext (a ⟶ b) w)
     (body : a :: Γ ⊢ b)
     (env : Env Γ) :
  Decomposition (plug ctx (Closure (LAM body) env)) := {
  decompose'_aux MT body env := DVal body env;
  decompose'_aux (ARG arg ctx) body env :=
    decompose' (FN body env ctx) arg;
  decompose'_aux (FN x env2 ctx) body env :=
    RedexxContext (Beta x env2 (Val (Closure (LAM body) env) _)) ctx
}.

Definition decompose {u} (c : Closed u) : Decomposition c :=
  decompose' MT c.

Equations headReduce {u} (c : Closed u) : Closed u :=
  headReduce c with decompose c := {
      headReduce ?(Closure (λ body) env) (Val body env) :=
        Closure (LAM body) env;
      headReduce ?(plug ctx (fromRedex redex)) (Redex×Context redex ctx) :=
        plug ctx (contract redex)
  }.

End CEK.
