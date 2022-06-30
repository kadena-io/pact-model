Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.Lists.List
  Ty
  Exp
  Ren
  Sub
  Sem.

Import ListNotations.

(** This typeclass abstracts everything we need to know about a language that
    uses the simply-typed language calculus as its foundation. *)

Class Lang (t : Type) (x : Env t → Ty t → Type) := {
  ren {Γ Γ' τ} : Ren Γ Γ' → x Γ τ → x Γ' τ;
  sub {Γ Γ' τ} : Sub Γ Γ' → x Γ τ → x Γ' τ;

  eval {τ} : x [] τ → Exp t x [] τ → Prop;

  SemT : t → Type;
  SemX {Γ τ} : x Γ τ → SemEnv SemT Γ → SemTy SemT τ;

  SemX_SemRen {Γ Γ' τ z} r E :
    (∀ τ' (e : Exp t x Γ τ'),
       SemExp SemT (@SemX) e (SemRen SemT r E) =
       SemExp SemT (@SemX) (RTmExp (ren:=@ren) r e) E) →
    SemX (Γ:=Γ) (τ:=τ) z (SemRen SemT r E) = SemX (Γ:=Γ') (ren r z) E;

  SemX_SemSub {Γ Γ' τ z} s E :
    (∀ τ' (e : Exp t x Γ τ'),
       SemExp SemT (@SemX) e (SemSub SemT (@SemX) s E) =
       SemExp SemT (@SemX) (STmExp (sub:=@sub) (ren:=@ren) s e) E) →
    SemX (Γ:=Γ) (τ:=τ) z (SemSub SemT (@SemX) s E) = SemX (Γ:=Γ') (sub s z) E;

  eval_sound τ (e1 : x [] τ) (e2 : Exp t x [] τ) :
    eval e1 e2 → SemX e1 = SemExp SemT (@SemX) e2
}.
