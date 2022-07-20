Require Import
  Hask.Control.Monad
  Hask.Data.Either
  Lib
  Ty
  Exp
  Sub
  Sem
  Step.

From Equations Require Import Equations.
Set Equations With UIP.

Section Lang.

Generalizable All Variables.

Import ListNotations.

Context {A : Type}.
Context `{S : HostExprsSem A}.

Class HostLang (A : Type) : Type := {
  has_host_exprs_sem :> HostExprsSem A;


(*
  CallHost_sound {Γ dom cod} (f : HostExp (dom ⟶ cod))
                 (v : Exp Γ dom) (H : ValueP v) se :
    (HostExpSem f >>= λ f', SemExp v se >>= λ x, f' x) =
      SemExp (CallHost f v H) se;

  CallHost_irr {Γ dom cod} (f : HostExp (dom ⟶ cod))
               (v : Exp Γ dom) (H : ValueP v) :
    ¬ (CallHost f v H = APP (HostedFun f) v);

  CallHost_preserves_renaming {Γ Γ' dom cod} (f : HostExp (dom ⟶ cod))
               (v : Exp Γ dom) (H : ValueP v) (σ : Ren Γ' Γ) :
    APP (HostedFun f) (RenExp σ v) ---> RenExp σ (CallHost f v H);

  CallHost_preserves_substitution {Γ Γ' dom cod} (f : HostExp (dom ⟶ cod))
               (v : Exp Γ dom) (H : ValueP v) (σ : Sub Γ' Γ) :
    APP (HostedFun f) (SubExp σ v) ---> SubExp σ (CallHost f v H);


  Reduce_sound {Γ τ} (h : HostExp τ) se :
    HostExpSem h = SemExp (projT1 (Reduce (Γ:=Γ) h)) se;

  Reduce_irr {Γ τ} (h : HostExp τ) :
    ¬ (projT1 (Reduce (Γ:=Γ) h) = HostedExp h);

  Reduce_preserves_renaming {Γ Γ' τ} (h : HostExp τ) (σ : Ren Γ Γ') :
    RenExp σ (HostedExp h) ---> RenExp σ (projT1 (Reduce h));

  Reduce_preserves_substitution {Γ Γ' τ} (h : HostExp τ) (σ : Sub Γ Γ') :
    SubExp σ (HostedExp h) ---> SubExp σ (projT1 (Reduce h));
*)
}.

End Lang.
