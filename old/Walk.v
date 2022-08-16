Require Import
  Pact.Lib
  Pact.Ty
  Pact.Exp
  Pact.Value.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Definition WalkExp
  (R : Env → Env → Set)
  `(r : R Γ Γ')
  (l : ∀ {Γ Γ' τ}, R Γ Γ' → R (τ :: Γ) (τ :: Γ'))
  (f : ∀ {Γ Γ' : Env} {τ : Ty}, R Γ Γ' → Var Γ' τ → Exp Γ τ)
  {τ} : Exp Γ' τ → Exp Γ τ :=
  let fix go {Γ Γ' τ} (r : R Γ Γ') (e : Exp Γ' τ) : Exp Γ τ :=
    match e with
    | VAR v         => f r v
    | APP e1 e2     => APP (go r e1) (go r e2)
    | LAM e         => LAM (go (l r) e)

    | Let x body    => Let (go r x) (go (l r) body)

    | Error         => Error
    | Catch e       => Catch (go r e)

    | Lit v         => Lit v
    | Bltn b        => Bltn b
    | Symbol s      => Symbol s

    | If b t e      => If (go r b) (go r t) (go r e)

    | Pair x y      => Pair (go r x) (go r y)
    | Fst p         => Fst (go r p)
    | Snd p         => Snd (go r p)

    | Inl x         => Inl (go r x)
    | Inr y         => Inr (go r y)
    | Case e g h    => Case (go r e) (go r g) (go r h)

    | Nil           => Nil
    | Cons x xs     => Cons (go r x) (go r xs)
    | Car xs        => Car (go r xs)
    | Cdr xs        => Cdr (go r xs)
    | IsNil xs      => IsNil (go r xs)

    | Seq exp1 exp2 => Seq (go r exp1) (go r exp2)

    | Capability Hp Hv n p v =>
        Capability Hp Hv (go r n) (go r p) (go r v)
    | WithCapability Hv mn p m c e =>
        WithCapability Hv (go r mn) (go r p) (go r m)
          (go r c) (go r e)
    | ComposeCapability Hv mn p m c =>
        ComposeCapability Hv (go r mn) (go r p) (go r m)
          (go r c)
    | InstallCapability c    => InstallCapability (go r c)
    | RequireCapability c    => RequireCapability (go r c)
    end
  in go r.
