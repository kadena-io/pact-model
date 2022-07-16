Require Import
  Coq.Arith.Arith
  Coq.micromega.Lia
  Lib
  RSWE.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Pact.

Import ListNotations.

Definition Gas : Type := nat.

Variable r : Type.
Variable s : Type.
Variable w : Type.

Inductive Err : Type :=
  | Err_Raise.

Definition PactM := @RSWE r s w Err.

Definition app `(f : a → PactM b) (x : PactM a) : PactM b :=
  gas <- getT ;
  if 0 <? gas
  then putT (gas - 1) ;;
       x >>= f
  else λ _, inl Err_CarNil.

Equations compares {τ : Ty} (gas : Gas)
          (p : PactM (PactTy τ)) (e : Err + SemTy τ) : Prop := {
  compares gas p (inl err) with p gas := {
    | inl err'       => err = err'
    | inr x'         => False
  };
  compares gas p (inr x) with p gas := {
    | inl err'       => False
    | inr (x', gas') => compares_exp gas' (τ:=τ) x' x
  }
}
where compares_exp {τ : Ty} (gas : Gas)
                (p : PactTy τ) (e : SemTy τ) : Prop := {
  compares_exp (τ:=TyUnit)     _   () () := True;
  compares_exp (τ:=dom ⟶ cod) gas f' f  :=
    ∀ (x' : PactTy dom) (x : SemTy dom),
      compares_exp (τ:=dom) gas x' x → compares (τ:=cod) gas (f' x') (f x)
}.

Notation "x ~=[ gas ]=~ y" := (compares gas x y) (at level 100).

Ltac simpler :=
  repeat
    (simpl;
     simp compares; simpl;
     unfold compares_clause_1; simpl;
     unfold compares_clause_2; simpl;
     unfold Prelude.apply; simpl).

Ltac enough_gas gas :=
  let H := fresh "H" in
  destruct (lt_dec 0 gas) as [H|H];
  [ apply Nat.ltb_lt in H;
    rewrite H;
    simpler
  | try lia ].

Lemma app_sound {dom cod : Ty}
      (x : PactTy cod) (x' : SemTy cod) :
  ∃ gas, ∀ gas', gas < gas' →
    compares_exp (τ:=cod) (gas' - 1) x x' →
    compares (τ:=cod) gas' (app pure (pure x)) (pure x').
Proof.
  unfold app.
  exists 2; intros.
  simpler.
  now enough_gas gas'.
Qed.

End Pact.
