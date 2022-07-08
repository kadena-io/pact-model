Require Export
  Coq.ZArith.ZArith
  Ty
  Exp
  Sub
  Sem
  Eval
  Norm
  CEK.

From Equations Require Import Equations.
Set Equations With UIP.

Generalizable All Variables.

Section Pact.

Import ListNotations.

Open Scope Ty_scope.
Open Scope Z_scope.

Inductive Pact := PactLang.     (* this is just a type-level tag *)

Derive NoConfusion for Pact.

Inductive PactTy := TyInteger.

Derive NoConfusion for PactTy.

Definition Pact_HostTypes : HostTypes Pact := {|
  HostTy := PactTy;
  HostTySem := λ ty,
    match ty with
    | TyInteger => Z
    end
|}.

Definition ℤ := TyHost (H:=Pact_HostTypes) TyInteger.
Arguments ℤ /.
(* Definition ℝ := TyHost TyDecimal. *)
(* Definition 𝕋 := TyHost TyTime. *)
(* Definition 𝕊 := TyHost TyString. *)
Definition 𝔹 := TyBool (H:=Pact_HostTypes).

Inductive PactExp : Ty (H:=Pact_HostTypes) → Type :=
  | PInteger : Z → PactExp ℤ
  | FAdd     : PactExp (ℤ × ℤ ⟶ ℤ).

Derive Signature NoConfusion Subterm for PactExp.

Definition Pact_HostExprs : HostExprs Pact := {|
  has_host_types := Pact_HostTypes;
  HostExp := PactExp
|}.

Equations Pact_HostExpSem `(e : PactExp τ) : SemTy (H:=Pact_HostTypes) τ :=
  Pact_HostExpSem (PInteger z) := z;
  Pact_HostExpSem FAdd         := λ '(x, y), x + y.

Fail Equations PactF
          {Γ : Env (H:=Pact_HostExprs)}
          {dom cod : Ty (H:=Pact_HostTypes)}
          (e : PactExp (dom ⟶ cod))
          (v : Exp (H:=Pact_HostExprs) Γ dom)
          (V : ValueP (H:=Pact_HostExprs) v) : Exp Γ cod :=
  PactF (dom:=?(ℤ × ℤ)) (cod:=?(ℤ))
        FAdd (Pair (Hosted (PInteger x)) (Hosted (PInteger y))) :=
    Hosted (H:=Pact_HostExprs) (PInteger (x + y)).

Definition PactF {Γ} `(e : PactExp (dom ⟶ cod))
           (v : Exp (H:=Pact_HostExprs) Γ dom) (V : ValueP v) : Exp Γ cod.
Proof.
  dependent destruction e.
  - inv V.
    inv X;  inv x0; rename H into x.
    inv X0; inv x0; rename H into y.
    exact (Hosted (H:=Pact_HostExprs) (PInteger (x + y))).
Defined.

Program Instance Pact_HostExprsSem : HostExprsSem Pact := {|
  has_host_exprs := Pact_HostExprs;
  HostExpSem := @Pact_HostExpSem;
  CallHost := @PactF;
  GetBool := λ _ x, exist _ _ _;
  GetPair := λ _ _ _ x, exist _ _ _;
|}.
Next Obligation. now inv X0. Defined.
Next Obligation. now inv x. Defined.
Next Obligation. now inv x. Defined.
Next Obligation. now inv x. Defined.
Next Obligation. now inv x. Defined.
Next Obligation. now inv x. Defined.
Next Obligation. now inv H. Defined.

Program Instance Pact_HostLang : HostLang Pact := {|
  has_host_exprs_sem := Pact_HostExprsSem;
|}.
Next Obligation.
  dependent destruction f; simp Pact_HostExpSem.
  dependent elimination H; reduce.
  dependent elimination v0; reduce.
  dependent elimination v1; reduce.
  dependent elimination x0; reduce.
  dependent elimination x; reduce.
  simpl; simp Pact_HostExpSem.
  pose proof Pact_HostExpSem_equation_2.
  now simpl in H; rewrite H.
Qed.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.

Definition num {Γ} (z : Z) : Exp Γ ℤ := Hosted (PInteger z).
Arguments num {Γ} z /.

Example exp_constant :
  run 10 (num 123) =
    MkΣ (num 123) Empty MT.
Proof. reflexivity. Qed.

Example exp_pair :
  run 20 (Pair (num 123) (num 456)) =
    MkΣ (Pair (num 123) (num 456)) Empty MT.
Proof. reflexivity. Qed.

Example exp_lam τ :
  run 10 (LAM (cod:=τ) (VAR ZV)) =
    MkΣ (LAM (VAR ZV)) Empty MT.
Proof. reflexivity. Qed.

Example exp_app :
  run 10 (APP (LAM (VAR ZV)) (num 123)) =
    MkΣ (num 123) Empty MT.
Proof. reflexivity. Qed.

Example exp_call_FAdd :
  run 10 (APP (Hosted FAdd) (Pair (num 123) (num 456))) =
    MkΣ (num 579) Empty MT.
Proof. reflexivity. Qed.

End Pact.
