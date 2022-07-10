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

Generalizable All Variables.

Section Pact.

Import ListNotations.

Open Scope Ty_scope.
Open Scope Z_scope.

Inductive Pact := PactLang.     (* this is just a type-level tag *)

Derive NoConfusion NoConfusionHom for Pact.

Inductive PactTy := TyInteger.

Derive NoConfusion NoConfusionHom for PactTy.

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
  Pact_HostExpSem FAdd         := uncurry Z.add.

Definition fun1 {Γ} `(f : SemTy dom → SemTy cod) (e : PactExp (dom ⟶ cod))
           (v : Exp (H:=Pact_HostExprs) Γ dom) (V : ValueP v) : Exp Γ cod.
Proof.
  dependent destruction e.
  - inv V.
    inv X;  inv x0; rename H into x.
    inv X0; inv x0; rename H into y.
    exact (HostedVal (H:=Pact_HostExprs) (PInteger (f (x, y)))).
Defined.

Fail Equations PactF {Γ : Env (H:=Pact_HostExprs)}
          {dom cod : Ty (H:=Pact_HostTypes)}
          (e : PactExp (dom ⟶ cod)) :
  ∀ v : Exp (H:=Pact_HostExprs) Γ dom,
    ValueP (H:=Pact_HostExprs) v → Exp Γ cod :=
  PactF FAdd := fun1 Z.add.

Definition PactF {Γ : Env (H:=Pact_HostExprs)}
           {dom cod : Ty (H:=Pact_HostTypes)}
           (e : PactExp (dom ⟶ cod)) :
  ∀ v : Exp (H:=Pact_HostExprs) Γ dom,
    ValueP (H:=Pact_HostExprs) v → Exp Γ cod.
Proof.
  inversion e; subst.
  - now apply fun1; auto; apply (uncurry Z.add).
Defined.

Instance Pact_HostExprsSem : HostExprsSem Pact := {|
  has_host_exprs := Pact_HostExprs;
  HostExpSem := @Pact_HostExpSem;
  CallHost := @PactF;
  Reduce := λ _ _ x,
    match x with
    | PInteger x => existT _ (HostedVal (H:=Pact_HostExprs) (PInteger x)) (HostedValP _)
    | FAdd       => existT _ (HostedFun (H:=Pact_HostExprs) FAdd) (HostedFunP _)
    end
|}.

Program Instance Pact_HostLang : HostLang Pact := {|
  has_host_exprs_sem := Pact_HostExprsSem;
|}.
Next Obligation.
  dependent destruction f.
  (* FAdd *)
  - dependent elimination H; reduce.
    dependent elimination v0; reduce.
    dependent elimination v1; reduce.
    dependent elimination x0; reduce.
    dependent elimination x; reduce.
    now simp Pact_HostExpSem.
Qed.
Next Obligation.
  dependent destruction f.
  (* FAdd *)
  - dependent elimination H; reduce.
    dependent elimination v0; reduce.
    dependent elimination v1; reduce.
    dependent elimination x0; reduce.
    dependent elimination x; reduce.
    simpl in H0.
    unfold solution_right in H0.
    unfold eq_rect_r in H0.
    unfold eq_rect in H0.
    simpl in H0.
    now inversion H0.
Qed.
Next Obligation.
  dependent destruction f.
  (* FAdd *)
  - pose proof (ST_AppHost Γ' _ _ FAdd (RenExp σ v) (RenExp_ValueP σ H)).
    dependent elimination H; reduce.
    dependent elimination v0; reduce.
    dependent elimination v1; reduce.
    dependent elimination x0; reduce.
    dependent elimination x; reduce.
    simpl in *.
    unfold solution_right in H0.
    unfold eq_rect_r in H0.
    unfold eq_rect in H0.
    simpl in H0.
    now apply H0.
Qed.
Next Obligation.
  dependent destruction f.
  (* FAdd *)
  - pose proof (ST_AppHost Γ' _ _ FAdd (SubExp σ v) (SubExp_ValueP σ H)).
    dependent elimination H; reduce.
    dependent elimination v0; reduce.
    dependent elimination v1; reduce.
    dependent elimination x0; reduce.
    dependent elimination x; reduce.
    simpl in *.
    unfold solution_right in H0.
    unfold eq_rect_r in H0.
    unfold eq_rect in H0.
    simpl in H0.
    now apply H0.
Qed.
Next Obligation.
  dependent destruction h.
  (* PInteger *)
  - now simpl.
  - now simpl.
Qed.
Next Obligation.
  dependent destruction h.
  (* PInteger *)
  - now simpl.
  - now simpl.
Qed.
Next Obligation.
  dependent destruction h.
  (* PInteger *)
  - now constructor.
  - now constructor.
Qed.
Next Obligation.
  dependent destruction h.
  (* PInteger *)
  - now constructor.
  - now constructor.
Qed.

Definition num {Γ} (z : Z) : Exp Γ ℤ := HostedVal (PInteger z).
Arguments num {Γ} z /.

Example exp_constant :
  run 10 (num 123) =
    MkΣ (num 123) Empty MT.
Proof. reflexivity. Qed.

Example exp_if_true :
  run 20 (If ETrue (num 123) (num 456)) =
    MkΣ (num 123) Empty MT.
Proof. reflexivity. Qed.

Example exp_if_false :
  run 20 (If EFalse (num 123) (num 456)) =
    MkΣ (num 456) Empty MT.
Proof. reflexivity. Qed.

Example exp_pair :
  run 20 (Pair (num 123) (num 456)) =
    MkΣ (Pair (num 123) (num 456)) Empty MT.
Proof. reflexivity. Qed.

Example exp_fst:
  run 20 (Fst (Pair (num 123) (num 456))) =
    MkΣ (num 123) Empty MT.
Proof. reflexivity. Qed.

Example exp_snd :
  run 20 (Snd (Pair (num 123) (num 456))) =
    MkΣ (num 456) Empty MT.
Proof. reflexivity. Qed.

Example exp_list :
  run 20 (Cons (num 123) (Cons (num 456) Nil)) =
    MkΣ (Cons (num 123) (Cons (num 456) Nil)) Empty MT.
Proof. reflexivity. Qed.

Example exp_car:
  run 20 (Car (num 0) (Cons (num 123) (Cons (num 456) Nil))) =
    MkΣ (num 123) Empty MT.
Proof. reflexivity. Qed.

Example exp_car_nil:
  run 20 (Car (num 0) Nil) =
    MkΣ (num 0) Empty MT.
Proof. reflexivity. Qed.

Example exp_cdr :
  run 20 (Cdr (Cons (num 123) (Cons (num 456) Nil))) =
    MkΣ (Cons (num 456) Nil) Empty MT.
Proof. reflexivity. Qed.

Example exp_cdr_nil :
  run 20 (Cdr (τ:=TyHost TyInteger) Nil) =
    MkΣ Nil Empty MT.
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
  run 10 (APP (HostedFun FAdd) (Pair (num 123) (num 456))) =
    MkΣ (num 579) Empty MT.
Proof. reflexivity. Qed.

End Pact.
