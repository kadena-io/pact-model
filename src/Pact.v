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

Inductive PactTy := TyInteger.

Derive NoConfusion for PactTy.

Definition Pact_HostTypes : HostTypes Pact := {|
  HostTy := PactTy;
  HostTySem := λ ty,
    match ty with
    | TyInteger => Z
    end
|}.

Inductive PactExp : Ty (H:=Pact_HostTypes) → Type :=
  | PInteger : Z → PactExp (TyHost (H:=Pact_HostTypes) TyInteger)
  | FAdd : PactExp (TyHost (H:=Pact_HostTypes) TyInteger ×
                    TyHost (H:=Pact_HostTypes) TyInteger
                      ⟶ TyHost (H:=Pact_HostTypes) TyInteger).

Derive Signature NoConfusion Subterm for PactExp.

Definition Pact_HostExprs : HostExprs Pact := {|
  has_host_types := Pact_HostTypes;
  HostExp := PactExp
|}.

Equations Pact_HostExpSem `(e : HostExp (HostExprs:=Pact_HostExprs) τ) : SemTy τ :=
  Pact_HostExpSem (PInteger z) := z;
  Pact_HostExpSem FAdd := λ '(x, y), x + y.

(*
Definition PactF {dom cod : Ty (H:=@has_host_types _ Pact_HostExprs)}
           `(e : PactExp (dom ⟶ cod))
           `(v : Exp Γ dom) (V : ValueP v) : Exp Γ cod :=
  match e with
  | FAdd =>
      match V with
      | PairP (@HostedP _ ?(@has_host_types _ Pact_HostExprs) _ _ (PInteger x))
              (HostedP (PInteger y)) => Hosted (PInteger (x + y))
      | _ => !
      end
  | _ => !
  end.
*)

Equations PactF {dom cod : Ty (H:=@has_host_types _ Pact_HostExprs)}
          (e : PactExp (dom ⟶ cod))
          `(v : Exp Γ dom) (V : ValueP v) : Exp Γ cod :=
  PactF FAdd (Pair (Hosted (PInteger x)) (Hosted (PInteger y))) _ :=
    Hosted (H:=Pact_HostExprs) (PInteger (x + y));
  PactF FAdd _ _ := _.
Next Obligation. now inv h. Defined.
Next Obligation. now inv V. Defined.
Next Obligation. now inv V. Defined.
Next Obligation. now inv V. Defined.
Next Obligation. now inv V. Defined.
Next Obligation. now inv V. Defined.
Next Obligation. now inv V. Defined.
Next Obligation. now inv V. Defined.
Next Obligation. now inv V. Defined.
Next Obligation. now inv V. Defined.
Next Obligation. now inv V. Defined.

Program Instance Pact_HostExprsSem : HostExprsSem Pact := {|
  has_host_exprs := Pact_HostExprs;
  HostExpSem := @Pact_HostExpSem;
  CallHost := λ Γ dom cod f, @PactF dom cod f Γ;
  GetBool := λ _ x, exist _ _ _;
  GetPair := λ _ _ _ x, exist _ _ _;
|}.
Next Obligation. now inv X0. Defined.
Next Obligation. now inv x. Defined.
Next Obligation. now inv x. Defined.
Next Obligation. now inv x. Defined.
Next Obligation. now inv x. Defined.
Next Obligation. now inv x. Defined.

Program Instance Pact_HostLang : HostLang Pact := {|
  has_host_exprs_sem := Pact_HostExprsSem;
|}.
Next Obligation.
  dependent induction f; simp Pact_HostExpSem.
  dependent elimination v; simp PactF; inversion H.
  reduce.
  simp PactF; simpl.
  inv X; inv X0.
  dependent elimination x.
  dependent elimination x0.
  simp PactF; simpl.
  now simp Pact_HostExpSem.
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

Example exp_constant :
  run 10 (Hosted (PInteger 123)) = MkΣ (Hosted (PInteger 123)) Empty MT.
Proof. reflexivity. Qed.

Example exp_pair :
  run 20 (Pair (Hosted (PInteger 123))
               (Hosted (PInteger 456))) =
    MkΣ (Pair (Hosted (PInteger 123)) (Hosted (PInteger 456))) Empty MT.
Proof. reflexivity. Qed.

Example exp_lam τ :
  run 10 (LAM (cod:=τ) (VAR ZV)) = MkΣ (LAM (VAR ZV)) Empty MT.
Proof. reflexivity. Qed.

Example exp_app :
  run 10 (APP (LAM (VAR ZV)) (Hosted (PInteger 123))) =
    MkΣ (Hosted (PInteger 123)) Empty MT.
Proof. reflexivity. Qed.

Example exp_call_FAdd :
  run 10 (APP (Hosted FAdd) (Pair (Hosted (PInteger 123)) (Hosted (PInteger 456)))) =
    MkΣ (Hosted (PInteger 579)) Empty MT.
Proof. reflexivity. Qed.

End Pact.
