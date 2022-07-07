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

Section Example.

Import ListNotations.

Example exp_constant :
  run 10 (Constant (LInteger 123%Z)) = MkV (VConst (LInteger 123%Z)).
Proof. reflexivity. Qed.

Example exp_pair :
  run 20 (Pair (Constant (LInteger 123%Z))
               (Constant (LInteger 456%Z))) =
    MkV (VPair (VConst (LInteger 123%Z))
               (VConst (LInteger 456%Z))).
Proof. reflexivity. Qed.

Example exp_lam τ :
  run 10 (LAM (cod:=τ) (VAR ZV)) =
    MkV (VClosure (Lambda (VAR ZV) Empty)).
Proof. reflexivity. Qed.

Example exp_app :
  run 10 (APP (LAM (VAR ZV)) (Constant (LInteger 123%Z))) =
    MkV (VConst (LInteger 123%Z)).
Proof. reflexivity. Qed.

End Example.
