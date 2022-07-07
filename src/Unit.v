Require Export
  Ty
  Exp
  Sem.

Inductive UnitT := TyUnit.

Derive NoConfusion for UnitT.

Definition Unit_HostTypes : HostTypes unit := {|
  HostTy := UnitT;
  HostTySem := λ 'UnitT, unit
|}.

Inductive UnitE : Ty → Type :=
  | EUnit : UnitE (@TyHost _ Unit_HostTypes TyUnit).

Derive NoConfusion for UnitE.

Definition Unit_HostExprs : HostExprs unit := {|
  has_host_types := Unit_HostTypes;
  HostExp := UnitE
|}.

Equations Unit_HostExpSem τ (e : HostExp (HostExprs:=Unit_HostExprs) τ) :
  SemTy τ := Unit_HostExpSem (TyHost TyUnit) EUnit := tt.

Program Definition Unit_HostLang : HostLang unit := {|
  has_host_exprs := Unit_HostExprs;
  HostExpSem := Unit_HostExpSem
|}.

