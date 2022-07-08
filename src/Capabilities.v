Require Import
  Coq.Program.Equality
  Coq.Unicode.Utf8
  Coq.Strings.String
  Coq.Sets.Ensembles
  EnsemblesExt
  Group.

From Equations Require Import Equations.

Generalizable All Variables.

(************************************************************************
 * The Pact language *)

Section Pact.

Inductive Ty : Set :=
  | TUnit
  | TInt
  | TString
  | TPair : Ty → Ty → Ty.

Derive NoConfusion Subterm for Ty.

Inductive Value : Ty → Set :=
  | VUnit     : Value TUnit
  | VInt      : nat → Value TInt
  | VString   : string → Value TString
  | VPair a b : Value a → Value b → Value (TPair a b).

Derive Signature NoConfusion for Value.

End Pact.

(************************************************************************
 * Capabilities *)

Record Sig (n : string) : Set := {
  paramTy : Ty;               (* this could be a product (i.e. pair) *)
  valueTy : Ty;               (* is TUnit for unmanaged caps *)
  valueMonoid : Monoid (Value valueTy)
}.

Arguments paramTy {n} _.
Arguments valueTy {n} _.
Arguments valueMonoid {n} _.

Inductive Cap `(S : Sig n) : Set :=
  | Token : Value (paramTy S) → Cap S.

Arguments Token {n S} _.

Record ACap : Set := {
  name : string;
  sig  : Sig name;
  cap  : Cap sig
}.

Inductive CapError : Set :=
  | UnknownCapability      : string → CapError
  | InvalidParameter       : ∀ t : Ty, Value t → CapError
  | InvalidValue           : ∀ t : Ty, Value t → CapError
  | CapabilityNotAvailable : ACap → CapError
  | ManagedError           : string → CapError
  | TypeError.

Record Def `(S : Sig n) : Type := {
  predicate : Value (paramTy S) → Ensemble ACap;
}.

Arguments predicate {n S} _.

Record Defs := {
  capabilities : ∀ (n : string) (S : Sig n), Ensemble (Def S)
}.

(************************************************************************
 * Handling capabilities
 *)

Inductive CExpr : Set :=
  | INSTALL {t} : ACap → Value t → CExpr
  | WITH    {t} : ACap → Value t → CExpr → CExpr
  | REQUIRE     : ACap → CExpr
  | SEQ         : CExpr → CExpr → CExpr.

Definition is_defined (D : Defs) (C : ACap) : Ensemble (Def (sig C)) :=
  capabilities D (name C) (sig C).

Definition Available := Ensemble { C : ACap & Value (valueTy (sig C)) }.

Definition set_available (A : Available) (C : ACap)
           (v : Value (valueTy (sig C))) : Available :=
  λ e, IF projT1 e = C
       then Singleton _ (existT _ C v) e
       else A e.

Inductive CEval (D : Defs) :
  Ensemble ACap →               (* granted capability tokens prior *)
  Available →                   (* resource available prior *)
  CExpr →
  Ensemble ACap →               (* granted capability tokens after *)
  Available →                   (* resource available after *)
  Prop :=

  (* install-capability *)
  | Eval_INSTALL cs ms (C : ACap) (val : Value (valueTy (sig C))) :
    ∀ avail, existT _ C avail ∉ ms →
    CEval D
      cs ms
      (INSTALL C val)
      cs (set_available ms C val)

  (* install-capability noop *)
  | Eval_INSTALL_noop cs ms (C : ACap) (val : Value (valueTy (sig C))) :
    ∀ avail, existT _ C avail ∈ ms →
    CEval D
      cs ms
      (INSTALL C val)
      cs ms

  (* with-capability *)
  | Eval_WITH cs ms ms' (C : ACap) (val : Value (valueTy (sig C))) expr :
    C ∉ cs →
    ∀ def, is_defined D C def →
    ∀ avail, (valueTy (sig C) = TUnit ∨ existT _ C avail ∈ ms) →
    ∀ is_monoid : Monoid (Value (valueTy (sig C))),
      is_monoid = valueMonoid (sig C) →
    ∀ remainder, avail = val ⊗ remainder →
    ∀ arg, cap C = Token arg →
    CEval D
      ({ C } ∪ predicate def arg ∪ cs)
      (set_available ms C remainder)
      expr
      ({ C } ∪ predicate def arg ∪ cs) ms' →
    CEval D
      cs ms
      (WITH C val expr)
      cs ms'

  | Eval_WITH_noop cs ms ms' (C : ACap) (val : Value (valueTy (sig C))) expr :
    C ∈ cs →
    CEval D
      cs ms
      expr
      cs ms' →
    CEval D
      cs ms
      (WITH C val expr)
      cs ms'

  (* require-capability *)
  | Eval_REQUIRE (C : ACap) cs ms :
    C ∈ cs →
    CEval D
      cs ms
      (REQUIRE C)
      cs ms

  (* Sequencing of two capability functions. An important thing to note here
     is that the set of available capabilities cannot be changed by a
     sequence, but only through the scoping provided by WITH. *)
  | Eval_SEQ cs ms ms' ms'' expr1 expr2 :
    CEval D
      cs ms
      expr1
      cs ms' →
    CEval D
      cs ms'
      expr2
      cs ms'' →
    CEval D
      cs ms
      (SEQ expr1 expr2)
      cs ms''.

Import EqNotations.

Lemma unit_dep t (H : t = TUnit) (v : Value t) : v = rew <- H in VUnit.
Proof.
  dependent elimination v; inversion H.
  now simpl_eq.
Qed.

Theorem With_With_Noop D cs (ms ms' : Available) expr
        (C : ACap) (val : Value (valueTy (sig C)))
        (single_definition : ∀ def def',
            is_defined D C def → is_defined D C def' → def = def')
        (single_avail : ∀ avail avail',
            existT _ C avail ∈ ms → existT _ C avail' ∈ ms → avail = avail')
        (monoid_right_inj : ∀ `{Monoid A} (x y y' : A),
            x ⊗ y = x ⊗ y' → y = y') :
  (* given that C is an instance of a defined capability *)
  ∀ def, is_defined D C def →
  (* and known that C has an argument *)
  ∀ arg, cap C = Token arg →
  (* and that C isn't already in scope *)
  C ∉ cs →
  (* and given that the capability has been installed *)
  ∀ avail, valueTy (sig C) = TUnit ∨ existT _ C avail ∈ ms →
  (* and knowing that the value type is a monoid *)
  ∀ is_monoid : Monoid (Value (valueTy (sig C))),
    is_monoid = valueMonoid (sig C) →
  (* and knowing that the remainder is a subset of the available amount *)
  ∀ remainder, avail = val ⊗ remainder →
  (* and provided that [expr] evaluates with the given environment *)
  CEval D ({ C } ∪ predicate def arg ∪ cs)
          (set_available ms C remainder) expr
          ({ C } ∪ predicate def arg ∪ cs) ms' →
  (* then we state the theorem that WITH is idempotent *)
  CEval D cs ms (WITH C val (WITH C val expr)) cs ms'
    ↔ CEval D cs ms (WITH C val expr) cs ms'.
Proof.
  split; intros.
  - inversion H6; subst; clear H6.
    + apply Eqdep.EqdepTheory.inj_pair2 in H9; subst.
      eapply Eval_WITH; eauto.
      rewrite H0 in H20; inversion H20; subst; clear H0 H20.
      specialize (single_definition def def0 H H12); subst.
      destruct H2, H13.
      * pose proof (unit_dep _ H0 remainder).
        rewrite H3 in H5.
        pose proof (unit_dep _ H0 remainder0).
        rewrite H4.
        now apply H5.
      * pose proof (unit_dep _ H0 remainder).
        rewrite H3 in H5.
        pose proof (unit_dep _ H0 remainder0).
        rewrite H4.
        now apply H5.
      * pose proof (unit_dep _ H2 remainder).
        rewrite H3 in H5.
        pose proof (unit_dep _ H2 remainder0).
        rewrite H4.
        now apply H5.
      * specialize (single_avail _ _ H0 H2).
        specialize (monoid_right_inj _ _ _ _ _ single_avail); subst.
        now apply H5.
    + now apply Eqdep.EqdepTheory.inj_pair2 in H12; subst.
  - inversion H6; subst; clear H6.
    + apply Eqdep.EqdepTheory.inj_pair2 in H9; subst.
      eapply Eval_WITH; eauto.
      rewrite H0 in H20; inversion H20; subst; clear H0 H20.
      specialize (single_definition def def0 H H12); subst.
      eapply Eval_WITH_noop; eauto.
      now apply Constructive_sets.Add_intro2.
    + apply Eqdep.EqdepTheory.inj_pair2 in H12; subst.
      eapply Eval_WITH_noop; eauto.
      now eapply Eval_WITH; eauto.
Qed.

(* Print Assumptions With_With_Noop. *)
