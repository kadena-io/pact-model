Require Import
  Coq.Unicode.Utf8
  (* Coq.ZArith.ZArith *)
  (* Coq.Logic.PropExtensionality *)
  (* Hask.Control.Monad *)
  Data.Semigroup
  Data.Monoid
  (* Data.Either *)
  (* Pact.Lib *)
  (* Pact.Ty *)
  (* Pact.Exp *)
  (* Pact.Value *)
  (* Pact.Ren *)
  (* Pact.Sub *)
  (* Pact.SemTy *)
  (* Pact.Lang *)
  (* Pact.Lang.Capability *)
  (* Pact.SemExp *)
  Coq.Classes.RelationClasses
  Coq.Classes.Morphisms
  (* Pact.Ltac *)
.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Set Equations With UIP. *)

Generalizable All Variables.
Set Primitive Projections.

(* Import ListNotations. *)

Declare Scope hoare_scope.
Declare Scope hoare_scope_ext.

Reserved Infix "\u" (at level 45, right associativity).
Reserved Infix "==>" (at level 55, right associativity).
Reserved Infix "===>" (at level 55, right associativity).
Reserved Infix "\*" (at level 41, right associativity).
Reserved Notation "'\exists' x1 .. xn , H"
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'").
Reserved Notation "'\forall' x1 .. xn , H"
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'").
Reserved Notation "\[ P ]" (at level 0, format "\[ P ]").
Reserved Notation "H1 \-* H2" (at level 43, right associativity).
Reserved Notation "Q1 \--* Q2" (at level 43).

Class HoareLogic (heap : Type) := {
  heap_empty : heap;

  (** In traditional Separation Logic, two heaps are compatible (that is, can
      be composed) if and only if they have disjoint domains, and their
      composition is just their union. *)
  heap_compat : heap → heap → Prop;

  heap_compat_irr {h} :
    h <> heap_empty →
    ¬ heap_compat h h;
  heap_compat_sym {h1 h2} :
    heap_compat h1 h2 →
    heap_compat h2 h1;
  heap_compat_empty_l {h} :
    heap_compat heap_empty h;

  heap_union : heap → heap → heap
    where "X \u Y" := (heap_union X Y) : hoare_scope;

  heap_compat_union_l_eq {h1 h2 h3} :
    heap_compat h1 h2 →
    heap_compat (h1 \u h2) h3 = (heap_compat h1 h3 ∧ heap_compat h2 h3);

  heap_union_empty_l {h} :
    heap_empty \u h = h;
  heap_union_comm {h1 h2} :
    heap_compat h1 h2 →
    h1 \u h2 = h2 \u h1;
  heap_union_assoc {h1 h2 h3} :
    heap_compat h1 h2 →
    heap_compat h2 h3 →
    heap_compat h1 h3 →
    (h1 \u h2) \u h3 = h1 \u (h2 \u h3);

  hprop := heap → Prop;
  himpl (H1 H2 : hprop) : Prop :=
    ∀ h : heap, H1 h → H2 h
    where "H1 ==> H2" := (himpl H1 H2) : hoare_scope;
  qimpl {A} (Q1 Q2 : A → hprop) : Prop :=
    ∀ v : A, Q1 v ==> Q2 v
    where "Q1 ===> Q2" := (qimpl Q1 Q2) : hoare_scope;

  hempty : hprop := λ h, h = heap_empty;

  hstar (H1 H2 : hprop) : hprop :=
    λ h, ∃ h1 h2,
        H1 h1
      ∧ H2 h2
      ∧ heap_compat h1 h2
      ∧ h = h1 \u h2
    where "H1 '\*' H2" := (hstar H1 H2) : hoare_scope;

  hexists {A} (J : A → hprop) : hprop :=
    λ h, ∃ x, J x h
    where "'\exists' x1 .. xn , H" :=
      (hexists (λ x1, .. (hexists (λ xn, H)) ..)) : hoare_scope;

  hforall {A : Type} (J : A → hprop) : hprop :=
    λ h, ∀ x, J x h
    where "'\forall' x1 .. xn , H" :=
      (hforall (λ x1, .. (hforall (λ xn, H)) ..)) : hoare_scope;

  hpure (P : Prop) : hprop :=
    hexists (λ p : P, hempty)
    where "\[ P ]" := (hpure P) : hoare_scope;

  hwand (H1 H2 : hprop) : hprop :=
    hexists (λ H : hprop, H \* (hpure (H1 \* H ==> H2)))
    where "H1 \-* H2" := (hwand H1 H2) : hoare_scope;

  qwand {A} (Q1 Q2 : A → hprop) : hprop :=
    hforall (λ x, hwand (Q1 x) (Q2 x))
    where "Q1 \--* Q2" := (qwand Q1 Q2) : hoare_scope;

  hor (H1 H2 : hprop) : hprop :=
    \exists (b : bool), if b then H1 else H2;

  hand (H1 H2 : hprop) : hprop :=
    \forall (b : bool), if b then H1 else H2;

  htop : hprop :=
    hexists (λ H : hprop, H);
}.

Infix "\u" := heap_union (at level 45, right associativity) : hoare_scope.
Infix "==>" := himpl (at level 55, right associativity) : hoare_scope.
Infix "===>" := qimpl (at level 55, right associativity) : hoare_scope.
Infix "\*" := hstar (at level 41, right associativity) : hoare_scope.
Notation "'\exists' x1 .. xn , H" :=
  (hexists (λ x1, .. (hexists (λ xn, H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\exists' '/ '  x1  ..  xn , '/ '  H ']'") : hoare_scope.
Notation "'\forall' x1 .. xn , H" :=
  (hforall (λ x1, .. (hforall (λ xn, H)) ..))
  (at level 39, x1 binder, H at level 50, right associativity,
   format "'[' '\forall' '/ '  x1  ..  xn , '/ '  H ']'") : hoare_scope.
Notation "\[ P ]" := (hpure P) (at level 0, format "\[ P ]") : hoare_scope.
Notation "H1 \-* H2" := (hwand H1 H2)
  (at level 43, right associativity) : hoare_scope.
Notation "Q1 \--* Q2" := (qwand Q1 Q2) (at level 43) : hoare_scope.

Notation "\[]" := hempty (at level 0) : hoare_scope.
Notation "Q \*+ H" := (λ x, hstar (Q x) H) (at level 40) : hoare_scope.
Notation "\Top" := htop (at level 0) : hoare_scope.

Delimit Scope hoare_scope with hprop.

Notation "H1 ==+> H2" := (H1%hprop ==> hstar H1%hprop H2%hprop)%hprop
  (at level 55, only parsing) : hoare_scope_ext.

Section Hoare.

Open Scope hoare_scope.

Context `{HL : HoareLogic heap}.

Implicit Types h : heap.
Implicit Types P : Prop.
Implicit Types H : hprop.

(** Properties of entailment *)

Lemma himpl_refl {H} :
  (H ==> H).
Proof. now repeat intro. Qed.

#[local] Hint Resolve himpl_refl : core.

Lemma himpl_trans {H2 H1 H3} :
  (H1 ==> H2) →
  (H2 ==> H3) →
  (H1 ==> H3).
Proof.
  repeat intro.
  now apply H0, H.
Qed.

#[export]
Program Instance himpl_PreOrder : PreOrder himpl.
Next Obligation.
  repeat intro.
  eapply himpl_trans; eauto.
Qed.

Lemma himpl_antisym {H1 H2} :
  (H1 ==> H2) →
  (H2 ==> H1) →
  (H1 = H2).
Proof. Admitted.

(** Additional properties of [himpl] *)

Lemma himpl_forall_trans {H1 H2} :
  (∀ H, H ==> H1 → H ==> H2) →
  (H1 ==> H2).
Proof. Admitted.

Lemma himpl_inv {H1 H2 h} :
  (H1 ==> H2) →
  (H1 h) →
  (H2 h).
Proof. auto. Qed.

(** Properties of entailment for postconditions *)

Lemma qimpl_refl {A} {Q : A → hprop} :
  (Q ===> Q).
Proof. Admitted.

#[local] Hint Resolve qimpl_refl : core.

Lemma qimpl_trans {A} {Q2 Q1 Q3 : A → hprop} :
  (Q1 ===> Q2) →
  (Q2 ===> Q3) →
  (Q1 ===> Q3).
Proof. Admitted.

#[export]
Program Instance qimpl_PreOrder {A} : PreOrder (qimpl (A:=A)).
Next Obligation.
  repeat intro.
  eapply qimpl_trans; eauto.
Qed.

Lemma qimpl_antisym {A} {Q1 Q2 : A → hprop} :
  (Q1 ===> Q2) →
  (Q2 ===> Q1) →
  (Q1 = Q2).
Proof. Admitted.

Lemma heap_compat_sym_eq {h1 h2} :
  heap_compat h1 h2 = heap_compat h2 h1.
Proof. Admitted.

Lemma heap_compat_empty_r {h} :
  heap_compat h heap_empty.
Proof.
  rewrite heap_compat_sym_eq.
  apply heap_compat_empty_l.
Qed.

Lemma heap_union_empty_r {h} :
  h \u heap_empty = h.
Proof. Admitted.

Lemma heap_compat_union_r_eq {h1 h2 h3} :
  heap_compat h2 h3 →
  heap_compat h1 (h2 \u h3) = (heap_compat h1 h2 ∧ heap_compat h1 h3).
Proof. Admitted.

Lemma heap_compat_union_l {h1 h2 h3} :
  heap_compat h1 h2 →
  heap_compat h1 h3 →
  heap_compat h2 h3 →
  heap_compat (h1 \u h2) h3.
Proof. Admitted.

Lemma heap_compat_union_r {h1 h2 h3} :
  heap_compat h1 h2 →
  heap_compat h1 h3 →
  heap_compat h2 h3 →
  heap_compat h1 (h2 \u h3).
Proof. Admitted.

(* ---------------------------------------------------------------------- *)
(* ** Tactic *)

(* Hint Rewrite heap_union_empty_l heap_union_empty_r heap_union_assoc : rew_heaps. *)

(* Tactic Notation "rew_heaps" := *)
(*   autorewrite with rew_heaps. *)
(* Tactic Notation "rew_heaps" "in" hyp(H) := *)
(*   autorewrite with rew_heaps in H. *)
(* Tactic Notation "rew_heaps" "in" "*" := *)
(*   autorewrite with rew_heaps in *. *)

(* ---------------------------------------------------------------------- *)
(* ** Introduction and Inversion Lemmas for Core Heap Predicates *)

(** Core heap predicates *)

Lemma hempty_intro :
  \[] heap_empty.
Proof. Admitted.

Lemma hempty_inv {h} :
  \[] h →
  h = heap_empty.
Proof. Admitted.

Lemma hstar_intro {H1 H2 : hprop} {h1 h2} :
  H1 h1 →
  H2 h2 →
  heap_compat h1 h2 →
  (H1 \* H2) (h1 \u h2).
Proof. Admitted.

Lemma hstar_inv {H1 H2 h} :
  (H1 \* H2) h →
  exists h1 h2, H1 h1 ∧ H2 h2 ∧ heap_compat h1 h2 ∧ h = h1 \u h2.
Proof. Admitted.

Lemma hexists_intro {A} {J : A → hprop} {x h} :
  J x h →
  (hexists J) h.
Proof. Admitted.

Lemma hexists_inv {A} {J : A → hprop} {h} :
  (hexists J) h →
  exists x, J x h.
Proof. Admitted.

Lemma hforall_intro {A} {J : A → hprop} {h} :
  (∀ x, J x h) →
  (hforall J) h.
Proof. Admitted.

Lemma hforall_inv {A} {J : A → hprop} {h} :
  (hforall J) h →
  ∀ x, J x h.
Proof. Admitted.

(** Derived heap predicates *)

Lemma hpure_intro {P} :
  P →
  \[P] heap_empty.
Proof. Admitted.

Lemma hpure_inv {P h} :
  \[P] h →
  P ∧ h = heap_empty.
Proof. Admitted.

(* ---------------------------------------------------------------------- *)
(* ** Proving core properties of operators *)

(** Lemmas from this section should be the last ones to access the
    internal definition of the operators hempty and hstar. *)

Section CoreProperties.

#[local] Hint Resolve heap_compat_empty_l heap_compat_empty_r
  heap_union_empty_l heap_union_empty_r hempty_intro
  heap_compat_union_l heap_compat_union_r : core.

(** Empty is left neutral for star *)

Lemma hstar_hempty_l {H} :
  \[] \* H = H.
Proof. Admitted.

(** Star is commutative *)

Lemma hstar_comm {H1 H2} :
   H1 \* H2 = H2 \* H1.
Proof. Admitted.

(** Star is associative *)

Lemma hstar_assoc {H1 H2 H3} :
  (H1 \* H2) \* H3 = H1 \* (H2 \* H3).
Proof. Admitted.

#[export]
Instance hstar_Semigroup : Semigroup hprop := {|
  mappend := hstar
|}.

#[export]
Program Instance hstar_SemigroupLaws : SemigroupLaws hprop.
Next Obligation.
  symmetry.
  apply hstar_assoc.
Qed.

(** Extrusion of existentials out of star *)

Lemma hstar_hexists {A} {J : A → hprop} {H} :
  (hexists J) \* H = hexists (fun x => (J x) \* H).
Proof. Admitted.

(** Extrusion of foralls out of star *)

Lemma hstar_hforall {H A} {J : A → hprop} :
  (hforall J) \* H ==> hforall (J \*+ H).
Proof. Admitted.

(** The frame property (star on H2) holds for entailment *)

Lemma himpl_frame_l {H2 H1 H1'} :
  H1 ==> H1' →
  (H1 \* H2) ==> (H1' \* H2).
Proof. Admitted.

(** Properties of [hpure] *)

Lemma hstar_hpure_l {P H h} :
  (\[P] \* H) h = (P ∧ H h).
Proof. Admitted.

End CoreProperties.

#[global] Opaque hempty hpure hstar hexists.

(* ---------------------------------------------------------------------- *)
(* ** Properties of [hstar] *)

Lemma hstar_hempty_r {H} :
  H \* \[] = H.
Proof. Admitted.

#[export]
Instance hstar_Monoid : Monoid hprop := {|
  mempty := hempty
|}.

#[export]
Program Instance hstar_MonoidLaws : MonoidLaws hprop.
Next Obligation. apply hstar_hempty_l. Qed.
Next Obligation. apply hstar_hempty_r. Qed.

Lemma himpl_frame_r {H1 H2 H2'} :
  H2 ==> H2' →
  (H1 \* H2) ==> (H1 \* H2').
Proof. Admitted.

Lemma himpl_frame_lr {H1 H1' H2 H2'} :
  H1 ==> H1' →
  H2 ==> H2' →
  (H1 \* H2) ==> (H1' \* H2').
Proof. Admitted.

Lemma himpl_hstar_trans_l {H1 H2 H3 H4} :
  H1 ==> H2 →
  H2 \* H3 ==> H4 →
  H1 \* H3 ==> H4.
Proof. Admitted.

Lemma himpl_hstar_trans_r {H1 H2 H3 H4} :
  H1 ==> H2 →
  H3 \* H2 ==> H4 →
  H3 \* H1 ==> H4.
Proof. Admitted.

(* ---------------------------------------------------------------------- *)
(** Properties of [hpure] *)

Lemma hstar_hpure_r {P H h} :
  (H \* \[P]) h = (H h ∧ P).
Proof. Admitted.

(* backward compatibility *)
Definition hstar_hpure {P H h} := @hstar_hpure_l P H h.

  (* corollary only used for the SL course *)
Lemma hstar_hpure_iff {P H h} :
  (\[P] \* H) h ↔ (P ∧ H h).
Proof. Admitted.

Lemma himpl_hstar_hpure_r {P H H'} :
  P →
  (H ==> H') →
  H ==> (\[P] \* H').
Proof. Admitted.

Lemma hpure_inv_hempty {P h} :
  \[P] h →
  P ∧ \[] h.
Proof. Admitted.

Lemma hpure_intro_hempty {P h} :
  \[] h →
  P →
  \[P] h.
Proof. Admitted.

Lemma himpl_hempty_hpure {P} :
  P →
  \[] ==> \[P].
Proof. Admitted.

Lemma himpl_hstar_hpure_l {P H H'} :
  (P → H ==> H') →
  (\[P] \* H) ==> H'.
Proof. Admitted.

Lemma hempty_eq_hpure_true :
  \[] = \[True].
Proof. Admitted.

Lemma hfalse_hstar_any {H} :
  \[False] \* H = \[False].
Proof. Admitted.

Lemma hpure_eq_hexists_empty {P} :
  \[P] = (\exists (p : P), \[]).
Proof. auto. Qed.

(* ---------------------------------------------------------------------- *)
(** Properties of [hexists] *)

Lemma himpl_hexists_l {A H} {J : A → hprop} :
  (∀ x, J x ==> H) →
  (hexists J) ==> H.
Proof. Admitted.

Lemma himpl_hexists_r {A} {x : A} {H J} :
  (H ==> J x) →
  H ==> (hexists J).
Proof. Admitted.

Lemma himpl_hexists {A} {J1 J2 : A → hprop} :
  J1 ===> J2 →
  hexists J1 ==> hexists J2.
Proof. Admitted.

(* ---------------------------------------------------------------------- *)
(** Properties of [hforall] *)

Lemma himpl_hforall_r {A} {J : A → hprop} {H} :
  (∀ x, H ==> J x) →
  H ==> (hforall J).
Proof. Admitted.

Lemma himpl_hforall_l {A x} {J : A → hprop} {H} :
  (J x ==> H) →
  (hforall J) ==> H.
Proof. Admitted.

Lemma himpl_hforall_l_exists {A} {J : A → hprop} {H} :
  (exists x, J x ==> H) →
  (hforall J) ==> H.
Proof. Admitted.

Lemma himpl_hforall {A} {J1 J2 : A → hprop} :
  J1 ===> J2 →
  hforall J1 ==> hforall J2.
Proof. Admitted.

Lemma hforall_specialize {A} {x : A} {J : A → hprop} :
  (hforall J) ==> (J x).
Proof. Admitted.

(* ---------------------------------------------------------------------- *)
(** Properties of hwand (others are found further in the file) *)

Lemma hwand_eq_hexists {H1 H2} :
  (H1 \-* H2) = (\exists H, H \* \[H1 \* H ==> H2]).
Proof. auto. Qed.

Lemma hwand_equiv {H0 H1 H2} :
  (H0 ==> H1 \-* H2) ↔ (H1 \* H0 ==> H2).
Proof. Admitted.

Lemma himpl_hwand_r {H1 H2 H3} :
  H2 \* H1 ==> H3 →
  H1 ==> (H2 \-* H3).
Proof. Admitted.

Lemma himpl_hwand_r_inv {H1 H2 H3} :
  H1 ==> (H2 \-* H3) →
  H2 \* H1 ==> H3.
Proof. Admitted.

Lemma hwand_cancel {H1 H2} :
  H1 \* (H1 \-* H2) ==> H2.
Proof. Admitted.

Arguments hwand_cancel : clear implicits.

Lemma himpl_hempty_hwand_same {H} :
  \[] ==> (H \-* H).
Proof. Admitted.

Lemma hwand_hempty_l {H} :
  (\[] \-* H) = H.
Proof. Admitted.

Lemma hwand_hpure_l {P H} :
  P →
  (\[P] \-* H) = H.
Proof. Admitted.

Arguments hwand_hpure_l : clear implicits.

Lemma hwand_curry {H1 H2 H3} :
  (H1 \* H2) \-* H3 ==> H1 \-* (H2 \-* H3).
Proof. Admitted.

Lemma hwand_uncurry {H1 H2 H3} :
  H1 \-* (H2 \-* H3) ==> (H1 \* H2) \-* H3.
Proof. Admitted.

Lemma hwand_curry_eq {H1 H2 H3} :
  (H1 \* H2) \-* H3 = H1 \-* (H2 \-* H3).
Proof. Admitted.

(* ---------------------------------------------------------------------- *)
(** Properties of [qwand] *)

Lemma qwand_equiv {H A} {Q1 Q2 : A → hprop} :
  H ==> (Q1 \--* Q2) ↔ (Q1 \*+ H) ===> Q2.
Proof. Admitted.

Lemma himpl_qwand_r {A} {Q1 Q2 : A → hprop} {H} :
  Q1 \*+ H ===> Q2 →
  H ==> (Q1 \--* Q2).
Proof. Admitted.

Arguments himpl_qwand_r [A].

Lemma qwand_specialize {A} {x : A} {Q1 Q2 : A → hprop} :
  (Q1 \--* Q2) ==> (Q1 x \-* Q2 x).
Proof. Admitted.

Arguments qwand_specialize [ A ].

(* ---------------------------------------------------------------------- *)
(** Properties of [htop] *)

Lemma htop_intro {h} :
  \Top h.
Proof. Admitted.

Lemma himpl_htop_r {H} :
  H ==> \Top.
Proof. Admitted.

Lemma htop_eq :
  \Top = (\exists H, H).
Proof. auto. Qed.

Lemma hstar_htop_htop :
  \Top \* \Top = \Top.
Proof. Admitted.

(* ---------------------------------------------------------------------- *)
(* ** Properties of [hor] *)

Lemma hor_eq_exists_bool {H1 H2} :
  hor H1 H2 = \exists (b : bool), if b then H1 else H2.
Proof. auto. Qed.

Lemma hor_sym {H1 H2} :
  hor H1 H2 = hor H2 H1.
Proof. Admitted.

Lemma himpl_hor_r_r {H1 H2} :
  H1 ==> hor H1 H2.
Proof. Admitted.

Lemma himpl_hor_r_l {H1 H2} :
  H2 ==> hor H1 H2.
Proof. Admitted.

Lemma himpl_hor_l {H1 H2 H3} :
  H1 ==> H3 →
  H2 ==> H3 →
  hor H1 H2 ==> H3.
Proof. Admitted.

#[global] Opaque hor.

(* ---------------------------------------------------------------------- *)
(* ** Properties of [hand] *)

Lemma hand_eq_forall_bool {H1 H2} :
  hand H1 H2 = \forall (b : bool), if b then H1 else H2.
Proof. auto. Qed.

Lemma hand_sym {H1 H2} :
  hand H1 H2 = hand H2 H1.
Proof. Admitted.

Lemma himpl_hand_l_r {H1 H2} :
  hand H1 H2 ==> H1.
Proof. Admitted.

Lemma himpl_hand_l_l {H1 H2} :
  hand H1 H2 ==> H2.
Proof. Admitted.

Lemma himpl_hand_r {H1 H2 H3} :
  H3 ==> H1 →
  H3 ==> H2 →
  H3 ==> hand H1 H2.
Proof. Admitted.

#[global] Opaque hand.

(** Experimental tactic [xsimpl_hand] *)

(* Tactic Notation "xsimpl_hand" := *)
(*    xsimpl; try (applys himpl_hand_r; xsimpl). *)

(* ---------------------------------------------------------------------- *)
(* ** Set operators to be opaque *)

#[global] Opaque hempty hpure hstar hexists htop hand hor.

(* ********************************************************************** *)
(* * More properties of the magic wand *)

(* ---------------------------------------------------------------------- *)
(* ** Properties of [hwand] *)

Lemma hwand_eq_hexists_hstar_hpure {H1 H2} :
  (H1 \-* H2) = (\exists H, H \* \[H1 \* H ==> H2]).
Proof. auto. Qed.

Lemma hwand_himpl {H1 H1' H2 H2'} :
  H1' ==> H1 →
  H2 ==> H2' →
  (H1 \-* H2) ==> (H1' \-* H2').
Proof. Admitted.

Lemma hwand_himpl_r {H1 H2 H2'} :
  H2 ==> H2' →
  (H1 \-* H2) ==> (H1 \-* H2').
Proof. Admitted.

Lemma hwand_himpl_l {H1' H1 H2} :
  H1' ==> H1 →
  (H1 \-* H2) ==> (H1' \-* H2).
Proof. Admitted.

Lemma hwand_hpure_r_intro {H1 H2} {P : Prop} :
  (P → H1 ==> H2) →
  H1 ==> (\[P] \-* H2).
Proof. Admitted.

Lemma hstar_hwand {H1 H2 H3} :
  (H1 \-* H2) \* H3 ==> H1 \-* (H2 \* H3).
Proof. Admitted.

Arguments hstar_hwand : clear implicits.

(* ---------------------------------------------------------------------- *)
(* ** Properties of [qwand] *)

Lemma himpl_qwand_hstar_same_r {A} {Q : A → hprop} {H} :
  H ==> Q \--* (Q \*+ H).
Proof. Admitted.

Lemma himpl_qwand_r_inv {H A} {Q1 Q2 : A → hprop} :
  H ==> (Q1 \--* Q2) →
  (Q1 \*+ H) ===> Q2.
Proof. Admitted.

Lemma hstar_qwand {H A} {Q1 Q2 : A → hprop} :
  (Q1 \--* Q2) \* H ==> Q1 \--* (Q2 \*+ H).
Proof. Admitted.

Lemma qwand_cancel {A} {Q1 Q2 : A → hprop} :
  Q1 \*+ (Q1 \--* Q2) ===> Q2.
Proof. Admitted.

Lemma qwand_cancel_part {H A} {Q1 Q2 : A → hprop} :
  H \* ((Q1 \*+ H) \--* Q2) ==> (Q1 \--* Q2).
Proof. Admitted.

Lemma qwand_himpl {A} {Q1 Q1' Q2 Q2' : A → hprop} :
  Q1' ===> Q1 →
  Q2 ===> Q2' →
  (Q1 \--* Q2) ==> (Q1' \--* Q2').
Proof. Admitted.

Lemma qwand_himpl_l {A} {Q1 Q1' Q2 : A → hprop} :
  Q1' ===> Q1 →
  (Q1 \--* Q2) ==> (Q1' \--* Q2).
Proof. Admitted.

Lemma qwand_himpl_r {A} {Q1 Q2 Q2' : A → hprop} :
  Q2 ===> Q2' →
  (Q1 \--* Q2) ==> (Q1 \--* Q2').
Proof. Admitted.

(* ********************************************************************** *)
(* * Tactics for heap entailments *)

(* ---------------------------------------------------------------------- *)
(** Specific cleanup for formulaes *)

Ltac on_formula_pre cont :=
  match goal with
  | |- _ ?H ?Q => cont H
  | |- _ _ ?H ?Q => cont H
  | |- _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ _ _ ?H ?Q => cont H
  | |- _ _ _ _ _ _ _ _ _ _ ?H ?Q => cont H
  end.

Ltac on_formula_post cont :=
  match goal with
  | |- _ ?H ?Q => cont Q
  | |- _ _ ?H ?Q => cont Q
  | |- _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ _ _ ?H ?Q => cont Q
  | |- _ _ _ _ _ _ _ _ _ _ ?H ?Q => cont Q
  end.

(* Ltac remove_empty_heaps_formula tt := *)
(*   repeat (on_formula_pre ltac:(remove_empty_heaps_from)). *)

(* ---------------------------------------------------------------------- *)
(* ** Tactic [xsimplh] to prove [H h] from [H' h] *)

(** [xsimplh] applies to a goal of the form [H h].
   It looks up for an hypothesis of the form [H' h],
   where [H'] is a heap predicate (whose type is syntactically [hprop]).
   It then turns the goal into [H ==> H'], and calls [xsimpl].

   This tactic is very useful for establishing the soundness of
   Separation Logic derivation rules. It should never be used in
   the verification of concrete programs, since a heap [h] should
   never appear explicitly in such a proof, all the reasoning being
   conducted at the level of heap predicates. *)

(* Ltac xsimplh_core tt := *)
(*   match goal with N: ?H ?h |- _ ?h => *)
(*     match type of H with hprop => *)
(*     applys himpl_inv N; clear N; xsimpl *)
(*   end end. *)

(* Tactic Notation "xsimplh" := xsimplh_core tt. *)
(* Tactic Notation "xsimplh" "~" := xsimplh; auto_tilde. *)
(* Tactic Notation "xsimplh" "*" := xsimplh; auto_star. *)

(* ********************************************************************** *)
(** * Predicate [local] *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of [local] *)

(** Type of characteristic formulae on values of type B *)

Notation "'~~' B + E" := (hprop → (B → hprop) → (E → Prop) → Prop)
  (at level 8, B at next level, E at next level, only parsing) : type_scope.

(** A formula [F] is mklocal (e.g. [F] could be the predicate SL [triple])
    if it is sufficient for establishing [F H Q] to establish that the
    the formula holds on a subheap, in the sense that [F H1 Q1] with
    [H = H1 \* H2] and [Q = Q1 \*+ H2]. *)

Definition local {B E} (F : ~~B+E) : Prop :=
  ∀ H Q Z,
    (H ==> \exists H1 H2 Q1, H1 \* H2 \*
             \[F H1 Q1 Z ∧ Q1 \*+ H2 ===> Q]) →
    F H Q Z.

(** [local_pred S] asserts that [local (S x)] holds for any [x].
    It is useful for describing loop invariants. *)

Definition local_pred {A B E} (S : A → ~~B+E) :=
  ∀ x, local (S x).

(* ---------------------------------------------------------------------- *)
(* ** Properties of [local] *)

(** Remark: for conciseness, we abbreviate names of lemmas,
    e.g. [local_inv_frame] is named [mklocal_conseq_frame]. *)

Section IsLocal.

Variables B E : Type.
Implicit Types (F : ~~B+E).

(** A introduction rule to establish [local], exposing the definition *)

Lemma local_intro {F} :
  (∀ H Q Z,
    (H ==> \exists H1 H2 Q1, H1 \* H2 \*
             \[F H1 Q1 Z ∧ Q1 \*+ H2 ===> Q]) →
    F H Q Z) →
  local F.
Proof. auto. Qed.

(** An elimination rule for [local] *)

Lemma local_elim {F H Q Z} :
  local F →
  (H ==> \exists H1 H2 Q1, H1 \* H2 \* \[F H1 Q1 Z ∧ Q1 \*+ H2 ===> Q]) →
  F H Q Z.
Proof. auto. Qed.

(** An elimination rule for [local] without [htop] *)

Lemma local_elim_frame {F H Q Z} :
  local F →
  (H ==> \exists H1 H2 Q1, H1 \* H2 \* \[F H1 Q1 Z ∧ Q1 \*+ H2 ===> Q]) →
  F H Q Z.
Proof. Admitted.

(** An elimination rule for [local] specialized for no frame, and no [htop] *)

Lemma local_elim_conseq_pre {F H Q Z} :
  local F →
  (H ==> \exists H1, H1 \* \[F H1 Q Z]) →
  F H Q Z.
Proof. Admitted.

(** Weaken and frame properties from [mklocal] *)

Lemma local_conseq_frame {H1 H2 Q1 F H Q Z} :
  local F →
  F H1 Q1 Z →
  H ==> H1 \* H2 →
  Q1 \*+ H2 ===> Q →
  F H Q Z.
Proof. Admitted.

(** Frame rule *)

Lemma local_frame {H2 Q1 Z H1 F} :
  local F →
  F H1 Q1 Z →
  F (H1 \* H2) (Q1 \*+ H2) Z.
Proof. Admitted.

(** Ramified frame rule *)

Lemma local_ramified_frame {Q1 H1 F H Q Z} :
  local F →
  F H1 Q1 Z →
  H ==> H1 \* (Q1 \--* Q) →
  F H Q Z.
Proof. Admitted.

(** Consequence rule *)

Lemma local_conseq {H' Q' F H Q Z} :
  local F →
  F H' Q' Z →
  H ==> H' →
  Q' ===> Q →
  F H Q Z.
Proof. Admitted.

(** Weakening on pre from [mklocal] *)

Lemma local_conseq_pre {H' F H Q Z} :
  local F →
  F H' Q Z →
  H ==> H' →
  F H Q Z.
Proof. Admitted.

(** Weakening on post from [mklocal] *)

Lemma local_conseq_post {Q' F H Q Z} :
  local F →
  F H Q' Z →
  Q' ===> Q →
  F H Q Z.
Proof. Admitted.

(** Extraction of pure facts from [mklocal] *)

Lemma local_hpure {F H P Q Z} :
  local F →
  (P → F H Q Z) →
  F (\[P] \* H) Q Z.
Proof. Admitted.

(** Extraction of existentials from [mklocal] *)

Lemma local_hexists {F A} {J : A → hprop} {Q Z} :
  local F →
  (∀ x, F (J x) Q Z) →
  F (hexists J) Q Z.
Proof. Admitted.

(** Extraction of existentials below a star from [mklocal] *)

Lemma local_hstar_hexists {F H A} {J : A → hprop} {Q Z} :
  local F →
  (∀ x, F ((J x) \* H) Q Z) →
   F (hexists J \* H) Q Z.
Proof. Admitted.

(** Extraction of forall from [mklocal] *)

Lemma local_hforall {A} {x : A} {F} {J : A → hprop} {Q Z} :
  local F →
  F (J x) Q Z →
  F (hforall J) Q Z.
Proof. Admitted.

Lemma local_hforall_exists {F A} {J : A → hprop} {Q Z} :
  local F →
  (exists x, F (J x) Q Z) →
  F (hforall J) Q Z.
Proof. Admitted.

(** Extraction of forall below a star from [mklocal] *)
(* --TODO needed? *)

Lemma local_hstar_hforall_l {F H A} {J : A → hprop} {Q Z} :
  local F →
  (exists x, F ((J x) \* H) Q Z) →
  F (hforall J \* H) Q Z.
Proof. Admitted.

(** Case analysis for [hor] *)

Lemma local_hor {F H1 H2 Q Z} :
  local F →
  F H1 Q Z →
  F H2 Q Z →
  F (hor H1 H2) Q Z.
Proof. Admitted.

(** Left branch for [hand] *)

Lemma local_hand_l {F H1 H2 Q Z} :
  local F →
  F H1 Q Z →
  F (hand H1 H2) Q Z.
Proof. Admitted.

(** Right branch for [hand] *)

Lemma local_hand_r {F H1 H2 Q Z} :
  local F →
  F H2 Q Z →
  F (hand H1 H2) Q Z.
Proof. Admitted.

(** Extraction of heap representation from [mklocal] *)

Lemma local_name_heap {F H Q Z} :
  local F →
  (∀ h, H h → F (λ h', h' = h) Q Z) →
  F H Q Z.
Proof. Admitted.

(** Extraction of pure facts from the precondition under local *)

Lemma local_prop {F H Q P Z} :
  local F →
  (H ==> H \* \[P]) →
  (P → F H Q Z) →
  F H Q Z.
Proof. Admitted.

(** Extraction of proof obligations from the precondition under local *)

Lemma local_hwand_hpure_l {F} {P : Prop} {H Q Z} :
  local F →
  P →
  F H Q Z →
  F (\[P] \-* H) Q Z.
Proof. Admitted.

End IsLocal.

#[global] Opaque local.

(** [xtpull] plays a similar role to [xpull], except that it works on
   goals of the form [F H Q], where [F] is typically a triple predicate
   or a characteristic formula.

   [xtpull] simplifies the precondition [H] as follows:
   - it removes empty heap predicates
   - it pulls pure facts out as hypotheses into the context
   - it pulls existentials as variables into the context.

   At the end, it regeneralizes in the goals the new variables
   from the context, so as to allow the user to introduce them
   by giving appropriate names. *)

(** Lemmas *)

Lemma xtpull_start {B E} {F : ~~B+E} {H Q Z} :
  F (\[] \* H) Q Z →
  F H Q Z.
Proof. Admitted.

Lemma xtpull_keep {B E} {F : ~~B+E} {H1 H2 H3 Q Z} :
  F ((H2 \* H1) \* H3) Q Z →
  F (H1 \* (H2 \* H3)) Q Z.
Proof. Admitted.

Lemma xtpull_assoc {B E} {F : ~~B+E} {H1 H2 H3 H4 Q Z} :
  F (H1 \* (H2 \* (H3 \* H4))) Q Z →
  F (H1 \* ((H2 \* H3) \* H4)) Q Z.
Proof. Admitted.

Lemma xtpull_starify {B E} {F : ~~B+E} {H1 H2 Q Z} :
  F (H1 \* (H2 \* \[])) Q Z →
  F (H1 \* H2) Q Z.
Proof. Admitted.

Lemma xtpull_empty {B E} {F : ~~B+E} {H1 H2 Q Z} :
  (F (H1 \* H2) Q Z) →
  F (H1 \* (\[] \* H2)) Q Z.
Proof. Admitted.

Lemma xtpull_hpure {B E} {F : ~~B+E} {H1 H2 P Q Z} :
  local F →
  (P → F (H1 \* H2) Q Z) →
  F (H1 \* (\[P] \* H2)) Q Z.
Proof. Admitted.

(* Lemma xtpull_id {A} {x X : A} {B E} {F : ~~B+E} {H1 H2 Q Z} : *)
(*   local F → *)
(*   (x = X → F (H1 \* H2) Q Z) → *)
(*   F (H1 \* (x ~> Id X \* H2)) Q Z. *)
(* Proof. Admitted. *)

Lemma xtpull_hexists {B E} {F : ~~B+E} {H1 H2 A} {J : A → hprop} {Q Z} :
  local F →
  (∀ x, F (H1 \* ((J x) \* H2)) Q Z) →
   F (H1 \* (hexists J \* H2)) Q Z.
Proof. Admitted.

(*--------------------------------------------------------*)
(* ** [xtchange] *)

(** [xtchange E] applies to a goal of the form [F H Q]
    and to a lemma [E] of type [H1 ==> H2] or [H1 = H2].
    It replaces the goal with [F H' Q], where [H']
    is computed by replacing [H1] with [H2] in [H].

    The substraction is computed by solving [H ==> H1 \* ?H']
    with [xsimpl]. If you need to solve this implication by hand,
    use [xtchange_no_simpl E] instead.

    [xtchange <- E] is useful when [E] has type [H2 = H1]
      instead of [H1 = H2].

    [xtchange_show E] is useful to visualize the instantiation
    of the lemma used to implement [xtchange].
    *)

(* Lemma used by [xtchange] *)

Lemma xtchange_lemma {H1 H1' H2 B E H Q Z} {F : ~~B+E} :
  local F →
  (H1 ==> H1') →
  (H ==> H1 \* H2) →
  F (H1' \* H2) Q Z →
  F H Q Z.
Proof. Admitted.

(* ********************************************************************** *)
(* * Iterated star *)

(* ---------------------------------------------------------------------- *)
(** Separation commutative monoid [(hstar,hempty)] *)

(* jww (2022-08-10): TODO: Semigroup, Monoid, Commutative Monoid *)
(* Definition sep_monoid := monoid_make hstar hempty. *)

(* ********************************************************************** *)
(* * Weakest-preconditions *)

(* ---------------------------------------------------------------------- *)
(* ** Definition of the weakest precondition for a formula *)

Definition weakestpre {B E : Type}
  (F : ~~ B+E) (Q : B → hprop) (Z : E → Prop) : hprop :=
  \exists (H:hprop), H \* \[F H Q Z].

Lemma weakestpre_eq {B E} {F : ~~B+E} {H Q Z} :
  local F → (* in fact, only requires weaken-pre and extract-hexists rules to hold *)
  F H Q Z = (H ==> weakestpre F Q Z).
Proof. Admitted.

Lemma weakestpre_conseq {B E} {F : ~~B+E} {Q1 Q2 Z} :
  local F →
  Q1 ===> Q2 →
  weakestpre F Q1 Z ==> weakestpre F Q2 Z.
Proof. Admitted.

Lemma weakestpre_conseq_wand {B E} {F : ~~B+E} {Q1 Q2 Z} :
  local F →
  (Q1 \--* Q2) \* weakestpre F Q1 Z ==> weakestpre F Q2 Z.
Proof. Admitted.

Lemma weakestpre_frame {B E} {F : ~~B+E} {H Q Z} :
  local F →
  (weakestpre F Q Z) \* H ==> weakestpre F (Q \*+ H) Z.
Proof. Admitted.

Lemma weakestpre_pre {B E} {F : ~~B+E} {Q Z} :
  local F →
  F (weakestpre F Q Z) Q Z.
Proof. Admitted.

Lemma himpl_weakestpre {B E} {F : ~~B+E} {H Q Z} :
  F H Q Z →
  H ==> weakestpre F Q Z.
Proof. Admitted.

End Hoare.

Require Import
  Pact.Lib
  Pact.Ltac
  Pact.Ty
  Pact.Exp
  Pact.Lang
  Pact.SemTy
  Pact.SemExp.

Section Sep.

Definition heap    : Type := PactState.
Definition val     : Ty → Type := SemTy (m:=PactM).

Context `{HL : HoareLogic heap}.

Definition vprop τ : Type := val τ → hprop.
Definition eprop   : Type := Err → Prop.

Open Scope hoare_scope.

Definition eimpl (Z1 Z2 : Err → Prop) : Prop :=
  ∀ e : Err, Z1 e → Z2 e.

Infix "==!>" := eimpl (at level 55, right associativity) : hoare_scope.

Implicit Type h : heap.
Implicit Type H : hprop.
Implicit Type Z : eprop.
Implicit Type P : Prop.

Import ListNotations.

Definition hoare `(e : Exp [] τ) H Q Z : Prop :=
  ∀ h : heap, H h →
    match ⟦e⟧ h : Err + ⟦τ⟧ * heap with
    | inr (v, h') => Q v h'
    | inl err => Z err
    end.

Lemma hoare_conseq {τ} {t : Exp [] τ} {H' Q' H Q Z} :
  hoare t H' Q' Z ->
  H ==> H' ->
  Q' ===> Q ->
  hoare t H Q Z.
Proof. Admitted.

Lemma hoare_named_heap {τ} {t : Exp [] τ} {H Q Z} :
  (∀ h, H h -> hoare t (λ h', h' = h) Q Z) ->
  hoare t H Q Z.
Proof. Admitted.

(*
Lemma hoare_val : ∀ v H Q,
  H ==> Q v ->
  hoare (trm_val v) H Q.

Lemma hoare_fun : ∀ x t1 H Q,
  H ==> Q (val_fun x t1) ->
  hoare (trm_fun x t1) H Q.

Lemma hoare_let : ∀ z t1 t2 H Q Q1,
  hoare t1 H Q1 ->
  (∀ v, hoare (subst1 z v t2) (Q1 v) Q) ->
  hoare (trm_let z t1 t2) H Q.

Lemma hoare_seq : ∀ t1 t2 H Q H1,
  hoare t1 H (fun r => H1) ->
  hoare t2 H1 Q ->
  hoare (trm_seq t1 t2) H Q.

Lemma hoare_if : ∀ (b:bool) t1 t2 H Q,
  hoare (if b then t1 else t2) H Q ->
  hoare (trm_if b t1 t2) H Q.

Lemma hoare_if_trm : ∀ Q1 t0 t1 t2 H Q,
  hoare t0 H Q1 ->
  (∀ v, hoare (trm_if v t1 t2) (Q1 v) Q) ->
  hoare (trm_if t0 t1 t2) H Q.

Lemma hoare_apps_funs : ∀ xs F vs t1 H Q,
  F = (val_funs xs t1) ->
  var_funs xs (length vs) ->
  hoare (substn xs vs t1) H Q ->
  hoare (trm_apps F vs) H Q.
*)

Definition quadruple {τ} (t : Exp [] τ) (H : hprop) (Q : val τ → hprop) Z :=
  ∀ H', hoare t (H \* H') (Q \*+ H') Z.

(* jww (2022-08-10): TODO *)
(* Lemma local_quadruple {τ} (t : Exp [] τ) : *)
(*   local (quadruple t). *)

Lemma triple_of_hoare {τ} {t : Exp [] τ} {H Q Z} :
  (∀ H', exists Q', hoare t (H \* H') Q' Z ∧ Q' ===> Q \*+ H') →
  quadruple t H Q Z.
Proof. Admitted.

Lemma hoare_of_quadruple {τ} {t : Exp [] τ} {H Q Z HF} :
  quadruple t H Q Z →
  hoare t (H \* HF) (fun r => Q r \* HF) Z.
Proof. Admitted.

Lemma quadruple_conseq {τ} {t : Exp [] τ} {H' Q' H Q Z} :
  quadruple t H' Q' Z →
  H ==> H' →
  Q' ===> Q →
  quadruple t H Q Z.
Proof. Admitted.

Lemma quadruple_frame {τ} {t : Exp [] τ} {H Q Z H'} :
  quadruple t H Q Z →
  quadruple t (H \* H') (Q \*+ H') Z.
Proof. Admitted.

Lemma quadruple_ramified_frame {τ} {t : Exp [] τ} {H1 Q1 H Q Z} :
  quadruple t H1 Q1 Z →
  H ==> H1 \* (Q1 \--* Q) →
  quadruple t H Q Z.
Proof. Admitted.

Lemma quadruple_hexists {τ} {t : Exp [] τ} {A : Type} {J : A → hprop} {Q Z} :
  (∀ x, quadruple t (J x) Q Z) →
  quadruple t (hexists J) Q Z.
Proof. Admitted.

Lemma quadruple_hforall {A} {x : A} {τ} {t : Exp [] τ} {J : A → hprop} {Q Z} :
  quadruple t (J x) Q Z →
  quadruple t (hforall J) Q Z.
Proof. Admitted.

Lemma quadruple_hpure {τ} {t : Exp [] τ} {P : Prop} {H Q Z} :
  (P → quadruple t H Q Z) →
  quadruple t (\[P] \* H) Q Z.
Proof. Admitted.

Lemma quadruple_hwand_hpure_l {τ} {t : Exp [] τ} {P : Prop} {H Q Z} :
  P →
  quadruple t H Q Z →
  quadruple t (\[P] \-* H) Q Z.
Proof. Admitted.

Lemma quadruple_hor {τ} {t : Exp [] τ} {H1 H2 Q Z} :
  quadruple t H1 Q Z →
  quadruple t H2 Q Z →
  quadruple t (hor H1 H2) Q Z.
Proof. Admitted.

Lemma quadruple_hand_l {τ} {t : Exp [] τ} {H1 H2 Q Z} :
  quadruple t H1 Q Z →
  quadruple t (hand H1 H2) Q Z.
Proof. Admitted.

Lemma quadruple_hand_r {τ} {t : Exp [] τ} {H1 H2 Q Z} :
  quadruple t H2 Q Z →
  quadruple t (hand H1 H2) Q Z.
Proof. Admitted.

Lemma quadruple_conseq_frame {τ} {t : Exp [] τ} {H2 H1 Q1 H Q Z} :
  quadruple t H1 Q1 Z →
  H ==> H1 \* H2 →
  Q1 \*+ H2 ===> Q →
  quadruple t H Q Z.
Proof. Admitted.

(*
Lemma quadruple_val {v H Q Z} :
  H ==> Q v →
  quadruple (trm_val v) H Q.
Proof.
  introv M. intros HF. applys hoare_val. { xchanges M. }
Qed.

Lemma quadruple_let {z t1 t2 H Q Q1} :
  quadruple t1 H Q1 →
  (∀ (X:val), quadruple (subst1 z X t2) (Q1 X) Q) →
  quadruple (trm_let z t1 t2) H Q.
Proof.
  introv M1 M2. intros HF. applys hoare_let.
  { applys M1. }
  { intros v. applys* hoare_of_quadruple. }
Qed.

Lemma quadruple_seq {t1 t2 H Q Q1} :
  quadruple t1 H Q1 →
  (∀ (X:val), quadruple t2 (Q1 X) Q) →
  quadruple (trm_seq t1 t2) H Q.
Proof.
  introv M1 M2. applys* quadruple_let. (* BIND intros. rewrite* subst1_anon. *)
Qed.

Lemma quadruple_if {(b:bool) t1 t2 H Q Z} :
  quadruple (if b then t1 else t2) H Q →
  quadruple (trm_if b t1 t2) H Q.
Proof.
  introv M1. intros HF. applys hoare_if. applys M1.
Qed.

Lemma quadruple_if_bool {(b:bool) t1 t2 H Q Z} :
  (b = true → quadruple t1 H Q) →
  (b = false → quadruple t2 H Q) →
  quadruple (trm_if b t1 t2) H Q.
Proof.
  introv M1 M2. applys quadruple_if. case_if*.
Qed.

Lemma quadruple_if_trm {Q1 t0 t1 t2 H Q Z} :
  quadruple t0 H Q1 →
  (∀ v, quadruple (trm_if v t1 t2) (Q1 v) Q) →
  quadruple (trm_if t0 t1 t2) H Q.
Proof.
  introv M1 M2. intros HF. applys* hoare_if_trm.
  { intros v. applys* hoare_of_quadruple. }
Qed.

Lemma quadruple_if_trm' {Q1 t0 t1 t2 H Q, (* not very useful *)
  quadruple t0 H Q1 →
  (∀ (b:bool), quadruple (if b then t1 else t2) (Q1 b) Q) →
  (∀ v, ~ is_val_bool v → (Q1 v) ==> \[False]) →
  quadruple (trm_if t0 t1 t2) H Q.
Proof.
  introv M1 M2 M3. applys* quadruple_if_trm.
  { intros v. tests C: (is_val_bool v).
    { destruct C as (b&E). subst. applys* quadruple_if. }
    { xtchange* M3. xtpull ;=>. false. } }
Qed.

Lemma quadruple_apps_funs {xs F (Vs:vals) t1 H Q Z} :
  F = (val_funs xs t1) →
  var_funs xs (length Vs) →
  quadruple (substn xs Vs t1) H Q →
  quadruple (trm_apps F Vs) H Q.
Proof. introv E N M. intros HF. applys* hoare_apps_funs. Qed.
*)

Definition formula τ := (val τ → hprop) → eprop → hprop.

Definition wp `(t : Exp [] τ) : formula τ :=
  weakestpre (quadruple t).

Definition WP : Type := ∀ τ (t : Exp [] τ), formula τ.

Definition formula' (B E : Type) := (B → hprop) → (E → Prop) → hprop.

Declare Scope pred_scope.
Open Scope pred_scope.

Notation "{{ H }} x ← e { Q | Z }" :=
  (hoare e H (λ x, Q) Z) (at level 1, e at next level) : pred_scope.

#[local] Hint Unfold hoare : core.

Theorem hoare_post_true H `(Q : vprop τ) Z e :
  (∀ v s, Q v s) →
  (∀ err, Z err) →
  {{H}} x ← e {Q x|Z}.
Proof.
  unfold hoare; sauto.
Qed.

Theorem hoare_pre_false H `(Q : vprop τ) Z e :
  (∀ s, ¬ (H s)) →
  {{H}} x ← e {Q x|Z}.
Proof.
  autounfold; intros.
  intuition.
Qed.

Ltac heaps :=
  repeat
    match goal with
    | [ H : (_ \* _) _  |- _ ] => destruct H
    | [ H : (\exists _, _) _  |- _ ] => destruct H
    | [ H : \[ _ ] _ |- _ ] => inversion H; subst; clear H
    end; reduce.

Theorem wp_equiv {H} `{e : Exp [] τ} {Q : vprop τ} {Z} :
  (H ==> wp e Q Z) ↔ (quadruple e H Q Z).
Proof.
  unfold himpl, wp, weakestpre, quadruple.
  split; repeat intro.
  - heaps.
    specialize (H0 _ H1).
    heaps.
    heaps.
    rewrite heap_compat_union_l_eq in H3; auto.
    reduce.
    rewrite heap_union_empty_r in H1.
    rewrite heap_union_empty_r.
    assert ((x1 \* H') (x2 \u x0))
      by now apply hstar_intro.
    unshelve epose proof (x _ _ H6); auto.
  - repeat eexists; eauto.
    apply heap_compat_empty_r.
    now rewrite heap_union_empty_r.
Qed.

Theorem wp_unique {wp1 wp2 : WP} :
  (∀ H τ (e : Exp [] τ) (Q : vprop τ) Z,
     quadruple e H Q Z ↔ H ==> wp1 _ e Q Z) →
  (∀ H τ (e : Exp [] τ) (Q : vprop τ) Z,
     quadruple e H Q Z ↔ H ==> wp2 _ e Q Z) →
  wp1 = wp2.
Proof.
  intros.
  extensionality τ.
  extensionality e.
  extensionality Q.
  extensionality Z.
  apply himpl_antisym.
  - destruct (H0 (wp1 τ e Q Z) τ e Q Z) as [H5 H6]; clear H0.
    apply H5; intros.
    apply H.
    reflexivity.
  - destruct (H (wp2 τ e Q Z) τ e Q Z) as [H5 H6]; clear H.
    apply H5; intros.
    apply H0.
    reflexivity.
Qed.

Theorem wp_from_weakest_pre (wp' : WP) :
  (∀ H τ (e : Exp [] τ) (Q : vprop τ) Z,
     quadruple e (wp' _ e Q Z) Q Z) →          (* wp_pre *)
  (∀ H τ (e : Exp [] τ) (Q : vprop τ) Z,
     quadruple e H Q Z → H ==> wp' _ e Q Z) → (* wp_weakest *)
  (∀ H τ (e : Exp [] τ) (Q : vprop τ) Z,
     H ==> wp' _ e Q Z ↔ quadruple e H Q Z).  (* wp_equiv *)
Proof.
  intros M1 M2.
  split; intro M.
  - eapply quadruple_conseq; eauto.
    reflexivity.
  - eapply M2; eauto.
Qed.

Notation "e =====> e'" :=
  (∀ Q Z, wp e Q Z ==> wp e' Q Z) (at level 100, e' at next level) : pred_scope.

Lemma eval_if_trm (t0 : Exp [] 𝔹) v0 {τ} (t1 t2 : Exp [] τ)
  (v : SemTy τ) s s' s'' :
  t0 ~[s => s']~> v0 →
  If (Lit (LitBool v0)) t1 t2 ~[s' => s'']~> v →
  If t0 t1 t2 ~[s => s'']~> v.
Proof.
  unfold eval.
  intros.
  simp SemExp in *; simpl in *; autounfold in *.
  now rewrite H.
Qed.

Lemma hoare_if H (b : Exp [] 𝔹) τ (t1 t2 : Exp [] τ)
  (Q' : vprop 𝔹) (Q : vprop τ) Z :
  hoare b H Q' Z →
  (∀ v, hoare (If (Lit (LitBool v)) t1 t2) (Q' v) Q Z) →
  hoare (If b t1 t2) H Q Z.
Proof.
  autounfold.
  repeat intro.
  simp SemExp in *; simpl in *; autounfold in *.
  specialize (H0 _ H2).
  destruct (⟦b⟧ _) eqn:Heqe; auto.
  reduce.
  specialize (H1 _ _ H0).
  simp SemExp in *; simpl in *; autounfold in *.
  exact H1.
Qed.

Lemma quadruple_if H (b : Exp [] 𝔹) τ (t1 t2 : Exp [] τ)
  (Q' : vprop 𝔹) (Q : vprop τ) Z :
  quadruple b H Q' Z →
  (∀ v, quadruple (If (Lit (LitBool v)) t1 t2) (Q' v) Q Z) →
  quadruple (If b t1 t2) H Q Z.
Proof.
  unfold quadruple.
  intros.
  eapply hoare_if; eauto.
  intros.
  apply H1.
Qed.

Ltac wp r H :=
  intros;
  eapply wp_equiv;
  eapply H; eauto;
  eapply wp_equiv;
  subst; reflexivity.

(* An if statement simply propagates the environment. *)
Corollary wp_if (b : Exp [] 𝔹) τ (t1 t2 : Exp [] τ) (Q : vprop τ) Z :
  wp b (λ v, wp (If (Lit (LitBool v)) t1 t2) Q Z) Z
    ==> wp (If b t1 t2) Q Z.
Proof.
  unfold wp.
  simpl.
  repeat intro.
  destruct H as [H [HH H0]].
  exists H.
Admitted.
(*
  split; auto.
  eapply quadruple_if; eauto; intros.
  simpl.
  unfold quadruple, hoare in *.
  intros.
  simpl in *.
  reduce.
  specialize (H0 _ _ (conj HH HH)).
  destruct (⟦b⟧ _);
  simp SemExp in *; simpl in *;
  unravel; reduce;
  exact (H3 _ _ (conj H1 H2)).
Qed.
*)

(*
Lemma quadruple_app_fun H `(v : Exp [] dom) x `(e : Exp [dom] cod)
  (Q : vprop cod) Z :
  (∀ s, v ~[ s => s ]~> x) →
  quadruple ⟦ (x, tt) ⊨ e ⟧ H Q Z →
  quadruple ⟦APP (LAM e) v⟧ H Q Z.
Proof.
  intros.
  repeat intro.
  specialize (H1 _ _ H2).
  simpl in *.
  erewrite sem_app_lam; eauto.
Qed.

Lemma wp_app_fun `(v : Exp [] dom) x `(e : Exp [dom] cod) :
  (∀ s, v ~[ s => s ]~> x) →
  ⟦ (x, tt) ⊨ e ⟧ =====> ⟦APP (LAM e) v⟧.
Proof. wp r quadruple_app_fun. Qed.
*)

(* This encodes a boolean predicate in positive normal form. *)
Inductive Pred : Ty → Set :=
  | P_True : Pred 𝔹
  | P_False : Pred 𝔹
  | P_Eq {τ} : Pred τ → Pred τ → Pred 𝔹
  | P_Or : Pred 𝔹 → Pred 𝔹 → Pred 𝔹
  | P_And : Pred 𝔹 → Pred 𝔹 → Pred 𝔹.

#[local] Hint Constructors Pred : core.

(*
Equations wpc `(e : Exp [] τ) {τ'}
  (Q : val τ → state → Pred τ') Z :
  state → Pred τ' :=
  wpc (Lit l) Q Z := Q (SemLit l);
  (* wpc (APP f v) Q Z := wp ⟦APP f v⟧ Q Z; *)
  wpc (Seq e1 e2) Q Z := wpc e1 (λ _, wpc e2 Q Z) Z;
  wpc (If b t e) Q Z :=
    wpc b (λ b', if b' then wpc t Q Z else wpc e Q Z) Z;
  wpc _ Q Z := _.
*)

(*
Equations wpc `(e : Exp [] τ) (Q : vprop τ) Z : hprop :=
  wpc (Lit l) Q Z := Q (SemLit l);
  wpc (APP f v) Q Z := wp ⟦APP f v⟧ Q Z;
  wpc (Seq e1 e2) Q Z := wpc e1 (λ _, wpc e2 Q Z) Z;
  wpc (If b t e) Q Z :=
    wpc b (λ b', if b' then wpc t Q Z else wpc e Q Z) Z;
  wpc _ Q Z := _.
*)

End Sep.
