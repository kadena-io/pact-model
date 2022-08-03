Require Import
  Hask.Control.Monad
  Hask.Control.Monad.Trans.State
  Pact.Data.Monoid
  Pact.Data.Either
  Pact.Lib
  Pact.Ty
  Pact.Value
  Pact.Exp
  Pact.SemTy
  Pact.Lang
  Pact.Lang.CapabilityType
  Pact.Lang.Capability
  Hask.Control.Lens.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Equations With UIP.

Generalizable All Variables.
Set Primitive Projections.

Import ListNotations.

Open Scope Ty_scope.

(******************************************************************************
 * Facts about Capabilities
 *)

Lemma get_cap_head `(c : Cap s) cs :
  get_cap c (AToken c :: cs) = Some (valueOf (s:=s) c).
Proof.
  destruct c.
  rewrite /= !eq_dec_refl //.
Qed.

Theorem with_capability_idem
  (n : string) `(c : Cap s)
  (p : Cap s → PactM unit)
  (m : reflectTy (TPair (valueTy s) (valueTy s)) →
       PactM (reflectTy (valueTy s)))
  `(f : PactM a) :
  with_capability n c p m (with_capability n c p m f) =
  with_capability n c p m f.
Proof.
  rewrite /with_capability /__check_capability.
  unravel.
  extensionality st.
  matches.
  - rewrite Heqe //.
    sauto.
  - do 2 matches.
    destruct (p _ _) as [|[? [? ?]]]; auto.
    simpl.
    destruct (__claim_resource _ _ _) as [|[? [? ?]]]; auto.
    simpl.
    rewrite get_cap_head //=.
    sauto.
Qed.

Theorem require_capability_idem (n : string) `(c : Cap s) :
  (require_capability c >> require_capability c) =
   require_capability c.
Proof.
  rewrite /require_capability.
  unravel; extensionality st.
  now repeat matches.
Qed.

Lemma extend_f {A B : Type} (f g : A → B) :
  (λ x, f x) = (λ x, g x) → (∀ x, f x = g x).
Proof.
  intros.
  setoid_rewrite <- eta_expansion in H.
  now rewrite H.
Qed.

Theorem with_require_sometimes_noop
  (n : string) `(c : Cap s)
  (p : Cap s → PactM unit)
  (m : reflectTy (TPair (valueTy s) (valueTy s)) →
       PactM (reflectTy (valueTy s))) :

  (* Assuming we are NOT within a defcap predicate... *)
  getsT __in_defcap = pure[PactM] false →

  (* Assuming we ARE within the defining module... *)
  getsT (__in_module n) = pure[PactM] true →

  (* Assuming the predicate always succeeds and changes nothing... *)
  p c = pure[PactM] tt →

  (* Assuming composed predicates only occur within a defcap: This should be
     true of the system as a whole, but this theorem is quantified over all
     possible states. *)
  (getsT __in_defcap = pure[PactM] false → getsT _to_compose = pure[PactM] []) →

  (* Assuming that the resource type is unit...  *)
  ∀ H, eq_dec (valueTy s) TUnit = left H ->

  (* Then just checking a capability is the same as doing nothing. *)
  with_capability n c p m (require_capability c) = pure[PactM] tt.

Proof.
  rewrite /with_capability /require_capability /__check_capability; intros.
  unravel; extensionality st.
  matches.
  - rewrite Heqe //.
  - matches.
    + exfalso.
      apply extend_f with (x:=st) in H.
      inv H.
      congruence.
    + matches.
      * destruct (p _ _) as [|[? [? ?]]] eqn:Heqe2; auto.
        ** rewrite H1 in Heqe2.
           discriminate.
        ** unfold __claim_resource.
           rewrite H4 /= get_cap_head /=.
           pose proof (H2 H).
           unfold getsT in H5.
           apply extend_f with (x:=st) in H5.
           inv H5.
           rewrite H1 in Heqe2.
           inv Heqe2.
           reflexivity.
      * exfalso.
        unfold getsT in H0.
        apply extend_f with (x:=st) in H0.
        inv H0.
        congruence.
Qed.
