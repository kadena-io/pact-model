Require Export
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Lists.List
  Coq.Logic.Classical
  Coq.Logic.ProofIrrelevance
  Coq.Relations.Relation_Definitions
  Coq.Sets.Ensembles
  Coq.Sets.Finite_sets
  Coq.Sets.Finite_sets_facts
  Coq.Sets.Powerset_facts
  Coq.Strings.String
  Coq.Unicode.Utf8
  Pact.Ltac.

Require Import
  Pact.Data.EnsemblesExt.

Definition PublicKey := unit.

Definition Signed (k : Ensemble PublicKey) {A : Type} (datum : A) := unit.

Definition Capability := unit.

Definition Database := unit.

Definition StateT (s : Type) (m : Type → Type) (a : Type) :=
  s → m (a * s)%type.

Definition Contract :=
  ∀ ks : Ensemble PublicKey,
    (* The data payload is a mapping of keys to values *)
    (string → string)
    (* The capabilities payload is a set of signed capabilities *)
  → Ensemble { ks' & Included _ ks' ks *
                       { c : Capability & Signed ks' c } }%type
  → StateT (Database * Ensemble PactModule) (Either Error) unit.
