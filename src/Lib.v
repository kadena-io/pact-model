Require Export
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Lists.List
  Coq.Logic.Classical
  Coq.Logic.ProofIrrelevance
  Coq.Program.Equality
  Coq.Program.Program
  Coq.Relations.Relation_Definitions
  Coq.Sets.Ensembles
  Coq.Sets.Finite_sets
  Coq.Sets.Finite_sets_facts
  Coq.Sets.Powerset_facts
  Coq.Strings.String
  Coq.Unicode.Utf8.

From Equations Require Import Equations.
Set Equations With UIP.

Corollary sum_id {X Y : Type} (e : X + Y) :
  match e with
  | inl x => inl x
  | inr y => inr y
  end = e.
Proof. now destruct e. Qed.
