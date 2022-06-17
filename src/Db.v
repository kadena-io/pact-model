Require Import
  Coq.Program.Program
  Coq.Unicode.Utf8
  Coq.micromega.Lia
  Coq.Classes.Morphisms
  Coq.Relations.Relation_Definitions
  Coq.Strings.String
  Coq.Vectors.Vector
  Coq.Lists.List
  Coq.Sets.Ensembles
  Coq.Logic.EqdepFacts.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Set Universe Polymorphism.

Generalizable All Variables.

Import ListNotations.

Definition stream (A : Type) : Type := nat → A.

Definition result_stream `(S : stream A) (B : A → Type) : Type :=
  ∀ n : nat, B (S n).

Definition dep_stream (A : Type) (B : A → Type) : Type :=
  ∀ S : stream A, result_stream S B.

Definition Schema : Type := list (string * Type).

Inductive Rec : Schema → Type :=
  | Empty : Rec []
  | Field name {ty S} : ty → Rec S → Rec ((name, ty) :: S).

(* jww (2022-06-15): Keys are just unique names at the moment *)
Definition Table (S : Schema) : Type := list (string * Rec S).

Open Scope string_scope.

Example same_record :
  Rec [("foo", nat : Type); ("bar", nat : Type); ("baz", nat : Type)].
Proof.
  exact (Field "foo" (1 : nat)
               (Field "bar" (2 : nat)
                      (Field "baz" (3 : nat) Empty))).
Qed.

Definition Database : Type := list (string * { S : Schema & Table S }).

Section Kadena.

Class EqDec (A : Type) := {
    eq_dec : ∀ x y : A, {x = y} + {x ≠ y}
}.

Fixpoint lookup {k v : Type} `{EqDec k} (i : k) (l : list (k * v)) : option v :=
  match l with
  | [] => None
  | (j, x) :: xs => if eq_dec i j then Some x else lookup i xs
  end.

(* At the moment all database operations are "global" and not constrained to
   what the capabilities of the contract permit it to see. *)
Inductive Op : Type :=
  | Noop
  | Query {a : Type} (q : Database → a)
  | Update (u : Database → Database).

Inductive Result : Op → Type :=
  | Nothing : Result Noop
  | Answer {a} {q : Database → a} : a → Result (Query q)
  | Updated {u} : Result (Update u)
  (* Any operation might result in an error. *)
  | Error {o} (msg : string) : Result o.

Definition Kadena := dep_stream Op Result.

Definition Contract : Type := list Op * Op.

Definition Modules : Schema := [ ("contract", Contract) ].

Definition NoopContract : Contract := ([], Noop).
Definition NoopModule : Rec Modules := Field "contract" NoopContract Empty.

Program Definition Store : Database :=
  [ ("modules", existT _ Modules [("noop", NoopModule)]) ].

Definition kda : Kadena.
Proof.
  repeat intro.
  induction (S n); constructor.
  apply q.
  exact Store.
Defined.

Fixpoint typeof {S : Schema} (r : Rec S) (field : string) : Type :=
  match r with
  | Empty => False
  | @Field name ty _ _ xs =>
      if name =? field then ty else typeof xs field
  end.

Equations get {S : Schema} (r : Rec S) (field : string) : typeof r field :=
  get Empty _ := False_rect _ _;
  get (Field name x xs) field := if name =? field then x else get xs field.

Program Definition call_noop_contract (k : Kadena) :=
  k (λ n, if Nat.eqb n 0
          then Update (λ _, Store) (* genesis *)
          else Query (λ db, match lookup "modules" db with
                            | Some (existT _ _ ms) =>
                                match lookup "noop" ms with
                                | Some r =>
                                    get r "contract"
                                | None => Error "failed"
                                end
                            | None => Error "failed"
                            end)) 1.

Lemma call_noop_contract_correct :
  call_noop_contract kda = Answer ().
Proof. reflexivity. Qed.

End Kadena.
