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

Generalizable All Variables.

Import ListNotations.

Inductive PactModule := MkPactModule (name : string).

Derive NoConfusion for Ascii.ascii.
Derive Subterm for Ascii.ascii.
Derive EqDec for Ascii.ascii.

Derive NoConfusion for string.
Derive Subterm for string.
Derive EqDec for string.

Derive NoConfusion for PactModule.
Derive Subterm for PactModule.
Derive EqDec for PactModule.

Definition moduleName (P : PactModule) : string :=
  match P with
  | MkPactModule name => name
  end.

Hypothesis signature : PactModule → Type.

Declare Instance signature_EqDec M : EqDec (signature M).

Record Signature : Type := {
  module       : PactModule;
  name         : string;
  paramTy      : Type;               (* this is often a product *)
  paramTyEqDec : EqDec paramTy;

  (* Fields only used for managed types *)
  valueTy      : Type;                       (* [()]  if unmanaged *)
  claim        : valueTy → string + valueTy; (* [inr] if unmanaged *)
}.

(* If two capability signatures in the same module have the same name, then
   they also must have the same parameter type. *)
Hypothesis unique_names : ∀ s s',
  module s = module s' → name s = name s' → paramTy s = paramTy s'.

Record Capability (S : Signature) : Type := {
  param : paramTy S;
  value : valueTy S;
  valid : signature (module S);
}.

(* It is unspecified how one obtains the core capability related to a module
   `M`, which grants the ability to grant further capabilities for that
   module. *)
Hypothesis module_capability : ∀ M : PactModule,
    Capability {| module  := MkPactModule "__pact"
                ; name    := moduleName M
                ; paramTy := signature M
                ; valueTy := ()
                ; claim   := inr
                |}.

(* If one has in hand the core Pact capability for a given module M, then
  capabilities can be granted for that module. *)
Definition grant {S : Signature} {r : Type}
           (pact : Capability {| module  := MkPactModule "__pact"
                               ; name    := moduleName (module S)
                               ; paramTy := signature (module S)
                               ; valueTy := ()
                               ; claim   := inr
                               |})
           (p : paramTy S)
           (v : valueTy S) : Capability S :=
  {| param := p
   ; value := v
   ; valid := param _ pact
   |}.

(* This just shows that requiring a capability has no semantics other than
   needing availability of the capability witness. *)
Definition require {S : Signature} {r : Type} :
  Capability S → r → r := λ _, id.

Fixpoint CapabilityList (l : list Signature) : Type :=
  match l with
  | [] => ()
  | s :: xs => (Capability s * CapabilityList xs)
  end.

Definition ccons `(x : Capability s) `(l : CapabilityList xs) :
  CapabilityList (s :: xs) := (x, l).

Equations csnoc `(x : Capability s) `(l : CapabilityList xs) :
  CapabilityList (xs ++ [s]) :=
  @csnoc s x [] () := (x, ());
  @csnoc s x (_ :: _) (y, ys) := ccons y (csnoc x ys).

Equations capp `(l1 : CapabilityList xs) `(l2 : CapabilityList ys) :
  CapabilityList (xs ++ ys) :=
  @capp [] () _ l2 := l2;
  @capp (_ :: _) (x, l1) _ l2 := ccons x (capp l1 l2).

Import EqNotations.

(* Capabilities are only weakly matched, since the first is considered the
   "granted" and the second the "required". Only the former is actually
   used. This matters only when it comes to managed capabilities. *)
Inductive weakly_matched {s1 s2} : Capability s1 → Capability s2 → Type :=
  | is_weakly_matched c1 c2 :
    ∀ (Hm : module s1 = module s2)
      (Hn : name   s1 = name   s2),
      param s1 c1 = rew <- [id] (unique_names s1 s2 Hm Hn) in param s2 c2
    → weakly_matched c1 c2.

(* Capabilities are only weakly matched, since the first is considered the
   "granted" and the second the "required". Only the former is actually
   used. This matters only when it comes to managed capabilities. *)
Equations weak_match `(c1 : Capability s1) `(c2 : Capability s2) :
  option (weakly_matched c1 c2) :=
  @weak_match s1 c1 s2 c2
    with eq_dec (module s1) (module s2),
         eq_dec (name s1)   (name s2) := {
    | in_left, in_left with
      @eq_dec _ (paramTyEqDec s1) (param s1 c1)
              (rew <- [id] (unique_names s1 s2 _ _) in (param s2 c2)) := {
      | in_left => Some (is_weakly_matched c1 c2 e0 e e1)
      | in_right => None
      }
    | _, _ := None
  }.

Record FoundCapability `(c : Capability s) : Type := {
  pre     : list Signature;
  sig     : Signature;
  post    : list Signature;
  before  : CapabilityList pre;
  found   : Capability sig;
  after   : CapabilityList post;
  matched : weakly_matched c found;
}.

Equations cextract' `(c : Capability s)
          `(l1 : CapabilityList xs) `(l2 : CapabilityList ys) :
  option (FoundCapability c) :=
  @cextract' _ _ _ _ [] _ := None;
  @cextract' s c xs l1 (y :: ys) (yc, ycs)
    with weak_match c yc := {
    | Some H :=
      Some {| pre     := xs
            ; sig     := y
            ; post    := ys
            ; before  := l1
            ; found   := yc
            ; after   := ycs
            ; matched := H
            |}
    | None := cextract' c (csnoc yc l1) ycs
    }.

(* Find whether there is a match for a value of a certain typed capability
   within a list of type capabilities. There could, for example, be multiple
   ALLOW_ACCESS capabilities, each instantiated for a different user name.
   Extract and return the value of the actual capability discovered, indexed
   by the value used to look it up. *)
Definition cextract `(c : Capability s) `(l : CapabilityList xs) :
  option (FoundCapability c) := @cextract' s c [] () xs l.

(* For managed capabilities we will want to recompose the list of extant
   capabilities by applying the result after "claiming" the required amount.
   For unmanaged capabilities, we just retain the original capability list
   before extraction. *)
Definition recompose `{c : Capability s} `(f : FoundCapability c)
           (x : Capability (sig c f)) :
  CapabilityList (pre c f ++ sig c f :: post c f) :=
  capp (before c f) (ccons x (after c f)).

