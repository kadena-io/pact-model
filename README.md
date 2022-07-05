# Formal Pact

This repository contains an implementation of the Pact language and a Pact
evaluator all in Coq, which is to be extracted into Haskell and used as a
module within the final Pact evaluator that runs on the Kadena blockchain.

## Roadmap

At the moment only the core of Pact is implemented: namely, a simply-typed
lambda calculus with primitive types and lists. Here is the roadmap of future
work, roughly in order:

- Prove soundness of CEK evaluator
- Extract computable evaluator to Haskell
- Add Builtins
- Add Row-types
- Add Modules
- Add Schemas
- Add Tables
- Add Guards
- Add Capabilities

## Theory

Specifically, this package defines the Pact using dependently-typed terms, so
that all programs are type-correct by construction. We then establish the
semantics of the languages in various ways.

### Denotational semantics

The denotational semantics of Pact are established by denoting terms into Coq,
thus providing a type-theoretic semantics for the language.

### Operational semantics

There is a small-step evaluation semantics that specifies how terms are
reduced operationally, and a proof that this implements the denotational
semantics. We also show that terms are strongly normalizing, with the
implication being that there always exists some amount of gas that can
complete any evaluation.

### Categorical semantics

The Pact language is a cartesian closed category, although its products are
not visible as such to the user, who is only able to use them to form n-tuples
in the form of "arrays".

### Computational CEK evaluator

An abstract CEK machine is used to build an evaluator for computational
reduction of Pact terms in the presence of gas. Since terms are strongly
normalization, there is always some amount of gas that will permit evaluation
to terminate in either a value or an abstraction.

Since abstractions are not made visible to users, terms may be distinguished
as either "internal" and "external", and we should be able to further show
that an AST for external terms only always terminate in a plain value.
