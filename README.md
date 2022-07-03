# Formal Pact

This repository contains an implementation of the Pact language and a Pact
evaluator all in Coq, which is to be extracted into Haskell and used as a
module within the final Pact evaluator that runs on the Kadena blockchain.

## Roadmap

At the moment only the core of Pact is implemented: namely, a simply-typed
lambda calculus with primitive types and lists. Here is the roadmap of future
work, roughly in order:

- Strong normalization
- Prove soundness of CEK evaluator
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

First, the denotational semantics of Pact are established by denoting terms
into Coq, thus providing a type-theoretic semantics for the language.

### Operational semantics

Next, there is a small-step evaluation semantics that specifies how terms are
reduced operationally, and a proof that this implements the denotational
semantics.

### Categorical semantics

### Computational evaluator
