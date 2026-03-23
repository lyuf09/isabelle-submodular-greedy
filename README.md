# Isabelle Formalization of Greedy Algorithms for Cardinality-Constrained Submodular Maximization

This repository develops an Isabelle/HOL formalization of deterministic greedy algorithms for monotone submodular maximization under a cardinality constraint, with an AFP-oriented focus on a reusable mathematical core and a clean proof architecture.

## Main theorem proved so far

For finite ground sets, monotone non-negative submodular objectives, and a cardinality constraint of size `k`, the development proves the classical approximation guarantee for deterministic greedy:
- the finite-step bound `1 - (1 - 1/k)^k`, and hence
- the standard corollary `1 - 1/e`.

In addition, the repository formalizes a lazy greedy refinement and proves it against the same abstract greedy specification, so that the lazy variant inherits the same approximation guarantee.

## Current AFP-oriented scope

The current AFP-oriented session focuses on:
- finite ground sets,
- monotone non-negative submodular set functions,
- cardinality constraints,
- deterministic greedy,
- lazy greedy as a refinement of the greedy baseline.

The present session does **not** include the stochastic line, toy experiments, or instance-specific executable material.

## Session

The AFP-oriented session is:

```text
Submodular_Greedy_AFP
```

It currently contains the following theories:

```text
Core/Submodular_Base
Core/Oracle_Cost

Algorithms/Greedy_Submodular_Construct
Algorithms/Lazy_Greedy_Stateful
Algorithms/Lazy_Greedy_Oracle

Proofs/Greedy_Step_Spec
Proofs/Greedy_Submodular_Approx
Proofs/Greedy_Approx_From_Spec
Proofs/Lazy_Greedy_Approx
Proofs/Lazy_Greedy_Stateful_StepSpec
Proofs/Lazy_Greedy_Stateful_Approx
```

## Proof architecture

The development is organized around three layers.

### 1. Core mathematical layer
`Core/Submodular_Base` provides the foundational locale and basic lemmas for finite-ground-set submodular maximization under a cardinality constraint.

`Core/Oracle_Cost` contains the basic oracle-cost layer used by the current development.

### 2. Algorithm layer
`Algorithms/Greedy_Submodular_Construct` formalizes the deterministic greedy construction.

`Algorithms/Lazy_Greedy_Stateful` provides a stateful lazy greedy development.

`Algorithms/Lazy_Greedy_Oracle` provides an oracle-oriented lazy greedy view used to connect lazy selection back to the abstract greedy specification.

### 3. Approximation layer
`Proofs/Greedy_Step_Spec` isolates the abstract one-step specification used by the approximation proof.

`Proofs/Greedy_Submodular_Approx` and `Proofs/Greedy_Approx_From_Spec` establish the classical deterministic greedy approximation guarantee.

`Proofs/Lazy_Greedy_Approx`, `Proofs/Lazy_Greedy_Stateful_StepSpec`, and `Proofs/Lazy_Greedy_Stateful_Approx` show that the lazy greedy refinement fits the same abstract framework and therefore inherits the same guarantee.

## Repository status

This repository still contains additional material outside the current AFP-oriented session, including stochastic greedy developments, complexity/accounting files, executable examples, and experimental files.

These remain in the repository as ongoing or future work, but they are not part of the current AFP session.

## Build

To build the current AFP-oriented session, run:

```bash
isabelle build -D . Submodular_Greedy_AFP
```

## Aim of the development

The aim of this project is not just to formalize one isolated theorem, but to provide a reusable Isabelle/HOL foundation for cardinality-constrained monotone submodular maximization, with:
- stable mathematical interfaces,
- modular proof structure,
- reusable greedy abstractions,
- and a clean path from the classical greedy baseline to implementation-level refinements such as lazy greedy.