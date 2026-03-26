# Isabelle Formalization of Greedy Algorithms for Cardinality-Constrained Submodular Maximization

This repository develops an Isabelle/HOL formalization of deterministic greedy algorithms for monotone non-negative submodular maximization under a cardinality constraint on a finite ground set.

The current AFP-oriented session proves the classical approximation guarantee for deterministic greedy, namely the finite-step bound `1 - (1 - 1/k)^k` and hence the standard corollary `1 - 1/e`. It also formalizes a stateful lazy greedy variant and shows that it satisfies the same abstract greedy specification, so that it inherits the same approximation guarantee.

## Current AFP-oriented scope

The current AFP-oriented session focuses on:
- finite ground sets,
- monotone non-negative submodular set functions,
- cardinality constraints,
- deterministic greedy,
- lazy greedy as a deterministic refinement of the greedy baseline.

It does **not** include the stochastic line, executable experiments, or instance-specific auxiliary material.

## Session

The AFP-oriented session is:

```text
Submodular_Greedy_AFP
```

It currently includes the following theories:

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

## Structure of the development

The development is organized into three layers.

### 1. Core mathematical layer
`Core/Submodular_Base` provides the main locale and basic lemmas for finite-ground-set monotone submodular maximization under a cardinality constraint.

`Core/Oracle_Cost` provides the oracle-cost layer used by the current development.

### 2. Algorithm layer
`Algorithms/Greedy_Submodular_Construct` formalizes the deterministic greedy construction.

`Algorithms/Lazy_Greedy_Stateful` formalizes a stateful lazy greedy variant.

`Algorithms/Lazy_Greedy_Oracle` provides the oracle-oriented lazy greedy view used to connect lazy selection to the abstract greedy specification.

### 3. Approximation layer
`Proofs/Greedy_Step_Spec` isolates the abstract one-step specification used in the approximation proof.

`Proofs/Greedy_Submodular_Approx` and `Proofs/Greedy_Approx_From_Spec` establish the classical deterministic greedy approximation guarantee.

`Proofs/Lazy_Greedy_Approx`, `Proofs/Lazy_Greedy_Stateful_StepSpec`, and `Proofs/Lazy_Greedy_Stateful_Approx` show that the lazy greedy variant fits the same abstract framework and therefore inherits the same guarantee.

## Repository status

The repository still contains additional material outside the current AFP-oriented session, including stochastic greedy developments, complexity/accounting files, executable examples, and experimental files.

These are not part of the current AFP session.

## Build

To build the current AFP-oriented session, run:

```bash
isabelle build -D . Submodular_Greedy_AFP
```

## Current goal

The current goal of the AFP-oriented session is to package a reusable Isabelle/HOL core for deterministic greedy approximation under a cardinality constraint, together with a lazy greedy refinement proved through the same abstract specification.