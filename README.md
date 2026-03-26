# Isabelle Formalization of Greedy Algorithms for Cardinality-Constrained Submodular Maximization

This repository contains an Isabelle/HOL formalization of deterministic greedy algorithms for monotone non-negative submodular maximization under a cardinality constraint on a finite ground set.

The main formal result is the classical approximation guarantee for deterministic greedy: the finite-step bound `1 - (1 - 1/k)^k`, and therefore the standard corollary `1 - 1/e`. The development also includes a stateful lazy greedy variant and shows that it satisfies the same abstract greedy step specification, so it inherits the same approximation guarantee.

## Scope

The present development focuses on:
- finite ground sets,
- monotone non-negative submodular set functions,
- cardinality constraints,
- deterministic greedy,
- lazy greedy as a deterministic refinement of the greedy baseline.

It does not include stochastic greedy, executable experiments, or instance-specific auxiliary material.

## AFP session

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

`Core/Oracle_Cost` provides the oracle-cost layer used in the current development.

### 2. Algorithm layer
`Algorithms/Greedy_Submodular_Construct` formalizes the deterministic greedy construction.

`Algorithms/Lazy_Greedy_Stateful` formalizes a stateful lazy greedy variant.

`Algorithms/Lazy_Greedy_Oracle` provides the oracle-oriented lazy greedy view used to connect lazy selection to the abstract greedy specification.

### 3. Approximation layer
`Proofs/Greedy_Step_Spec` isolates the abstract one-step specification used in the approximation proof.

`Proofs/Greedy_Submodular_Approx` and `Proofs/Greedy_Approx_From_Spec` establish the classical deterministic greedy approximation guarantee.

`Proofs/Lazy_Greedy_Approx`, `Proofs/Lazy_Greedy_Stateful_StepSpec`, and `Proofs/Lazy_Greedy_Stateful_Approx` show that the lazy greedy variant fits the same abstract framework and therefore inherits the same guarantee.

## Build

To build the AFP session, run:

```bash
isabelle build -D . Submodular_Greedy_AFP
```