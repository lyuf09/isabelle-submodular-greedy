# Isabelle Formalization of Greedy Algorithms for Cardinality-Constrained Submodular Maximization

This repository contains an Isabelle/HOL formalization of monotone non-negative submodular maximization under a cardinality constraint on a finite ground set.

## Main result

The main formal result is the classical Nemhauser–Wolsey approximation guarantee for deterministic greedy: after `k` steps, the greedy solution satisfies the finite-step bound `1 - (1 - 1/k)^k`, and hence also the standard corollary `1 - 1/e`.

The development also includes a verified lazy greedy refinement. The lazy algorithm is formalized within the same deterministic framework and shown to satisfy the same approximation guarantee.

## Scope

This AFP-oriented branch focuses on:
- finite ground sets,
- monotone non-negative submodular set functions,
- cardinality constraints,
- deterministic greedy,
- lazy greedy as a verified deterministic refinement.

It does not include stochastic greedy, executable experiments, or instance-specific auxiliary material.

## AFP session

The AFP session is:

```text
Submodular_Greedy_AFP
```

It contains the following theories:

```text
Core/Submodular_Base

Algorithms/Greedy_Submodular_Construct
Algorithms/Lazy_Greedy_Stateful
Algorithms/Lazy_Greedy_Oracle

Proofs/Greedy_Step_Spec
Proofs/Greedy_Submodular_Approx
Proofs/Greedy_Approx_From_Spec
Proofs/Lazy_Greedy_Stateful_StepSpec
Proofs/Lazy_Greedy_Stateful_Approx
```

## Structure

The AFP-oriented development is organized into three layers.

### Core layer

`Core/Submodular_Base` provides the main locale and foundational lemmas for finite-ground-set monotone submodular maximization under a cardinality constraint.

### Algorithm layer

`Algorithms/Greedy_Submodular_Construct` formalizes the deterministic greedy construction.

`Algorithms/Lazy_Greedy_Stateful` formalizes the verified stateful lazy greedy algorithm.

`Algorithms/Lazy_Greedy_Oracle` provides the lazy-selection backend based on cached upper bounds that is reused by the verified lazy greedy development.

### Proof layer

`Proofs/Greedy_Step_Spec` isolates the abstract one-step greedy specification used by the approximation argument.

`Proofs/Greedy_Submodular_Approx` proves the classical finite-step approximation bound for deterministic greedy.

`Proofs/Greedy_Approx_From_Spec` packages the generic transfer from the step specification to the approximation guarantee.

`Proofs/Lazy_Greedy_Stateful_StepSpec` packages the per-iteration facts for the verified stateful lazy run.

`Proofs/Lazy_Greedy_Stateful_Approx` proves the corresponding approximation guarantee for `lazy_set`.


## Build

To build the AFP session, run:

```bash
isabelle build -D . Submodular_Greedy_AFP
```