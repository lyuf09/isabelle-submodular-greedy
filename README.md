# Isabelle Formalization of Greedy Algorithms for Cardinality-Constrained Submodular Maximization

This repository contains an Isabelle/HOL formalization of deterministic greedy algorithms for monotone non-negative submodular maximization under a cardinality constraint on a finite ground set.

The main formal result is the classical Nemhauser–Wolsey approximation guarantee for deterministic greedy: the finite-step bound `1 - (1 - 1/k)^k`, and hence the standard corollary `1 - 1/e`. The development also includes a verified stateful lazy greedy variant. This line reuses the classical OPT_k and submodular infrastructure, together with packaged per-iteration lemmas for the lazy run, and proves the same approximation guarantee via a separate stateful gap-recurrence argument.

## Scope

The current AFP-oriented development focuses on:
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

Algorithms/Greedy_Submodular_Construct
Algorithms/Lazy_Greedy_Stateful
Algorithms/Lazy_Greedy_Oracle

Proofs/Greedy_Step_Spec
Proofs/Greedy_Submodular_Approx
Proofs/Greedy_Approx_From_Spec
Proofs/Lazy_Greedy_Stateful_StepSpec
Proofs/Lazy_Greedy_Stateful_Approx
```

## Structure of the development

The development is organized into three layers.

### 1. Core mathematical layer
`Core/Submodular_Base` provides the main locale and basic lemmas for finite-ground-set monotone submodular maximization under a cardinality constraint.

### 2. Algorithm layer
`Algorithms/Greedy_Submodular_Construct` formalizes the deterministic greedy construction.

`Algorithms/Lazy_Greedy_Stateful` formalizes a verified stateful lazy greedy variant.

`Algorithms/Lazy_Greedy_Oracle` provides the oracle-oriented lazy selection layer used to connect lazy greedy to the abstract greedy step specification.

### 3. Approximation layer
`Proofs/Greedy_Step_Spec` isolates the abstract one-step specification used in the approximation proof.

`Proofs/Greedy_Submodular_Approx` and `Proofs/Greedy_Approx_From_Spec` establish the classical deterministic greedy approximation guarantee.

`Proofs/Lazy_Greedy_Stateful_StepSpec` packages the per-iteration facts of the verified stateful lazy run. `Proofs/Lazy_Greedy_Stateful_Approx` then combines these facts with the classical core infrastructure to prove the same approximation guarantee for `lazy_set`.

## Build

To build the AFP session, run:

```bash
isabelle build -D . Submodular_Greedy_AFP
```