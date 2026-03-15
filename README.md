# Isabelle Formalization of Greedy Algorithms for Cardinality-Constrained Submodular Maximization

This repository develops a modular Isabelle/HOL formalization of approximation guarantees for greedy-type algorithms under a cardinality constraint, with a current focus on:

- the classical deterministic greedy algorithm,
- lazy greedy variants,
- stochastic greedy sampling layers,
- oracle-cost models and comparison experiments,
- small executable instances and exhaustive sanity checks.

The long-term goal is to build a reusable formal framework for proving approximation guarantees for modern submodular maximization algorithms in a way that is:

- mathematically transparent,
- modular across algorithmic variants,
- suitable for further extensions in complexity and executable experiments.

---

## Main formalization themes

We work in the setting of monotone submodular maximization under a cardinality constraint. The development currently covers:

- abstract submodular infrastructure,
- greedy construction and approximation proofs,
- lazy greedy via step-spec / oracle interfaces,
- stochastic greedy sampling and hit-probability lower-bound layers,
- oracle-cost accounting for deterministic and lazy/stochastic variants,
- concrete coverage-style instances and toy experiments.

---

## Repository structure

```text
Core/
  Submodular_Base
  Oracle_Cost

Algorithms/
  Greedy_Submodular_Construct
  Lazy_Greedy_Stateful
  Lazy_Greedy_Oracle
  Stochastic_Greedy

Proofs/
  Greedy_Step_Spec
  Greedy_Submodular_Approx
  Greedy_Approx_From_Spec
  Lazy_Greedy_Approx
  Lazy_Greedy_Stateful_Approx
  Lazy_Greedy_Stateful_StepSpec
  Stochastic_Greedy_Sampling
  Stochastic_Greedy_Weighted_Sampling
  Stochastic_Greedy_OneStep
  Stochastic_Greedy_Approx
  Stochastic_Greedy_Uniform_WR

Complexity/
  Lazy_Greedy_OracleCost
  Lazy_Greedy_TotalOracleCost
  Lazy_Greedy_Compare_NaiveScan
  Stochastic_Greedy_OracleCost

Instances/
  Coverage_Setup
  Coverage_Interpretation_Toy
  Coverage_Exhaustive_Bridge

Experiments/
  Cost_Model
  Experiments_Exhaustive
  Experiments_Coverage_Example
  Experiments_Coverage_Suboptimal
  Experiments_Nonsubmodular_Counterexample
  Experiments_Exhaustive_Correctness
  Lazy_vs_Greedy_Toy
  Stochastic_vs_Greedy_Toy

The main session is:

```bash
Submodular_Greedy_Experiments
```

---

## Current formal results

### 1. Classical greedy
The repository contains a formal approximation proof for the classical cardinality-constrained greedy algorithm, following the standard Nemhauser-Wolsey gap-recurrence argument.

This part provides the baseline construction and approximation infrastructure used by later algorithmic variants.

### 2. Lazy greedy
The lazy-greedy part is split into:
- an algorithmic/stateful layer,
- an oracle/step-spec abstraction layer,
- an approximation transfer theorem from the abstract step specification,
- oracle-cost and total-cost accounting theories.

This yields a modular route from a lazy argmax oracle to the standard greedy approximation guarantee, while also supporting explicit comparison against naive scanning in the cost model.

### 3. Stochastic greedy
The stochastic-greedy development currently includes:
- abstract sampling-space infrastructure,
- weighted sampling interfaces,
- one-step hit/miss analysis,
- approximation-layer theories,
- a concrete uniform with-replacement sampling model over the remaining set.

In particular, the theory

```bash
Proofs/Stochastic_Greedy_Uniform_WR
```
now develops the concrete uniform with-replacement list model over V - S, including:

- the concrete list space wr_space_on,
- the induced uniform space uniform_wr_space,
- the uniform probability uniform_wr_prob,
- exact hit/miss event decompositions,
- exact miss-event counting,
- exact hit/miss probability formulas,
- lower bounds connecting the concrete model to the abstract hit-probability layer.

The current concrete theory proves the intended analytic lower bounds, including the exponential-type and linearized hit lower bounds, while explicitly recording the edge case that:

- a genuine with-replacement model over V - S is incompatible with a global non-emptiness axiom when V - S = {} and s > 0.

Accordingly, the final locale interpretation is intentionally postponed until the weighted sampling locale is patched with the natural side condition:

```bash
V - S ≠ {} ∨ s = 0
```

This means the concrete stochastic theory is already formalized and builds successfully, but one abstraction-layer patch is still needed before the final interpretation bridge is sealed completely.

---

## Executable / sanity-check components

The repository also contains small concrete instances and experiments, including:

- toy coverage interpretations,
- exhaustive checks,
- coverage examples,
- suboptimality illustrations,
- a nonsubmodular counterexample,
- toy comparisons between lazy greedy and standard greedy,
- toy comparisons between stochastic greedy and standard greedy.

These are meant as lightweight validation / illustration layers rather than large-scale benchmarking.

---

## Build instructions

A typical ROOT session looks like:

```bash
session Submodular_Greedy_Experiments = HOL +
  sessions "HOL-Library" "HOL-Analysis"
  ...
```

Note that:
-HOL-Analysis is the session name used in ROOT,
-while "HOL-Analysis.Analysis" is a theory import used inside .thy files.


To build the session locally:

```bash
isabelle build -D .

```

To build the main session explicitly:

```bash
isabelle build -d . Submodular_Greedy_Experiments
```

---

## Design philosophy
This repository aims to keep the formalization:

### 1. modular
so that deterministic greedy, lazy greedy, and stochastic greedy can share infrastructure without collapsing into one monolithic proof file;

### 2. algorithm-aware
so that executable constructions, oracle models, and cost accounting are part of the formal story;

### 3. research-oriented
so that the project can support future extensions to more modern greedy variants and sharper complexity / approximation interfaces.


---

## Current Status

At the moment:

- the deterministic greedy baseline is formalized,

- the lazy-greedy approximation and cost layers are formalized,

- the stochastic-greedy framework is substantially developed,

- the concrete uniform with-replacement stochastic model now builds successfully,

- the remaining main abstraction task is to patch the weighted sampling locale so that the final stochastic interpretation can be completed in a mathematically clean way.

See also:

```bash
Current_Status_and_Planned_Next_Steps.md
```

for a more detailed progress summary and roadmap.

---

## Planned Next Steps

The most immediate next steps are:

1. patch the abstract weighted sampling locale with the feasibility side condition
V - S ≠ {} ∨ s = 0;

2. complete the final interpretation from the concrete uniform with-replacement model to the abstract stochastic hit layer;

3. package the end-to-end stochastic approximation statement as cleanly as the lazy-greedy part;

4. continue with sharper cost / comparison statements and larger executable examples.

---

## Notes

This is an active research-style formalization project. Some theories are already in a relatively stable form; others are deliberately written as modular bridge layers so that abstraction boundaries can still be improved without rewriting the whole development.
The repository therefore reflects both completed formal proofs and in-progress architectural refinement.

---

Supervised and developed as part of an ongoing research project.
