# Isabelle Formalisation of Submodular Greedy Optimisation

This repository develops a **modular Isabelle/HOL framework for reasoning about
submodular maximisation algorithms**, with an initial focus on the classical
greedy algorithm for monotone submodular functions under a cardinality
constraint.

The development is structured as a reusable library: core notions such as
submodular set functions, feasibility constraints, and algorithmic oracles are
isolated via locales, allowing the framework to be extended to different greedy
variants, constraints, and instantiations.

As a first milestone, the repository includes a complete formal proof of the
Nemhauser–Wolsey **(1 − 1/e)** approximation guarantee for greedy maximisation.

## Contents

- `Submodular_Base.thy`  
  Core locales for finite submodular set functions, monotonicity, marginal
  gains, and feasibility under a cardinality constraint. This file is intended
  to serve as the foundational interface for further algorithmic developments.

- `Greedy_Submodular_Construct.thy`  
  Formal definition of the greedy algorithm using standard library notions
  (e.g. `is_arg_max`), together with structural invariants of the greedy
  sequence.

- `Greedy_Submodular_Approx.thy`  
  Formalisation of the submodular calculus underlying the analysis, including
  averaging arguments, gap recurrence, and the proof of the
  (1 − 1/e) approximation bound.

- `Experiments_Exhaustive.thy`  
  Small executable experiments (list-level refinement layer) and helper definitions for exhaustive baselines.

- `Experiments_Exhaustive_Correctness.thy`  
  Correctness/optimality facts for the exhaustive baseline `enum_opt_set`, including feasibility and optimality over enumerated candidates.

- `Coverage_Interpretation_Toy.thy`  
  Interpretation of the abstract greedy approximation theorem for a toy coverage function, exposing the `(1 - 1/e)` guarantee for this instance.

- `Coverage_Exhaustive_Bridge.thy`  
  End-to-end bridge for the toy coverage instance: proves `enum_opt_set = OPT_k` and derives a clean greedy-vs-true-optimum statement (`CovToy_greedy_vs_enum`).

- `Current_Status_and_Planned_Next_Steps.md`  
  A brief research note describing the current status of the project and
  outlining possible extensions and directions.

## Toy coverage: end-to-end guarantee (greedy vs true optimum)

To build everything:

```bash
isabelle build -D .
```

Key files:
- `Coverage_Interpretation_Toy.thy`: interprets the abstract theorem layer for the toy coverage function and exposes the `(1 - 1/e)` guarantee.
- `Experiments_Exhaustive_Correctness.thy`: proves correctness/optimality properties of the exhaustive baseline `enum_opt_set`.
- `Coverage_Exhaustive_Bridge.thy`: bridges `enum_opt_set` to `CovToy.OPT_k` and derives a clean end-to-end statement.

Final theorem (toy instance):
- `CovToy_greedy_vs_enum`:
  `f_cov_real (CovToy.greedy_set k) ≥ (1 - 1 / exp 1) * f_cov_real (enum_opt_set f_cov_real Vlist k)`

## Status
This is an ongoing, research-oriented development. The current codebase already
supports a clean separation between submodular assumptions, feasibility
constraints, and algorithmic reasoning, and is intended to function as a
reusable framework rather than a single-purpose formalisation.

## Future Directions

Planned extensions of the framework include:

- Further modularisation of submodular assumptions and constraints via locales
- Instantiations of the framework (e.g. coverage functions)
- Formalisation of modern greedy variants (LazyGreedy, StochasticGreedy, etc.)
- Reasoning about computational complexity and algorithmic behaviour
- Code extraction and small executable experiments

---

Supervised and developed as part of an ongoing research project.
