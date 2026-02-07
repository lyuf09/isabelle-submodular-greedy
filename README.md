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

- `Current_Status_and_Planned_Next_Steps.pdf`  
  A brief research note describing the current status of the project and
  outlining possible extensions and directions.

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
