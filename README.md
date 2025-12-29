# Isabelle Formalisation of Submodular Greedy Optimisation

This repository contains an Isabelle formalisation of the classical greedy
(1 − 1/e) approximation bound for monotone submodular maximisation under a
cardinality constraint.

## Contents

- `Greedy_Submodular_Construct.thy`  
  Formal definition of the greedy algorithm, marginal gains, and structural
  invariants of the greedy sequence.

- `Greedy_Submodular_Approx.thy`  
  Formalisation of the submodular calculus, averaging lemma, gap recurrence,
  and the Nemhauser–Wolsey (1 − 1/e) approximation guarantee.

- `Current_Status_and_Planned_Next_Steps (1).pdf`  
  Current status and planned next steps, including possible instantiations,
  extensions, and executable experiments.

## Status

This is a research-oriented development, intended as a basis for a reusable framework for
reasoning about submodular optimisation algorithms in Isabelle/HOL.

## Future Directions

- Modularisation of submodular assumptions via locales  
- Instantiations (e.g. coverage functions)
- Formalisation of modern greedy variants (LazyGreedy, StochasticGreedy)
- Code extraction and small executable experiments

---

Supervised and developed as part of an ongoing research project.
