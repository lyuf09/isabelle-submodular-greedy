# Isabelle Formalization of Greedy Algorithms for Cardinality-Constrained Submodular Maximization

This repository develops a modular Isabelle/HOL formalization of approximation guarantees for greedy-type algorithms under a cardinality constraint, with a current focus on:

- the classical deterministic greedy algorithm,
- lazy greedy variants,
- stochastic greedy sampling and approximation layers,
- oracle-cost models and comparison experiments,
- small executable instances and exhaustive sanity checks.

The long-term goal is to build a reusable formal framework for proving approximation guarantees for modern submodular maximization algorithms in a way that is:

- mathematically transparent,
- modular across algorithmic variants,
- suitable for further extensions in complexity and executable experiments.

---

## Main formalization themes

We work in the setting of monotone submodular maximization under a cardinality constraint.

The development currently covers:

- abstract submodular infrastructure,
- greedy construction and approximation proofs,
- lazy greedy via step-spec / oracle interfaces,
- stochastic greedy sampling, expected one-step, gap-recurrence, and final approximation layers,
- oracle-cost accounting for deterministic, lazy, and stochastic variants,
- concrete coverage-style instances and toy experiments.

---

## Repository structure

'''text
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
  Stochastic_Greedy_Uniform_WR_Interpretation
  Stochastic_Greedy_Expected_OneStep
  Stochastic_Greedy_Gap_Bridge
  Stochastic_Greedy_Uniform_WR_DeliverableA
  Stochastic_Greedy_Uniform_WR_Final

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
'''

The main session is:

'''text
Submodular_Greedy_Experiments
'''

---

## Current formal results

### 1. Classical greedy

The repository contains a formal approximation proof for the classical cardinality-constrained greedy algorithm, following the standard Nemhauser-Wolsey gap-recurrence argument.

This part provides the baseline construction and approximation infrastructure used by later algorithmic variants.

### 2. Lazy greedy

The lazy-greedy development is split into:

- an algorithmic/stateful layer,
- an oracle/step-spec abstraction layer,
- an approximation transfer theorem from the abstract step specification,
- oracle-cost and total-cost accounting theories.

This yields a modular route from a lazy argmax oracle to the standard greedy approximation guarantee, while also supporting explicit comparison against naive scanning in the cost model.

### 3. Stochastic greedy

The stochastic-greedy development now includes:

- abstract sampling-space infrastructure,
- weighted sampling interfaces,
- one-step hit/miss analysis,
- a concrete uniform with-replacement sampling model over the remaining set,
- a completed interpretation layer from the concrete uniform model to the abstract weighted / hit-probability interfaces,
- an expected one-step gain layer,
- a recurrence-based approximation layer,
- a concrete first-hit symmetry bridge for the uniform with-replacement model,
- a final k-step approximation wrapper yielding an end-to-end stochastic approximation theorem line.

In particular, the theory `Proofs/Stochastic_Greedy_Uniform_WR` develops the concrete uniform with-replacement list model over `V - S`, including:

- the concrete list space `wr_space_on`,
- the induced uniform space `uniform_wr_space`,
- the uniform probability `uniform_wr_prob`,
- exact hit/miss event decompositions,
- exact miss-event counting,
- exact hit/miss probability formulas,
- exponential-type and linearized lower bounds on hit probability.

The theory `Proofs/Stochastic_Greedy_Uniform_WR_Interpretation` then connects this concrete model to the abstract weighted-sampling and weighted-hit locales.

The theory `Proofs/Stochastic_Greedy_Expected_OneStep` packages the expectation layer on top of the deterministic one-step bridge, including:

- expected-step-gain definitions,
- hit/miss decomposition of expected gain,
- lower bounds by weighted hit-event averages,
- reusable lower-bound templates of the form
  `expected_step_gain ≥ hit_prob_of × c`.

The theory `Proofs/Stochastic_Greedy_Approx` isolates the approximation algebra:

- multiplicative gap-contraction templates,
- closed-form recurrence solving via `stoch_gap_factor`,
- reusable approximation-from-recurrence statements.

The theory `Proofs/Stochastic_Greedy_Uniform_WR_DeliverableA` supplies the missing concrete one-step bridge for the uniform with-replacement model. Its main contributions include:

- the first residual-hit selector,
- deterministic residual-gap lower bounds,
- a symmetry / equal-probability argument for the first residual-optimal hit,
- the concrete expected one-step lower bound
  `expected_step_gain ≥ (alpha_stoch s / k) * gap`,
- the corresponding epsilon-parameterized one-step corollary.

Finally, `Proofs/Stochastic_Greedy_Uniform_WR_Final` packages this bridge into a final k-step theorem line. In the current architecture, this final layer is stated for any set-valued state sequence satisfying the appropriate value-update and feasibility conditions. This yields:

- a generic alpha-version value lower bound,
- an exponential-form epsilon corollary,
- an AAAI-style bound of the form
  `1 - 1 / exp 1 - eps`.

In other words, the repository now contains a completed concrete stochastic approximation theorem line for the uniform with-replacement model, within the present abstraction boundary of the development.

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

'''text
session Submodular_Greedy_Experiments = HOL +
  sessions "HOL-Library" "HOL-Analysis"
  ...
'''

Note that:

- `HOL-Analysis` is the session name used in `ROOT`,
- while `HOL-Analysis.Analysis` is a theory import used inside `.thy` files.

To build the session locally:

'''text
isabelle build -D .
'''

To build the main session explicitly:

'''text
isabelle build -d . Submodular_Greedy_Experiments
'''

---

## Design philosophy

This repository aims to keep the formalization:

### 1. Modular

Deterministic greedy, lazy greedy, and stochastic greedy share infrastructure without collapsing into one monolithic proof file.

### 2. Algorithm-aware

Executable constructions, oracle models, and cost accounting are treated as part of the formal story rather than as external commentary.

### 3. Research-oriented

The project is designed to support further extensions to more modern greedy variants and sharper complexity / approximation interfaces.

---

## Current status

At the moment:

- the deterministic greedy baseline is formalized,
- the lazy-greedy approximation and cost layers are formalized,
- the stochastic-greedy framework includes sampling, interpretation, expected one-step, recurrence, and concrete final approximation layers,
- the concrete uniform with-replacement stochastic model is connected to the abstract weighted / hit-probability interfaces,
- the concrete one-step bridge and the final k-step approximation wrapper for the uniform with-replacement stochastic model are formalized,
- the repository now contains a completed AAAI-style stochastic approximation theorem line for the current abstraction boundary.

What remains is no longer the basic stochastic theorem line itself, but rather further packaging and extensions, such as:

- sharpening cost/comparison statements,
- improving the connection to more explicit run semantics if desired,
- expanding executable validations,
- preparing the development for AFP-style presentation and submission.

See also:

`Current_Status_and_Planned_Next_Steps.md`

for a more detailed progress summary and roadmap.

---

## Planned next steps

The most immediate next steps are:

1. clean up and package the completed stochastic theorem line for presentation quality;
2. strengthen the oracle-cost and comparison story around the stochastic variant;
3. continue with larger executable examples and cleaner experiment packaging;
4. prepare the overall development for AFP-style packaging and submission;
5. explore further extensions beyond the current uniform with-replacement theorem line.

---

## Notes

This is an active research-style formalization project.

Some theories are already in a relatively stable form; others are deliberately written as modular bridge layers so that abstraction boundaries can still be improved without rewriting the whole development.

The repository therefore reflects both completed formal proofs and ongoing architectural refinement.

---

Supervised and developed as part of an ongoing research project.
