# Isabelle Formalization of Greedy Algorithms for Cardinality-Constrained Submodular Maximization

This repository develops a modular Isabelle/HOL formalization of approximation guarantees, executable layers, and oracle-cost accounting for greedy-style algorithms under a cardinality constraint, with a current focus on three main lines:

- the classical deterministic greedy algorithm,
- lazy greedy variants with stateful and oracle-oriented views,
- stochastic greedy with a concrete uniform with-replacement sampling model.

The long-term goal is to build a reusable Isabelle library for modern submodular maximization algorithms that is:

- mathematically transparent,
- modular across algorithmic variants,
- explicit about abstraction boundaries,
- reusable for both theorem proving and small executable sanity checks.

---

## Main current contributions

The current development includes the following main components.

### 1. Classical greedy baseline

The repository contains a foundational formalization of the standard Nemhauser-Wolsey style approximation line for monotone non-negative submodular maximization under a cardinality constraint. The proof architecture is separated into:

- construction / executable greedy layers,
- abstract step-spec interfaces,
- approximation theorems from those interfaces.

This baseline provides the reusable backbone for later variants.

### 2. Lazy greedy line

The lazy greedy part of the repository develops:

- a stateful executable lazy greedy layer,
- an oracle-oriented lazy greedy view,
- step-spec packaging for lazy selection rules,
- approximation theorems inherited from the abstract greedy framework,
- oracle-cost accounting,
- comparison against naive full-scan greedy.

This gives a structured formal treatment of lazy evaluation as an algorithmic refinement of the classical greedy baseline.

### 3. Stochastic greedy line

The stochastic greedy part now contains a complete theorem-level line for the standard monotone non-negative submodular cardinality-constrained setting, based on a concrete uniform with-replacement sampling model over the remaining set.

The repository now includes:

- a deterministic trace layer for stochastic greedy execution,
- exact gain-evaluation counters at the algorithm level,
- sampling lemmas and weighted-sampling abstractions,
- one-step expected-gain lower bounds,
- recurrence-based approximation packaging,
- a concrete uniform with-replacement bridge,
- a final k-step approximation wrapper,
- exact oracle-cost theorems for the stochastic trace layer,
- a thin paper-facing packaging that places approximation and oracle budget guarantees side by side under the same epsilon-driven sample-size discipline.

At the current abstraction boundary, the executable stochastic algorithm is still represented by a deterministic trace layer, while the approximation side is phrased via abstract state-sequence / recurrence packaging. The final stochastic wrapper is therefore honest about this separation: it packages the approximation guarantee and the trace-level oracle-cost guarantee together, but does not yet identify them as a single fully probabilistic run semantics.

---

## Current mathematical scope

The repository currently focuses on:

- finite ground sets,
- monotone non-negative submodular objectives,
- cardinality constraints,
- deterministic greedy,
- lazy greedy,
- stochastic greedy with uniform with-replacement sampling over the remaining set.

The present development does not yet aim to formalize:

- matroid or general independence constraints,
- heavy empirical evaluation,
- a fully unified probabilistic operational semantics linking the executable stochastic trace and the abstract approximation recurrence in one single semantic object.

---

## Session structure

The repository is organized into the following directories:

- `Core`
- `Algorithms`
- `Proofs`
- `Instances`
- `Experiments`
- `Complexity`

The main session currently contains the following theories:

```text
Core/Submodular_Base
Core/Oracle_Cost

Algorithms/Greedy_Submodular_Construct
Algorithms/Lazy_Greedy_Stateful
Algorithms/Lazy_Greedy_Oracle
Algorithms/Stochastic_Greedy

Proofs/Greedy_Step_Spec
Proofs/Greedy_Submodular_Approx
Proofs/Greedy_Approx_From_Spec
Proofs/Lazy_Greedy_Approx
Proofs/Lazy_Greedy_Stateful_Approx
Proofs/Lazy_Greedy_Stateful_StepSpec
Proofs/Stochastic_Greedy_Sampling
Proofs/Stochastic_Greedy_Weighted_Sampling
Proofs/Stochastic_Greedy_OneStep
Proofs/Stochastic_Greedy_Approx
Proofs/Stochastic_Greedy_Uniform_WR
Proofs/Stochastic_Greedy_Gap_Bridge
Proofs/Stochastic_Greedy_Uniform_WR_Interpretation
Proofs/Stochastic_Greedy_Expected_OneStep
Proofs/Stochastic_Greedy_Uniform_WR_DeliverableA
Proofs/Stochastic_Greedy_Uniform_WR_Final

Complexity/Lazy_Greedy_OracleCost
Complexity/Lazy_Greedy_TotalOracleCost
Complexity/Lazy_Greedy_Compare_NaiveScan
Complexity/Stochastic_Greedy_OracleCost

Instances/Coverage_Setup
Instances/Coverage_Interpretation_Toy
Instances/Coverage_Exhaustive_Bridge

Experiments/Cost_Model
Experiments/Experiments_Exhaustive
Experiments/Experiments_Coverage_Example
Experiments/Experiments_Coverage_Suboptimal
Experiments/Experiments_Nonsubmodular_Counterexample
Experiments/Experiments_Exhaustive_Correctness
Experiments/Lazy_vs_Greedy_Toy
Experiments/Stochastic_vs_Greedy_Toy
```

---

## Detailed theory guide

### Core

#### `Core/Submodular_Base`
Foundational locale and basic lemmas for finite-ground-set submodular maximization under a cardinality constraint. This is the main mathematical base used throughout the repository.

#### `Core/Oracle_Cost`
Basic oracle-cost conventions and cost-model parameters used by later complexity theories. This separates algorithmic counting from paper-facing oracle-cost accounting.

---

### Algorithms

#### `Algorithms/Greedy_Submodular_Construct`
Core deterministic greedy construction layer. This theory provides the baseline greedy iteration, the set-valued construction story, and the basic executable backbone used by the classical approximation line.

#### `Algorithms/Lazy_Greedy_Stateful`
Stateful lazy greedy execution layer. This theory formalizes lazy candidate management at the algorithm level and serves as the main executable stateful lazy layer.

#### `Algorithms/Lazy_Greedy_Oracle`
Oracle-oriented lazy greedy interface. This theory provides a lazy argmax oracle view suitable for reuse by the abstract step-spec approximation framework.

#### `Algorithms/Stochastic_Greedy`
Deterministic trace layer for stochastic greedy. The algorithm is parameterized by an explicit trace of sampled candidate lists rather than by probability directly. This theory now also contains the cost-facing counting interface:

- sampled candidate pools,
- deterministic one-step and multi-step trace execution,
- feasibility invariants,
- exact per-step gain-evaluation counters,
- exact trace-level total gain-evaluation counters,
- sample-size discipline predicates (`trace_sample_bound`, `trace_sample_size`),
- exact theorem-level bounds of the form “total gain evaluations are at most `k * s`”.

This is the main executable / cost-facing interface for the stochastic line.

---

### Proofs: classical greedy

#### `Proofs/Greedy_Step_Spec`
Abstract step-spec interface for greedy-style progress statements. This theory packages the one-step assumptions needed to derive approximation guarantees.

#### `Proofs/Greedy_Submodular_Approx`
Classical greedy approximation infrastructure for monotone submodular maximization under a cardinality constraint. This is the main deterministic approximation backbone.

#### `Proofs/Greedy_Approx_From_Spec`
Reusable bridge from step-spec assumptions to approximation guarantees. This makes the classical approximation line modular and reusable for later algorithmic variants.

---

### Proofs: lazy greedy

#### `Proofs/Lazy_Greedy_Approx`
Approximation theorem line for lazy greedy using the oracle-oriented lazy selection rule inside the abstract greedy approximation framework.

#### `Proofs/Lazy_Greedy_Stateful_Approx`
Approximation theorem line for the stateful lazy greedy layer.

#### `Proofs/Lazy_Greedy_Stateful_StepSpec`
Step-spec packaging for the stateful lazy greedy construction. This theory connects the stateful algorithmic layer to the abstract approximation infrastructure.

---

### Proofs: stochastic greedy

#### `Proofs/Stochastic_Greedy_Sampling`
Sampling-lemma layer for stochastic greedy. This theory develops the core probability-side inequalities needed for hit / miss style arguments and alpha-style sampling parameters.

#### `Proofs/Stochastic_Greedy_Weighted_Sampling`
Abstract weighted-sampling interface for stochastic greedy one-step analysis. This theory isolates the sampling assumptions needed by later expected-gain arguments.

#### `Proofs/Stochastic_Greedy_OneStep`
Core one-step theorem layer for stochastic greedy. This theory develops the deterministic and probabilistic ingredients needed for one-step progress statements.

#### `Proofs/Stochastic_Greedy_Approx`
Abstract recurrence and approximation packaging for stochastic greedy. This theory provides the main recurrence-level infrastructure for final approximation theorems.

#### `Proofs/Stochastic_Greedy_Uniform_WR`
Concrete uniform with-replacement sampling development over the remaining set. This is the main concrete stochastic model currently used in the repository.

#### `Proofs/Stochastic_Greedy_Gap_Bridge`
Bridge theory connecting one-step stochastic progress statements to the gap-recurrence viewpoint used in the final approximation line.

#### `Proofs/Stochastic_Greedy_Uniform_WR_Interpretation`
Interpretation layer instantiating the abstract stochastic framework with the concrete uniform with-replacement model.

#### `Proofs/Stochastic_Greedy_Expected_OneStep`
Expected one-step gain packaging. This theory sits between the lower-level one-step / sampling material and the final recurrence-level approximation theorems.

#### `Proofs/Stochastic_Greedy_Uniform_WR_DeliverableA`
Concrete central bridge for the mathematically core part of stochastic Deliverable A. This theory packages the uniform with-replacement one-step theorem into the concrete alpha-over-k progress form that drives the final approximation line.

#### `Proofs/Stochastic_Greedy_Uniform_WR_Final`
Final approximation wrapper for the uniform with-replacement stochastic greedy line. This theory now contains:

- the generic alpha-version final theorem,
- the closed-form exponential bound at `i = k`,
- the paper-facing `1 - 1/e - eps` style theorem,
- thin paper-facing packaging that places the approximation guarantee together with the trace-level oracle-budget guarantee under the same epsilon-driven sample-size discipline.

This is currently the main final stochastic wrapper for theorem-level presentation.

---

### Complexity

#### `Complexity/Lazy_Greedy_OracleCost`
Per-step oracle-cost accounting for lazy greedy.

#### `Complexity/Lazy_Greedy_TotalOracleCost`
Total oracle-cost theorems for lazy greedy over a full run.

#### `Complexity/Lazy_Greedy_Compare_NaiveScan`
Comparison theorems showing how lazy greedy oracle usage relates to naive full-scan greedy.

#### `Complexity/Stochastic_Greedy_OracleCost`
Formal oracle-cost theorem file for stochastic greedy. This theory is no longer just a skeleton. It now contains:

- paper-facing `k * s` total budget packaging,
- oracle-budget versions derived from `gain_call_cost`,
- exact per-step oracle-call upper bounds,
- exact trace-level oracle-call upper bounds,
- exact final `k`-step oracle-call bounds,
- epsilon-instantiated oracle-budget corollaries using `sample_size_eps_ceil`.

Together with `Algorithms/Stochastic_Greedy`, this closes the theorem-level stochastic cost story at the current development stage.

---

### Instances

#### `Instances/Coverage_Setup`
Coverage-style instance setup used for toy experiments and executable sanity checks.

#### `Instances/Coverage_Interpretation_Toy`
Toy interpretation of the coverage setup for executable examples and small-scale experiments.

#### `Instances/Coverage_Exhaustive_Bridge`
Bridge between coverage instances and exhaustive validation / comparison layers.

---

### Experiments

#### `Experiments/Cost_Model`
Shared experiment-facing cost conventions and simple paper-facing cost parameters.

#### `Experiments/Experiments_Exhaustive`
Exhaustive experiment / sanity-check layer over small finite instances.

#### `Experiments/Experiments_Coverage_Example`
Concrete coverage-based example runs.

#### `Experiments/Experiments_Coverage_Suboptimal`
Coverage examples illustrating suboptimal choices or comparison phenomena.

#### `Experiments/Experiments_Nonsubmodular_Counterexample`
Counterexample-oriented experiment layer showing why the target assumptions matter.

#### `Experiments/Experiments_Exhaustive_Correctness`
Correctness-oriented exhaustive validation utilities.

#### `Experiments/Lazy_vs_Greedy_Toy`
Toy comparison layer for lazy greedy versus classical greedy.

#### `Experiments/Stochastic_vs_Greedy_Toy`
Current stochastic-versus-greedy toy experiment shell / lightweight placeholder for future small-scale stochastic executable validation. At present, the repository’s stochastic theorem-level contribution is stronger than its stochastic experiment layer; the experiment side remains intentionally lightweight.

---

## Current status by line

### Classical greedy
The classical deterministic greedy theorem line is stable and serves as the foundational baseline.

### Lazy greedy
The lazy greedy line includes algorithmic execution, approximation theorems, and oracle-cost comparison theorems, and is already relatively mature.

### Stochastic greedy
The stochastic greedy line now includes:

- deterministic trace execution,
- concrete uniform with-replacement sampling,
- one-step expected-gain bridge,
- final approximation packaging up to the paper-facing `1 - 1/e - eps` form,
- exact oracle-cost theorem packaging on the deterministic trace layer,
- thin paper-facing paired packaging of approximation and oracle-budget statements.

The main remaining limitation is not the lack of theorem-level stochastic approximation or cost results, but the current abstraction boundary: the final approximation theorem and the executable trace-level oracle-cost theorem are packaged side by side rather than unified as one single fully probabilistic run semantics.

---

## What is already formalized for stochastic greedy

At the current stage, the repository already formalizes the following core stochastic story.

### Mathematical approximation side
For the concrete uniform with-replacement model, the repository proves a final expected-value approximation theorem of AAAI-style form, under the standard monotone non-negative submodular + cardinality assumptions and the epsilon-driven sample-size discipline.

### Cost side
For the deterministic stochastic trace layer, the repository proves exact theorem-level bounds showing that:

- per-step gain evaluations are controlled by the sampled pool size,
- total gain evaluations are bounded by `k * s`,
- the corresponding oracle-call budget is bounded by `gain_call_cost * k * s`,
- epsilon-instantiated bounds are available using `sample_size_eps_ceil`.

### Honest abstraction statement
The present repository does not yet claim that the executable trace object and the abstract recurrence object are already a single unified probabilistic semantic entity. Instead, it gives a clear theorem-level side-by-side package:

- final approximation theorem for the abstract state-sequence view,
- final oracle-budget theorem for the executable trace view,
- shared epsilon-driven parameterization tying the two together in a paper-facing way.

---

## Build

The repository is intended to be built as an Isabelle session.

A standard build command is:

```text
isabelle build -D .
```

If you prefer to build the main session explicitly, use the session name declared in the project `ROOT` file.

---

## Suggested reading order

A reasonable reading order for the main formal story is:

1. `Core/Submodular_Base`
2. `Algorithms/Greedy_Submodular_Construct`
3. `Proofs/Greedy_Step_Spec`
4. `Proofs/Greedy_Submodular_Approx`
5. `Algorithms/Lazy_Greedy_Stateful`
6. `Proofs/Lazy_Greedy_Stateful_StepSpec`
7. `Proofs/Lazy_Greedy_Stateful_Approx`
8. `Algorithms/Stochastic_Greedy`
9. `Proofs/Stochastic_Greedy_Sampling`
10. `Proofs/Stochastic_Greedy_Weighted_Sampling`
11. `Proofs/Stochastic_Greedy_OneStep`
12. `Proofs/Stochastic_Greedy_Expected_OneStep`
13. `Proofs/Stochastic_Greedy_Approx`
14. `Proofs/Stochastic_Greedy_Uniform_WR`
15. `Proofs/Stochastic_Greedy_Uniform_WR_Interpretation`
16. `Proofs/Stochastic_Greedy_Uniform_WR_DeliverableA`
17. `Complexity/Stochastic_Greedy_OracleCost`
18. `Proofs/Stochastic_Greedy_Uniform_WR_Final`

This order follows the project’s actual layering from foundational locale material to algorithmic layers, then to approximation theorems, cost accounting, and final packaging.

---

## Intended near-term use

The current repository is already suitable as the basis for:

- AFP-style cleanup and submission preparation,
- a conference-oriented writeup built on the same formal core,
- further strengthening of lightweight experiments and presentation layers.

In particular, the current stochastic line is no longer merely a proof sketch or skeleton: it now contains a concrete theorem-level approximation story, a formal theorem-level oracle-cost story, and a thin final packaging suitable for paper-facing exposition.

---

## Notes on experiments

The repository does contain executable and toy-experiment material, especially around coverage instances and greedy / lazy comparisons. However, the formal core of the project is stronger and more mature than the current experiment layer. This is deliberate: the main emphasis of the development is on reusable theorem infrastructure rather than large-scale empirical benchmarking.

Future experiment work may strengthen:

- stochastic-vs-greedy toy comparisons,
- parameter-sensitivity illustrations,
- small executable oracle-count demonstrations aligned with the exact theorem-level budgets.

---

## Summary

This repository currently provides a modular Isabelle/HOL formalization of:

- classical greedy approximation guarantees,
- lazy greedy algorithmic and oracle-cost refinements,
- stochastic greedy approximation and oracle-cost guarantees under a concrete uniform with-replacement model,
- executable toy-instance support and small sanity-check infrastructure.

The development is designed not only to formalize individual theorems, but also to build a reusable proof architecture for modern submodular greedy algorithms.
