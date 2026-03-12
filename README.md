# Isabelle Formalisation of Submodular Greedy Optimisation

This repository develops a modular Isabelle/HOL framework for reasoning about submodular maximisation algorithms, currently focused on monotone submodular functions under a cardinality constraint.

The development is organised as a reusable library rather than a single isolated proof. Core notions such as submodularity, monotonicity, feasibility constraints, greedy-step specifications, and oracle-cost accounting are separated via locales and auxiliary theory layers, so that further greedy variants can be added in a principled and reusable way.

At present, the repository contains:

- a completed foundational theorem line for the classical greedy algorithm, including a full formal proof of the Nemhauser--Wolsey `(1 - 1/e)` approximation guarantee;
- a completed stateful / implementation-level extension beyond classical greedy, namely a verified LazyGreedy development with explicit state, correctness bridges, inherited approximation guarantees, and an initial oracle-cost layer;
- small executable toy instances, exhaustive baselines for tiny ground sets, and sanity-check counterexamples.

---

## Repository Layout

- `Core/Submodular_Base.thy`  
  Core locales for finite monotone submodular set functions, marginal gains, feasibility, and cardinality constraints.

- `Core/Oracle_Cost.thy`  
  A basic oracle-cost model used to reason about gain evaluations and total oracle calls.

- `Algorithms/Greedy_Submodular_Construct.thy`  
  Formal construction of the classical greedy sequence and its structural invariants.

- `Algorithms/Lazy_Greedy_Stateful.thy`  
  A stateful LazyGreedy formulation with cached upper bounds and explicit algorithmic state.

- `Algorithms/Lazy_Greedy_Oracle.thy`  
  An auxiliary oracle-style LazyGreedy layer that packages lazy upper-bound tightening into a greedy-style oracle view, mainly for compatibility and theorem-facing reuse.

- `Proofs/Greedy_Step_Spec.thy`  
  A packaged step-spec interface for the classical greedy step.

- `Proofs/Greedy_Approx_From_Spec.thy`  
  Reusable approximation reasoning from an abstract greedy step specification.

- `Proofs/Greedy_Submodular_Approx.thy`  
  The main approximation analysis for classical greedy, culminating in the Nemhauser--Wolsey `(1 - 1/e)` guarantee.

- `Proofs/Lazy_Greedy_Stateful_StepSpec.thy`  
  Per-step correctness facts for the stateful LazyGreedy construction, showing that each lazy step still realises a valid argmax-style greedy choice over the remaining elements.

- `Proofs/Lazy_Greedy_Stateful_Approx.thy`  
  Approximation analysis for the stateful LazyGreedy construction, proving the same `(1 - 1/e)` guarantee via a correctness bridge back to the classical greedy-style step specification.

- `Proofs/Lazy_Greedy_Approx.thy`  
  A theorem-facing compatibility wrapper exposing the LazyGreedy approximation result in a convenient form.

- `Complexity/Lazy_Greedy_OracleCost.thy`  
  Per-round oracle-cost accounting for LazyGreedy.

- `Complexity/Lazy_Greedy_TotalOracleCost.thy`  
  Global oracle-cost bounds for the full LazyGreedy run.

- `Complexity/Lazy_Greedy_Compare_NaiveScan.thy`  
  Comparison lemmas relating LazyGreedy cost bounds to a naive scan baseline.

- `Instances/Coverage_Setup.thy`  
  A reusable coverage-function setup used as a concrete monotone submodular instance.

- `Instances/Coverage_Interpretation_Toy.thy`  
  Interpretation of the abstract theorem layer for a toy coverage objective.

- `Instances/Coverage_Exhaustive_Bridge.thy`  
  End-to-end bridge from the executable exhaustive optimum to the abstract `OPT_k` notion on the toy instance.

- `Experiments/Experiments_Exhaustive.thy`  
  Executable exhaustive baseline for very small finite instances.

- `Experiments/Experiments_Exhaustive_Correctness.thy`  
  Feasibility and optimality facts for the executable exhaustive baseline.

- `Experiments/Experiments_Coverage_Example.thy`  
  A tiny coverage example with recorded outputs and query counters.

- `Experiments/Experiments_Coverage_Suboptimal.thy`  
  A small monotone submodular example where greedy is strictly suboptimal.

- `Experiments/Experiments_Nonsubmodular_Counterexample.thy`  
  A monotone but non-submodular counterexample illustrating the necessity of submodularity.

- `Experiments/Lazy_vs_Greedy_Toy.thy`  
  A toy executable comparison between naive greedy scanning and a lazy refinement.

- `Experiments/Cost_Model.thy`  
  A small experimental cost-model helper defining simple oracle-call conventions and naive greedy scan cost baselines.

- `Current_Status_and_Planned_Next_Steps.md`  
  A research-oriented status note summarising what has been completed and what comes next.

---

## Main Formal Results

### 1. Classical greedy foundation
The repository contains a complete formalisation of the standard Nemhauser--Wolsey approximation theorem for monotone submodular maximisation under a cardinality constraint:
- greedy is defined abstractly over a finite ground set;
- the proof establishes the standard averaging lemma, gap recurrence, and final `(1 - 1/e)` approximation bound.

### 2. Verified LazyGreedy as a stateful extension
The repository also contains a verified LazyGreedy development, positioned as the first completed stateful / implementation-level extension beyond classical greedy:
- the algorithm maintains explicit state and cached upper bounds;
- key invariants are tracked directly at the level of the algorithmic state;
- per-step correctness is packaged through a bridge back to a greedy-style argmax specification;
- the same Nemhauser--Wolsey `(1 - 1/e)` approximation guarantee is inherited for the lazy construction;
- a basic formal oracle-cost accounting is provided, together with comparison lemmas against a naive scan baseline.

### 3. Tiny executable baselines and sanity checks
For small finite examples, the repository includes:
- executable exhaustive optimisation baselines;
- toy coverage instances;
- explicit examples where greedy is suboptimal but still consistent with the approximation theorem;
- explicit non-submodular counterexamples where the classical guarantee can fail.

---

## Build

To build everything from the repository root:

```bash
isabelle build -D .
```


For interactive work in Isabelle/jEdit, open the repository and select the session defined in ROOT (currently Submodular_Greedy_Experiments).

---

## Current Status

This is an ongoing research-oriented development, but it is already substantially stronger than a minimal “classical greedy only” formalisation.

At present, the repository should be viewed as a reusable Isabelle/HOL framework for submodular greedy optimisation with:

- a completed foundational theorem line for classical greedy;

- a verified LazyGreedy development as a substantial implementation-level / stateful extension beyond that foundation;

- reusable instance machinery for coverage objectives;

- executable toy experiments and exhaustive baselines;

- an initial formal complexity layer based on oracle-call accounting.

---

## Planned Next Steps

The most immediate next direction is the formalisation of StochasticGreedy as the next main theorem line beyond the current classical-greedy foundation and LazyGreedy stateful extension.

The primary near-term goals are:

- formalisation of StochasticGreedy and its approximation / query-complexity guarantees;

- code extraction and small-scale empirical validation against executable baselines;

- further polishing and packaging of the current development for a research-oriented formal-methods submission.

Longer-term extensions may include:

- further refinement of the complexity story for lazy and stochastic variants;

- connections to Isabelle’s existing matroid-related infrastructure;

- additional concrete submodular instances and benchmark-style case studies.

---

## Positioning

The broader goal of the project is not just to formalise one approximation theorem, but to build a modular Isabelle/HOL library for modern submodular optimisation algorithms and their analyses.

Within that programme, the classical greedy development is the foundational theorem line. The LazyGreedy development should be viewed as a completed stateful / implementation-level extension beyond classical greedy, rather than as a wholly separate major approximation-theory line. The next main target for a more independent theorem contribution is StochasticGreedy.
---

Supervised and developed as part of an ongoing research project.
