# Isabelle Formalisation of Submodular Greedy Optimisation

This repository develops a modular Isabelle/HOL framework for reasoning about submodular maximisation algorithms, with a current focus on monotone submodular functions under a cardinality constraint.

The development is organised as a reusable library rather than a single isolated proof. Core notions such as submodularity, monotonicity, feasibility constraints, greedy-step specifications, and oracle-cost accounting are separated cleanly via locales and auxiliary theory layers, so that further greedy variants can be added in a principled way.

At present, the repository contains two main completed theorem lines at the theory level:

- the classical greedy algorithm, with a complete formal proof of the Nemhauser--Wolsey `(1 - 1/e)` approximation guarantee;
- a stateful LazyGreedy line, including step-spec packaging, the same `(1 - 1/e)` approximation guarantee, and basic formal oracle-cost accounting.

In addition, the repository includes small executable toy instances, exhaustive baselines for tiny ground sets, and sanity-check counterexamples.

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

- `Proofs/Greedy_Step_Spec.thy`  
  A packaged step-spec interface for the classical greedy step.

- `Proofs/Greedy_Approx_From_Spec.thy`  
  Reusable approximation reasoning from an abstract greedy step specification.

- `Proofs/Greedy_Submodular_Approx.thy`  
  The main approximation analysis for classical greedy, culminating in the Nemhauser--Wolsey `(1 - 1/e)` guarantee.

- `Proofs/Lazy_Greedy_Stateful_StepSpec.thy`  
  Per-step correctness facts for the stateful LazyGreedy construction, showing that each lazy step still realises a valid argmax-style greedy choice over the remaining elements.

- `Proofs/Lazy_Greedy_Stateful_Approx.thy`  
  Approximation analysis for the stateful LazyGreedy construction, proving the same `(1 - 1/e)` guarantee.

- `Proofs/Lazy_Greedy_Approx.thy`  
  A wrapper layer exposing the lazy approximation result in a convenient theorem-facing form.

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

- `Current_Status_and_Planned_Next_Steps.md`  
  A research-oriented status note summarising what has been completed and what comes next.

---

## Main Formal Results

### 1. Classical greedy line
The repository contains a complete formalisation of the standard Nemhauser--Wolsey approximation theorem for monotone submodular maximisation under a cardinality constraint:
- greedy is defined abstractly over a finite ground set;
- the proof establishes the usual averaging lemma, gap recurrence, and final `(1 - 1/e)` approximation bound.

### 2. Stateful LazyGreedy line
The repository also contains a stateful LazyGreedy development:
- the algorithm maintains explicit state and upper bounds;
- per-step correctness is packaged as a greedy-style step specification;
- the same Nemhauser--Wolsey `(1 - 1/e)` approximation guarantee is recovered for the lazy construction;
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

Current Status

This is an ongoing research-oriented development, but the theory-level status is now stronger than a minimal “classical greedy only” formalisation.

At the moment, the repository should be viewed as a reusable Isabelle/HOL framework for submodular greedy optimisation with:

a completed classical greedy theorem line;

a completed stateful LazyGreedy theorem line at the theory level;

reusable instance machinery for coverage objectives;

executable toy experiments and exhaustive baselines;

an initial formal complexity layer based on oracle-call accounting.

Planned Next Steps

Natural next directions include:

formalisation of additional modern greedy variants, especially StochasticGreedy and LazierThanLazyGreedy;

code extraction and empirical validation against executable baselines;

stronger complexity refinements for lazy variants;

connecting the present submodular library to Isabelle’s existing matroid-related infrastructure;

additional concrete submodular instances and benchmark-style case studies.

Positioning

The broader goal of the project is not just to formalise one approximation theorem, but to build a modular Isabelle/HOL library for modern submodular optimisation algorithms and their analyses.

The current repository already supports this direction in a meaningful way: the classical greedy line is complete, and the LazyGreedy line has now also been formalised at the theory level.

Supervised and developed as part of an ongoing research project.
