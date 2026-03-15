# Current Status and Planned Next Steps

## 1. Current Status of the Formalisation

The repository has now clearly moved well beyond a “classical greedy only” stage. It already contains:

- a completed foundational classical greedy development,
- a completed LazyGreedy extension at the stateful / implementation level,
- a substantial StochasticGreedy development,
- small executable baselines and sanity-check experiments,
- reusable concrete interpreted instances,
- and initial oracle-cost frameworks for both lazy and stochastic variants.

The project is therefore best viewed not as a single isolated approximation proof, but as a growing Isabelle/HOL framework for cardinality-constrained submodular maximisation and modern greedy-style variants.

---

## 1.1 Core architecture

The development is organised modularly.

- `Core/Submodular_Base.thy` provides the main abstract interface for finite monotone submodular set functions, marginal gains, feasibility, and cardinality constraints.
- `Core/Oracle_Cost.thy` introduces a lightweight oracle-cost layer reused by later complexity arguments.

More broadly, the current design separates:

- abstract optimisation assumptions,
- algorithmic constructions,
- approximation proofs,
- concrete instance interpretations,
- executable experiments,
- and complexity / accounting arguments.

This separation is important for turning the project into a reusable Isabelle/HOL library rather than a single isolated proof development.

---

## 1.2 Classical greedy foundation (completed)

The classical greedy development is complete.

Main ingredients:

- `Algorithms/Greedy_Submodular_Construct.thy`
- `Proofs/Greedy_Step_Spec.thy`
- `Proofs/Greedy_Approx_From_Spec.thy`
- `Proofs/Greedy_Submodular_Approx.thy`

This line establishes:

- the abstract greedy sequence `greedy_set`,
- structural invariants of the greedy construction,
- a reusable greedy-step specification,
- the standard averaging lemma and gap recurrence,
- and the Nemhauser--Wolsey `(1 - 1/e)` approximation guarantee for monotone submodular maximisation under a cardinality constraint.

So the foundational classical theorem line is fully formalised.

---

## 1.3 LazyGreedy as a completed stateful extension beyond classical greedy

A verified LazyGreedy development is now also in place.

Main ingredients:

- `Algorithms/Lazy_Greedy_Stateful.thy`
- `Algorithms/Lazy_Greedy_Oracle.thy`
- `Proofs/Lazy_Greedy_Stateful_StepSpec.thy`
- `Proofs/Lazy_Greedy_Stateful_Approx.thy`
- `Proofs/Lazy_Greedy_Approx.thy`
- `Complexity/Lazy_Greedy_OracleCost.thy`
- `Complexity/Lazy_Greedy_TotalOracleCost.thy`
- `Complexity/Lazy_Greedy_Compare_NaiveScan.thy`

This development is best viewed not as a wholly separate major approximation-theory line, but as the first completed stateful / implementation-level extension beyond the classical greedy foundation.

Its current contribution has six main aspects.

### (a) Explicit algorithmic state

A stateful lazy construction is defined explicitly, with internal state carrying the current selected set together with cached upper-bound information.

### (b) State-based invariants

The development tracks key structural facts directly at the level of the algorithmic state, making the lazy procedure a genuine formal object rather than an informal implementation trick.

### (c) Per-step correctness bridge

`Proofs/Lazy_Greedy_Stateful_StepSpec.thy` packages the lazy step into a greedy-style step specification. In particular, it shows that whenever the remaining set is nonempty, the lazy choice:

- belongs to `V - lazy_set i`,
- is feasible as the next selected element,
- and attains the maximum marginal gain over the current remaining candidates.

This is the key bridge from the stateful lazy implementation back to the reusable greedy approximation framework.

### (d) Inherited approximation guarantee

Using that step-spec packaging, `Proofs/Lazy_Greedy_Stateful_Approx.thy` recovers the same Nemhauser--Wolsey `(1 - 1/e)` approximation guarantee for `lazy_set`.

Thus the lazy construction is formally connected back to the same abstract guarantee as classical greedy, rather than being left merely as an implementation heuristic.

### (e) Oracle-style compatibility layer

`Algorithms/Lazy_Greedy_Oracle.thy` provides an auxiliary oracle-style view of LazyGreedy, packaging lazy upper-bound tightening into a greedy-style oracle interface. Together with `Proofs/Lazy_Greedy_Approx.thy`, this gives a convenient theorem-facing compatibility layer around the main stateful development.

### (f) Oracle-cost layer

The LazyGreedy development also includes an initial formal complexity layer:

- per-round gain-evaluation accounting,
- total oracle-cost upper bounds for a full run,
- and comparison lemmas against a naive scan baseline.

This does not yet claim a final polished asymptotic complexity theory for every lazy variant, but it does provide a genuine formal starting point for cost reasoning rather than leaving complexity entirely informal.

---

## 1.4 StochasticGreedy development (substantially developed)

The repository now also contains a substantial StochasticGreedy line.

Main ingredients:

- `Algorithms/Stochastic_Greedy.thy`
- `Proofs/Stochastic_Greedy_Sampling.thy`
- `Proofs/Stochastic_Greedy_Weighted_Sampling.thy`
- `Proofs/Stochastic_Greedy_OneStep.thy`
- `Proofs/Stochastic_Greedy_Approx.thy`
- `Proofs/Stochastic_Greedy_Uniform_WR.thy`
- `Complexity/Stochastic_Greedy_OracleCost.thy`
- `Experiments/Stochastic_vs_Greedy_Toy.thy`

This stochastic development should be understood in two layers.

### (a) Abstract stochastic layer

The abstract layer already introduces:

- sampling-space infrastructure,
- weighted sampling interfaces,
- hit / miss event reasoning,
- one-step gain arguments,
- and approximation-layer packaging.

So the project has already moved beyond the question of whether a stochastic-greedy formalisation is possible in principle.

### (b) Concrete uniform with-replacement model over the remaining set

A major recent milestone is the buildable concrete theory

- `Proofs/Stochastic_Greedy_Uniform_WR.thy`

which formalises uniform with-replacement sampling over the remaining set `V - S`.

This theory develops:

- a concrete list space `wr_space_on`,
- the induced uniform sampling space `uniform_wr_space`,
- the uniform probability mass `uniform_wr_prob`,
- exact hit / miss event decompositions,
- exact miss-event counting,
- exact hit / miss probability formulas,
- and the intended lower bounds connecting the concrete model to the abstract hit layer.

In particular, the theory now proves the concrete exponential-style and linearised hit lower bounds needed for the stochastic approximation story, and it is part of the main session build.

### (c) What remains open in the stochastic line

The remaining issue is not the absence of a concrete stochastic development: that part now exists and builds successfully.

The main remaining task is to patch the abstraction boundary in `Proofs/Stochastic_Greedy_Weighted_Sampling.thy`. At present, the sampling-space / probability-mass assumptions are too global for a genuine with-replacement model over `V - S`, because the edge case

- `V - S = {}`
- and `s > 0`

is incompatible with a nonempty with-replacement sample space.

Accordingly, the concrete theory records the natural feasibility side condition

```text
V - S ≠ {} ∨ s = 0
```

and the final locale interpretation should be added only after the weighted sampling locale is patched to reflect this condition cleanly.

So the stochastic line is best described as:

- substantially developed and already buildable at the concrete level,

- with one remaining abstraction / interpretation step still to be sealed.

---

## 1.5 Executable baselines and sanity-check instances

The repository includes several runnable small-instance theories:

- Experiments/Experiments_Exhaustive.thy
- Experiments/Experiments_Exhaustive_Correctness.thy
- Experiments/Experiments_Coverage_Example.thy
- Experiments/Experiments_Coverage_Suboptimal.thy
- Experiments/Experiments_Nonsubmodular_Counterexample.thy
- Experiments/Lazy_vs_Greedy_Toy.thy
- Experiments/Stochastic_vs_Greedy_Toy.thy
- Experiments/Cost_Model.thy

These serve several purposes:
- they provide tiny executable baselines;
- they expose recorded outputs on concrete instances;
- they illustrate that greedy can be strictly suboptimal even in the monotone submodular setting;
- they show explicitly that once submodularity is dropped, the classical approximation guarantee can fail;
- they provide small experimental playgrounds for comparing standard greedy, LazyGreedy, and StochasticGreedy on toy cases;
- and they include a lightweight cost-model helper for simple oracle-call conventions and scan-cost baselines.

---

## 1.6 Concrete instance layer

The repository also includes a reusable concrete instance line based on coverage functions:
- Instances/Coverage_Setup.thy
- Instances/Coverage_Interpretation_Toy.thy
- Instances/Coverage_Exhaustive_Bridge.thy

This gives:
- a clean monotone submodular instance family,
- an interpretation of the abstract theorem layer on a toy coverage objective,
- and an end-to-end bridge from the executable exhaustive optimum to the abstract OPT_k notion.

This concrete layer is useful both for validation and for communicating the abstract formal results on explicit examples.

---

## 1.7 Summary of the present status

At this point, the repository already supports the following picture:
- a completed foundational classical greedy theorem line;
- a completed LazyGreedy development as a stateful / implementation-level extension beyond that foundation;
- a substantial StochasticGreedy development, including a buildable concrete uniform with-replacement theory;
- small executable baselines and sanity-check examples;
- reusable concrete interpreted instances;
- and initial formal oracle-cost layers.

It is therefore now better viewed as a modular Isabelle/HOL framework for submodular greedy optimisation than as a single proof of the classical greedy approximation theorem.


