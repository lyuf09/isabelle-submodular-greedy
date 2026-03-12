# Current Status and Planned Next Steps

## 1. Current Status of the Formalisation

The repository has now clearly moved beyond a “classical greedy only” stage. At the theory level, it already contains a completed foundational classical greedy development, together with a completed LazyGreedy extension at the stateful / implementation level, small executable baselines, concrete interpreted instances, and an initial oracle-cost framework.

### 1.1 Core architecture

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

### 1.2 Classical greedy foundation (completed)

The classical greedy development is complete.

Main ingredients:
- `Algorithms/Greedy_Submodular_Construct.thy`
- `Proofs/Greedy_Step_Spec.thy`
- `Proofs/Greedy_Approx_From_Spec.thy`
- `Proofs/Greedy_Submodular_Approx.thy`

This line establishes:
- the abstract greedy sequence `greedy_set`;
- structural invariants of the greedy construction;
- a reusable greedy-step specification;
- the standard averaging lemma and gap recurrence;
- and the Nemhauser--Wolsey `(1 - 1/e)` approximation guarantee for monotone submodular maximisation under a cardinality constraint.

So the foundational classical theorem line is fully formalised.

### 1.3 Verified LazyGreedy as a completed stateful extension beyond classical greedy

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

Its current contribution has five main aspects.

#### (a) Explicit algorithmic state
A stateful lazy construction is defined explicitly, with internal state carrying the current selected set together with cached upper-bound information.

#### (b) State-based invariants
The development tracks key structural facts directly at the level of the algorithmic state, making the lazy procedure a genuine formal object rather than an informal implementation trick.

#### (c) Per-step correctness bridge
`Proofs/Lazy_Greedy_Stateful_StepSpec.thy` packages the lazy step into a greedy-style step specification. In particular, it shows that whenever the remaining set is nonempty, the lazy choice:
- belongs to `V - lazy_set i`,
- is feasible as the next selected element,
- and attains the maximum marginal gain over the current remaining candidates.

This is the key bridge from the stateful lazy implementation back to the reusable greedy approximation framework.

#### (d) Inherited approximation guarantee
Using that step-spec packaging, `Proofs/Lazy_Greedy_Stateful_Approx.thy` recovers the same Nemhauser--Wolsey `(1 - 1/e)` approximation guarantee for `lazy_set`.

Thus the lazy construction is formally connected back to the same abstract guarantee as classical greedy, rather than being left merely as an implementation heuristic.

#### (e) Oracle-style compatibility layer
`Algorithms/Lazy_Greedy_Oracle.thy` provides an auxiliary oracle-style view of LazyGreedy, packaging lazy upper-bound tightening into a greedy-style oracle interface. Together with `Proofs/Lazy_Greedy_Approx.thy`, this gives a convenient theorem-facing compatibility layer around the main stateful development.

#### (f) Oracle-cost layer
The LazyGreedy development also includes an initial formal complexity layer:
- per-round gain-evaluation accounting;
- total oracle-cost upper bounds for a full run;
- and comparison lemmas against a naive scan baseline.

This does not yet claim a final polished asymptotic complexity theory for every lazy variant, but it does provide a genuine formal starting point for cost reasoning rather than leaving complexity entirely informal.

### 1.4 Executable baselines and sanity-check instances

The repository includes several runnable small-instance theories:

- `Experiments/Experiments_Exhaustive.thy`
- `Experiments/Experiments_Exhaustive_Correctness.thy`
- `Experiments/Experiments_Coverage_Example.thy`
- `Experiments/Experiments_Coverage_Suboptimal.thy`
- `Experiments/Experiments_Nonsubmodular_Counterexample.thy`
- `Experiments/Lazy_vs_Greedy_Toy.thy`
- `Experiments/Cost_Model.thy`

These serve several purposes:
- they provide tiny executable baselines;
- they expose recorded outputs on concrete instances;
- they illustrate that greedy can be strictly suboptimal even in the monotone submodular setting;
- they show explicitly that once submodularity is dropped, the classical approximation guarantee can fail;
- they provide a small experimental playground for comparing naive greedy scanning with lazy refinements;
- and they include a lightweight cost-model helper for simple oracle-call conventions and scan-cost baselines.

### 1.5 Concrete instance layer

The repository also includes a reusable concrete instance line based on coverage functions:

- `Instances/Coverage_Setup.thy`
- `Instances/Coverage_Interpretation_Toy.thy`
- `Instances/Coverage_Exhaustive_Bridge.thy`

This gives:
- a clean monotone submodular instance family;
- an interpretation of the abstract theorem layer on a toy coverage objective;
- and an end-to-end bridge from the executable exhaustive optimum to the abstract `OPT_k` notion.

This concrete layer is useful both for validation and for communicating the abstract formal results on explicit examples.

### 1.6 Summary of the present status

At this point, the repository already supports the following picture:
- a completed foundational classical greedy theorem line;
- a completed LazyGreedy development as a stateful / implementation-level extension beyond that foundation;
- small executable baselines and sanity-check examples;
- reusable concrete interpreted instances;
- and an initial formal oracle-cost layer.

It is therefore now better viewed as a modular Isabelle/HOL framework for submodular greedy optimisation than as a single proof of the classical greedy approximation theorem.

---

## 2. Planned Next Steps

The next stage of the project should deepen the present framework in a focused way rather than merely broaden it.

### 2.1 Formalise StochasticGreedy as the next main theorem line

The most immediate next target is `StochasticGreedy`.

At this point, the development is in a much stronger position for such an extension than before, since the verified LazyGreedy development has already exercised the general pattern:

algorithmic construction -> correctness packaging -> approximation transfer -> cost accounting.

A StochasticGreedy development would add a genuinely new dimension to the library. Beyond deterministic greedy-style reasoning, it would require a principled treatment of sampled candidate sets, expected progress, and query-complexity bounds. This makes it the natural next main theorem target for the project.

A further variant such as `LazierThanLazyGreedy` remains a natural follow-up direction, but it is better viewed as a subsequent extension rather than an immediate parallel target.

### 2.2 Prepare the development for AFP-level maturity

A central next step is to consolidate the current theory into a more polished AFP-style entry.

This includes:
- stabilising the main interfaces and theorem endpoints;
- sharpening the document-level narrative of the development;
- keeping the present theory lines modular and reusable;
- and ensuring that future extensions can be added without major refactoring of the existing structure.

The goal is not only to add more results, but also to make the current framework read as a mature and reusable formal library.

### 2.3 Code extraction and small-scale empirical validation

Once the StochasticGreedy line and the surrounding interfaces are sufficiently stable, a natural next step is:
- code extraction from the formal developments,
- executable comparison against small baselines,
- and small-scale empirical validation of the extracted implementations.

This would connect the present formal theory more directly to algorithm engineering and provide a clearer bridge from abstract proofs to executable artefacts.

### 2.4 Strengthen the complexity layer

The current oracle-cost results already provide a meaningful first complexity layer, but there is still room for refinement.

Natural directions include:
- sharper accounting for lazy rounds;
- stronger comparisons with naive scanning;
- query-complexity analyses for stochastic variants;
- and, in the longer term, refined cost analyses for approximate lazy methods.

### 2.5 Connect to matroid-related infrastructure

A particularly interesting medium-term direction is to relate the present submodular development to Isabelle’s existing libraries around matroid-style combinatorial structure.

This could matter in at least two ways:
- richer feasible-set abstractions beyond pure cardinality constraints;
- and a cleaner interface for future constrained submodular optimisation results.

### 2.6 More concrete instances and case studies

It would also be useful to add:
- more concrete submodular instance families;
- more benchmark-style executable examples;
- and additional bridges from abstract theorems to concrete interpreted models.

---

## 3. Positioning

The present project is increasingly best viewed not as a one-off formalisation, but as a small and growing Isabelle/HOL library for modern submodular optimisation.

The completed classical greedy development provides the foundational theorem layer. The completed LazyGreedy development is the first substantial stateful / implementation-level extension beyond that foundation: it introduces explicit state, tracks algorithmic invariants, proves per-step correctness via a bridge back to greedy-style maximality, inherits the same approximation guarantee, and adds an initial oracle-cost layer.

The next objective is therefore not merely to accumulate more algorithm names, but to deepen the library in a principled way: first by consolidating the current architecture, and then by extending it to a genuinely new main theorem target such as `StochasticGreedy`.

This makes the project a plausible base for a sustained sequence of follow-up developments, rather than a single isolated formal result.