# Current Status and Planned Next Steps

## 1. Current Status of the Formalisation

The repository has now moved beyond a “classical greedy only” stage. At the theory level, it contains a completed classical greedy line and a completed stateful LazyGreedy line, together with executable toy baselines and an initial oracle-cost framework.

### 1.1 Core architecture

The development is organised modularly.

- `Core/Submodular_Base.thy` provides the main abstract interface for finite monotone submodular set functions, marginal gains, feasibility, and cardinality constraints.
- `Core/Oracle_Cost.thy` introduces a lightweight oracle-cost layer that is reused by later complexity arguments.
- The overall design separates:
  - abstract optimisation assumptions,
  - algorithmic constructions,
  - approximation proofs,
  - instance interpretations,
  - executable experiments,
  - and complexity/accounting arguments.

This separation is important for extending the library to further greedy variants.

### 1.2 Classical greedy line (completed)

The classical greedy development is complete.

Main ingredients:
- `Algorithms/Greedy_Submodular_Construct.thy`
- `Proofs/Greedy_Step_Spec.thy`
- `Proofs/Greedy_Approx_From_Spec.thy`
- `Proofs/Greedy_Submodular_Approx.thy`

This line establishes:
- the abstract greedy sequence `greedy_set`;
- structural invariants of the greedy construction;
- a reusable greedy step specification;
- the standard averaging lemma and gap recurrence;
- the Nemhauser--Wolsey `(1 - 1/e)` approximation guarantee for monotone submodular maximisation under a cardinality constraint.

So the classical theorem line is fully formalised.

### 1.3 Stateful LazyGreedy line (completed at the theory level)

The stateful LazyGreedy development is now also in place.

Main ingredients:
- `Algorithms/Lazy_Greedy_Stateful.thy`
- `Proofs/Lazy_Greedy_Stateful_StepSpec.thy`
- `Proofs/Lazy_Greedy_Stateful_Approx.thy`
- `Proofs/Lazy_Greedy_Approx.thy`
- `Complexity/Lazy_Greedy_OracleCost.thy`
- `Complexity/Lazy_Greedy_TotalOracleCost.thy`
- `Complexity/Lazy_Greedy_Compare_NaiveScan.thy`

This line contributes four main pieces.

#### (a) Algorithmic formalisation
A stateful lazy construction is defined explicitly, with internal state carrying the current selected set together with cached upper-bound information.

#### (b) Per-step correctness
The file `Lazy_Greedy_Stateful_StepSpec.thy` packages the lazy step into a greedy-style step specification. In particular, it shows that whenever the remaining set is nonempty, the lazy choice:
- belongs to `V - lazy_set i`,
- is feasible as the next selected element,
- and attains the maximum marginal gain over the current remaining candidates.

This is the key bridge from the stateful lazy implementation to the existing greedy approximation framework.

#### (c) Approximation guarantee
Using that step-spec packaging, `Lazy_Greedy_Stateful_Approx.thy` recovers the same Nemhauser--Wolsey `(1 - 1/e)` approximation guarantee for `lazy_set`.

So at the approximation-theorem level, LazyGreedy is no longer just an implementation idea: it is formally connected back to the same abstract guarantee as classical greedy.

#### (d) Oracle-cost accounting
The LazyGreedy line also has an initial formal complexity layer:
- per-round gain-evaluation accounting;
- total oracle-cost upper bounds for a full run;
- and comparison lemmas against a naive scan baseline.

This does **not** yet claim a final polished asymptotic complexity theory for every lazy variant, but it does provide a real formal starting point for cost reasoning rather than leaving complexity entirely informal.

### 1.4 Executable baselines and sanity-check instances

The repository includes several runnable small-instance theories:

- `Experiments/Experiments_Exhaustive.thy`
- `Experiments/Experiments_Exhaustive_Correctness.thy`
- `Experiments/Experiments_Coverage_Example.thy`
- `Experiments/Experiments_Coverage_Suboptimal.thy`
- `Experiments/Experiments_Nonsubmodular_Counterexample.thy`
- `Experiments/Lazy_vs_Greedy_Toy.thy`

These serve several purposes:
- they provide tiny executable baselines;
- they expose recorded outputs on concrete instances;
- they illustrate that greedy can be strictly suboptimal even in the monotone submodular setting;
- they show explicitly that once submodularity is dropped, the classical approximation guarantee can fail;
- and they provide a small experimental playground for comparing naive greedy scanning with lazy refinements.

### 1.5 Concrete instance layer

The repository also includes a reusable concrete instance line based on coverage functions:

- `Instances/Coverage_Setup.thy`
- `Instances/Coverage_Interpretation_Toy.thy`
- `Instances/Coverage_Exhaustive_Bridge.thy`

This gives:
- a clean monotone submodular instance family;
- an interpretation of the abstract theorem layer on a toy coverage objective;
- and an end-to-end bridge from the executable exhaustive optimum to the abstract `OPT_k` notion.

This is useful both for validation and for communicating the formal results on concrete examples.

---

## 2. What is now established

At this point, the repository supports the following summary statement:

1. The classical greedy approximation theorem is fully formalised.
2. A stateful LazyGreedy line is also formalised at the theory level.
3. The LazyGreedy line includes:
   - algorithmic state,
   - packaged per-step correctness,
   - the same `(1 - 1/e)` approximation guarantee,
   - and basic formal oracle-cost accounting.
4. The project already contains small executable baselines and concrete interpreted instances.

So it is now reasonable to describe the repository as a modular Isabelle/HOL framework for submodular greedy optimisation, rather than only as a single proof of the classical greedy theorem.

---

## 3. Planned Next Steps

The next stage of the project is intended to deepen the present framework rather than merely broaden it.

### 3.1 Formalise a stochastic modern greedy variant

The most immediate next target is `StochasticGreedy`.

At this point, the development is in a much stronger position for such an extension than before, since the completed LazyGreedy line has already exercised the general pattern
algorithmic construction -> step packaging -> approximation transfer -> cost accounting.

A stochastic greedy development would add a genuinely new dimension to the library: beyond deterministic greedy-style reasoning, it would require a principled treatment of sampled candidate sets, expected progress, and query-complexity bounds. This would substantially strengthen the scope of the present framework.

A further variant such as `LazierThanLazyGreedy` remains a natural follow-up direction, but it is better viewed as a subsequent extension rather than an immediate parallel target.

### 3.2 Prepare the development for AFP-level maturity

A central next step is to consolidate the current theory into a more polished AFP-style entry.

This includes:
- stabilising the main interfaces and theorem endpoints;
- sharpening the document-level narrative of the development;
- keeping the current theory lines modular and reusable;
- and ensuring that future extensions can be added without major refactoring of the existing structure.

The goal is not only to add more results, but also to make the current framework read as a mature and reusable formal library.

### 3.3 Code extraction and empirical validation

Once the theory layer is sufficiently stable, a natural next step is:
- code extraction from the formal developments,
- executable comparison against small baselines,
- and empirical validation of the extracted implementations.

This would connect the present formal theory more directly to algorithm engineering and provide a clearer bridge from abstract proofs to executable artefacts.

### 3.4 Strengthen the complexity layer

The current oracle-cost results already provide a meaningful first complexity layer, but there is still room for refinement.

Natural directions include:
- sharper accounting for lazy rounds,
- stronger comparisons with naive scanning,
- and, in the longer term, variant-specific cost analyses for stochastic and approximate lazy methods.

### 3.5 Connect to matroid-related infrastructure

A particularly interesting medium-term direction is to relate the present submodular development to Isabelle’s existing libraries around matroid-style combinatorial structure.

This could matter in at least two ways:
- richer feasible-set abstractions beyond pure cardinality constraints;
- and a cleaner interface for future constrained submodular optimisation results.

### 3.6 More concrete instances and case studies

It would also be useful to add:
- more concrete submodular instance families;
- more benchmark-style executable examples;
- and additional bridges from abstract theorems to concrete interpreted models.

---

## 4. Positioning note

The present project is increasingly best viewed not as a one-off formalisation, but as a small and growing Isabelle/HOL library for modern submodular optimisation.

The completed classical greedy line provides the foundational theorem layer.

The completed stateful LazyGreedy line is the first substantial extension beyond that foundation, showing that the framework can already support nontrivial modern variants together with approximation and oracle-cost reasoning.

The next objective is therefore not merely to accumulate more algorithm names, but to deepen the library in a principled way: first by consolidating the current architecture, and then by extending it to a genuinely new variant such as `StochasticGreedy`.

This makes the project a plausible base for a sustained sequence of follow-up developments, rather than a single isolated formal result.