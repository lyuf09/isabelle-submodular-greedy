# Current Status and Planned Next Steps

## 1. Current Status of the Formalisation

The repository has now clearly moved beyond a “classical greedy only” stage. At this point it contains:

- a completed classical greedy approximation line,
- a completed lazy-greedy approximation line with stateful and oracle-level structure,
- oracle-cost layers for lazy and stochastic variants,
- concrete interpreted instances and executable toy experiments,
- and a substantially expanded stochastic-greedy line.

The overall development is no longer best viewed as a single theorem formalisation. It is better understood as a growing Isabelle/HOL framework for approximation proofs of greedy-type algorithms for cardinality-constrained submodular maximization.

---

## 2. High-Level Structure

The current design is intentionally modular.

### 2.1 Core layer

Theories in `Core/` provide the abstract base layer for finite monotone submodular set functions, gains, feasibility, and oracle-cost bookkeeping.

This layer is shared by all later algorithmic variants.

### 2.2 Algorithm layer

Theories in `Algorithms/` define the executable or stateful algorithmic objects, including:

- classical greedy construction,
- lazy-greedy stateful machinery,
- lazy oracle views,
- stochastic greedy sampling-level constructions.

### 2.3 Proof layer

Theories in `Proofs/` contain the main approximation and bridge results, including:

- the classical greedy approximation line,
- the step-spec abstraction used to transfer lazy-greedy approximation results,
- stochastic sampling and hit/miss infrastructure,
- expected one-step stochastic results,
- recurrence-level approximation lemmas,
- and an abstract stochastic gap-bridge layer.

### 2.4 Concrete instances and experiments

Theories in `Instances/` and `Experiments/` provide:

- toy coverage-style interpretations,
- exhaustive sanity checks,
- small executable comparison experiments,
- counterexample-style illustrations outside the intended submodular setting.

### 2.5 Complexity / oracle-cost layer

Theories in `Complexity/` formalize oracle-cost accounting and comparison results for lazy and stochastic variants.

---

## 3. Completed and Stable Components

### 3.1 Classical greedy

The classical deterministic greedy line is completed.

This includes:

- the construction layer,
- the standard Nemhauser-Wolsey style approximation proof,
- and the reusable approximation infrastructure that later variants build on.

At this point, the classical line is no longer the main blocker for the project.

### 3.2 Lazy greedy

The lazy-greedy line is also in a strong state.

It now contains:

- a stateful algorithmic formulation,
- a lazy-oracle abstraction,
- a step-spec interface,
- transfer results from abstract step specifications to approximation guarantees,
- and oracle-cost / total-cost theories.

This part already has the shape of a reusable library component rather than an isolated one-off proof.

### 3.3 Concrete instances and executable checks

The repository already contains a nontrivial “interpretation + executable sanity check” layer via coverage-style examples and small toy experiments.

These components are useful both for validation and for demonstrating that the development is not purely abstract.

---

## 4. Status of the StochasticGreedy Line

The stochastic line has advanced substantially compared with its earlier sampling-only stage.

### 4.1 Sampling and weighted interfaces

The development already includes:

- abstract sampling-space infrastructure,
- weighted sampling locales,
- hit / miss event decomposition,
- and lower-bound interfaces for hit probability.

### 4.2 Concrete uniform with-replacement model

A concrete uniform with-replacement list model over the remaining set `V - S` has been formalized.

This includes:

- the concrete list space,
- uniform probabilities,
- exact hit / miss probability formulas,
- exact miss-event counting,
- exponential-type lower bounds,
- and linearized hit-probability lower bounds.

### 4.3 Interpretation layer

The concrete uniform with-replacement model is now connected to the abstract weighted-sampling and weighted-hit locales through a dedicated interpretation layer.

This is an important milestone, because the stochastic line is no longer only a collection of concrete counting lemmas: it now feeds into the abstract proof architecture.

### 4.4 Expected one-step layer

A dedicated expectation layer has now been added.

This packages:

- the definition of sampled one-step gain,
- the definition of expected one-step gain,
- hit / miss decomposition of expected gain,
- lower bounds by weighted hit-event averages,
- and reusable lower-bound templates of the form

  `expected_step_gain ≥ hit_prob_of × c`.

This fills the main gap left open by the earlier deterministic one-step file.

### 4.5 Approximation recurrence layer

A separate approximation layer has now been added for the stochastic line.

This layer isolates:

- multiplicative gap-contraction templates,
- recurrence-solving lemmas based on `stoch_gap_factor`,
- and reusable approximation-from-recurrence statements.

So the recurrence algebra is no longer merely planned; it has now been formalized as a reusable component.

### 4.6 Abstract gap-bridge layer

A further abstraction layer has been added to package the assumptions under which one-step lower bounds imply a stochastic gap recurrence and then a closed-form lower bound on value.

This layer does not yet constitute the final fully concrete end-to-end stochastic theorem for a specific run semantics, but it makes the remaining gap very explicit.

---

## 5. What Has Changed Conceptually

Earlier in the project, the stochastic line was blocked mainly at the level of sampling abstractions and concrete-model integration.

That is no longer the right way to describe the status.

The main stochastic bottleneck has now moved upward:

- the sampling layer exists,
- the concrete uniform model exists,
- the interpretation layer exists,
- the expected one-step layer exists,
- the recurrence solver exists,
- and the abstract gap-bridge layer exists.

What remains is no longer “build the stochastic infrastructure”.  
What remains is to instantiate the final abstract bridge into a concrete end-to-end stochastic approximation theorem.

This is a much narrower and more mature remaining task.

---

## 6. Current Best Description of the Project

At the present stage, the repository is best described as:

- a completed classical greedy formalisation,
- a completed lazy-greedy formalisation with cost layers,
- a substantially developed stochastic-greedy framework with interpretation, expected one-step, recurrence, and abstract gap-bridge components,
- plus concrete instances and executable experiments.

In other words, the project has already crossed the boundary from “formalising one approximation proof” into “building a reusable Isabelle/HOL submodular-greedy library architecture”.

---

## 7. Remaining Main Tasks

Although substantial progress has been made, the project is not fully closed yet.

### 7.1 Main stochastic theorem instantiation

The main remaining technical task is:

- instantiate the abstract stochastic gap bridge into a fully concrete end-to-end stochastic approximation theorem.

This is currently the most important open item on the stochastic side.

### 7.2 Final stochastic theorem packaging

Once the concrete end-to-end theorem is in place, the stochastic line should be packaged more cleanly as a finished theorem line, comparable in clarity to the lazy-greedy part.

That includes:

- clearer top-level theorem endpoints,
- cleaner dependency presentation,
- and a more polished narrative in the proof document.

### 7.3 Documentation and repository narrative alignment

Some repository-level narrative still reflects an earlier stage of the project.

These descriptions should be updated so that the README and status notes match the current theory graph, especially for the stochastic line.

### 7.4 AFP-oriented cleanup

Even once the theory side is finished, the repository will still need AFP-oriented cleanup, including:

- final scope decisions,
- document preparation,
- theory-narrative polishing,
- submission-style packaging,
- and final build / document checks.

---

## 8. Immediate Next Steps

The most immediate next steps are therefore:

1. instantiate the abstract stochastic gap bridge into a concrete end-to-end approximation theorem;
2. expose that theorem as the clean stochastic endpoint of the current library;
3. update the repository narrative so that it matches the current formal state of the code;
4. begin AFP-oriented cleanup once the stochastic endpoint is concretely sealed.

---

## 9. Longer-Term Direction

After the current stochastic line is sealed more concretely, the development is well positioned for several future directions, including:

- stronger stochastic complexity / oracle-cost comparisons,
- additional executable case studies,
- further greedy variants beyond the current deterministic / lazy / stochastic triad,
- and paper / archive packaging aimed at AFP and later publication venues.

---

## 10. Summary

The current repository status can be summarized as follows:

- classical greedy: completed;
- lazy greedy: completed at the main approximation level, with cost layers;
- stochastic greedy: substantially developed, with the remaining work now concentrated in the final concrete gap-bridge instantiation rather than in basic infrastructure.

This means the project is now much closer to “final theorem-line completion plus packaging” than to “early-stage framework construction”.
