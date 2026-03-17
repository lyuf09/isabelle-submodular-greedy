# Current Status and Planned Next Steps

This note summarizes the current status of the Isabelle/HOL formalization project on greedy algorithms for cardinality-constrained submodular maximization, with particular attention to the newly completed stochastic-greedy milestone.

---

## Executive summary

The repository now contains:

- a formal deterministic greedy baseline,
- a modular lazy-greedy approximation and oracle-cost development,
- a concrete uniform with-replacement stochastic-greedy theorem line that reaches a final AAAI-style approximation statement.

The major recent milestone is that the stochastic development has moved beyond:

- sampling-space infrastructure,
- interpretation to weighted-hit abstractions,
- expected one-step templates,
- and abstract gap-bridge packaging,

and now includes a completed concrete bridge and final wrapper for the uniform with-replacement model.

This means that the main mathematical content originally identified as “Deliverable A” is now complete within the current abstraction boundary of the development.

---

## What has been completed

### 1. Deterministic greedy baseline

The classical cardinality-constrained greedy approximation proof is formalized using the standard Nemhauser-Wolsey gap-recurrence route.

This supplies:

- the basic greedy construction layer,
- deterministic approximation infrastructure,
- reusable monotonicity / submodularity lemmas used later by lazy and stochastic variants.

### 2. Lazy greedy line

The lazy-greedy line is formalized in a modular way through:

- a stateful algorithm layer,
- an oracle / step-spec interface,
- an approximation transfer theorem,
- oracle-cost and total-cost accounting theories.

This part is already structurally close to a polished reusable component.

### 3. Stochastic greedy line

The stochastic-greedy part now contains the following full chain:

- abstract sampling-space infrastructure,
- weighted-sampling interfaces,
- hit/miss probability analysis,
- a concrete uniform with-replacement model on the remaining set,
- interpretation into the abstract weighted-hit framework,
- expected one-step gain infrastructure,
- recurrence-based approximation algebra,
- a concrete first-hit symmetry bridge,
- a final k-step approximation wrapper.

Concretely, the newly completed theories are:

- `Proofs/Stochastic_Greedy_Uniform_WR_DeliverableA`
- `Proofs/Stochastic_Greedy_Uniform_WR_Final`

These theories add the missing concrete bridge and final theorem line for the uniform with-replacement stochastic model.

---

## What the new stochastic milestone achieves

The new development proves a concrete expected one-step lower bound of the form

- `expected_step_gain ≥ (alpha_stoch s / k) * gap`

for the uniform with-replacement model.

It then packages this into a k-step approximation wrapper and derives:

- a generic alpha-version value lower bound,
- an epsilon-parameterized exponential-form final bound,
- an AAAI-style approximation statement of the form
  `1 - 1 / exp 1 - eps`.

In other words, the stochastic development is no longer “abstractly ready in principle” but now contains a completed end-to-end theorem line for a concrete sampling model.

---

## Important scope clarification

The final stochastic theorem is currently packaged at the level of a set-valued state sequence satisfying:

- feasibility (`A i ⊆ V`),
- value domination by `OPT`,
- the expected one-step update equation.

This matches the current abstraction boundary of the repository.

So the present milestone should be understood as:

- a completed concrete stochastic approximation theorem line for the uniform with-replacement model,
- packaged through the current recurrence / state-sequence interface,

rather than as a fully probabilistic run-semantics formalization of the executable stochastic algorithm.

This is an intentional architectural choice and not a missing mathematical gap in the present theorem line.

---

## Repository status by area

### Stable / largely completed components

- `Core/Submodular_Base`
- `Algorithms/Greedy_Submodular_Construct`
- `Proofs/Greedy_Submodular_Approx`
- `Proofs/Greedy_Approx_From_Spec`
- lazy-greedy approximation and cost theories
- concrete stochastic Deliverable-A bridge
- concrete stochastic final wrapper for the uniform WR model

### Mature but still good candidates for polishing

- stochastic approximation packaging
- stochastic comparison / cost presentation
- documentation and naming consistency across stochastic files
- experiment-facing organization

### Open extension directions

- stronger oracle-cost stories for stochastic variants
- more explicit run-semantics integration if desired
- larger executable validations / experiments
- possible extensions beyond the present uniform WR theorem line

---

## Current interpretation of Deliverable A

The original Deliverable A goal was to formalize the main stochastic-greedy approximation theorem line corresponding to the standard cardinality-constrained monotone-submodular setting.

That milestone is now considered complete in the following sense:

- the hard concrete one-step bridge is formalized,
- the bridge has been connected to the recurrence solver,
- the final approximation wrapper has been proved,
- an AAAI-style epsilon theorem statement has been derived.

So, at the level of theorem content, Deliverable A is complete.

What remains is not “finishing Deliverable A” but rather:

- packaging,
- polishing,
- strengthening related auxiliary stories,
- and deciding how far to push the development toward AFP-style presentation and future extensions.

---

## Immediate next steps

### 1. Packaging and cleanup

The highest-priority near-term task is to clean and package the stochastic theorem line:

- remove obviously redundant assumptions where appropriate,
- standardize theorem naming and comments,
- trim helper lemmas that can be made more local or more reusable,
- make the final theorem narrative easier to read for external reviewers.

### 2. README / project narrative update

The repository description should now reflect that the stochastic line is no longer merely abstract or partial.

In particular, the README should describe:

- the new Deliverable-A bridge theory,
- the new final wrapper,
- the existence of a completed concrete stochastic theorem line for the uniform WR model.

### 3. Cost / comparison story

A natural technical next step is to strengthen the stochastic comparison side:

- oracle-count presentation,
- explicit comparison against deterministic greedy / lazy greedy,
- cleaner cost-oriented statements around the current stochastic model.

### 4. AFP-style preparation

The project is now much closer to a coherent submission-grade narrative.

Important preparation tasks include:

- reorganizing the stochastic files into a cleaner final hierarchy if needed,
- checking imports and dependency minimality,
- improving comment style and theorem statements,
- reducing ad hoc proof-engineering leftovers where possible.

---

## Medium-term research directions

Beyond immediate cleanup, the development could naturally continue in several directions:

1. a cleaner run-semantics connection for the stochastic algorithm;
2. stronger cost / complexity packaging;
3. broader experiment layers;
4. extensions to additional stochastic or hybrid greedy variants;
5. further modularization for publication / AFP presentation quality.

---

## Bottom line

At present, the project contains:

- a completed deterministic baseline,
- a strong lazy-greedy line,
- and now a completed concrete stochastic approximation theorem line for the uniform with-replacement model.

This marks a substantial transition in the repository:

the stochastic part is no longer merely an abstract scaffold, but an actual completed theorem line with a final approximation statement.

The project is therefore moving from “core theorem development” into “packaging, refinement, and presentation-quality polishing”.