# Current Status and Planned Next Steps (as of 2026-03-05)

## 0. Snapshot

This repository formalises the classical Nemhauser–Wolsey (1 - 1/e) approximation guarantee for monotone submodular maximisation under a cardinality constraint, together with a runnable Isabelle session containing tiny executable instances, exhaustive baselines, and instrumentation for empirical counters.

Key deliverables:
- Greedy (baseline): fully formalised construction + (1 - 1/e) approximation theorem.
- LazyGreedy (stateful): per-step argmax correctness + the same (1 - 1/e) guarantee for `lazy_set`.
- Complexity notes (oracle-cost): bounds for inner lazy selection and lifted bounds for the outer stateful loop.
- Executable experiments: tiny coverage instances, an exhaustive optimum baseline, a non-submodular counterexample, and a toy greedy-vs-lazy comparison with counters.

Build / run:
- `isabelle build -D .`
- `isabelle jedit -d . -l Submodular_Greedy_Experiments`


## 1. Formalisation Overview

The development is organised into layered theories:

### 1.1 Core layer

- `Core/Submodular_Base`
  - Defines the main locale `Submodular_Func` on a finite ground set `V`:
    non-negativity, monotonicity, submodularity, and `f {}` = 0.
- `Core/Oracle_Cost`
  - Provides a lightweight counting convention for oracle calls (used by cost-model / experiments).

### 1.2 Greedy construction layer

- `Algorithms/Greedy_Submodular_Construct`
  - Establishes `Greedy_Setup`, fixing:
    - a finite ground set `V`,
    - a budget `k`,
    - a non-negative, monotone, submodular set function `f` with `f {}` = 0.
  - Defines:
    - marginal gain `gain(S,e)`,
    - a maximiser interface `argmax_gain`,
    - the greedy sequence `greedy_set : nat => 'a set`.
  - Proves core structural properties:
    - `greedy_set i ⊆ V` and finiteness,
    - monotonicity: `i ≤ j ⟹ greedy_set i ⊆ greedy_set j`,
    - cardinality bounds: `card (greedy_set i) ≤ i` and `card (greedy_set i) ≤ min i (card V)`,
    - a state-transition lemma for `greedy_set (Suc i)` when `V - greedy_set i ≠ {}`.
  - Adds a list-view of the greedy construction (`greedy_sequence`) with indexing lemmas.

### 1.3 Greedy approximation layer (baseline theorem)

- `Proofs/Greedy_Submodular_Approx`
  - Proves the analytic inequality (for all `k ≥ 1`):
    - `(1 - 1/k)^k ≤ exp (-1)` and `1 - (1 - 1/k)^k ≥ 1 - 1/e`.
  - Inside the greedy locale:
    - non-negativity of marginal gains,
    - diminishing returns + telescoping inequality,
    - averaging lemma:
      for any feasible `S`, there exists `e ∈ V - S` with
      `gain(S,e) ≥ (OPT_k - f(S)) / k`,
    - defines the feasible family `F_k = {S ⊆ V | card S ≤ k}` and a canonical maximiser `OPT_set`,
    - defines the gap `gap(i) = OPT_k - f(greedy_set i)` and proves geometric decay:
      `gap(i) ≤ (1 - 1/k)^i * OPT_k`,
    - derives the Nemhauser–Wolsey guarantee:
      `f(greedy_set k) ≥ (1 - 1/e) * OPT_k`.
- `Proofs/Greedy_Step_Spec` + `Proofs/Greedy_Approx_From_Spec`
  - Modular bridge: any `select` oracle satisfying the usual per-step “membership + argmax” spec can reuse
    the baseline greedy approximation theorem without redoing the analytic proof.

At this point, the classical greedy approximation theorem is fully formalised and reusable via a step-spec interface.

### 1.4 LazyGreedy line (stateful)

This line formalises a stateful “lazy” selection procedure with cached upper bounds, and proves that the resulting `lazy_set` achieves the same (1 - 1/e) approximation ratio.

- `Algorithms/Lazy_Greedy_Stateful`
  - Defines the lazy-greedy state (`Sg`, `ubg`) and a step function `lazy_step`.
  - Establishes key invariants such as `ub_valid` preservation across steps.
- `Proofs/Lazy_Greedy_Stateful_StepSpec`
  - Packages stateful lazy greedy into a clean per-step interface:
    - membership of the chosen element in the remainder,
    - the argmax (max-gain) property over the remainder,
    - the set-update shape lemma for `lazy_set (Suc i)`.
- `Proofs/Lazy_Greedy_Stateful_Approx`
  - Proves the Nemhauser–Wolsey (1 - 1/e) guarantee for the stateful lazy algorithm:
    `f (lazy_set k) ≥ (1 - 1 / exp 1) * OPT_k`.
  - The proof follows the standard gap-recurrence argument, using:
    (i) the `OPT_k` infrastructure from the baseline greedy development, and
    (ii) the per-step argmax property already proved for the stateful lazy step.

#### Oracle-cost / complexity notes (LazyGreedy)

- `Complexity/Lazy_Greedy_OracleCost`
  - Inner-loop bounds for the lazy selection procedure:
    - `gain_evals ≤ fuel` (and with `fuel = card A`, `gain_evals ≤ card A`),
    - refined bound: `gain_evals ≤ card (untight S A ub) + 1`,
      where `untight` is the set of candidates whose upper bounds are still loose.
- `Complexity/Lazy_Greedy_TotalOracleCost`
  - Lifts the inner bounds to the outer stateful loop over `m` steps:
    - coarse bound: total oracle calls are `O(m * card V)`,
    - refined “potential-style” bound via the sum of per-step `card (untight ...) + 1`.

Together, the LazyGreedy line now has: (a) correctness at the per-step level, (b) approximation ratio, and (c) a basic formal oracle-cost accounting.


## 2. Executable Experiments (Session `Submodular_Greedy_Experiments`)

To support supervisor feedback (baseline + runnable tiny instances + recorded outputs), the repository includes an Isabelle session with executable examples:

### 2.1 Files

- `Experiments/Experiments_Exhaustive.thy`
  - Exhaustive baseline `enum_opt_set` for tiny instances (enumerate candidates, filter by `|S| ≤ k`, fold argmax).
- `Experiments/Experiments_Exhaustive_Correctness.thy`
  - Feasibility + optimality lemmas for `enum_opt_set`.
- `Experiments/Experiments_Coverage_Example.thy`
  - Coverage instance 1 (`|V|=5`, `k=2`) + counters.
- `Experiments/Experiments_Coverage_Suboptimal.thy`
  - Coverage instance 2 (`|V|=3`, `k=2`) where greedy is strictly suboptimal + counters.
- `Experiments/Experiments_Nonsubmodular_Counterexample.thy`
  - Monotone but non-submodular counterexample with an explicit witness lemma + recorded ratio below `1 - 1/e`.
- `Experiments/Cost_Model.thy`
  - Counting convention and derived counters for the naive greedy scan baseline.
- `Experiments/Lazy_vs_Greedy_Toy.thy`
  - Executable toy comparison: naive greedy vs. a deterministic list-level lazy greedy refinement,
    reporting solution/value and counters in a fixed format (`toy_summary`, `toy_checks`).

### 2.2 Counting convention (oracle calls)

- Each marginal gain evaluation `gain(S,e) = f(S ∪ {e}) - f(S)` is counted as two calls to `f`.
- Naive greedy scans remaining elements each round. In the worst case, the number of marginal comparisons is
  `sum_{i=0..k-1} (|V| - i)`.
- Exhaustive baseline enumerates all candidates with `|S| ≤ k` (grows combinatorially with `|V|`).
- The toy lazy comparison additionally records:
  - `gain_evals`: number of gain computations performed by the lazy selection loop,
  - `tighten_steps`: number of iterations where an upper bound is tightened (recomputed).

### 2.3 Recorded outputs (tiny instances)

#### Coverage instance 1 (`|V|=5`, `k=2`)

- `f_cov greedy_sol = 4`
- `f_cov opt_sol = 4`
- ratio (integer %) = `100`
- `greedy_f_evals = 18`
- `exhaustive_candidates = 16`

#### Coverage instance 2 (`|V|=3`, `k=2`) — greedy strictly suboptimal

- `greedy_sol2 = {A0, C0}`
- `f2 greedy_sol2 = 5`
- `opt_sol2 = {B0, C0}`
- `f2 opt_sol2 = 6`
- ratio (integer %) = `83` (i.e. `5*100 div 6 = 83`)
- `greedy_f_evals2 = 10`
- `exhaustive_candidates2 = 7`

This shows that even for monotone submodular objectives greedy can be strictly below optimum, while remaining consistent with the `(1 - 1/e)` guarantee.

#### Non-submodular counterexample (`|V|=3`, `k=2`) — ratio below `1 - 1/e`

- `greedy_sol = {A, C}`, `f_bad greedy_sol = 100`
- `opt_sol = {B, C}`, `f_bad opt_sol = 200`
- ratio (integer %) = `50`
- `greedy_f_evals = 10`
- `exhaustive_candidates = 7`
- plus a lemma giving an explicit witness that `f_bad` is not submodular.

This demonstrates that submodularity is essential for the classical approximation guarantee.

#### Lazy vs. greedy toy comparison (deterministic, fixed format)

- `toy_summary` prints two records (GREEDY and LAZY) of the form:
  `(tag, solution_as_list, f_value, gain_evals, tighten_steps, oracle_calls)`.
- `toy_checks` includes simple boolean checks such as:
  - same objective value,
  - lazy gain-evals <= greedy marginal-evals,
  - lazy oracle-calls <= greedy oracle-calls.


## 3. Coverage instantiation and exhaustive bridge

### 3.1 Coverage locale (reusable)

- `Instances/Coverage_Setup.thy`
  - Introduces a reusable locale `Coverage_Setup` and proves the induced coverage objective is monotone and submodular on finite `V`,
    hence instantiates `Submodular_Func`.

### 3.2 Toy interpretation + bridge to exhaustive optimum

- `Instances/Coverage_Interpretation_Toy.thy`
  - Exposes the toy instance’s main (1 - 1/e) approximation theorem.
- `Instances/Coverage_Exhaustive_Bridge.thy`
  - Proves `f_cov_real (enum_opt_set f_cov_real Vlist k) = OPT_k` (under `distinct Vlist`),
  - derives a clean comparison theorem:
    `f_cov_real (CovToy.greedy_set k) ≥ (1 - 1 / exp 1) * f_cov_real (enum_opt_set f_cov_real Vlist k)`.


## 4. Planned Next Steps (post-2026-03-05)

### 4.1 Modern submodular maximisation algorithms
Extend beyond LazyGreedy to additional modern variants (e.g. StochasticGreedy, LazierThanLazyGreedy),
with:
- formal correctness arguments,
- formal oracle-cost / evaluation-count bounds,
- extracted code + runnable experiments.

### 4.2 Code extraction + empirical validation harness
After stabilising the theory interfaces, extract executable code for:
- greedy baseline,
- stateful LazyGreedy,
and run a small suite of reproducible toy instances with counters.

### 4.3 Connect to matroid infrastructure
Explore aligning the submodular library with Isabelle’s existing matroid development,
to support matroid-constrained submodular optimisation (beyond cardinality constraints).


## 5. Changelog

### 2026-03-05
- Added the stateful LazyGreedy approximation theorem (`Proofs/Lazy_Greedy_Stateful_Approx`).
- Added a packaged step-spec interface for the stateful lazy step (`Proofs/Lazy_Greedy_Stateful_StepSpec`).
- Added oracle-cost bounds for LazyGreedy selection (inner loop) and lifted bounds for the outer stateful loop (`Complexity/`).
- Added an executable greedy-vs-lazy toy comparison with counters (`Experiments/Lazy_vs_Greedy_Toy`).
- Session wiring: updated `ROOT` so `isabelle build -D .` runs end-to-end.

### 2026-02-16
- Added `Experiments_Exhaustive_Correctness.thy`: feasibility + optimality lemmas for `enum_opt_set`.
- Updated `ROOT` to include `sessions "HOL-Library"` (needed for `HOL-Library.Sublist`) and to build the new theory as part of the session.
- Added `Coverage_Exhaustive_Bridge.thy`, connecting `enum_opt_set` (exhaustive optimum) to `OPT_k`,
  and proving a direct greedy-vs-exhaustive bound for the toy instance.

