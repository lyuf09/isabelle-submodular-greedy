# Current Status and Planned Next Steps

## 1. Current Status of the Formalisation

The formal development is organised into two main Isabelle theory files.

### 1.1 `Greedy_Submodular_Construct`

- Established the locale `Greedy_Setup`, fixing:
  - a finite ground set `V`,
  - a cardinality budget `k`,
  - a non-negative, monotone, submodular set function `f` with `f {} = 0`.
- Defined:
  - marginal gain `gain(S,e)`,
  - a maximiser interface `argmax_gain`,
  - the greedy sequence `greedy_set : nat => 'a set`.
- Proved core structural properties:
  - `greedy_set i ⊆ V` and each `greedy_set i` is finite,
  - monotonicity: `i ≤ j ⟹ greedy_set i ⊆ greedy_set j`,
  - cardinality bounds: `card (greedy_set i) ≤ i` and `card (greedy_set i) ≤ min i (card V)`,
  - a state-transition lemma for `greedy_set (i+1)` when `V - greedy_set i ≠ {}`.
- Added a list-view of the greedy construction (`greedy_sequence`) with indexing lemmas.

### 1.2 `Greedy_Submodular_Approx`

- Proved the analytic inequality (for all `k ≥ 1`):
  - `(1 - 1/k)^k ≤ exp (-1)` and `1 - (1 - 1/k)^k ≥ 1 - 1/e`.
- Inside the greedy locale:
  - non-negativity of marginal gains and basic non-emptiness lemmas,
  - diminishing returns + submodular telescoping inequality,
  - averaging lemma:
    - for any feasible `S`, there exists `e ∈ V - S` such that `gain(S,e) ≥ (OPT_k - f(S))/k`,
  - defined the feasible family `F_k = {S ⊆ V | card S ≤ k}` and a canonical maximiser `OPT_set`,
  - defined the gap sequence `gap(i) = OPT_k - f(greedy_set i)` and proved geometric decay:
    - `gap(i) ≤ (1 - 1/k)^i * OPT_k`,
  - derived the Nemhauser–Wolsey guarantee:
    - `f(greedy_set k) ≥ (1 - 1/e) * OPT_k`.

At this point, the classical greedy approximation theorem for monotone submodular maximisation under a cardinality constraint is fully formalised.

---

## 2. Executable Experiments and Empirical Complexity Notes

To address supervisor feedback (baseline + small runnable instances + recorded outputs), I added a small Isabelle session for executable experiments:

- Session: `Submodular_Greedy_Experiments` (via a minimal `ROOT`).
- Files:
  - `Experiments_Exhaustive.thy`: exhaustive baseline `enum_opt_set` for tiny instances (enumerate candidates, filter by `|S| ≤ k`, fold argmax).
  - `Experiments_Coverage_Example.thy`: coverage instance 1 (`|V|=5`, `k=2`) + counters.
  - `Experiments_Coverage_Suboptimal.thy`: coverage instance 2 (`|V|=3`, `k=2`) where greedy is strictly suboptimal + counters.
  - `Experiments_Nonsubmodular_Counterexample.thy`: monotone but **non-submodular** counterexample with an explicit witness lemma + recorded ratio below `1 - 1/e`.

### 2.1 Counting convention (oracle calls)

- Each marginal gain evaluation `gain(S,e) = f(S ∪ {e}) - f(S)` is counted as **two calls** to `f`.
- Greedy scans remaining elements each round. In the worst case, the number of marginal comparisons is `Σ_{i=0}^{k-1} (|V| - i)`.
- Exhaustive baseline enumerates a finite set of candidates with `|S| ≤ k` (size grows combinatorially with `|V|`).

### 2.2 Recorded outputs (tiny instances)

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

This explicitly shows that even for monotone submodular objectives greedy can be strictly below optimum (while remaining consistent with the `(1 - 1/e)` guarantee).

#### Non-submodular counterexample (`|V|=3`, `k=2`) — ratio below `1 - 1/e`

- `greedy_sol = {A, C}`, `f_bad greedy_sol = 100`
- `opt_sol = {B, C}`, `f_bad opt_sol = 200`
- ratio (integer %) = `50`
- `greedy_f_evals = 10`
- `exhaustive_candidates = 7`
- plus a lemma giving an explicit witness that `f_bad` is not submodular.

This demonstrates that the classical approximation guarantee relies essentially on submodularity: once submodularity is dropped, greedy can fall below `1 - 1/e`.

---

## 3. Planned Next Steps

### 3.1 Baseline correctness lemmas (`enum_opt_set`)

Add short lemmas stating that `enum_opt_set` returns:
- a feasible set (`S ⊆ set Vlist` and `card S ≤ k`), and
- a maximiser over the finite feasible family.

### 3.2 Coverage as a locale interpretation

Introduce a locale `Coverage_Setup` (finite universe `U`, ground set `V`, mapping `g : V ⇒ Pow U`, budget `k`),
prove `f_cov(S) = card (⋃x∈S. g x)` satisfies `Greedy_Setup`, and instantiate the main theorem via `interpret`.

### 3.3 Documentation polish

- Add a brief “How to run experiments” section in `README.md`:
  - `isabelle build -D .`
  - `isabelle jedit -d . -l Submodular_Greedy_Experiments`
  - open the experiment theories and click `value ...` lines to view outputs in the Output panel.

## 2026-02-07 Update: P1 Experiments + Coverage Interpretation

### What’s new (concrete deliverables)
- **Executable baseline + counters (tiny instances)**:
  - Added a tiny exhaustive maximiser (`enum_opt_set`) over candidates `subseqs_upto_k Vlist k`, plus simple evaluation counters.
  - Added runnable toy instances comparing **greedy vs exhaustive** (value/ratio + basic oracle-call intuition).

- **Toy coverage instantiation connected to the abstract theorem layer**:
  - Defined `f_cov_real : Item set ⇒ real` from the toy coverage objective and proved (on `V = set Vlist`) the required facts:
    - `f_cov_real {} = 0`
    - monotonicity on subsets of `V`
    - submodularity on subsets of `V`
  - Interpreted the abstract locale as:
    - `CovToy: Greedy_Setup V f_cov_real k (Submodular_Func.argmax_gain_some f_cov_real)`
  - Exposed the instantiated Nemhauser–Wolsey guarantee as a named lemma:
    - `CovToy_main_bound` (derived from `CovToy.greedy_approximation`).

- **Non-submodular “assumption-violation” counterexample (debugging track)**:
  - Added a small non-submodular set function with an explicit witness and a tiny instance where greedy underperforms the true optimum by a visible margin (sanity-checking the necessity of assumptions).

### Key files
- `Coverage_Interpretation_Toy.thy` — coverage objective + locale interpretation + `CovToy_main_bound`.
- `Experiments_Exhaustive.thy` / `Experiments_Coverage_Example.thy` / `Experiments_Coverage_Suboptimal.thy` (and related experiment theories) — runnable greedy vs exhaustive comparisons.

### Next steps (if we want to tighten the story further)
- (Optional) Add a short note clarifying that the executable `greedy_list` layer is a runnable sanity check; a refinement proof connecting it to the abstract `greedy_set` can be future work.
- Add 1–2 more tiny hand-crafted instances (coverage + non-submodular) to illustrate trends (ratios + counts).
