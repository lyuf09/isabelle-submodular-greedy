# Progress

## 2025-12-30

- Added a new `Submodular_Base.thy` to modularise the core submodular setting
  (`Submodular_Setup` locale) and the marginal gain definition `gain`.
- Added auxiliary lemmas aligning the monotonicity assumption with the standard
  library (`monotone_on (Pow V) (⊆) (≤) f`) and a basic non-negativity fact for gains.
- Refactored `Greedy_Submodular_Construct.thy` to build on the new base locale.
- Refactored `Greedy_Submodular_Approx.thy` accordingly (work in progress) to reduce
  duplicated assumptions and reuse the shared setup.
- Added a DR-style (diminishing returns) definition of submodularity, without yet
  proving equivalence to the standard definition.


## 2025-12-31

- Clarified and stabilised the locale architecture around `Submodular_Func` and `Cardinality_Constraint`, including proper scoping of assumptions, definitions, and derived lemmas, and avoiding leakage of assumptions across locales.
-Systematically refactored the greedy construction layer to remove over-strong or redundant existential assumptions (e.g. eliminating `argmax_gain_exists`) and replace them with a clean `argmax_gain_some` choice-based interface compatible with Isabelle’s logic.
-Resolved multiple structural issues related to `locale`, `context`, and `interpretation` usage, including:
 -correct placement of `context … begin … end` blocks,
 -understanding when `interpretation` is legal and when it leads to type-class or type-variable clashes,
 -identifying and fixing implicit type mismatches caused by unconstrained schematic variables.
-Reworked greedy step lemmas (`greedy_increment_nonempty`, state transition lemmas, etc.) to:
 -avoid fragile rewrites,
 -rely only on set-theoretic facts (`V - S ≠ {} ↔ ¬ V ⊆ S`),
 -make the control flow of the greedy definition explicit and robust under simplification.
-Isolated and fixed recurring proof failures caused by definitional mismatches (e.g. `insert x S` vs `S ∪ {x}`, `V ⊆ S` vs `V - S = {}`), ensuring all greedy transition lemmas simplify cleanly with `simp` rather than ad-hoc tactics.
-Cleaned up auxiliary lemmas about element selection and membership, ensuring that:
 -membership facts (`x ∈ V - S`, `x ∉ S`) are derived in a minimal and locale-compatible way,
 -no hidden finiteness or maximality assumptions are introduced implicitly.
-Improved overall proof robustness and maintainability, reducing “red zones” and brittle proof steps, and aligning the development more closely with Isabelle best practices for large structured formalizations.
