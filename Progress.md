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
