theory Stochastic_Greedy_OracleCost
  imports "../Algorithms/Stochastic_Greedy"
          "../Core/Oracle_Cost"
          "../Proofs/Stochastic_Greedy_Sampling"
begin

section \<open>Oracle-cost skeleton for StochasticGreedy\<close>

text \<open>
At the executable level, the stochastic algorithm only evaluates gains on the
sampled pool of each round. The exact per-run accounting will be added later.
For now we record the paper-facing sample-size formulas and the coarse k \<cdot> s
budget that should drive the eventual cost theorem.
\<close>

definition stochastic_total_budget :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "stochastic_total_budget k s = k * s"

lemma stochastic_total_budget_nonneg:
  "0 \<le> int (stochastic_total_budget k s)"
  unfolding stochastic_total_budget_def by simp

context Cardinality_Constraint
begin

definition stochastic_eps_budget :: "real \<Rightarrow> nat" where
  "stochastic_eps_budget eps = stochastic_total_budget k (sample_size_eps eps)"

lemma stochastic_total_budget_unfold:
  "stochastic_total_budget k s = k * s"
  unfolding stochastic_total_budget_def by simp

lemma stochastic_eps_budget_unfold:
  "stochastic_eps_budget eps = k * sample_size_eps eps"
  unfolding stochastic_eps_budget_def stochastic_total_budget_def by simp

end

end