theory Stochastic_Greedy_OracleCost
  imports "../Algorithms/Stochastic_Greedy"
          "../Core/Oracle_Cost"
          "../Proofs/Stochastic_Greedy_Uniform_WR_DeliverableA"
begin

section \<open>Oracle-cost bounds for StochasticGreedy\<close>

text \<open>
At the deterministic trace layer, each round evaluates marginal gains only on
the sampled candidate pool. Since the executable algorithm first collapses the
sample list to the set sampled_candidates (V - S) xs and then performs an
argmax over that set, the exact gain-evaluation count is tracked by
stoch_step_gain_evals / stoch_run_trace_gain_evals from Algorithms/Stochastic_Greedy.

This theory lifts those exact gain-evaluation bounds into paper-facing oracle
cost bounds using the cost model from Core/Oracle_Cost.
\<close>

definition stochastic_total_budget :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "stochastic_total_budget k s = k * s"

definition stochastic_total_oracle_budget :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "stochastic_total_oracle_budget k s = gain_call_cost * stochastic_total_budget k s"

lemma stochastic_total_budget_nonneg:
  "0 \<le> int (stochastic_total_budget k s)"
  unfolding stochastic_total_budget_def
  by simp

lemma stochastic_total_budget_unfold [simp]:
  "stochastic_total_budget k s = k * s"
  unfolding stochastic_total_budget_def
  by simp

lemma stochastic_total_oracle_budget_unfold [simp]:
  "stochastic_total_oracle_budget k s = gain_call_cost * k * s"
  unfolding stochastic_total_oracle_budget_def stochastic_total_budget_def
  by (simp add: mult.assoc)

context Cardinality_Constraint
begin

definition stoch_step_oracle_calls :: "'a set \<Rightarrow> 'a list \<Rightarrow> nat" where
  "stoch_step_oracle_calls S xs = gain_call_cost * stoch_step_gain_evals S xs"

definition stoch_run_trace_oracle_calls :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a list list \<Rightarrow> nat" where
  "stoch_run_trace_oracle_calls t S Rs =
     gain_call_cost * stoch_run_trace_gain_evals t S Rs"

definition stochastic_greedy_trace_oracle_calls :: "'a list list \<Rightarrow> nat" where
  "stochastic_greedy_trace_oracle_calls Rs =
     gain_call_cost * stochastic_greedy_trace_gain_evals Rs"

definition stochastic_eps_budget :: "real \<Rightarrow> nat" where
  "stochastic_eps_budget eps =
     stochastic_total_budget k (sample_size_eps_ceil eps)"

definition stochastic_eps_oracle_budget :: "real \<Rightarrow> nat" where
  "stochastic_eps_oracle_budget eps =
     stochastic_total_oracle_budget k (sample_size_eps_ceil eps)"

lemma stoch_step_oracle_calls_alt [simp]:
  "stoch_step_oracle_calls S xs = gain_call_cost * stoch_step_gain_evals S xs"
  unfolding stoch_step_oracle_calls_def
  by simp

lemma stoch_run_trace_oracle_calls_alt [simp]:
  "stoch_run_trace_oracle_calls t S Rs =
     gain_call_cost * stoch_run_trace_gain_evals t S Rs"
  unfolding stoch_run_trace_oracle_calls_def
  by simp

lemma stochastic_greedy_trace_oracle_calls_alt [simp]:
  "stochastic_greedy_trace_oracle_calls Rs =
     gain_call_cost * stochastic_greedy_trace_gain_evals Rs"
  unfolding stochastic_greedy_trace_oracle_calls_def
  by simp

lemma stochastic_eps_budget_unfold [simp]:
  "stochastic_eps_budget eps = k * sample_size_eps_ceil eps"
  unfolding stochastic_eps_budget_def
  by simp

lemma stochastic_eps_oracle_budget_unfold [simp]:
  "stochastic_eps_oracle_budget eps = gain_call_cost * k * sample_size_eps_ceil eps"
  unfolding stochastic_eps_oracle_budget_def
  by (simp add: mult.assoc)

subsection \<open>Per-step exact bounds\<close>

lemma stoch_step_oracle_calls_le:
  assumes "length xs \<le> s"
  shows "stoch_step_oracle_calls S xs \<le> gain_call_cost * s"
proof -
  have evals_le: "stoch_step_gain_evals S xs \<le> s"
    using stoch_step_gain_evals_le[OF assms] .
  have "gain_call_cost * stoch_step_gain_evals S xs \<le> gain_call_cost * s"
    using evals_le by (intro mult_left_mono) simp_all
  then show ?thesis
    unfolding stoch_step_oracle_calls_def .
qed

subsection \<open>Trace-level exact bounds\<close>

lemma stoch_run_trace_gain_evals_le_budget:
  assumes "trace_sample_bound s Rs"
  shows "stoch_run_trace_gain_evals t S Rs \<le> stochastic_total_budget t s"
  using stoch_run_trace_gain_evals_le[OF assms, of t S]
  unfolding stochastic_total_budget_def
  by simp

lemma stoch_run_trace_oracle_calls_le:
  assumes "trace_sample_bound s Rs"
  shows "stoch_run_trace_oracle_calls t S Rs \<le> gain_call_cost * t * s"
proof -
  have evals_le: "stoch_run_trace_gain_evals t S Rs \<le> t * s"
    using stoch_run_trace_gain_evals_le[OF assms, of t S] .
  have "gain_call_cost * stoch_run_trace_gain_evals t S Rs \<le> gain_call_cost * (t * s)"
    using evals_le by (intro mult_left_mono) simp_all
  then show ?thesis
    unfolding stoch_run_trace_oracle_calls_def
    by (simp add: mult.assoc)
qed

lemma stoch_run_trace_oracle_calls_le_budget:
  assumes "trace_sample_bound s Rs"
  shows "stoch_run_trace_oracle_calls t S Rs \<le> stochastic_total_oracle_budget t s"
  using stoch_run_trace_oracle_calls_le[OF assms, of t S]
  unfolding stochastic_total_oracle_budget_def stochastic_total_budget_def
  by (simp add: mult.assoc)

subsection \<open>Final k-step bounds\<close>

corollary stochastic_greedy_trace_gain_evals_le_budget:
  assumes "trace_sample_bound s Rs"
  shows "stochastic_greedy_trace_gain_evals Rs \<le> stochastic_total_budget k s"
  using stochastic_greedy_trace_gain_evals_le[OF assms]
  unfolding stochastic_total_budget_def
  by simp

corollary stochastic_greedy_trace_oracle_calls_le:
  assumes "trace_sample_bound s Rs"
  shows "stochastic_greedy_trace_oracle_calls Rs \<le> gain_call_cost * k * s"
proof -
  have evals_le: "stochastic_greedy_trace_gain_evals Rs \<le> k * s"
    using stochastic_greedy_trace_gain_evals_le[OF assms] .
  have "gain_call_cost * stochastic_greedy_trace_gain_evals Rs \<le> gain_call_cost * (k * s)"
    using evals_le by (intro mult_left_mono) simp_all
  then show ?thesis
    unfolding stochastic_greedy_trace_oracle_calls_def
    by (simp add: mult.assoc)
qed

corollary stochastic_greedy_trace_oracle_calls_le_budget:
  assumes "trace_sample_bound s Rs"
  shows "stochastic_greedy_trace_oracle_calls Rs \<le> stochastic_total_oracle_budget k s"
  using stochastic_greedy_trace_oracle_calls_le[OF assms]
  unfolding stochastic_total_oracle_budget_def stochastic_total_budget_def
  by (simp add: mult.assoc)

corollary stochastic_greedy_trace_gain_evals_le_size_budget:
  assumes "trace_sample_size s Rs"
  shows "stochastic_greedy_trace_gain_evals Rs \<le> stochastic_total_budget k s"
  using trace_sample_size_imp_bound[OF assms]
        stochastic_greedy_trace_gain_evals_le_budget
  by blast

corollary stochastic_greedy_trace_oracle_calls_le_size_budget:
  assumes "trace_sample_size s Rs"
  shows "stochastic_greedy_trace_oracle_calls Rs \<le> stochastic_total_oracle_budget k s"
  using trace_sample_size_imp_bound[OF assms]
        stochastic_greedy_trace_oracle_calls_le_budget
  by blast

subsection \<open>Epsilon-instantiated corollaries\<close>

corollary stochastic_greedy_trace_gain_evals_le_eps_budget:
  assumes "trace_sample_bound (sample_size_eps_ceil eps) Rs"
  shows "stochastic_greedy_trace_gain_evals Rs \<le> stochastic_eps_budget eps"
  using stochastic_greedy_trace_gain_evals_le_budget[OF assms]
  unfolding stochastic_eps_budget_def
  by simp

corollary stochastic_greedy_trace_oracle_calls_le_eps_budget:
  assumes "trace_sample_bound (sample_size_eps_ceil eps) Rs"
  shows "stochastic_greedy_trace_oracle_calls Rs \<le> stochastic_eps_oracle_budget eps"
  using stochastic_greedy_trace_oracle_calls_le_budget[OF assms]
  unfolding stochastic_eps_oracle_budget_def
  by simp

corollary stochastic_greedy_trace_gain_evals_le_eps_budget_size:
  assumes "trace_sample_size (sample_size_eps_ceil eps) Rs"
  shows "stochastic_greedy_trace_gain_evals Rs \<le> stochastic_eps_budget eps"
  using trace_sample_size_imp_bound[OF assms]
        stochastic_greedy_trace_gain_evals_le_eps_budget
  by blast

corollary stochastic_greedy_trace_oracle_calls_le_eps_budget_size:
  assumes "trace_sample_size (sample_size_eps_ceil eps) Rs"
  shows "stochastic_greedy_trace_oracle_calls Rs \<le> stochastic_eps_oracle_budget eps"
  using trace_sample_size_imp_bound[OF assms]
        stochastic_greedy_trace_oracle_calls_le_eps_budget
  by blast

end

end