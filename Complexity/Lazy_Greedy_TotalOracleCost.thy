theory Lazy_Greedy_TotalOracleCost
  imports Lazy_Greedy_OracleCost
begin

text \<open>
  Total oracle-cost bounds for the outer stateful lazy greedy loop.

  We lift the inner bound from Lazy_Greedy_OracleCost:
    - per-step gain evaluations \<le> card A
    - refined: per-step gain evaluations \<le> card (untight \<dots>) + 1
  to bounds over m outer iterations.

  The stateful algorithm is defined in Algorithms/Lazy_Greedy_Stateful:
    lazy_state 0 = init_state
    lazy_state (Suc i) = lazy_step (lazy_state i)
  and each non-empty outer step calls lazy_select on A = remaining st.
\<close>

context Cardinality_Constraint
begin

subsection \<open>Per-step costs\<close>

definition step_gain_evals :: "nat \<Rightarrow> nat" where
  "step_gain_evals i =
     (let st = lazy_state i; A = remaining st in
        if A = {} then 0 else lazy_select_gain_evals (Sg st) A (ubg st))"

definition step_tighten_steps :: "nat \<Rightarrow> nat" where
  "step_tighten_steps i =
     (let st = lazy_state i; A = remaining st; ub = ubg st in
        if A = {} then 0 else lazy_tighten_steps_fuel (card A) (Sg st) A ub)"

lemma remaining_subset_V: "remaining (lazy_state i) \<subseteq> V"
  by (simp add: remaining_def lazy_set_def)

lemma finite_remaining: "finite (remaining (lazy_state i))"
  using finite_V remaining_subset_V by (meson finite_subset)

lemma step_gain_evals_le_cardV:
  "step_gain_evals i \<le> card V"
proof -
  let ?st = "lazy_state i"
  let ?A  = "remaining ?st"
  show ?thesis
  proof (cases "?A = {}")
    case True
    thus ?thesis
      by (simp add: step_gain_evals_def Let_def)
  next
    case False
    have inner: "lazy_select_gain_evals (Sg ?st) ?A (ubg ?st) \<le> card ?A"
      using lazy_select_gain_evals_le_cardA by simp
    have A_le_V: "card ?A \<le> card V"
      using finite_V remaining_subset_V by (rule card_mono)
    show ?thesis
      using inner A_le_V False
      by (simp add: step_gain_evals_def Let_def le_trans)
  qed
qed

subsection \<open>Total costs over m outer steps\<close>

fun total_gain_evals :: "nat \<Rightarrow> nat" where
  "total_gain_evals 0 = 0"
| "total_gain_evals (Suc m) = total_gain_evals m + step_gain_evals m"

fun total_tighten_steps :: "nat \<Rightarrow> nat" where
  "total_tighten_steps 0 = 0"
| "total_tighten_steps (Suc m) = total_tighten_steps m + step_tighten_steps m"

lemma total_gain_evals_le_m_cardV:
  "total_gain_evals m \<le> m * card V"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have step: "step_gain_evals m \<le> card V"
    using step_gain_evals_le_cardV by simp
  have "total_gain_evals (Suc m)
        = total_gain_evals m + step_gain_evals m"
    by simp
  also have "\<dots> \<le> (m * card V) + card V"
    using Suc.IH step by simp
  also have "\<dots> = (Suc m) * card V"
    by simp
  finally show ?case .
qed

definition total_oracle_calls :: "nat \<Rightarrow> nat" where
  "total_oracle_calls m = gain_call_cost * total_gain_evals m"

lemma total_oracle_calls_le_m_cardV:
  "total_oracle_calls m \<le> gain_call_cost * (m * card V)"
proof -
  have "gain_call_cost * total_gain_evals m \<le> gain_call_cost * (m * card V)"
    using total_gain_evals_le_m_cardV by (simp add: mult_left_mono)
  thus ?thesis
    by (simp add: total_oracle_calls_def)
qed

subsection \<open>Refined (potential-style) bound via untight\<close>

definition step_gain_bound_untight :: "nat \<Rightarrow> nat" where
  "step_gain_bound_untight i =
     (let st = lazy_state i; A = remaining st; ub = ubg st in
        if A = {} then 0 else card (untight (Sg st) A ub) + 1)"

lemma step_gain_evals_le_untight_plus1:
  "step_gain_evals i \<le> step_gain_bound_untight i"
proof -
  let ?st = "lazy_state i"
  let ?A  = "remaining ?st"
  let ?S  = "Sg ?st"
  let ?ub = "ubg ?st"
  show ?thesis
  proof (cases "?A = {}")
    case True
    thus ?thesis
      by (simp add: step_gain_evals_def step_gain_bound_untight_def Let_def)
  next
    case False
    have finA: "finite ?A" using finite_remaining by simp
    have ubv: "ub_valid ?S ?A ?ub"
      using lazy_state_ub_valid[of i] by simp
    have inner:
      "lazy_select_gain_evals ?S ?A ?ub \<le> card (untight ?S ?A ?ub) + 1"
      using lazy_select_gain_evals_le_card_untight_plus1[OF finA False ubv] .
    thus ?thesis
      using False
      by (simp add: step_gain_evals_def step_gain_bound_untight_def Let_def)
  qed
qed

lemma total_gain_evals_le_sum_untight:
  "total_gain_evals m \<le> (\<Sum> i < m. step_gain_bound_untight i)"
proof (induction m)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have step: "step_gain_evals m \<le> step_gain_bound_untight m"
    using step_gain_evals_le_untight_plus1 by simp
  have "total_gain_evals (Suc m) = total_gain_evals m + step_gain_evals m"
    by simp
  also have "\<dots> \<le> (\<Sum> i < m. step_gain_bound_untight i) + step_gain_bound_untight m"
    using Suc.IH step by simp
  also have "\<dots> = (\<Sum> i < Suc m. step_gain_bound_untight i)"
    by simp
  finally show ?case .
qed

end

end