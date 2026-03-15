theory Stochastic_Greedy_Gap_Bridge
  imports Stochastic_Greedy_Approx
begin

section \<open>Abstract gap bridge for StochasticGreedy\<close>

text \<open>
This theory isolates the remaining bridge between the expected one-step lower
bound from theory Stochastic_Greedy_Expected_OneStep and the recurrence
solver from theory Stochastic_Greedy_Approx.

The purpose of this file is not yet to prove the concrete combinatorial bridge
for a specific sampling model. Instead, it packages the exact abstract
assumptions under which the final stochastic gap recurrence and the resulting
closed-form approximation bound follow.
\<close>

locale Stochastic_Greedy_Gap_Bridge =
  Stochastic_Greedy_Weighted_Hit_Model V f k sample_space sample_prob
  for V :: "'a set" and f :: "'a set \<Rightarrow> real" and k :: nat
    and sample_space :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set"
    and sample_prob :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> real" +
  fixes OPT :: "'a set"
    and s :: nat
    and State :: "nat \<Rightarrow> 'a set"
    and Gap :: "nat \<Rightarrow> real"
    and c_at :: "nat \<Rightarrow> real"
    and OPT_bound :: real
  assumes OPT_subset: "OPT \<subseteq> V"
      and OPT_finite: "finite OPT"
      and OPT_card: "card OPT \<le> k"
      and k_pos: "0 < k"
      and alpha_nonneg: "0 \<le> alpha_stoch s"
      and alpha_le_k: "alpha_stoch s \<le> real k"
      and state_subset: "\<And>i. State i \<subseteq> V"
      and gap_nonneg: "\<And>i. 0 \<le> Gap i"
      and gap_init: "Gap 0 \<le> OPT_bound"
      and opt_bound_nonneg: "0 \<le> OPT_bound"
      and gap_step_eq: "\<And>i. Gap (Suc i) = Gap i - expected_step_gain (State i) s"
      and c_nonneg: "\<And>i. 0 \<le> c_at i"
      and c_lower_hit:
        "\<And>i xs. xs \<in> hit_event OPT (State i) s
               \<Longrightarrow> c_at i \<le> avg_gain_on (State i) (residual_hit_pool OPT (State i) xs)"
      and hit_lb_ge_alpha:
        "\<And>i. alpha_stoch s \<le> hit_lb_linear s (residual_card OPT (State i))"
      and c_ge_gap_over_k:
        "\<And>i. Gap i / real k \<le> c_at i"
begin

lemma expected_step_gain_ge_alpha_times_c:
  "expected_step_gain (State i) s \<ge> alpha_stoch s * c_at i"
proof -
  have step_ge_lb:
    "expected_step_gain (State i) s
      \<ge> hit_lb_linear s (residual_card OPT (State i)) * c_at i"
  proof (rule expected_step_gain_ge_hit_lb_linear_times_c
              [where OPT = OPT and S = "State i" and s = s and c = "c_at i"])
    show "OPT \<subseteq> V"
      by (rule OPT_subset)
    show "finite OPT"
      by (rule OPT_finite)
    show "card OPT \<le> k"
      by (rule OPT_card)
    show "State i \<subseteq> V"
      by (rule state_subset)
    show "0 \<le> c_at i"
      by (rule c_nonneg)
    fix xs
    assume hxs: "xs \<in> hit_event OPT (State i) s"
    show "c_at i \<le> avg_gain_on (State i) (residual_hit_pool OPT (State i) xs)"
      using c_lower_hit[where i = i and xs = xs] hxs
      by simp
  qed

  have alpha_times_c_le:
    "alpha_stoch s * c_at i
      \<le> hit_lb_linear s (residual_card OPT (State i)) * c_at i"
    using mult_right_mono[OF hit_lb_ge_alpha[of i] c_nonneg[of i]] .

  from step_ge_lb alpha_times_c_le show ?thesis
    by linarith
qed

lemma expected_step_gain_ge_alpha_over_k_gap:
  "expected_step_gain (State i) s \<ge> (alpha_stoch s / real k) * Gap i"
proof -
  have step_ge_alpha_c:
    "expected_step_gain (State i) s \<ge> alpha_stoch s * c_at i"
    by (rule expected_step_gain_ge_alpha_times_c)

  have scaled_gap_le:
    "(alpha_stoch s / real k) * Gap i \<le> alpha_stoch s * c_at i"
  proof -
    have h1:
      "alpha_stoch s * (Gap i / real k) \<le> alpha_stoch s * c_at i"
      using mult_left_mono[OF c_ge_gap_over_k[of i] alpha_nonneg] .

    have h2:
      "(alpha_stoch s / real k) * Gap i = alpha_stoch s * (Gap i / real k)"
      using k_pos
      by (simp add: field_simps)

    from h1 h2 show ?thesis
      by simp
  qed

  from step_ge_alpha_c scaled_gap_le show ?thesis
    by linarith
qed

lemma gap_recurrence:
  "Gap (Suc i) \<le> (1 - alpha_stoch s / real k) * Gap i"
proof -
  have "Gap (Suc i) = Gap i - expected_step_gain (State i) s"
    using gap_step_eq[of i] .

  also have "... \<le> (1 - alpha_stoch s / real k) * Gap i"
    by (rule one_step_progress_to_gap_contraction[
              OF k_pos alpha_le_k gap_nonneg[of i] expected_step_gain_ge_alpha_over_k_gap[of i]])

  finally show ?thesis .
qed

theorem gap_closed_form:
  "Gap i \<le> stoch_gap_factor s i * OPT_bound"
  by (rule stochastic_approx_from_gap_recurrence[
            where Gap = Gap and s = s and OPT = OPT_bound and i = i,
            OF k_pos alpha_le_k alpha_nonneg gap_init gap_recurrence opt_bound_nonneg])

theorem value_lower_bound_from_gap:
  fixes Value :: "nat \<Rightarrow> real"
  assumes value_gap_eq: "Value i = OPT_bound - Gap i"
  shows "Value i \<ge> (1 - stoch_gap_factor s i) * OPT_bound"
proof -
  have hgap: "Gap i \<le> stoch_gap_factor s i * OPT_bound"
    by (rule gap_closed_form)

  have h1: "Value i = OPT_bound - Gap i"
    using value_gap_eq .

  have h2: "Value i \<ge> OPT_bound - stoch_gap_factor s i * OPT_bound"
    using h1 hgap
    by linarith

  have h3: "OPT_bound - stoch_gap_factor s i * OPT_bound
            = (1 - stoch_gap_factor s i) * OPT_bound"
    by (simp add: algebra_simps)

  from h2 h3 show ?thesis
    by linarith
qed

end

end