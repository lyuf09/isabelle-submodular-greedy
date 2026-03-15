theory Stochastic_Greedy_Expected_OneStep
  imports Stochastic_Greedy_OneStep Stochastic_Greedy_Weighted_Sampling
begin

section \<open>Expected one-step gain for weighted sampling models\<close>

text \<open>
This theory adds a first expectation layer on top of the deterministic
one-step bridge from Stochastic_Greedy_OneStep and the weighted sampling
interface from Stochastic_Greedy_Weighted_Sampling.

At the current level of abstraction we can already prove:
  • a weighted expected-gain decomposition over hit / miss events;
  • a lower bound by the weighted average of hit-pool average gains;
  • a reusable template of the form
      expected_step_gain \<ge> hit_prob_of \<times> c,
    provided one has a pointwise lower bound c on all hit-event average gains.

The final bridge that turns c into the average gain over the full residual
optimal set is intentionally left to a later theory.
\<close>

context Stochastic_Greedy_Weighted_Sampling
begin

definition sampled_step_gain :: "'a set \<Rightarrow> 'a list \<Rightarrow> real" where
  "sampled_step_gain S xs =
     (let A = sampled_candidates (V - S) xs in
      if A = {} then 0 else gain S (argmax_gain_on S A))"

definition expected_step_gain :: "'a set \<Rightarrow> nat \<Rightarrow> real" where
  "expected_step_gain S s =
     (\<Sum>xs\<in>sample_space S s. sample_prob S s xs * sampled_step_gain S xs)"

lemma sampled_step_gain_zero_if_empty:
  assumes "sampled_candidates (V - S) xs = {}"
  shows "sampled_step_gain S xs = 0"
  using assms
  unfolding sampled_step_gain_def
  by (simp add: Let_def)

lemma sampled_step_gain_eq_if_nonempty:
  assumes "sampled_candidates (V - S) xs \<noteq> {}"
  shows "sampled_step_gain S xs = gain S (sampled_argmax S xs)"
  using assms
  unfolding sampled_step_gain_def sampled_argmax_def
  by (simp add: Let_def)

lemma sampled_step_gain_eq_if_hit:
  assumes hit: "hits_residual OPT S xs"
  shows "sampled_step_gain S xs = gain S (sampled_argmax S xs)"
  by (rule sampled_step_gain_eq_if_nonempty[OF hits_residual_imp_sample_nonempty[OF hit]])

lemma sampled_step_gain_nonneg:
  assumes hS: "S \<subseteq> V"
      and hxs: "xs \<in> sample_space S s"
  shows "0 \<le> sampled_step_gain S xs"
proof (cases "sampled_candidates (V - S) xs = {}")
  case True
  then show ?thesis
    unfolding sampled_step_gain_def
    by (simp add: Let_def)
next
  case False
  let ?A = "sampled_candidates (V - S) xs"
  have chosen_in_A: "argmax_gain_on S ?A \<in> ?A"
    using argmax_gain_on_mem[OF finite_sampled_candidates False] .
  then have chosen_in_rem: "argmax_gain_on S ?A \<in> V - S"
    unfolding sampled_candidates_def
    by auto
  have "0 \<le> gain S (argmax_gain_on S ?A)"
    using gain_nonneg[OF hS chosen_in_rem] .
  then show ?thesis
    unfolding sampled_step_gain_def
    using False
    by (simp add: Let_def)
qed

lemma expected_step_gain_nonneg:
  assumes hS: "S \<subseteq> V"
  shows "0 \<le> expected_step_gain S s"
  unfolding expected_step_gain_def
proof (rule sum_nonneg)
  fix xs
  assume hxs: "xs \<in> sample_space S s"
  have "0 \<le> sample_prob S s xs"
    using sample_prob_nonneg[OF hxs] .
  moreover have "0 \<le> sampled_step_gain S xs"
    using sampled_step_gain_nonneg[OF hS hxs] .
  ultimately show "0 \<le> sample_prob S s xs * sampled_step_gain S xs"
    by simp
qed

lemma sampled_step_gain_ge_avg_residual_hit:
  assumes hit: "xs \<in> hit_event OPT S s"
  shows "sampled_step_gain S xs
         \<ge> avg_gain_on S (residual_hit_pool OPT S xs)"
proof -
  have hit_res: "hits_residual OPT S xs"
    using hit unfolding hit_event_def by auto
  have "sampled_step_gain S xs = gain S (sampled_argmax S xs)"
    by (rule sampled_step_gain_eq_if_hit[OF hit_res])
  also have "... \<ge> avg_gain_on S (residual_hit_pool OPT S xs)"
    using sampled_argmax_ge_avg_residual_hit[OF hit_res] .
  finally show ?thesis .
qed

lemma expected_step_gain_split_hit_miss:
  "expected_step_gain S s =
     (\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs * sampled_step_gain S xs) +
     (\<Sum>xs\<in>miss_event OPT S s. sample_prob S s xs * sampled_step_gain S xs)"
proof -
  have
    "(\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs * sampled_step_gain S xs) +
     (\<Sum>xs\<in>miss_event OPT S s. sample_prob S s xs * sampled_step_gain S xs)
     =
     (\<Sum>xs\<in>hit_event OPT S s \<union> miss_event OPT S s.
        sample_prob S s xs * sampled_step_gain S xs)"
    using hit_miss_disjoint
    by (simp add: sum.union_disjoint)
  also have
    "... =
     (\<Sum>xs\<in>sample_space S s. sample_prob S s xs * sampled_step_gain S xs)"
    using hit_miss_union by simp
  finally show ?thesis
    unfolding expected_step_gain_def
    by simp
qed

lemma expected_step_gain_ge_hit_weighted_avg:
  assumes hS: "S \<subseteq> V"
  shows "expected_step_gain S s
         \<ge> (\<Sum>xs\<in>hit_event OPT S s.
              sample_prob S s xs * avg_gain_on S (residual_hit_pool OPT S xs))"
proof -
  have split:
    "expected_step_gain S s =
       (\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs * sampled_step_gain S xs) +
       (\<Sum>xs\<in>miss_event OPT S s. sample_prob S s xs * sampled_step_gain S xs)"
    by (rule expected_step_gain_split_hit_miss)

  have miss_nonneg:
    "0 \<le> (\<Sum>xs\<in>miss_event OPT S s. sample_prob S s xs * sampled_step_gain S xs)"
  proof (rule sum_nonneg)
    fix xs
    assume hxs: "xs \<in> miss_event OPT S s"
    then have xs_space: "xs \<in> sample_space S s"
      using miss_event_memD by blast
    have "0 \<le> sample_prob S s xs"
      using sample_prob_nonneg[OF xs_space] .
    moreover have "0 \<le> sampled_step_gain S xs"
      using sampled_step_gain_nonneg[OF hS xs_space] .
    ultimately show "0 \<le> sample_prob S s xs * sampled_step_gain S xs"
      by simp
  qed

  have hit_mono:
    "(\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs * avg_gain_on S (residual_hit_pool OPT S xs))
     \<le>
     (\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs * sampled_step_gain S xs)"
  proof (rule sum_mono)
    fix xs
    assume hxs: "xs \<in> hit_event OPT S s"
    have p_nonneg: "0 \<le> sample_prob S s xs"
      using hxs hit_event_memD sample_prob_nonneg by blast
    have avg_le_gain:
      "avg_gain_on S (residual_hit_pool OPT S xs) \<le> sampled_step_gain S xs"
      using sampled_step_gain_ge_avg_residual_hit[OF hxs] .
    show "sample_prob S s xs * avg_gain_on S (residual_hit_pool OPT S xs)
          \<le> sample_prob S s xs * sampled_step_gain S xs"
      using mult_left_mono[OF avg_le_gain p_nonneg] .
  qed

    have h1:
      "expected_step_gain S s
        \<ge> (\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs * sampled_step_gain S xs)"
      using split miss_nonneg
      by linarith

    have h2:
      "(\<Sum>xs\<in>hit_event OPT S s.
          sample_prob S s xs * avg_gain_on S (residual_hit_pool OPT S xs))
       \<le>
       (\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs * sampled_step_gain S xs)"
      using hit_mono .

    from h1 h2 show ?thesis
      by linarith
  qed

lemma expected_step_gain_ge_hit_prob_times_c:
  assumes hS: "S \<subseteq> V"
      and hc: "0 \<le> c"
      and c_lower:
        "\<And>xs. xs \<in> hit_event OPT S s
              \<Longrightarrow> c \<le> avg_gain_on S (residual_hit_pool OPT S xs)"
  shows "expected_step_gain S s \<ge> hit_prob_of OPT S s * c"
proof -
  have base:
    "expected_step_gain S s
      \<ge> (\<Sum>xs\<in>hit_event OPT S s.
           sample_prob S s xs * avg_gain_on S (residual_hit_pool OPT S xs))"
    using expected_step_gain_ge_hit_weighted_avg[OF hS] .

  have hit_to_c:
    "(\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs * c)
     \<le>
     (\<Sum>xs\<in>hit_event OPT S s.
        sample_prob S s xs * avg_gain_on S (residual_hit_pool OPT S xs))"
  proof (rule sum_mono)
    fix xs
    assume hxs: "xs \<in> hit_event OPT S s"
    have p_nonneg: "0 \<le> sample_prob S s xs"
      using hxs hit_event_memD sample_prob_nonneg by blast
    have c_le:
      "c \<le> avg_gain_on S (residual_hit_pool OPT S xs)"
      using c_lower[OF hxs] .
    have "sample_prob S s xs * c = c * sample_prob S s xs"
      by (simp add: mult.commute)
    also have "... \<le> avg_gain_on S (residual_hit_pool OPT S xs) * sample_prob S s xs"
      using mult_right_mono[OF c_le p_nonneg] .
    also have "... = sample_prob S s xs * avg_gain_on S (residual_hit_pool OPT S xs)"
      by (simp add: mult.commute)
    finally show
      "sample_prob S s xs * c
       \<le> sample_prob S s xs * avg_gain_on S (residual_hit_pool OPT S xs)" .
  qed

  have const_sum:
    "(\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs * c) = hit_prob_of OPT S s * c"
  proof -
    have "(\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs * c)
        = (\<Sum>xs\<in>hit_event OPT S s. c * sample_prob S s xs)"
      by (simp add: mult.commute)
    also have "... = c * (\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs)"
      by (simp add: sum_distrib_left)
    also have "... = hit_prob_of OPT S s * c"
      unfolding hit_prob_of_def
      by (simp add: mult.commute)
    finally show ?thesis .
  qed

  have hmain:
    "expected_step_gain S s
      \<ge> (\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs * c)"
    using base hit_to_c
    by linarith

  from hmain const_sum show ?thesis
    by simp
qed

end

context Stochastic_Greedy_Weighted_Hit_Model
begin

theorem expected_step_gain_ge_hit_lb_linear_times_c:
  assumes hOPT: "OPT \<subseteq> V"
      and hfin: "finite OPT"
      and hcard: "card OPT \<le> k"
      and hS: "S \<subseteq> V"
      and hc: "0 \<le> c"
      and c_lower:
        "\<And>xs. xs \<in> hit_event OPT S s
              \<Longrightarrow> c \<le> avg_gain_on S (residual_hit_pool OPT S xs)"
  shows "expected_step_gain S s
         \<ge> hit_lb_linear s (residual_card OPT S) * c"
proof -
  have step_ge_hit:
    "expected_step_gain S s \<ge> hit_prob_of OPT S s * c"
    using expected_step_gain_ge_hit_prob_times_c[OF hS hc c_lower] .

  have hit_ge_lb:
    "hit_prob_of OPT S s \<ge> hit_lb_linear s (residual_card OPT S)"
    using hit_prob_of_linear_lower[OF hOPT hfin hcard hS] .

  have "hit_prob_of OPT S s * c \<ge> hit_lb_linear s (residual_card OPT S) * c"
    using mult_right_mono[OF hit_ge_lb hc] .

  with step_ge_hit show ?thesis
    by linarith
qed

end

end