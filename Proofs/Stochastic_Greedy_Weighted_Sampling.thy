theory Stochastic_Greedy_Weighted_Sampling
  imports Stochastic_Greedy_Sampling
begin

section \<open>Concrete finite weighted sampling models\<close>

text \<open>
This theory refines the abstract hit-probability layer from
Stochastic_Greedy_Sampling into a concrete finite weighted sampling model.

At this stage we only introduce the concrete objects and their most basic
structural properties. Probability inequalities and interpretations back into
the abstract hit-model interface are deferred to later stages.
\<close>

locale Stochastic_Greedy_Weighted_Sampling =
  Cardinality_Constraint V f k
  for V :: "'a set" and f :: "'a set \<Rightarrow> real" and k :: nat +
  fixes sample_space :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set"
    and sample_prob  :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> real"
  assumes finite_sample_space:
    "finite (sample_space S s)"
  assumes sample_space_mem:
    "xs \<in> sample_space S s \<Longrightarrow> length xs = s \<and> set xs \<subseteq> V - S"
  assumes sample_prob_nonneg:
    "xs \<in> sample_space S s \<Longrightarrow> 0 \<le> sample_prob S s xs"
  assumes sample_mass_1:
    "(\<Sum>xs\<in>sample_space S s. sample_prob S s xs) = 1"
begin

definition hit_event :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a list set" where
  "hit_event OPT S s = {xs. xs \<in> sample_space S s \<and> hits_residual OPT S xs}"

definition miss_event :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a list set" where
  "miss_event OPT S s = {xs. xs \<in> sample_space S s \<and> misses_residual OPT S xs}"

definition hit_prob_of :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> real" where
  "hit_prob_of OPT S s =
     (\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs)"

definition miss_prob_of :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> real" where
  "miss_prob_of OPT S s =
     (\<Sum>xs\<in>miss_event OPT S s. sample_prob S s xs)"

lemma sample_space_mem_length:
  assumes "xs \<in> sample_space S s"
  shows "length xs = s"
  using assms sample_space_mem by auto

lemma sample_space_mem_subset:
  assumes "xs \<in> sample_space S s"
  shows "set xs \<subseteq> V - S"
  using assms sample_space_mem by auto

lemma hit_event_memD:
  assumes "xs \<in> hit_event OPT S s"
  shows "xs \<in> sample_space S s"
  using assms
  unfolding hit_event_def
  by auto

lemma miss_event_memD:
  assumes "xs \<in> miss_event OPT S s"
  shows "xs \<in> sample_space S s"
  using assms
  unfolding miss_event_def
  by blast

lemma finite_hit_event [simp]:
  "finite (hit_event OPT S s)"
proof -
  have "hit_event OPT S s \<subseteq> sample_space S s"
    using hit_event_memD by blast
  then show ?thesis
    using finite_sample_space finite_subset by blast
qed

lemma finite_miss_event [simp]:
  "finite (miss_event OPT S s)"
proof -
  have "miss_event OPT S s \<subseteq> sample_space S s"
    using miss_event_memD by blast
  then show ?thesis
    using finite_sample_space finite_subset by blast
qed

lemma hit_event_iff:
  "xs \<in> hit_event OPT S s \<longleftrightarrow> xs \<in> sample_space S s \<and> hits_residual OPT S xs"
  unfolding hit_event_def
  by auto

lemma miss_event_iff:
  "xs \<in> miss_event OPT S s \<longleftrightarrow> xs \<in> sample_space S s \<and> misses_residual OPT S xs"
  unfolding miss_event_def by auto

lemma hit_event_subset_sample_space:
  "hit_event OPT S s \<subseteq> sample_space S s"
  using hit_event_memD by blast

lemma miss_event_subset_sample_space:
  "miss_event OPT S s \<subseteq> sample_space S s"
  using miss_event_memD by blast

lemma hit_miss_disjoint:
  "hit_event OPT S s \<inter> miss_event OPT S s = {}"
  unfolding hit_event_def miss_event_def
            hits_residual_def misses_residual_def
  by auto

lemma hit_miss_union:
  "hit_event OPT S s \<union> miss_event OPT S s = sample_space S s"
  unfolding hit_event_def miss_event_def
            hits_residual_def misses_residual_def
  by auto

lemma miss_event_eq_diff_hit:
  "miss_event OPT S s = sample_space S s - hit_event OPT S s"
  using hit_miss_union hit_miss_disjoint by blast

lemma hit_event_eq_diff_miss:
  "hit_event OPT S s = sample_space S s - miss_event OPT S s"
  using hit_miss_union hit_miss_disjoint by blast

lemma hit_prob_of_nonneg:
  "0 \<le> hit_prob_of OPT S s"
  unfolding hit_prob_of_def
proof (rule sum_nonneg)
  fix xs
  assume "xs \<in> hit_event OPT S s"
  then show "0 \<le> sample_prob S s xs"
    using hit_event_memD sample_prob_nonneg by blast
qed

lemma miss_prob_of_nonneg:
  "0 \<le> miss_prob_of OPT S s"
  unfolding miss_prob_of_def
proof (rule sum_nonneg)
  fix xs
  assume "xs \<in> miss_event OPT S s"
  then show "0 \<le> sample_prob S s xs"
    using miss_event_memD sample_prob_nonneg by blast
qed

lemma hit_prob_of_plus_miss_prob_of:
  "hit_prob_of OPT S s + miss_prob_of OPT S s = 1"
proof -
  have
    "(\<Sum>xs\<in>hit_event OPT S s. sample_prob S s xs) +
     (\<Sum>xs\<in>miss_event OPT S s. sample_prob S s xs)
     = (\<Sum>xs\<in>hit_event OPT S s \<union> miss_event OPT S s. sample_prob S s xs)"
    using hit_miss_disjoint
    by (simp add: sum.union_disjoint)

  also have
    "... = (\<Sum>xs\<in>sample_space S s. sample_prob S s xs)"
    using hit_miss_union by simp

  also have
    "... = 1"
    using sample_mass_1 by simp

  finally show ?thesis
    unfolding hit_prob_of_def miss_prob_of_def .
qed

lemma hit_prob_of_eq_1_minus_miss_prob_of:
  "hit_prob_of OPT S s = 1 - miss_prob_of OPT S s"
  using hit_prob_of_plus_miss_prob_of[of OPT S s]
  by simp

lemma miss_prob_of_eq_1_minus_hit_prob_of:
  "miss_prob_of OPT S s = 1 - hit_prob_of OPT S s"
  using hit_prob_of_plus_miss_prob_of[of OPT S s]
  by (simp add: add.commute)

lemma hit_prob_of_le_1:
  "hit_prob_of OPT S s \<le> 1"
proof -
  have "hit_prob_of OPT S s = 1 - miss_prob_of OPT S s"
    using hit_prob_of_plus_miss_prob_of[of OPT S s]
    by simp
  also have "... \<le> 1"
    using miss_prob_of_nonneg[of OPT S s]
    by simp
  finally show ?thesis .
qed

lemma miss_prob_of_le_1:
  "miss_prob_of OPT S s \<le> 1"
proof -
  have "miss_prob_of OPT S s = 1 - hit_prob_of OPT S s"
    using hit_prob_of_plus_miss_prob_of[of OPT S s]
    by (simp add: add.commute)
  also have "... \<le> 1"
    using hit_prob_of_nonneg[of OPT S s]
    by simp
  finally show ?thesis .
qed

lemma hit_prob_of_bounds:
  "0 \<le> hit_prob_of OPT S s \<and> hit_prob_of OPT S s \<le> 1"
  using hit_prob_of_nonneg hit_prob_of_le_1 by auto

lemma miss_prob_of_bounds:
  "0 \<le> miss_prob_of OPT S s \<and> miss_prob_of OPT S s \<le> 1"
  using miss_prob_of_nonneg miss_prob_of_le_1 by auto

lemma hit_prob_of_lower_zero:
  "0 \<le> hit_prob_of OPT S s"
  using hit_prob_of_nonneg by simp

lemma hit_prob_of_upper_one:
  "hit_prob_of OPT S s \<le> 1"
  using hit_prob_of_le_1 by simp

end

locale Stochastic_Greedy_Weighted_Hit_Model =
  Stochastic_Greedy_Weighted_Sampling V f k sample_space sample_prob
  for V :: "'a set" and f :: "'a set \<Rightarrow> real" and k :: nat
    and sample_space :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set"
    and sample_prob  :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> real" +
  assumes hit_prob_of_linear_lower:
    "OPT \<subseteq> V \<Longrightarrow> finite OPT \<Longrightarrow> card OPT \<le> k \<Longrightarrow> S \<subseteq> V
      \<Longrightarrow> hit_prob_of OPT S s \<ge> hit_lb_linear s (residual_card OPT S)"
begin

sublocale weighted_hit: Stochastic_Greedy_Hit_Model V f k hit_prob_of
proof
  fix OPT S s
  show "0 \<le> hit_prob_of OPT S s"
    by (rule hit_prob_of_nonneg)
next
  fix OPT S s
  show "hit_prob_of OPT S s \<le> 1"
    by (rule hit_prob_of_le_1)
next
  fix OPT S s
  assume "OPT \<subseteq> V"
     and "finite OPT"
     and "card OPT \<le> k"
     and "S \<subseteq> V"
  then show "hit_prob_of OPT S s \<ge> hit_lb_linear s (residual_card OPT S)"
    by (rule hit_prob_of_linear_lower)
qed

end

end