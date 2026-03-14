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
     (\<Sum>xs\<in>sample_space S s.
        if hits_residual OPT S xs then sample_prob S s xs else 0)"

definition miss_prob_of :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> real" where
  "miss_prob_of OPT S s =
     (\<Sum>xs\<in>sample_space S s.
        if misses_residual OPT S xs then sample_prob S s xs else 0)"

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
  by blast

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

text \<open>
Next step:
  add basic finite-sum lemmas for hit_prob_of and miss_prob_of, and only then
  connect this concrete object back to the abstract locale
  Stochastic_Greedy_Hit_Model.
\<close>

end

end