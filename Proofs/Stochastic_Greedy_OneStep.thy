theory Stochastic_Greedy_OneStep
  imports Stochastic_Greedy_Sampling
begin

section \<open>Deterministic one-step bridge for StochasticGreedy\<close>

text \<open>
This theory develops the deterministic bridge used later in the stochastic
one-step analysis.

At this stage we do not yet formalise probability or expectation. Instead, we
show that whenever the sampled pool hits the residual optimal set, the element
chosen by the sampled argmax has marginal gain at least as large as the average
marginal gain over the hit residual pool.

This isolates the purely deterministic part of the later expected-gain proof.
\<close>

context Cardinality_Constraint
begin

definition residual_candidates :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "residual_candidates OPT S = residual_opt OPT S"

definition residual_hit_pool :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> 'a set" where
  "residual_hit_pool OPT S xs =
     sampled_candidates (V - S) xs \<inter> residual_opt OPT S"

definition sampled_argmax :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "sampled_argmax S xs =
     argmax_gain_on S (sampled_candidates (V - S) xs)"

definition avg_gain_on :: "'a set \<Rightarrow> 'a set \<Rightarrow> real" where
  "avg_gain_on S A =
     (if finite A \<and> A \<noteq> {}
      then (\<Sum>x\<in>A. gain S x) / real (card A)
      else 0)"

lemma residual_candidates_alt [simp]:
  "residual_candidates OPT S = residual_opt OPT S"
  unfolding residual_candidates_def by simp

lemma residual_candidates_subset_V:
  assumes "OPT \<subseteq> V" "S \<subseteq> V"
  shows "residual_candidates OPT S \<subseteq> V"
  using assms
  unfolding residual_candidates_def residual_opt_def
  by auto

lemma finite_residual_candidates [simp]:
  assumes "OPT \<subseteq> V"
  shows "finite (residual_candidates OPT S)"
proof -
  have "finite OPT"
    using assms finite_V finite_subset by blast
  then show ?thesis
    unfolding residual_candidates_def residual_opt_def
    by simp
qed

lemma residual_hit_pool_alt [simp]:
  "residual_hit_pool OPT S xs =
     sampled_candidates (V - S) xs \<inter> residual_opt OPT S"
  unfolding residual_hit_pool_def by simp

lemma sampled_argmax_alt [simp]:
  "sampled_argmax S xs =
     argmax_gain_on S (sampled_candidates (V - S) xs)"
  unfolding sampled_argmax_def by simp

lemma avg_gain_on_eq:
  assumes "finite A" "A \<noteq> {}"
  shows "avg_gain_on S A = (\<Sum>x\<in>A. gain S x) / real (card A)"
  using assms unfolding avg_gain_on_def by simp

lemma residual_hit_pool_subset_sampled:
  "residual_hit_pool OPT S xs \<subseteq> sampled_candidates (V - S) xs"
  unfolding residual_hit_pool_def by auto

lemma residual_hit_pool_subset_residual:
  "residual_hit_pool OPT S xs \<subseteq> residual_opt OPT S"
  unfolding residual_hit_pool_def by auto

lemma finite_residual_hit_pool [simp]:
  "finite (residual_hit_pool OPT S xs)"
  unfolding residual_hit_pool_def by simp

lemma hits_residual_iff_residual_hit_pool_nonempty:
  "hits_residual OPT S xs \<longleftrightarrow> residual_hit_pool OPT S xs \<noteq> {}"
  unfolding hits_residual_def residual_hit_pool_def by auto

lemma sampled_argmax_ge_residual_hit_pool:
  assumes hit: "hits_residual OPT S xs"
      and y_in: "y \<in> residual_hit_pool OPT S xs"
  shows "gain S y \<le> gain S (sampled_argmax S xs)"
proof -
  have y_sampled: "y \<in> sampled_candidates (V - S) xs"
    using y_in unfolding residual_hit_pool_def by auto
  have nonempty: "sampled_candidates (V - S) xs \<noteq> {}"
    using hit hits_residual_imp_sample_nonempty by blast
  have fin_sampled: "finite (sampled_candidates (V - S) xs)"
    by simp
  show ?thesis
    unfolding sampled_argmax_def
    using argmax_gain_on_max[OF fin_sampled nonempty y_sampled] .
qed

lemma avg_gain_on_le_bound:
  assumes finA: "finite A"
      and neA: "A \<noteq> {}"
      and pointwise: "\<And>x. x \<in> A \<Longrightarrow> gain S x \<le> c"
  shows "avg_gain_on S A \<le> c"
proof -
  have cardpos_nat: "0 < card A"
    using finA neA by (simp add: card_gt_0_iff)

  have cardpos: "0 < real (card A)"
    using cardpos_nat by simp

  have sum_le: "(\<Sum>x\<in>A. gain S x) \<le> (\<Sum>x\<in>A. c)"
    using finA pointwise by (intro sum_mono) auto
  also have "... = real (card A) * c"
    using finA by simp
  finally have sum_le': "(\<Sum>x\<in>A. gain S x) \<le> real (card A) * c" .

  have avg_le: "(\<Sum>x\<in>A. gain S x) / real (card A) \<le> c"
  proof -
    have "(\<Sum>x\<in>A. gain S x) / real (card A)
          \<le> (real (card A) * c) / real (card A)"
      using sum_le' cardpos
      by (intro divide_right_mono) auto
    also have "... = c"
      using cardpos by simp
    finally show ?thesis .
  qed

  show ?thesis
    using avg_le finA neA
    unfolding avg_gain_on_def
    by simp
qed

lemma avg_residual_hit_le_sample_argmax:
  assumes hit: "hits_residual OPT S xs"
  shows
    "avg_gain_on S (residual_hit_pool OPT S xs)
     \<le> gain S (sampled_argmax S xs)"
proof -
  have ne_pool: "residual_hit_pool OPT S xs \<noteq> {}"
    using hit hits_residual_iff_residual_hit_pool_nonempty by blast

  have pointwise:
    "\<And>y. y \<in> residual_hit_pool OPT S xs
         \<Longrightarrow> gain S y \<le> gain S (sampled_argmax S xs)"
    using hit sampled_argmax_ge_residual_hit_pool by blast

  show ?thesis
    using avg_gain_on_le_bound[of "residual_hit_pool OPT S xs" S
      "gain S (sampled_argmax S xs)"]
          ne_pool pointwise
    by simp
qed

lemma avg_gain_on_empty [simp]:
  "avg_gain_on S {} = 0"
  unfolding avg_gain_on_def by simp

lemma avg_gain_on_nonempty_eq:
  assumes "finite A" "A \<noteq> {}"
  shows "avg_gain_on S A = (\<Sum>x\<in>A. gain S x) / real (card A)"
  using assms by (rule avg_gain_on_eq)

lemma sampled_argmax_ge_avg_residual_hit:
  assumes hit: "hits_residual OPT S xs"
  shows "gain S (sampled_argmax S xs)
         \<ge> avg_gain_on S (residual_hit_pool OPT S xs)"
  using avg_residual_hit_le_sample_argmax[OF hit] by simp

text \<open>
  Next target:
  instantiate the abstract hit-probability interface from
  Stochastic_Greedy_Sampling, and combine it with the present deterministic
  bridge to derive the expected one-step gain inequality.
\<close>

end

end