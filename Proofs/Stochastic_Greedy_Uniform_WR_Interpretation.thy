theory Stochastic_Greedy_Uniform_WR_Interpretation
  imports Stochastic_Greedy_Uniform_WR
begin

section \<open>Locale interpretations for the uniform with-replacement model\<close>

text \<open>
This theory turns the concrete uniform with-replacement model developed in
theory Stochastic_Greedy_Uniform_WR into interpretations of the abstract
weighted-sampling locales.
\<close>

context Cardinality_Constraint
begin

text \<open>
For the locale interpretation we need a normalization lemma that matches the
current weighted-sampling interface exactly, i.e. without an extra assumption
of the form @{term "S \<subseteq> V"}.
\<close>

lemma uniform_wr_mass_1_raw:
  fixes S :: "'a set" and s :: nat
  assumes feas: "V - S \<noteq> {} \<or> s = 0"
  shows "(\<Sum>xs\<in>uniform_wr_space S s. uniform_wr_prob S s xs) = 1"
proof -
  let ?U = "uniform_wr_space S s"

  have finU: "finite ?U"
    by simp

  have cardU: "card ?U = card (V - S) ^ s"
    unfolding uniform_wr_space_def
    using card_wr_space_on[of "V - S" s] finite_V
    by simp

  have cardU_nz: "card ?U \<noteq> 0"
  proof (cases "s = 0")
    case True
    with cardU show ?thesis
      by simp
  next
    case False
    with feas have diff_ne: "V - S \<noteq> {}"
      by auto
    have fin_diff: "finite (V - S)"
      using finite_V by simp
    have card_diff_nz: "card (V - S) \<noteq> 0"
      using fin_diff diff_ne
      by (simp add: card_eq_0_iff)
    with cardU False show ?thesis
      by simp
  qed

  have "(\<Sum>xs\<in>?U. uniform_wr_prob S s xs)
      = (\<Sum>xs\<in>?U. inverse (real (card ?U)))"
    by (rule sum.cong) (auto simp: uniform_wr_prob_def)
  also have "... = real (card ?U) * inverse (real (card ?U))"
    using finU by simp
  also have "... = 1"
    using cardU_nz by simp
  finally show ?thesis .
qed

sublocale uniform_wr_weighted:
  Stochastic_Greedy_Weighted_Sampling V f k uniform_wr_space uniform_wr_prob
proof (unfold_locales)
  fix S :: "'a set" and s :: nat
  show "finite (uniform_wr_space S s)"
    by simp
next
  fix xs :: "'a list" and S :: "'a set" and s :: nat
  assume "xs \<in> uniform_wr_space S s"
  then show "length xs = s \<and> set xs \<subseteq> V - S"
    using uniform_wr_space_mem_iff
    by blast
next
  fix xs :: "'a list" and S :: "'a set" and s :: nat
  assume "xs \<in> uniform_wr_space S s"
  show "0 \<le> uniform_wr_prob S s xs"
    by (rule uniform_wr_prob_nonneg)
next
  fix S :: "'a set" and s :: nat
  assume "V - S \<noteq> {} \<or> s = 0"
  then show "(\<Sum>xs\<in>uniform_wr_space S s. uniform_wr_prob S s xs) = 1"
    by (rule uniform_wr_mass_1_raw)
qed

lemma uniform_wr_weighted_hit_prob_eq:
  fixes OPT :: "'a set" and S :: "'a set" and s :: nat
  shows "uniform_wr_weighted.hit_prob_of OPT S s
       = uniform_wr_hit_prob OPT S s"
  unfolding uniform_wr_weighted.hit_prob_of_def
            uniform_wr_weighted.hit_event_def
            uniform_wr_hit_prob_def
            uniform_wr_hit_event_def
  by simp

lemma uniform_wr_weighted_miss_prob_eq:
  fixes OPT :: "'a set" and S :: "'a set" and s :: nat
  shows "uniform_wr_weighted.miss_prob_of OPT S s
       = uniform_wr_miss_prob OPT S s"
  unfolding uniform_wr_weighted.miss_prob_of_def
            uniform_wr_weighted.miss_event_def
            uniform_wr_miss_prob_def
            uniform_wr_miss_event_def
  by simp

sublocale uniform_wr_hit:
  Stochastic_Greedy_Weighted_Hit_Model V f k uniform_wr_space uniform_wr_prob
proof (unfold_locales)
  fix OPT :: "'a set" and S :: "'a set" and s :: nat
  assume hOPT: "OPT \<subseteq> V"
     and hfin: "finite OPT"
     and hcard: "card OPT \<le> k"
     and hS:   "S \<subseteq> V"
  show "uniform_wr_weighted.hit_prob_of OPT S s
        \<ge> hit_lb_linear s (residual_card OPT S)"
    using uniform_wr_weighted_hit_prob_eq
          uniform_wr_hit_prob_ge_hit_lb_linear[OF hOPT hfin hcard hS]
    by simp
qed

end

end