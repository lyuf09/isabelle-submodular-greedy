theory Stochastic_Greedy_Sampling
  imports "../Algorithms/Stochastic_Greedy"
begin

section \<open>Sampling-event layer for StochasticGreedy\<close>

text \<open>
This theory develops the deterministic event layer that will later support the
probabilistic analysis of StochasticGreedy.

At this stage we do not formalise probability yet. Instead, we isolate:
  • the residual optimal set OPT - S;
  • the event that a sampled list hits that residual set;
  • basic set/cardinality facts used later in the one-step expected-gain proof.
\<close>

context Cardinality_Constraint
begin

definition residual_opt :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "residual_opt OPT S = OPT - S"

definition hits_residual :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" where
  "hits_residual OPT S xs \<longleftrightarrow>
     sampled_candidates (V - S) xs \<inter> residual_opt OPT S \<noteq> {}"

definition misses_residual :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" where
  "misses_residual OPT S xs \<longleftrightarrow>
     sampled_candidates (V - S) xs \<inter> residual_opt OPT S = {}"

definition alpha_stoch :: "nat \<Rightarrow> real" where
  "alpha_stoch s = 1 - exp (- (real s * real k / real (card V)))"

definition sample_size_eps :: "real \<Rightarrow> nat" where
  "sample_size_eps eps =
     nat \<lceil>(real (card V) / real k) * ln (1 / eps)\<rceil>"

lemma residual_opt_alt [simp]:
  "residual_opt OPT S = OPT - S"
  unfolding residual_opt_def by simp

lemma finite_residual_opt [simp]:
  assumes "finite OPT"
  shows "finite (residual_opt OPT S)"
  using assms unfolding residual_opt_def by simp

lemma residual_opt_subset_OPT:
  "residual_opt OPT S \<subseteq> OPT"
  unfolding residual_opt_def by auto

lemma residual_opt_subset_remaining:
  assumes "OPT \<subseteq> V"
  shows "residual_opt OPT S \<subseteq> V - S"
  using assms unfolding residual_opt_def by auto

lemma card_residual_opt_le_k:
  assumes finOPT: "finite OPT"
      and cardOPT: "card OPT \<le> k"
  shows "card (residual_opt OPT S) \<le> k"
proof -
  have sub: "residual_opt OPT S \<subseteq> OPT"
    unfolding residual_opt_def by auto
  have "card (residual_opt OPT S) \<le> card OPT"
    using finOPT sub
    by (rule card_mono)
  also have "... \<le> k"
    using cardOPT .
  finally show ?thesis .
qed

lemma hits_residual_iff_not_misses [simp]:
  "hits_residual OPT S xs \<longleftrightarrow> \<not> misses_residual OPT S xs"
  unfolding hits_residual_def misses_residual_def by auto

lemma misses_residual_iff_not_hits [simp]:
  "misses_residual OPT S xs \<longleftrightarrow> \<not> hits_residual OPT S xs"
  unfolding hits_residual_def misses_residual_def by auto

lemma hits_residual_imp_sample_nonempty:
  assumes "hits_residual OPT S xs"
  shows "sampled_candidates (V - S) xs \<noteq> {}"
  using assms unfolding hits_residual_def by auto

lemma hits_residual_imp_residual_nonempty:
  assumes "hits_residual OPT S xs"
  shows "residual_opt OPT S \<noteq> {}"
  using assms unfolding hits_residual_def by auto

lemma hits_residual_set_form:
  assumes "OPT \<subseteq> V"
  shows "hits_residual OPT S xs \<longleftrightarrow> set xs \<inter> (OPT - S) \<noteq> {}"
  using assms
  unfolding hits_residual_def residual_opt_def sampled_candidates_def
  by auto

lemma misses_residual_set_form:
  assumes "OPT \<subseteq> V"
  shows "misses_residual OPT S xs \<longleftrightarrow> set xs \<inter> (OPT - S) = {}"
  using assms
  unfolding misses_residual_def residual_opt_def sampled_candidates_def
  by auto

lemma hits_residual_iff_ex:
  assumes "OPT \<subseteq> V"
  shows "hits_residual OPT S xs \<longleftrightarrow> (\<exists>x\<in>set xs. x \<in> OPT - S)"
  using assms
  unfolding hits_residual_def residual_opt_def sampled_candidates_def
  by auto

lemma misses_residual_iff_ball:
  assumes "OPT \<subseteq> V"
  shows "misses_residual OPT S xs \<longleftrightarrow> (\<forall>x\<in>set xs. x \<notin> OPT - S)"
  using assms
  unfolding misses_residual_def residual_opt_def sampled_candidates_def
  by auto

lemma alpha_stoch_le_1:
  "alpha_stoch s \<le> 1"
proof -
  have "0 < exp (- (real s * real k / real (card V)))"
    by simp
  then show ?thesis
    unfolding alpha_stoch_def by linarith
qed

lemma alpha_stoch_ge_0:
  "0 \<le> alpha_stoch s"
proof -
  have "- (real s * real k / real (card V)) \<le> 0"
    by simp
  hence "exp (- (real s * real k / real (card V))) \<le> 1"
    using exp_le_one_iff by blast
  thus ?thesis
    unfolding alpha_stoch_def by linarith
qed

lemma alpha_stoch_bounds:
  "0 \<le> alpha_stoch s \<and> alpha_stoch s \<le> 1"
  using alpha_stoch_ge_0 alpha_stoch_le_1 by auto

lemma sample_size_eps_nonneg:
  "0 \<le> real (sample_size_eps eps)"
  by simp

text \<open>
Next target for the following stage:

  Under a random-sampling model for xs, prove a lower bound on the probability
  that hits_residual OPT S xs holds. The first bridge theorem should express the
  hit event in terms of set xs \<inter> (OPT - S), using the lemmas established above.
\<close>

end

end