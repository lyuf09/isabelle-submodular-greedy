theory Stochastic_Greedy_Sampling
  imports "../Algorithms/Stochastic_Greedy"
begin

section \<open>Sampling-event and hit-probability interface for StochasticGreedy\<close>

text \<open>
This theory develops the abstract sampling-event layer used later in the
stochastic analysis of StochasticGreedy.

At this stage we deliberately avoid committing to a concrete probability
formalisation. Instead, we isolate:

  • the residual optimal set OPT - S;
  • the deterministic hit / miss events for a sampled list;
  • paper-facing lower-bound expressions for hit probabilities;
  • an abstract locale packaging the hit-probability guarantee that the later
    one-step and approximation theories will consume.

Concrete weighted sampling models are developed separately, in order to keep
this theory lightweight and stable.
\<close>

context Cardinality_Constraint
begin

subsection \<open>Residual set and hit / miss events\<close>

definition residual_opt :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "residual_opt OPT S = OPT - S"

definition hits_residual :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" where
  "hits_residual OPT S xs \<longleftrightarrow>
     sampled_candidates (V - S) xs \<inter> residual_opt OPT S \<noteq> {}"

definition misses_residual :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> bool" where
  "misses_residual OPT S xs \<longleftrightarrow>
     sampled_candidates (V - S) xs \<inter> residual_opt OPT S = {}"

definition residual_card :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat" where
  "residual_card OPT S = card (residual_opt OPT S)"

lemma residual_opt_alt [simp]:
  "residual_opt OPT S = OPT - S"
  unfolding residual_opt_def by simp

lemma residual_card_alt [simp]:
  "residual_card OPT S = card (residual_opt OPT S)"
  unfolding residual_card_def by simp

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
    using finOPT sub by (rule card_mono)
  also have "... \<le> k"
    using cardOPT .
  finally show ?thesis .
qed

lemma residual_card_le_k:
  assumes finOPT: "finite OPT"
      and cardOPT: "card OPT \<le> k"
  shows "residual_card OPT S \<le> k"
  using card_residual_opt_le_k[OF finOPT cardOPT]
  unfolding residual_card_def by simp

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

subsection \<open>Paper-facing lower-bound expressions\<close>

definition alpha_stoch :: "nat \<Rightarrow> real" where
  "alpha_stoch s = 1 - exp (- (real s * real k / real (card V)))"

definition sample_size_eps :: "real \<Rightarrow> nat" where
  "sample_size_eps eps =
     nat \<lceil>(real (card V) / real k) * ln (1 / eps)\<rceil>"

definition hit_lb_exp :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "hit_lb_exp s m = 1 - exp (- (real s * real m / real (card V)))"

definition hit_lb_linear :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "hit_lb_linear s m =
     (if k = 0 then 0 else alpha_stoch s * real m / real k)"

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

lemma hit_lb_exp_0_left [simp]:
  "hit_lb_exp 0 m = 0"
  unfolding hit_lb_exp_def by simp

lemma hit_lb_exp_0_right [simp]:
  "hit_lb_exp s 0 = 0"
  unfolding hit_lb_exp_def by simp

lemma hit_lb_exp_le_1:
  "hit_lb_exp s m \<le> 1"
proof -
  have "0 < exp (- (real s * real m / real (card V)))"
    by simp
  then show ?thesis
    unfolding hit_lb_exp_def by linarith
qed

lemma hit_lb_exp_ge_0:
  "0 \<le> hit_lb_exp s m"
proof -
  have "- (real s * real m / real (card V)) \<le> 0"
    by simp
  hence "exp (- (real s * real m / real (card V))) \<le> 1"
    using exp_le_one_iff by blast
  thus ?thesis
    unfolding hit_lb_exp_def by linarith
qed

lemma hit_lb_exp_bounds:
  "0 \<le> hit_lb_exp s m \<and> hit_lb_exp s m \<le> 1"
  using hit_lb_exp_ge_0 hit_lb_exp_le_1 by auto

lemma alpha_stoch_eq_hit_lb_exp_k:
  "alpha_stoch s = hit_lb_exp s k"
  unfolding alpha_stoch_def hit_lb_exp_def by simp

lemma hit_lb_linear_0_left [simp]:
  "hit_lb_linear 0 m = 0"
  unfolding hit_lb_linear_def alpha_stoch_def by simp

lemma hit_lb_linear_0_right [simp]:
  "hit_lb_linear s 0 = 0"
  unfolding hit_lb_linear_def by simp

lemma hit_lb_linear_nonneg:
  "0 \<le> hit_lb_linear s m"
proof (cases "k = 0")
  case True
  then show ?thesis
    unfolding hit_lb_linear_def by simp
next
  case False
  then show ?thesis
    unfolding hit_lb_linear_def
    using alpha_stoch_ge_0 by simp
qed

lemma hit_lb_linear_at_k:
  assumes "k > 0"
  shows "hit_lb_linear s k = alpha_stoch s"
  using assms
  unfolding hit_lb_linear_def by simp

lemma hit_lb_linear_residual_card_at_k:
  assumes finOPT: "finite OPT"
      and cardOPT: "card OPT \<le> k"
      and "residual_card OPT S = k"
      and "k > 0"
  shows "hit_lb_linear s (residual_card OPT S) = alpha_stoch s"
  using assms
  unfolding residual_card_def
  by (simp add: hit_lb_linear_at_k)

end

subsection \<open>Abstract hit-probability interface\<close>

text \<open>
The concrete probabilistic sampling model is deliberately postponed.
Instead, we package the paper-facing lower bound as an abstract locale.

Later, an instantiation should interpret hit_prob OPT S s as the probability
that a with-replacement sample of length s from the remaining set V - S hits
the residual set OPT - S.
\<close>

locale Stochastic_Greedy_Hit_Model =
  Cardinality_Constraint V f k
  for V :: "'a set" and f :: "'a set \<Rightarrow> real" and k :: nat +
  fixes hit_prob :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> real"
  assumes hit_prob_nonneg:
    "0 \<le> hit_prob OPT S s"
  assumes hit_prob_le_1:
    "hit_prob OPT S s \<le> 1"
  assumes hit_prob_linear_lower:
    "OPT \<subseteq> V \<Longrightarrow> finite OPT \<Longrightarrow> card OPT \<le> k \<Longrightarrow> S \<subseteq> V \<Longrightarrow>
     hit_prob OPT S s \<ge> hit_lb_linear s (residual_card OPT S)"
begin

lemma hit_prob_bounds:
  "0 \<le> hit_prob OPT S s \<and> hit_prob OPT S s \<le> 1"
  using hit_prob_nonneg hit_prob_le_1 by auto

lemma hit_prob_lower_residual:
  assumes "OPT \<subseteq> V" "finite OPT" "card OPT \<le> k" "S \<subseteq> V"
  shows "hit_prob OPT S s \<ge> hit_lb_linear s (residual_card OPT S)"
  using assms hit_prob_linear_lower by blast

lemma hit_prob_lower_zero:
  "0 \<le> hit_prob OPT S s"
  using hit_prob_nonneg by simp

lemma hit_prob_upper_one:
  "hit_prob OPT S s \<le> 1"
  using hit_prob_le_1 by simp

end

text \<open>
note:
  concrete weighted sampling models are developed in a separate theory, so that
  this abstract sampling layer remains stable and easy to reuse.
\<close>

end
