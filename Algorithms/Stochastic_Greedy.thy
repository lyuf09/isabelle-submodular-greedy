theory Stochastic_Greedy
  imports Greedy_Submodular_Construct
begin

section \<open>StochasticGreedy: deterministic trace layer\<close>

text \<open>
This theory introduces a deterministic execution layer for StochasticGreedy.
Rather than formalising probability immediately, we parameterise the algorithm
by an explicit trace of sampled candidate lists. This keeps the executable layer
separate from the later probabilistic analysis.

The intended interpretation is:
  • each round receives a sampled list of candidates from the remaining set;
  • duplicates are allowed at the list level;
  • the algorithm selects an element of maximum marginal gain from the sampled pool.

Later theories will impose probabilistic assumptions on how these lists are
generated, but this file only develops the deterministic backbone.
\<close>

context Submodular_Func
begin

definition sampled_candidates :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a set" where
  "sampled_candidates A xs = set xs \<inter> A"

definition argmax_gain_on :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "argmax_gain_on S A =
     (SOME x. x \<in> A \<and> is_arg_max (gain S) (\<lambda>y. y \<in> A) x)"

lemma sampled_candidates_subset [simp]:
  "sampled_candidates A xs \<subseteq> A"
  unfolding sampled_candidates_def by auto

lemma finite_sampled_candidates [simp]:
  "finite (sampled_candidates A xs)"
  unfolding sampled_candidates_def by simp

lemma sampled_candidates_nonemptyI:
  assumes "x \<in> set xs" "x \<in> A"
  shows "sampled_candidates A xs \<noteq> {}"
  using assms unfolding sampled_candidates_def by auto

lemma argmax_gain_on_mem:
  assumes finA: "finite A" and neA: "A \<noteq> {}"
  shows "argmax_gain_on S A \<in> A"
proof -
  have ex_in: "\<exists>x\<in>A. is_arg_max (gain S) (\<lambda>y. y \<in> A) x"
    using finite_is_arg_max_in[OF finA neA] by blast
  hence ex: "\<exists>x. x \<in> A \<and> is_arg_max (gain S) (\<lambda>y. y \<in> A) x"
    by blast
  show ?thesis
    unfolding argmax_gain_on_def
    using someI_ex[OF ex] by blast
qed

lemma argmax_gain_on_max:
  assumes finA: "finite A" and neA: "A \<noteq> {}" and yA: "y \<in> A"
  shows "gain S y \<le> gain S (argmax_gain_on S A)"
proof -
  have ex_in: "\<exists>x\<in>A. is_arg_max (gain S) (\<lambda>z. z \<in> A) x"
    using finite_is_arg_max_in[OF finA neA] by blast
  hence ex: "\<exists>x. x \<in> A \<and> is_arg_max (gain S) (\<lambda>z. z \<in> A) x"
    by blast
  have chosen: "is_arg_max (gain S) (\<lambda>z. z \<in> A) (argmax_gain_on S A)"
    unfolding argmax_gain_on_def
    using someI_ex[OF ex] by blast
  show ?thesis
    using is_arg_maxD_le[OF chosen yA] .
qed

end

context Cardinality_Constraint
begin

definition stochastic_step_from :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a set" where
  "stochastic_step_from S xs =
     (let A = sampled_candidates (V - S) xs in
      if A = {} then S else S \<union> {argmax_gain_on S A})"

fun stochastic_run_trace :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a list list \<Rightarrow> 'a set" where
  "stochastic_run_trace 0 S Rs = S"
| "stochastic_run_trace (Suc t) S [] = S"
| "stochastic_run_trace (Suc t) S (R # Rs) =
     stochastic_run_trace t (stochastic_step_from S R) Rs"

definition stochastic_greedy_trace :: "'a list list \<Rightarrow> 'a set" where
  "stochastic_greedy_trace Rs = stochastic_run_trace k {} Rs"

lemma stochastic_step_from_subset_V:
  assumes "S \<subseteq> V"
  shows "stochastic_step_from S xs \<subseteq> V"
proof (cases "sampled_candidates (V - S) xs = {}")
  case True
  then show ?thesis
    using assms unfolding stochastic_step_from_def
    by (simp add: Let_def)
next
  case False
  let ?A = "sampled_candidates (V - S) xs"

  have chosen_in_A: "argmax_gain_on S ?A \<in> ?A"
    using False argmax_gain_on_mem by simp

  have chosen_in_V: "argmax_gain_on S ?A \<in> V"
    using chosen_in_A
    unfolding sampled_candidates_def
    by auto

  have step_eq: "stochastic_step_from S xs = S \<union> {argmax_gain_on S ?A}"
    using False unfolding stochastic_step_from_def
    by (simp add: Let_def)

  show ?thesis
    unfolding step_eq
    using assms chosen_in_V
    by auto
qed

lemma stochastic_step_from_extensive:
  assumes "S \<subseteq> V"
  shows "S \<subseteq> stochastic_step_from S xs"
  using assms unfolding stochastic_step_from_def by (auto simp: Let_def)

lemma stochastic_step_from_card_le:
  assumes "S \<subseteq> V"
  shows "card (stochastic_step_from S xs) \<le> Suc (card S)"
proof (cases "sampled_candidates (V - S) xs = {}")
  case True
  then show ?thesis
    unfolding stochastic_step_from_def
    by (simp add: Let_def)
next
  case False
  let ?A = "sampled_candidates (V - S) xs"

  have finite_S: "finite S"
    using assms finite_V finite_subset by blast

  have chosen_in: "argmax_gain_on S ?A \<in> ?A"
    using False argmax_gain_on_mem by simp

  have chosen_notin: "argmax_gain_on S ?A \<notin> S"
    using chosen_in
    unfolding sampled_candidates_def
    by auto

  have step_eq:
    "stochastic_step_from S xs = S \<union> {argmax_gain_on S ?A}"
    using False
    unfolding stochastic_step_from_def
    by (simp add: Let_def)

  have "card (stochastic_step_from S xs) = card (S \<union> {argmax_gain_on S ?A})"
    using step_eq by simp
  also have "... = Suc (card S)"
    using finite_S chosen_notin
    by simp
  finally show ?thesis
    by simp
qed

lemma stochastic_run_trace_subset_V:
  assumes "S \<subseteq> V"
  shows "stochastic_run_trace t S Rs \<subseteq> V"
  using assms
proof (induction t arbitrary: S Rs)
  case 0
  then show ?case by simp
next
  case (Suc t)
  then show ?case
  proof (cases Rs)
    case Nil
    then show ?thesis using Suc.prems by simp
  next
    case (Cons R Rs')
    have step_subset: "stochastic_step_from S R \<subseteq> V"
      using stochastic_step_from_subset_V Suc.prems by blast
    have "stochastic_run_trace t (stochastic_step_from S R) Rs' \<subseteq> V"
      using Suc.IH[OF step_subset] .
    then show ?thesis
      using Cons by simp
  qed
qed

lemma stochastic_run_trace_card_le:
  assumes "S \<subseteq> V"
  shows "card (stochastic_run_trace t S Rs) \<le> card S + t"
  using assms
proof (induction t arbitrary: S Rs)
  case 0
  then show ?case by simp
next
  case (Suc t)
  then show ?case
  proof (cases Rs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons R Rs')
    have step_subset: "stochastic_step_from S R \<subseteq> V"
      using stochastic_step_from_subset_V Suc.prems by blast
    have step_card: "card (stochastic_step_from S R) \<le> Suc (card S)"
      using stochastic_step_from_card_le Suc.prems by blast
    have IH:
      "card (stochastic_run_trace t (stochastic_step_from S R) Rs') \<le>
       card (stochastic_step_from S R) + t"
      using Suc.IH[OF step_subset] .
    have "card (stochastic_run_trace (Suc t) S (R # Rs')) \<le>
          card (stochastic_step_from S R) + t"
      using IH by simp
    also have "... \<le> Suc (card S) + t"
      using step_card by simp
    also have "... = card S + Suc t"
      by simp
    finally show ?thesis
      using Cons by simp
  qed
qed

corollary stochastic_greedy_trace_subset_V:
  "stochastic_greedy_trace Rs \<subseteq> V"
  unfolding stochastic_greedy_trace_def
  using stochastic_run_trace_subset_V by simp

corollary stochastic_greedy_trace_card_le:
  "card (stochastic_greedy_trace Rs) \<le> k"
  unfolding stochastic_greedy_trace_def
  using stochastic_run_trace_card_le[of "{}" k Rs] by simp

end

end