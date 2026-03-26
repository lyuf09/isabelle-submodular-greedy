theory Lazy_Greedy_Stateful_Approx
  imports
    Greedy_Submodular_Approx
    Lazy_Greedy_Stateful_StepSpec
begin

text \<open>
  Approximation guarantee for the verified stateful LazyGreedy construction
  (Lazy_Greedy_Stateful), viewed as a substantial implementation-level / stateful
  extension beyond classical greedy. We show that lazy_set inherits the classical
  Nemhauser–Wolsey (1 - 1/e) guarantee via a correctness bridge back to the
  reusable greedy-step specification. The proof follows the standard gap-recurrence
  argument, using:
    (1) the OPT_k infrastructure from Greedy_Submodular_Approx, and
    (2) the packaged per-step step-spec lemmas from Lazy_Greedy_Stateful_StepSpec.
\<close>

context Cardinality_Constraint
begin

interpretation Greedy_Some: Greedy_Setup V f k argmax_gain_some
  by (unfold_locales) (auto intro: argmax_gain_some_mem argmax_gain_some_max)

abbreviation OPT_k :: real where
  "OPT_k \<equiv> Greedy_Some.OPT_k"

definition gapL :: "nat \<Rightarrow> real" where
  "gapL i = OPT_k - f (lazy_set i)"

lemma lazy_set_0[simp]: "lazy_set 0 = {}"
  by (simp add: lazy_set_def init_state_def)

lemma lazy_set_subset_V[simp]: "lazy_set i \<subseteq> V"
  using lazy_state_subset_V[of i]
  by (simp add: lazy_set_def)

lemma lazy_set_finite[simp]: "finite (lazy_set i)"
  using finite_V lazy_set_subset_V
  by (meson finite_subset)

lemma remaining_lazy_state[simp]: "remaining (lazy_state i) = V - lazy_set i"
  by (simp add: remaining_def lazy_set_def)

lemma card_lazy_le_i: "card (lazy_set i) \<le> i"
proof (induction i)
  case 0
  then show ?case by simp
next
  case (Suc i)
  show ?case
  proof (cases "V - lazy_set i = {}")
    case True
    have "lazy_step (lazy_state i) = lazy_state i"
      using lazy_step_idle[of "lazy_state i"] True by simp
    hence "lazy_set (Suc i) = lazy_set i"
      by (simp add: lazy_set_def)
    thus ?thesis using Suc.IH by simp
  next
    case False
    have ins: "lazy_set (Suc i) = insert (lazy_choice i) (lazy_set i)"
      using lazy_set_Suc_insert_V_minus_S[OF False] .
    have xin: "lazy_choice i \<in> V - lazy_set i"
      using lazy_choice_in_V_minus_S[OF False] .
    have xnot: "lazy_choice i \<notin> lazy_set i" using xin by simp
    have "card (lazy_set (Suc i)) = card (lazy_set i) + 1"
      using ins xnot by simp
    thus ?thesis using Suc.IH by simp
  qed
qed

lemma card_lazy_lt_k:
  "i < k \<Longrightarrow> card (lazy_set i) < k"
  using card_lazy_le_i by (meson le_less_trans)

lemma lazy_remainder_nonempty:
  "i < k \<Longrightarrow> k \<le> card V \<Longrightarrow> V - lazy_set i \<noteq> {}"
proof -
  assume i_lt_k: "i < k"
  assume k_le: "k \<le> card V"

  have "card (lazy_set i) \<le> i" by (rule card_lazy_le_i)
  also have "... < k" using i_lt_k by simp
  also have "... \<le> card V" using k_le by simp
  finally have ltV: "card (lazy_set i) < card V" .

  have S_sub: "lazy_set i \<subseteq> V" by simp

  show "V - lazy_set i \<noteq> {}"
  proof
    assume empty: "V - lazy_set i = {}"
    have V_sub: "V \<subseteq> lazy_set i"
      using empty by auto

    have eq: "lazy_set i = V"
      using subset_antisym[OF S_sub V_sub] by simp

    thus False
      using ltV by simp
  qed
qed

lemma lazy_set_feasible:
  assumes "i \<le> k"
  shows "feasible (lazy_set i)"
proof -
  have sub: "lazy_set i \<subseteq> V" by simp
  have card_le_k: "card (lazy_set i) \<le> k"
    using card_lazy_le_i assms by (rule le_trans)
  show ?thesis
    using sub card_le_k
    by (simp add: feasible_set_k_def feasible_def)
qed

lemma gapL_nonneg:
  assumes "i \<le> k"
  shows "0 \<le> gapL i"
proof -
  have feas: "feasible (lazy_set i)"
    using lazy_set_feasible[OF assms] .
  have ub: "f (lazy_set i) \<le> OPT_k"
    using Greedy_Some.OPT_k_upper_bound[OF feas] by simp
  show ?thesis
    using ub by (simp add: gapL_def)
qed

lemma lazy_step_ineq:
  "i < k \<Longrightarrow> k \<le> card V \<Longrightarrow> gain (lazy_set i) (lazy_choice i) \<ge> gapL i / real k"
proof -
  assume i_lt_k: "i < k"
  assume k_le: "k \<le> card V"

  have S_sub: "lazy_set i \<subseteq> V" by simp
  have cardS_lt_k: "card (lazy_set i) < k" using card_lazy_lt_k[OF i_lt_k] .

    obtain X where X_feas: "feasible X" and X_opt: "f X = OPT_k"
      using Greedy_Some.exists_opt_set by blast

    from X_feas have X_sub: "X \<subseteq> V" and cardX_le_k: "card X \<le> k"
      unfolding feasible_def by auto

    from Greedy_Some.marginal_gain_lower_bound[OF S_sub X_sub k_le cardS_lt_k cardX_le_k]
    obtain e where e_in: "e \<in> V - lazy_set i"
         and e_lb: "gain (lazy_set i) e \<ge> (f X - f (lazy_set i)) / real k"
      by blast

  have rem_ne: "V - lazy_set i \<noteq> {}"
    using lazy_remainder_nonempty[OF i_lt_k k_le] .
  have argmax:
    "\<forall>y\<in>V - lazy_set i. gain (lazy_set i) y \<le> gain (lazy_set i) (lazy_choice i)"
    using lazy_choice_argmax_V_minus_S[OF rem_ne] .
  have e_le: "gain (lazy_set i) e \<le> gain (lazy_set i) (lazy_choice i)"
    using argmax e_in by auto

  have "(f X - f (lazy_set i)) / real k = gapL i / real k"
    using X_opt by (simp add: gapL_def)

  have e_lb': "gapL i / real k \<le> gain (lazy_set i) e"
    using e_lb X_opt
    by (simp add: gapL_def)

  have "gapL i / real k \<le> gain (lazy_set i) (lazy_choice i)"
    using order_trans[OF e_lb' e_le] .

  show "gain (lazy_set i) (lazy_choice i) \<ge> gapL i / real k"
    by (simp add: \<open>gapL i / real k \<le> gain (lazy_set i) (lazy_choice i)\<close>)
qed

lemma gapL_step:
  "i < k \<Longrightarrow> k \<le> card V \<Longrightarrow> gapL (Suc i) \<le> (1 - 1 / real k) * gapL i"
proof -
  assume i_lt_k: "i < k"
  assume k_le: "k \<le> card V"

  have rem_ne: "V - lazy_set i \<noteq> {}"
    using lazy_remainder_nonempty[OF i_lt_k k_le] .
  have ins: "lazy_set (Suc i) = insert (lazy_choice i) (lazy_set i)"
    using lazy_set_Suc_insert_V_minus_S[OF rem_ne] .

  have step_gain: "f (lazy_set (Suc i)) = f (lazy_set i) + gain (lazy_set i) (lazy_choice i)"
    using ins by (simp add: gain_def algebra_simps)

  have gap_suc: "gapL (Suc i) = gapL i - gain (lazy_set i) (lazy_choice i)"
    by (simp add: gapL_def step_gain)

  have gain_lb: "gain (lazy_set i) (lazy_choice i) \<ge> gapL i / real k"
    using lazy_step_ineq[OF i_lt_k k_le] .

  have "gapL (Suc i) \<le> gapL i - gapL i / real k"
    using gap_suc gain_lb by linarith
  also have "... = (1 - 1 / real k) * gapL i"
    by (simp add: algebra_simps)
  finally show "gapL (Suc i) \<le> (1 - 1 / real k) * gapL i" .
qed

lemma gapL_geometric:
  "k > 0 \<Longrightarrow> k \<le> card V \<Longrightarrow> i \<le> k \<Longrightarrow> gapL i \<le> (1 - 1 / real k) ^ i * OPT_k"
proof (induction i)
  case 0
  then show ?case
    by (simp add: gapL_def f_empty)
next
  case (Suc i)
  have i_le_k: "i \<le> k" using Suc.prems by simp
  have i_lt_k: "i < k" using Suc.prems by simp

  have step: "gapL (Suc i) \<le> (1 - 1 / real k) * gapL i"
    using gapL_step[OF i_lt_k Suc.prems(2)] .

  have coef_nonneg: "0 \<le> (1 - 1 / real k)"
  proof -
    have "1 \<le> real k" using Suc.prems(1) by simp
    then have "1 / real k \<le> 1" by (simp add: field_simps)
    thus ?thesis by simp
  qed

  have IH: "gapL i \<le> (1 - 1 / real k) ^ i * OPT_k"
    using Suc.IH[OF Suc.prems(1) Suc.prems(2) i_le_k] .

  have mult_mono:
    "(1 - 1 / real k) * gapL i
     \<le> (1 - 1 / real k) * ((1 - 1 / real k) ^ i * OPT_k)"
    using IH coef_nonneg by (rule mult_left_mono)

  have pow_Suc:
    "(1 - 1 / real k) * ((1 - 1 / real k) ^ i * OPT_k)
     = (1 - 1 / real k) ^ (Suc i) * OPT_k"
    by (simp add: mult_ac)

  have "gapL (Suc i) \<le> (1 - 1 / real k) * ((1 - 1 / real k) ^ i * OPT_k)"
    using step mult_mono by (rule order_trans)
  thus ?case by (simp add: pow_Suc)
qed

theorem lazy_stateful_approximation:
  "k > 0 \<Longrightarrow> k \<le> card V \<Longrightarrow> f (lazy_set k) \<ge> (1 - 1 / exp 1) * OPT_k"
proof -
  assume k_pos: "k > 0"
  assume k_le: "k \<le> card V"

  have gap_bound: "gapL k \<le> (1 - 1 / real k) ^ k * OPT_k"
    using gapL_geometric[OF k_pos k_le, of k] by simp

  have f_eq: "f (lazy_set k) = OPT_k - gapL k"
    by (simp add: gapL_def)

  have lower: "OPT_k - gapL k \<ge> OPT_k - (1 - 1 / real k) ^ k * OPT_k"
    using gap_bound by linarith

  have base_bound: "f (lazy_set k) \<ge> (1 - (1 - 1 / real k) ^ k) * OPT_k"
  proof -
    have "f (lazy_set k) \<ge> OPT_k - (1 - 1 / real k) ^ k * OPT_k"
      using f_eq lower by simp
    also have "OPT_k - (1 - 1 / real k) ^ k * OPT_k
               = (1 - (1 - 1 / real k) ^ k) * OPT_k"
      by (simp add: algebra_simps)
    finally show ?thesis .
  qed

  have k_ge1: "k \<ge> 1" using k_pos by simp
  have coeff_bound: "1 - (1 - 1 / real k) ^ k \<ge> 1 - 1 / exp 1"
    using coeff_ge_1_minus_inv_exp[OF k_ge1] .

  have nonneg: "0 \<le> OPT_k"
    using Greedy_Some.OPT_k_nonneg by simp

  have coeff_mono:
    "(1 - (1 - 1 / real k) ^ k) * OPT_k \<ge> (1 - 1 / exp 1) * OPT_k"
    using coeff_bound nonneg by (rule mult_right_mono)

  show "f (lazy_set k) \<ge> (1 - 1 / exp 1) * OPT_k"
    using base_bound coeff_mono by (meson order_trans)
qed

end

end