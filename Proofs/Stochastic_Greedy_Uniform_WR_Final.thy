theory Stochastic_Greedy_Uniform_WR_Final
  imports
    Stochastic_Greedy_Uniform_WR_DeliverableA
    Stochastic_Greedy_Approx
    "../Complexity/Stochastic_Greedy_OracleCost"
begin

section \<open>Final approximation wrapper for uniform WR StochasticGreedy\<close>

text \<open>
This theory packages the concrete one-step bridge from
Stochastic_Greedy_Uniform_WR_DeliverableA into a final k-step approximation
statement.

At the current stage of the development, the executable stochastic algorithm is
still represented by a deterministic trace layer, while the approximation layer
in Stochastic_Greedy_Approx is phrased abstractly in terms of a gap recurrence.
Accordingly, the present theory proves the final guarantee for any set-valued
state sequence A :: nat \<Rightarrow> 'a set satisfying:

  (1) A i \<subseteq> V,
  (2) f (A i) \<le> f OPT,
  (3) f (A (Suc i)) = f (A i) + expected_step_gain (A i) s,

together with the standard normalization f {} = 0.
\<close>

context Cardinality_Constraint
begin

subsection \<open>Auxiliary analytic bounds\<close>

lemma alpha_stoch_le_real_k:
  assumes k_pos: "0 < k"
  shows "alpha_stoch s \<le> real k"
proof -
  have "alpha_stoch s \<le> 1"
    by (rule alpha_stoch_le_1)
  with k_pos show ?thesis
    by linarith
qed

lemma opt_nonneg_from_normalized:
  assumes OPT_sub: "OPT \<subseteq> V"
  assumes norm0:   "f {} = 0"
  shows "0 \<le> f OPT"
proof -
  have "f {} \<le> f OPT"
    using monotone_f[rule_format, of "{}" OPT] OPT_sub
    by auto
  with norm0 show ?thesis
    by linarith
qed

subsection \<open>Gap recurrence from the concrete one-step theorem\<close>

lemma uniform_wr_gap_recurrence_alpha:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes k_pos:    "0 < k"
  assumes A_sub:    "A i \<subseteq> V"
  assumes A_le_OPT: "f (A i) \<le> f OPT"
  assumes step_eq:
    "f (A (Suc i)) = f (A i) + uniform_wr_weighted.expected_step_gain (A i) s"
  shows
    "f OPT - f (A (Suc i))
      \<le> (1 - alpha_stoch s / real k) * (f OPT - f (A i))"
proof -
  have step_lb:
    "uniform_wr_weighted.expected_step_gain (A i) s
      \<ge> (alpha_stoch s / real k) * (f OPT - f (A i))"
    using uniform_wr_expected_step_gain_ge_alpha_gap_over_k
      [OF OPT_sub OPT_fin OPT_card A_sub k_pos, of s]
    by simp

  have gap_nonneg: "0 \<le> f OPT - f (A i)"
    using A_le_OPT by linarith

  have alpha_le_k: "alpha_stoch s \<le> real k"
    by (rule alpha_stoch_le_real_k[OF k_pos])

  have contract:
    "(f OPT - f (A i)) - uniform_wr_weighted.expected_step_gain (A i) s
      \<le> (1 - alpha_stoch s / real k) * (f OPT - f (A i))"
    using one_step_progress_to_gap_contraction[OF k_pos alpha_le_k gap_nonneg step_lb]
    by simp

  have gap_step:
    "f OPT - f (A (Suc i))
      = (f OPT - f (A i)) - uniform_wr_weighted.expected_step_gain (A i) s"
    using step_eq by linarith

  show ?thesis
    using gap_step contract
    by linarith
qed

subsection \<open>Generic alpha-version final theorem\<close>

theorem uniform_wr_gap_bound_alpha:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes k_pos:    "0 < k"
  assumes A0:       "A 0 = {}"
  assumes A_sub:    "\<And>i. A i \<subseteq> V"
  assumes A_le_OPT: "\<And>i. f (A i) \<le> f OPT"
  assumes step_eq:
    "\<And>i. f (A (Suc i)) = f (A i) + uniform_wr_weighted.expected_step_gain (A i) s"
  assumes norm0:    "f {} = 0"
  shows
    "f OPT - f (A i) \<le> stoch_gap_factor s i * f OPT"
proof -
  have alpha_le_k: "alpha_stoch s \<le> real k"
    by (rule alpha_stoch_le_real_k[OF k_pos])

  have alpha_nonneg: "0 \<le> alpha_stoch s"
    by (rule alpha_stoch_ge_0)

  have Gap0:
    "(\<lambda>j. f OPT - f (A j)) 0 \<le> f OPT"
    using A0 norm0
    by simp

  have Gap_rec:
    "(\<lambda>m. f OPT - f (A m)) (Suc j)
      \<le> (1 - alpha_stoch s / real k) * (\<lambda>m. f OPT - f (A m)) j"
    for j
  proof -
    have rec_j:
      "f OPT - f (A (Suc j))
        \<le> (1 - alpha_stoch s / real k) * (f OPT - f (A j))"
      using uniform_wr_gap_recurrence_alpha[
        where A = A and i = j and s = s,
        OF OPT_sub OPT_fin OPT_card k_pos A_sub[of j] A_le_OPT[of j] step_eq[of j]
      ]
      by simp
    show ?thesis
      using rec_j by simp
  qed

  have OPT_nonneg: "0 \<le> f OPT"
  proof -
    have "{} \<subseteq> OPT"
      using OPT_sub by auto
    then have "f {} \<le> f OPT"
      using monotone_f[rule_format, of "{}" OPT] OPT_sub
      by auto
    with norm0 show ?thesis
      by linarith
  qed

  show ?thesis
    by (rule stochastic_approx_from_gap_recurrence[
          where Gap = "\<lambda>j. f OPT - f (A j)" and OPT = "f OPT" and s = s and i = i,
          OF k_pos alpha_le_k alpha_nonneg Gap0 Gap_rec OPT_nonneg])
qed

corollary uniform_wr_value_bound_alpha:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes k_pos:    "0 < k"
  assumes A0:       "A 0 = {}"
  assumes A_sub:    "\<And>i. A i \<subseteq> V"
  assumes A_le_OPT: "\<And>i. f (A i) \<le> f OPT"
  assumes step_eq:
    "\<And>i. f (A (Suc i)) = f (A i) + uniform_wr_weighted.expected_step_gain (A i) s"
  assumes norm0:    "f {} = 0"
  shows
    "f (A i) \<ge> (1 - stoch_gap_factor s i) * f OPT"
proof -
  have gap_bd:
    "f OPT - f (A i) \<le> stoch_gap_factor s i * f OPT"
    using uniform_wr_gap_bound_alpha[
      where A = A and i = i and s = s,
      OF OPT_sub OPT_fin OPT_card k_pos A0 A_sub A_le_OPT step_eq norm0
    ]
    by simp

  have lower1:
    "f (A i) \<ge> f OPT - stoch_gap_factor s i * f OPT"
    using gap_bd by linarith

  have rewrite_rhs:
    "f OPT - stoch_gap_factor s i * f OPT
     = (1 - stoch_gap_factor s i) * f OPT"
  proof -
    have "f OPT - stoch_gap_factor s i * f OPT
        = f OPT * (1 - stoch_gap_factor s i)"
      by (simp add: algebra_simps)
    also have "... = (1 - stoch_gap_factor s i) * f OPT"
      by (simp add: mult.commute)
    finally show ?thesis .
  qed

  from lower1 rewrite_rhs show ?thesis
    by simp
qed

subsection \<open>Closed-form exponential bound at i = k\<close>

lemma stoch_gap_factor_at_k_le_exp_neg_alpha:
  assumes k_pos: "0 < k"
  shows "stoch_gap_factor s k \<le> exp (- alpha_stoch s)"
proof -
  have alpha_le_k: "alpha_stoch s \<le> real k"
    by (rule alpha_stoch_le_real_k[OF k_pos])

  have alpha_nonneg: "0 \<le> alpha_stoch s"
    by (rule alpha_stoch_ge_0)

  have "(1 - alpha_stoch s / real k) ^ k \<le> exp (- alpha_stoch s)"
    using k_pos alpha_le_k alpha_nonneg exp_ge_one_minus_x_over_n_power_n
    by presburger
  then show ?thesis
    unfolding stoch_gap_factor_def .
qed

theorem uniform_wr_value_bound_eps_exp:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes k_pos:    "0 < k"
  assumes k_le_V:   "k \<le> card V"
  assumes A0:       "A 0 = {}"
  assumes A_sub:    "\<And>i. A i \<subseteq> V"
  assumes A_le_OPT: "\<And>i. f (A i) \<le> f OPT"
  assumes step_eq:
    "\<And>i. f (A (Suc i)) = f (A i) + uniform_wr_weighted.expected_step_gain (A i) (sample_size_eps_ceil eps)"
  assumes norm0:    "f {} = 0"
  assumes eps:      "0 < eps" "eps < 1"
  shows
    "f (A k) \<ge> (1 - exp (-(1 - eps))) * f OPT"
proof -
  let ?s = "sample_size_eps_ceil eps"

  have base:
    "f (A k) \<ge> (1 - stoch_gap_factor ?s k) * f OPT"
    using uniform_wr_value_bound_alpha[
      where A = A and i = k and s = ?s,
      OF OPT_sub OPT_fin OPT_card k_pos A0 A_sub A_le_OPT step_eq norm0
    ]
    by simp

  have gapfac_le:
    "stoch_gap_factor ?s k \<le> exp (- alpha_stoch ?s)"
    by (rule stoch_gap_factor_at_k_le_exp_neg_alpha[OF k_pos, of ?s])

  have alpha_ge:
    "alpha_stoch ?s \<ge> 1 - eps"
    using alpha_stoch_sample_size_eps_ceil_ge_one_minus_eps[OF k_pos k_le_V eps]
    by simp

  have exp_mono:
    "exp (- alpha_stoch ?s) \<le> exp (-(1 - eps))"
    using alpha_ge
    by simp

  have coeff_ge:
    "1 - stoch_gap_factor ?s k \<ge> 1 - exp (-(1 - eps))"
    using gapfac_le exp_mono
    by linarith

  have OPT_nonneg: "0 \<le> f OPT"
  proof -
    have "{} \<subseteq> OPT"
      using OPT_sub by auto
    then have "f {} \<le> f OPT"
      using monotone_f[rule_format, of "{}" OPT] OPT_sub
      by auto
    with norm0 show ?thesis
      by linarith
  qed

  have scaled_ge:
    "(1 - stoch_gap_factor ?s k) * f OPT
      \<ge> (1 - exp (-(1 - eps))) * f OPT"
    using coeff_ge OPT_nonneg
    by (intro mult_right_mono) simp_all

  show ?thesis
    using base scaled_ge
    by linarith
qed

subsection \<open>Paper-facing AAAI form\<close>

lemma exp_eps_secant_bound:
  fixes eps :: real
  assumes eps01: "0 \<le> eps" "eps \<le> 1"
  shows "exp eps \<le> 1 - eps + eps * exp 1"
proof -
  have exp_convex_01: "convex_on {0..1} exp"
    by (rule convex_on_subset[OF exp_convex]) auto

  have h:
    "exp (((1 - eps) * 0) + eps * 1)
      \<le> (1 - eps) * exp 0 + eps * exp 1"
    using convex_onD_Icc[OF exp_convex_01, of eps] eps01
    by simp

  then show ?thesis
    by simp
qed

lemma exp_shift_bound_eps:
  fixes eps :: real
  assumes eps01: "0 \<le> eps" "eps \<le> 1"
  shows "exp (-(1 - eps)) \<le> exp (-1) + eps"
proof -
  have secant: "exp eps \<le> 1 - eps + eps * exp 1"
    using exp_eps_secant_bound[of eps] eps01
    by simp

  have shift:
    "exp (-(1 - eps)) = exp eps * exp (-1)"
  proof -
    have "exp (-(1 - eps)) = exp (eps - 1)"
      by simp
    also have "... = exp (eps + (-1))"
      by (subst diff_conv_add_uminus) simp
    also have "... = exp eps * exp (-1)"
      by (rule exp_add)
    finally show ?thesis .
  qed

  have expm1_pos: "0 < exp (-1::real)"
    using exp_gt_zero[of "-1::real"] .

  have expm1_nonneg: "0 \<le> exp (-1::real)"
    using expm1_pos by linarith

  have step1:
    "exp eps * exp (-1) \<le> (1 - eps + eps * exp 1) * exp (-1)"
    using secant expm1_nonneg
    by (intro mult_right_mono) simp_all

  have exp_cancel: "exp (1::real) * exp (-1) = 1"
  proof -
    have "exp (1::real) * exp (-1) = exp ((1::real) + (-1))"
      by (subst exp_add[symmetric]) simp
    also have "... = 1"
      by simp
    finally show ?thesis .
  qed

  have step2:
    "(1 - eps + eps * exp 1) * exp (-1) = exp (-1) - eps * exp (-1) + eps"
  proof -
    have "(1 - eps + eps * exp 1) * exp (-1)
        = (1 - eps) * exp (-1) + eps * exp 1 * exp (-1)"
      by (simp add: algebra_simps)
    also have "... = exp (-1) - eps * exp (-1) + eps * (exp 1 * exp (-1))"
      by (simp add: algebra_simps)
    also have "... = exp (-1) - eps * exp (-1) + eps"
      using exp_cancel by simp
    finally show ?thesis .
  qed

  have step3:
    "exp (-1) - eps * exp (-1) + eps \<le> exp (-1) + eps"
  proof -
    have "0 \<le> eps * exp (-1)"
      using eps01 expm1_nonneg
      by (intro mult_nonneg_nonneg) simp_all
    then show ?thesis
      by linarith
  qed

  show ?thesis
    using shift step1 step2 step3
    by linarith
qed

theorem uniform_wr_value_bound_eps_AAAI:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes k_pos:    "0 < k"
  assumes k_le_V:   "k \<le> card V"
  assumes A0:       "A 0 = {}"
  assumes A_sub:    "\<And>i. A i \<subseteq> V"
  assumes A_le_OPT: "\<And>i. f (A i) \<le> f OPT"
  assumes step_eq:
    "\<And>i. f (A (Suc i)) = f (A i) + uniform_wr_weighted.expected_step_gain (A i) (sample_size_eps_ceil eps)"
  assumes norm0:    "f {} = 0"
  assumes eps:      "0 < eps" "eps < 1"
  shows
    "f (A k) \<ge> (1 - exp (-1) - eps) * f OPT"
proof -
  have stronger:
    "f (A k) \<ge> (1 - exp (-(1 - eps))) * f OPT"
    using uniform_wr_value_bound_eps_exp[
      where A = A,
      OF OPT_sub OPT_fin OPT_card k_pos k_le_V A0 A_sub A_le_OPT step_eq norm0 eps
    ]
    by simp

  have shift_bd: "exp (-(1 - eps)) \<le> exp (-1) + eps"
    using exp_shift_bound_eps[of eps] eps
    by simp

  have coeff_ge:
    "1 - exp (-(1 - eps)) \<ge> 1 - exp (-1) - eps"
    using shift_bd
    by linarith

  have OPT_nonneg: "0 \<le> f OPT"
    by (rule opt_nonneg_from_normalized[OF OPT_sub norm0])

  have scaled_ge:
    "(1 - exp (-(1 - eps))) * f OPT
      \<ge> (1 - exp (-1) - eps) * f OPT"
    using coeff_ge OPT_nonneg
    by (intro mult_right_mono) simp_all

  show ?thesis
    using stronger scaled_ge
    by linarith
qed

corollary uniform_wr_value_bound_eps_AAAI_invexp:
  fixes A :: "nat \<Rightarrow> 'a set"
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes k_pos:    "0 < k"
  assumes k_le_V:   "k \<le> card V"
  assumes A0:       "A 0 = {}"
  assumes A_sub:    "\<And>i. A i \<subseteq> V"
  assumes A_le_OPT: "\<And>i. f (A i) \<le> f OPT"
  assumes step_eq:
    "\<And>i. f (A (Suc i)) = f (A i) + uniform_wr_weighted.expected_step_gain (A i) (sample_size_eps_ceil eps)"
  assumes norm0:    "f {} = 0"
  assumes eps:      "0 < eps" "eps < 1"
  shows
    "f (A k) \<ge> (1 - 1 / exp 1 - eps) * f OPT"
proof -
  have base_AAAI:
    "f (A k) \<ge> (1 - exp (-1) - eps) * f OPT"
    using uniform_wr_value_bound_eps_AAAI[
      where A = A,
      OF OPT_sub OPT_fin OPT_card k_pos k_le_V A0 A_sub A_le_OPT step_eq norm0 eps
    ]
    by simp
  then show ?thesis
    by (simp add: exp_minus field_simps)
qed


subsection \<open>Thin paper-facing packaging with oracle budget\<close>

text \<open>
The current abstraction boundary separates:

  • the approximation theorem, which is phrased for an abstract set-valued
    state sequence A satisfying the established one-step value-update equation;

  • the executable stochastic trace layer, whose oracle cost is counted via
    stochastic_greedy_trace_oracle_calls.

The following corollaries do not yet identify these two objects as the same
semantic run. Rather, they package the two guarantees side by side under the
same epsilon-driven sample-size discipline sample_size_eps_ceil eps.
\<close>

corollary uniform_wr_trace_gain_evals_le_eps_budget_size:
  assumes trace_sz: "trace_sample_size (sample_size_eps_ceil eps) Rs"
  shows
    "stochastic_greedy_trace_gain_evals Rs \<le> stochastic_eps_budget eps"
  using stochastic_greedy_trace_gain_evals_le_eps_budget_size[OF trace_sz] .

corollary uniform_wr_trace_oracle_calls_le_eps_budget_size:
  assumes trace_sz: "trace_sample_size (sample_size_eps_ceil eps) Rs"
  shows
    "stochastic_greedy_trace_oracle_calls Rs \<le> stochastic_eps_oracle_budget eps"
  using stochastic_greedy_trace_oracle_calls_le_eps_budget_size[OF trace_sz] .

theorem uniform_wr_AAAI_package:
  fixes A  :: "nat \<Rightarrow> 'a set"
    and Rs :: "'a list list"
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes k_pos:    "0 < k"
  assumes k_le_V:   "k \<le> card V"
  assumes A0:       "A 0 = {}"
  assumes A_sub:    "\<And>i. A i \<subseteq> V"
  assumes A_le_OPT: "\<And>i. f (A i) \<le> f OPT"
  assumes step_eq:
    "\<And>i. f (A (Suc i)) =
          f (A i) + uniform_wr_weighted.expected_step_gain (A i) (sample_size_eps_ceil eps)"
  assumes norm0:    "f {} = 0"
  assumes eps:      "0 < eps" "eps < 1"
  assumes trace_sz: "trace_sample_size (sample_size_eps_ceil eps) Rs"
  shows
    "f (A k) \<ge> (1 - exp (-1) - eps) * f OPT
     \<and> stochastic_greedy_trace_oracle_calls Rs \<le> stochastic_eps_oracle_budget eps"
proof
  show "f (A k) \<ge> (1 - exp (-1) - eps) * f OPT"
    using uniform_wr_value_bound_eps_AAAI[
      where A = A,
      OF OPT_sub OPT_fin OPT_card k_pos k_le_V A0 A_sub A_le_OPT step_eq norm0 eps
    ]
    by simp

  show "stochastic_greedy_trace_oracle_calls Rs \<le> stochastic_eps_oracle_budget eps"
    using uniform_wr_trace_oracle_calls_le_eps_budget_size[OF trace_sz] .
qed

corollary uniform_wr_AAAI_package_invexp:
  fixes A  :: "nat \<Rightarrow> 'a set"
    and Rs :: "'a list list"
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes k_pos:    "0 < k"
  assumes k_le_V:   "k \<le> card V"
  assumes A0:       "A 0 = {}"
  assumes A_sub:    "\<And>i. A i \<subseteq> V"
  assumes A_le_OPT: "\<And>i. f (A i) \<le> f OPT"
  assumes step_eq:
    "\<And>i. f (A (Suc i)) =
          f (A i) + uniform_wr_weighted.expected_step_gain (A i) (sample_size_eps_ceil eps)"
  assumes norm0:    "f {} = 0"
  assumes eps:      "0 < eps" "eps < 1"
  assumes trace_sz: "trace_sample_size (sample_size_eps_ceil eps) Rs"
  shows
    "f (A k) \<ge> (1 - 1 / exp 1 - eps) * f OPT
     \<and> stochastic_greedy_trace_oracle_calls Rs \<le> stochastic_eps_oracle_budget eps"
proof
  show "f (A k) \<ge> (1 - 1 / exp 1 - eps) * f OPT"
    using uniform_wr_value_bound_eps_AAAI_invexp[
      where A = A,
      OF OPT_sub OPT_fin OPT_card k_pos k_le_V A0 A_sub A_le_OPT step_eq norm0 eps
    ]
    by simp

  show "stochastic_greedy_trace_oracle_calls Rs \<le> stochastic_eps_oracle_budget eps"
    using uniform_wr_trace_oracle_calls_le_eps_budget_size[OF trace_sz] .
qed

end

end