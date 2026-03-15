theory Stochastic_Greedy_Approx
  imports Stochastic_Greedy_Expected_OneStep
begin

section \<open>Approximation layer for StochasticGreedy\<close>

text \<open>
This theory packages the recurrence layer for the StochasticGreedy analysis.

The probabilistic one-step layer is developed in
theory Stochastic_Greedy_Expected_OneStep.  The present theory isolates the
pure approximation algebra:

  • convert a one-step gap inequality into a multiplicative gap recurrence;
  • solve the recurrence in closed form using @{term stoch_gap_factor};
  • provide a reusable template for the final stochastic approximation theorem.

The final fully concrete StochasticGreedy guarantee still depends on an
additional bridge identifying the one-step lower-bound constant with a residual
gap quantity.
\<close>

context Cardinality_Constraint
begin

definition stoch_gap_factor :: "nat \<Rightarrow> nat \<Rightarrow> real" where
  "stoch_gap_factor s i = (1 - alpha_stoch s / real k) ^ i"

lemma stoch_gap_factor_0 [simp]:
  "stoch_gap_factor s 0 = 1"
  unfolding stoch_gap_factor_def
  by simp

lemma stoch_gap_factor_Suc:
  "stoch_gap_factor s (Suc i)
   = (1 - alpha_stoch s / real k) * stoch_gap_factor s i"
  unfolding stoch_gap_factor_def
  by simp

lemma stoch_gap_factor_nonneg:
  assumes hk: "0 < k"
      and h\<alpha>: "alpha_stoch s \<le> real k"
      and h\<alpha>0: "0 \<le> alpha_stoch s"
  shows "0 \<le> stoch_gap_factor s i"
proof -
  have "0 \<le> 1 - alpha_stoch s / real k"
    using hk h\<alpha>
    by (simp add: field_simps)
  then show ?thesis
    unfolding stoch_gap_factor_def
    by simp
qed

lemma one_step_progress_to_gap_contraction:
  assumes hk: "0 < k"
      and h\<alpha>: "alpha_stoch s \<le> real k"
      and gap_nonneg: "0 \<le> gap"
      and step_lb: "step_gain \<ge> (alpha_stoch s / real k) * gap"
  shows "gap - step_gain \<le> (1 - alpha_stoch s / real k) * gap"
proof -
  have "gap - step_gain \<le> gap - (alpha_stoch s / real k) * gap"
    using step_lb by linarith
  also have "... = (1 - alpha_stoch s / real k) * gap"
    by (simp add: algebra_simps)
  finally show ?thesis .
qed

lemma stochastic_gap_recurrence_closed_form:
  fixes G :: "nat \<Rightarrow> real"
  assumes hk: "0 < k"
      and h\<alpha>: "alpha_stoch s \<le> real k"
      and h\<alpha>0: "0 \<le> alpha_stoch s"
      and G0: "G 0 \<le> B"
      and rec: "\<And>i. G (Suc i) \<le> (1 - alpha_stoch s / real k) * G i"
      and B_nonneg: "0 \<le> B"
  shows "G i \<le> stoch_gap_factor s i * B"
proof (induction i)
  case 0
  show ?case
    using G0 by simp
next
  case (Suc i)
  have "G (Suc i) \<le> (1 - alpha_stoch s / real k) * G i"
    using rec by simp
  also have "... \<le> (1 - alpha_stoch s / real k) * (stoch_gap_factor s i * B)"
  proof -
    have hfac: "0 \<le> 1 - alpha_stoch s / real k"
      using hk h\<alpha>
      by (simp add: field_simps)
    have "G i \<le> stoch_gap_factor s i * B"
      using Suc.IH .
    then show ?thesis
      using hfac
      by (intro mult_left_mono) simp_all
  qed
  also have "... = stoch_gap_factor s (Suc i) * B"
    by (simp add: stoch_gap_factor_Suc algebra_simps)
  finally show ?case .
qed

text \<open>
Template theorem.
If a stochastic process admits a one-step expected gap contraction of the
standard multiplicative form, then the gap after @{term i} rounds is bounded by
@{term "stoch_gap_factor s i"} times the initial gap bound.
\<close>

theorem stochastic_approx_from_gap_recurrence:
  fixes Gap :: "nat \<Rightarrow> real"
  assumes hk: "0 < k"
      and h\<alpha>: "alpha_stoch s \<le> real k"
      and h\<alpha>0: "0 \<le> alpha_stoch s"
      and Gap0: "Gap 0 \<le> OPT"
      and Gap_rec:
        "\<And>i. Gap (Suc i) \<le> (1 - alpha_stoch s / real k) * Gap i"
      and OPT_nonneg: "0 \<le> OPT"
  shows "Gap i \<le> stoch_gap_factor s i * OPT"
  by (rule stochastic_gap_recurrence_closed_form[
            where G = Gap and s = s and B = OPT and i = i,
            OF hk h\<alpha> h\<alpha>0 Gap0 Gap_rec OPT_nonneg])

text \<open>
The fully concrete StochasticGreedy approximation theorem will be obtained by
instantiating @{term Gap} with the expected residual gap of the stochastic run,
once the missing bridge from the one-step lower-bound constant to a residual-gap
quantity has been formalised.
\<close>

end

end