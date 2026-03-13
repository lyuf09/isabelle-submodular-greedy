theory Stochastic_Greedy_OneStep
  imports Stochastic_Greedy_Sampling
begin

section \<open>One-step progress interface for StochasticGreedy\<close>

text \<open>
The purpose of this theory is to isolate the central one-step expected-gain
lemma of StochasticGreedy.

Unlike the deterministic classical greedy proof, the stochastic variant will be
organised around a decomposition into:
  • sampling lemmas about hitting OPT - S,
  • a symmetry / averaging lemma on the sampled intersection,
  • a one-step expected marginal-gain bound.

We deliberately keep this file as an interface layer during the first week, so
that the final theorem statement can be stabilised before the probabilistic
infrastructure is developed.
\<close>

context Cardinality_Constraint
begin

definition residual_candidates :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "residual_candidates OPT S = OPT - S"

lemma residual_candidates_subset_V:
  assumes "OPT \<subseteq> V" "S \<subseteq> V"
  shows "residual_candidates OPT S \<subseteq> V"
  using assms unfolding residual_candidates_def by auto

lemma finite_residual_candidates [simp]:
  assumes "OPT \<subseteq> V"
  shows "finite (residual_candidates OPT S)"
proof -
  have "finite OPT"
    using assms finite_V finite_subset by blast
  then show ?thesis
    unfolding residual_candidates_def by simp
qed

text \<open>
Planned target theorem for a later stage:

  Assuming an appropriate random-sampling model for the trace generated in one
  round, show that the expected marginal gain of the chosen element is bounded
  below by a suitable alpha_stoch-scaled average over the residual optimal set.

That theorem will serve as the bridge from the sampling layer to the final
approximation recurrence.
\<close>

end

end