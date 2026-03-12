theory Lazy_Greedy_Approx
  imports
    "Greedy_Approx_From_Spec"
begin

text \<open>
This theory exposes the lazy approximation result in a convenient theorem-facing
form by instantiating the step-spec locale Greedy_Step_Oracle with the lazy
argmax oracle argmax_gain_lazy (defined in Lazy_Greedy). In this way, the
LazyGreedy construction is connected back to the reusable classical greedy
framework, and the Nemhauser–Wolsey (1 - 1/e) approximation guarantee is
recovered via Greedy_Approx_From_Spec.
\<close>

context Cardinality_Constraint
begin

interpretation LazyStep: Greedy_Step_Oracle V f k argmax_gain_lazy
proof
  fix S :: "'a set" and A :: "'a set"
  show "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> argmax_gain_lazy S A \<in> A"
    using argmax_gain_lazy_mem by blast
  show "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<forall>y\<in>A. gain S y \<le> gain S (argmax_gain_lazy S A))"
    using argmax_gain_lazy_max by blast
qed

theorem lazy_greedy_approximation:
  assumes "k > 0" "k \<le> card V"
  shows "f (Greedy_Setup.greedy_set V argmax_gain_lazy k)
       \<ge> (1 - 1 / exp 1) * Greedy_Setup.OPT_k V f k"
  using LazyStep.spec_greedy_approximation'[OF assms] .

end

end