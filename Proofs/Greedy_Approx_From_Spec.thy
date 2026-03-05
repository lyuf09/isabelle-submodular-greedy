theory Greedy_Approx_From_Spec
  imports
    "Greedy_Step_Spec"
    "Greedy_Submodular_Approx"
begin

text \<open>
Bridge file: from the step-spec locale Greedy_Step_Oracle to the existing
Nemhauser–Wolsey (1 − 1/e) guarantee proved in context Greedy_Setup.

After importing Greedy_Submodular_Approx, the theorem greedy_approximation
is available in context Greedy_Setup.
Since Greedy_Step_Spec establishes sublocale Greedy_Setup V f k select,
we can reuse greedy_approximation immediately for any oracle select
satisfying the step-spec assumptions.
\<close>

context Greedy_Step_Oracle
begin

text \<open>Match the naming style used for LazyOracle in Greedy_Submodular_Approx.\<close>

abbreviation spec_greedy_set :: "nat \<Rightarrow> 'a set" where
  "spec_greedy_set i \<equiv> Greedy_Setup.greedy_set V select i"

abbreviation spec_OPT_k :: real where
  "spec_OPT_k \<equiv> Greedy_Setup.OPT_k V f k"

lemmas spec_greedy_approximation = greedy_approximation

text \<open>Optional: a wrapper theorem with an explicit statement.\<close>
theorem spec_greedy_approximation':
  assumes "k > 0" "k \<le> card V"
  shows "f (spec_greedy_set k) \<ge> (1 - 1 / exp 1) * spec_OPT_k"
  using spec_greedy_approximation[OF assms] .

end

end