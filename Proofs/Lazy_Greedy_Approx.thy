theory Lazy_Greedy_Approx
  imports Lazy_Greedy_Stateful_Approx
begin

text \<open>
  Legacy oracle-view approximation theorem for the non-stateful lazy selector.
  This theory instantiates the step-spec locale Greedy_Step_Oracle with the
  lazy argmax oracle argmax_gain_lazy.
  The main theorem-facing LazyGreedy result in this repository is the
  stateful one over lazy_set.
\<close>

context Cardinality_Constraint
begin

theorem lazy_oracle_greedy_approximation:
  assumes "k > 0" "k \<le> card V"
  shows "f (lazy_set k) \<ge> (1 - 1 / exp 1) * OPT_k"
  using lazy_stateful_approximation[OF assms] .

end

end