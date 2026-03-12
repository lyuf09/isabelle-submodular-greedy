theory Lazy_Greedy_Approx
  imports Lazy_Greedy_Stateful_Approx
begin

text \<open>
  Compatibility wrapper exposing the LazyGreedy approximation result
  in a legacy oracle-oriented form.
  The main approximation development for LazyGreedy in this repository
  is the stateful one over lazy_set, proved in Lazy_Greedy_Stateful_Approx.
  This theory simply re-exports that result under theorem-facing legacy naming.
\<close>

context Cardinality_Constraint
begin

theorem lazy_oracle_greedy_approximation:
  assumes "k > 0" "k \<le> card V"
  shows "f (lazy_set k) \<ge> (1 - 1 / exp 1) * OPT_k"
  using lazy_stateful_approximation[OF assms] .

end

end