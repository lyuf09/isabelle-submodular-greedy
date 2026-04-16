theory Lazy_Greedy_Oracle_Approx
  imports "../Algorithms/Lazy_Greedy_Oracle" "Greedy_Approx_From_Spec"
begin

context Cardinality_Constraint
begin

interpretation Lazy_Oracle: Greedy_Step_Oracle V f k argmax_gain_lazy
proof
  fix S :: "'a set" and A :: "'a set"
  assume finA: "finite A"
  assume neA: "A \<noteq> {}"
  show "argmax_gain_lazy S A \<in> A"
    using argmax_gain_lazy_mem[OF finA neA] .
  show "\<forall>y\<in>A. gain S y \<le> gain S (argmax_gain_lazy S A)"
    using argmax_gain_lazy_max[OF finA neA] .
qed

abbreviation lazy_oracle_greedy_set :: "nat \<Rightarrow> 'a set"
  where "lazy_oracle_greedy_set i \<equiv> Greedy_Setup.greedy_set V argmax_gain_lazy i"

abbreviation lazy_oracle_OPT_k :: real
  where "lazy_oracle_OPT_k \<equiv> Greedy_Setup.OPT_k V f k"

lemmas lazy_oracle_greedy_approximation =
  Lazy_Oracle.spec_greedy_approximation

theorem lazy_oracle_greedy_approximation':
  assumes "k > 0" "k \<le> card V"
  shows "f (lazy_oracle_greedy_set k) \<ge> (1 - 1 / exp 1) * lazy_oracle_OPT_k"
  using Lazy_Oracle.spec_greedy_approximation[OF assms] .

end

end