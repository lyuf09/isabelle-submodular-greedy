theory Greedy_Step_Spec
  imports
    "../Algorithms/Greedy_Submodular_Construct"
begin

text \<open>
Step-spec interface for greedy-style algorithms.

Any oracle select that (on every finite non-empty candidate set A)
returns an element in A whose marginal gain is maximal
can be interpreted as the argmax oracle in locale Greedy_Setup.
\<close>

locale Greedy_Step_Oracle =
  Cardinality_Constraint V f k
  for V :: "'a set" and f :: "'a set \<Rightarrow> real" and k :: nat +
  fixes select :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a"
  assumes select_mem:
    "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> select S A \<in> A"
  assumes select_max:
    "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> (\<forall>y \<in> A. gain S y \<le> gain S (select S A))"
begin

sublocale Greedy_Setup V f k select
proof
  fix S :: "'a set" and A :: "'a set"
  assume finA: "finite A"
  assume neA: "A \<noteq> {}"
  show "select S A \<in> A"
    using select_mem[OF finA neA] .
  show "\<forall>y \<in> A. gain S y \<le> gain S (select S A)"
    using select_max[OF finA neA] .
qed

end

end