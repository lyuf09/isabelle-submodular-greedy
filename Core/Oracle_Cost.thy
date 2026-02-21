theory Oracle_Cost
  imports Main
begin

definition f_call_cost :: nat where
  "f_call_cost = 1"

definition gain_call_cost :: nat where
  "gain_call_cost = 2 * f_call_cost"

definition naive_greedy_gain_evals :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "naive_greedy_gain_evals n k =
     (\<Sum> i < k. n - i)"

definition naive_greedy_oracle_calls :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "naive_greedy_oracle_calls n k =
     gain_call_cost * naive_greedy_gain_evals n k"

end
