theory Cost_Model
  imports Main
begin

(* Cost model conventions:
   - One evaluation of f counts as 1 oracle call.
   - One evaluation of gain f S e is modelled as 2 oracle calls
     (because gain typically needs two calls to f). *)

definition f_call_cost :: nat where
  "f_call_cost = 1"

definition gain_call_cost :: nat where
  "gain_call_cost = 2 * f_call_cost"

(* Naive greedy scans all remaining elements each round:
   total gain evaluations = sum_{i=0..k-1} (n - i)
   total oracle calls = gain_call_cost * that number. *)

definition greedy_scan_gain_evals :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "greedy_scan_gain_evals n k = (\<Sum>i<k. (n - i))"

definition greedy_scan_oracle_calls :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "greedy_scan_oracle_calls n k = gain_call_cost * greedy_scan_gain_evals n k"

end