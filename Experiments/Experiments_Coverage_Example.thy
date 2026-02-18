theory Experiments_Coverage_Example
  imports Experiments_Exhaustive
begin

datatype Item = A | B | C | D | E
datatype Feature = F1 | F2 | F3 | F4 | F5

fun g :: "Item => Feature set" where
  "g A = {F1, F2}" |
  "g B = {F2, F3}" |
  "g C = {F3, F4}" |
  "g D = {F4, F5}" |
  "g E = {F1, F5}"

definition f_cov :: "Item set => nat" where
  "f_cov S = card (\<Union>x\<in>S. g x)"

definition gain :: "('a set => nat) => 'a set => 'a => nat" where
  "gain f S e = f (insert e S) - f S"

definition argmax1 :: "('a => 'b::linorder) => 'a list => 'a" where
  "argmax1 h xs =
     (case xs of
        [] => undefined
      | x#xs' => foldl (%best y. if h best <= h y then y else best) x xs')"

fun greedy_list :: "('a set => nat) => nat => 'a list => 'a set => 'a set" where
  "greedy_list f 0 Vlist S = S" |
  "greedy_list f (Suc k) Vlist S =
     (let R = filter (%e. e \<notin> S) Vlist in
      if R = [] then S
      else
        let best = argmax1 (%e. gain f S e) R in
        greedy_list f k Vlist (insert best S))"

definition Vlist :: "Item list" where
  "Vlist = [A, B, C, D, E]"

definition k :: nat where
  "k = 2"

definition greedy_sol :: "Item set" where
  "greedy_sol = greedy_list f_cov k Vlist {}"

definition opt_sol :: "Item set" where
  "opt_sol = enum_opt_set f_cov Vlist k"

value "greedy_sol"
value "f_cov greedy_sol"
value "opt_sol"
value "f_cov opt_sol"
value "if f_cov opt_sol = 0 then (0::nat) else (f_cov greedy_sol * 100 div f_cov opt_sol)"

definition greedy_marginal_evals :: nat where
  "greedy_marginal_evals =
     sum_list (map (%i. length Vlist - i) [0..<k])"

definition greedy_f_evals :: nat where
  "greedy_f_evals = 2 * greedy_marginal_evals"

definition exhaustive_candidates :: nat where
  "exhaustive_candidates = length (subseqs_upto_k Vlist k)"

value "greedy_marginal_evals"
value "greedy_f_evals"
value "exhaustive_candidates"

end