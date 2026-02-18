theory Experiments_Coverage_Suboptimal
  imports Experiments_Exhaustive
begin

text \<open>
A tiny monotone submodular (coverage) instance where greedy is strictly suboptimal.

We use a coverage function f(S) = |\<Union>_{x\<in>S} g(x)| under a cardinality constraint k=2.
The instance is constructed so that greedy picks a large singleton first, but then
its second choice adds only 1 new feature; whereas the optimal pair covers 6 features.
\<close>

datatype Item2 = A0 | B0 | C0
datatype Feature2 = H1 | H2 | H3 | H4 | H5 | H6

fun g2 :: "Item2 => Feature2 set" where
  "g2 A0 = {H1, H2, H3, H4}" |
  "g2 B0 = {H1, H2, H5}" |
  "g2 C0 = {H3, H4, H6}"

definition f2 :: "Item2 set => nat" where
  "f2 S = card (\<Union>x\<in>S. g2 x)"

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

definition Vlist2 :: "Item2 list" where
  "Vlist2 = [A0, B0, C0]"

definition k2 :: nat where
  "k2 = 2"

definition greedy_sol2 :: "Item2 set" where
  "greedy_sol2 = greedy_list f2 k2 Vlist2 {}"

definition opt_sol2 :: "Item2 set" where
  "opt_sol2 = enum_opt_set f2 Vlist2 k2"

text \<open>Core outputs: sets, values, and ratio (as an integer percentage).\<close>

value "greedy_sol2"
value "f2 greedy_sol2"
value "opt_sol2"
value "f2 opt_sol2"
value "if f2 opt_sol2 = 0 then (0::nat) else (f2 greedy_sol2 * 100 div f2 opt_sol2)"

text \<open>Basic empirical counts (same counting convention as in the first toy example).\<close>

definition greedy_marginal_evals2 :: nat where
  "greedy_marginal_evals2 =
     sum_list (map (%i. length Vlist2 - i) [0..<k2])"

definition greedy_f_evals2 :: nat where
  "greedy_f_evals2 = 2 * greedy_marginal_evals2"

definition exhaustive_candidates2 :: nat where
  "exhaustive_candidates2 = length (subseqs_upto_k Vlist2 k2)"

value "greedy_marginal_evals2"
value "greedy_f_evals2"
value "exhaustive_candidates2"

end