theory Experiments_Nonsubmodular_Counterexample
  imports Experiments_Exhaustive
begin

text \<open>
A tiny monotone but non-submodular set function where greedy can be worse than 1 - 1/e.

We use V = {A,B,C}, k = 2.
Define a monotone function f such that:
  f({A}) = 100, f({B}) = 60, f({C}) = 60,
  f({A,B}) = 100, f({A,C}) = 100,
  f({B,C}) = 200, f({A,B,C}) = 200.
Greedy picks A first (largest singleton), then adds nothing; optimum is {B,C}.
Ratio = 100 / 200 = 0.5 (< 1 - 1/e).
\<close>

datatype Elem = A | B | C

definition f_bad :: "Elem set => nat" where
  "f_bad S =
     (if S = {} then 0
      else if S = {A} then 100
      else if S = {B} then 60
      else if S = {C} then 60
      else if S = {A,B} then 100
      else if S = {A,C} then 100
      else if S = {B,C} then 200
      else 200)"

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

definition Vlist :: "Elem list" where
  "Vlist = [A, B, C]"

definition k :: nat where
  "k = 2"

definition greedy_sol :: "Elem set" where
  "greedy_sol = greedy_list f_bad k Vlist {}"

definition opt_sol :: "Elem set" where
  "opt_sol = enum_opt_set f_bad Vlist k"

text \<open>Show a concrete violation of submodularity via the standard inequality.\<close>

lemma not_submodular_witness:
  "f_bad {B} + f_bad {C} < f_bad ({B} \<union> {C}) + f_bad ({B} \<inter> {C})"
  by (simp add: f_bad_def; auto)

text \<open>Executable outputs.\<close>

value "greedy_sol"
value "f_bad greedy_sol"
value "opt_sol"
value "f_bad opt_sol"
value "if f_bad opt_sol = 0 then (0::nat) else (f_bad greedy_sol * 100 div f_bad opt_sol)"

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