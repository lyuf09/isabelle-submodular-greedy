theory Lazy_vs_Greedy_Toy
  imports
    Experiments_Coverage_Example
    Cost_Model
begin

text \<open>
Executable toy comparison: naive greedy vs. a list-level lazy greedy refinement.

We reuse the toy coverage instance from Experiments_Coverage_Example:
  - Item / Feature / g / f_cov / gain / Vlist / k
  - greedy_sol / greedy_marginal_evals / greedy_f_evals

We implement a deterministic, executable "lazy argmax" loop over a cached
upper-bound list (Item \<times> nat), together with counters:
  - gain_evals: number of gain computations performed
  - tighten_steps: number of iterations where we updated an upper bound
\<close>


type_synonym ub_list = "(Item * nat) list"

definition remaining_ubs :: "Item set \<Rightarrow> ub_list \<Rightarrow> ub_list" where
  "remaining_ubs S ubs = filter (\<lambda>p. fst p \<notin> S) ubs"

definition argmax_pair1 :: "ub_list \<Rightarrow> (Item \<times> nat)" where
  "argmax_pair1 xs =
    (case xs of
       [] \<Rightarrow> undefined
     | x # xs' \<Rightarrow> foldl (\<lambda>best y. if snd best \<le> snd y then y else best) x xs')"

fun update_ub :: "Item \<Rightarrow> nat \<Rightarrow> ub_list \<Rightarrow> ub_list" where
  "update_ub e u [] = []"
| "update_ub e u (p # ps) =
     (if fst p = e then (e, u) # ps else p # update_ub e u ps)"

definition ub_init :: ub_list where
  "ub_init = map (\<lambda>e. (e, gain f_cov {} e)) Vlist"


type_synonym sel_res = "Item * ub_list * nat * nat"

fun lazy_select_fuel :: "nat \<Rightarrow> (Item set \<Rightarrow> nat) \<Rightarrow> Item set \<Rightarrow> ub_list \<Rightarrow> sel_res" where
  "lazy_select_fuel 0 f S ubs =
     (let rs = remaining_ubs S ubs;
          best = argmax_pair1 rs
      in (fst best, ubs, 0, 0))"
| "lazy_select_fuel (Suc n) f S ubs =
     (let rs   = remaining_ubs S ubs;
          best = argmax_pair1 rs;
          e    = fst best;
          ub   = snd best;
          g    = gain f S e;
          ubs' = update_ub e g ubs
      in if g = ub then (e, ubs', 1, 0)
         else (case lazy_select_fuel n f S ubs' of (e', ubs'', ge, ts) \<Rightarrow> (e', ubs'', Suc ge, Suc ts)))"

definition lazy_select :: "(Item set \<Rightarrow> nat) \<Rightarrow> Item set \<Rightarrow> ub_list \<Rightarrow> sel_res" where
  "lazy_select f S ubs = lazy_select_fuel (length (remaining_ubs S ubs)) f S ubs"


type_synonym run_res = "Item set * ub_list * nat * nat"

fun lazy_greedy_list :: "(Item set \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ub_list \<Rightarrow> Item set \<Rightarrow> run_res" where
  "lazy_greedy_list f 0 ubs S = (S, ubs, 0, 0)"
| "lazy_greedy_list f (Suc kk) ubs S =
     (let rs = remaining_ubs S ubs in
        if rs = [] then (S, ubs, 0, 0)
        else
          (case lazy_select f S ubs of (e, ubs', ge1, ts1) \<Rightarrow>
             (case lazy_greedy_list f kk ubs' (insert e S) of (S', ubs'', ge2, ts2) \<Rightarrow>
                (S', ubs'', ge1 + ge2, ts1 + ts2))))"

definition lazy_run :: run_res where
  "lazy_run = lazy_greedy_list f_cov k ub_init {}"

definition lazy_sol :: "Item set" where
  "lazy_sol = (case lazy_run of (S, ubs, ge, ts) \<Rightarrow> S)"

definition lazy_gain_evals :: nat where
  "lazy_gain_evals = (case lazy_run of (S, ubs, ge, ts) \<Rightarrow> ge)"

definition lazy_tighten_steps :: nat where
  "lazy_tighten_steps = (case lazy_run of (S, ubs, ge, ts) \<Rightarrow> ts)"

definition lazy_f_evals :: nat where
  "lazy_f_evals = gain_call_cost * lazy_gain_evals"


text \<open>
  Paper-artifact output (deterministic, fixed format):

    report = (tag, solution_as_list, f_value, gain_evals, tighten_steps, oracle_calls)

  We order the solution by Vlist to avoid any reliance on a linorder instance for Item.
\<close>

definition sol_as_list :: "Item set \<Rightarrow> Item list" where
  "sol_as_list S = filter (\<lambda>e. e \<in> S) Vlist"

type_synonym run_report = "string * Item list * nat * nat * nat * nat"

definition greedy_f_evals :: nat where
  "greedy_f_evals = gain_call_cost * greedy_marginal_evals"

definition greedy_report :: run_report where
  "greedy_report =
     (''GREEDY'',
      sol_as_list greedy_sol,
      f_cov greedy_sol,
      greedy_marginal_evals,
      0,
      greedy_f_evals)"

definition lazy_report :: run_report where
  "lazy_report =
     (''LAZY'',
      sol_as_list lazy_sol,
      f_cov lazy_sol,
      lazy_gain_evals,
      lazy_tighten_steps,
      lazy_f_evals)"

definition toy_summary :: "run_report list" where
  "toy_summary = [greedy_report, lazy_report]"

definition toy_checks :: "(string \<times> bool) list" where
  "toy_checks =
     [( ''same_value'', f_cov lazy_sol = f_cov greedy_sol ),
      ( ''lazy_gain_evals_le_greedy'', lazy_gain_evals \<le> greedy_marginal_evals ),
      ( ''lazy_oracle_calls_le_greedy'', lazy_f_evals \<le> greedy_f_evals )]"

value toy_summary
value toy_checks

end