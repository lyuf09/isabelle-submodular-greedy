theory Stochastic_vs_Greedy_Toy
  imports
    Experiments_Coverage_Example
    Cost_Model
begin

section \<open>Toy coverage sanity check for StochasticGreedy\<close>

text \<open>
Executable toy comparison: classical greedy vs. a deterministic-trace
refinement of StochasticGreedy on the small coverage instance already used
elsewhere in the repository.

This file is intentionally lightweight. It does not attempt any large-scale or
statistical experiment. Instead, it provides:

  • one fixed toy coverage instance,
  • one fixed sampled trace for the stochastic execution layer,
  • one small comparison of utility / gain-evaluation count / oracle-call count,
  • one cost sanity check against the expected k \<cdot> s budget.

This is an AFP-style executable sanity layer rather than a conference-style
empirical evaluation.
\<close>

subsection \<open>A small executable stochastic refinement\<close>

text \<open>
Unlike the abstract theorem layer, the present toy file uses a fully executable
refinement built directly on the nat-valued coverage objective f_cov from
Experiments_Coverage_Example.
\<close>

definition sampled_candidates_list :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sampled_candidates_list S xs = remdups (filter (\<lambda>e. e \<notin> set S) xs)"

definition stochastic_step_list :: "(Item set \<Rightarrow> nat) \<Rightarrow> Item list \<Rightarrow> Item list \<Rightarrow> Item list" where
  "stochastic_step_list f S xs =
     (let cand = sampled_candidates_list S xs in
      if cand = [] then S
      else
        let best = argmax1 (\<lambda>e. gain f (set S) e) cand
        in S @ [best])"

fun stochastic_run_trace_list :: "(Item set \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> Item list \<Rightarrow> Item list list \<Rightarrow> Item list" where
  "stochastic_run_trace_list f 0 S Rs = S"
| "stochastic_run_trace_list f (Suc t) S [] = S"
| "stochastic_run_trace_list f (Suc t) S (R # Rs) =
     stochastic_run_trace_list f t (stochastic_step_list f S R) Rs"

definition stochastic_greedy_trace_list :: "Item list list \<Rightarrow> Item list" where
  "stochastic_greedy_trace_list Rs = stochastic_run_trace_list f_cov k [] Rs"

definition stoch_step_gain_evals_exec :: "Item list \<Rightarrow> Item list \<Rightarrow> nat" where
  "stoch_step_gain_evals_exec S xs = length (sampled_candidates_list S xs)"

fun stoch_run_trace_gain_evals_exec :: "nat \<Rightarrow> Item list \<Rightarrow> Item list list \<Rightarrow> nat" where
  "stoch_run_trace_gain_evals_exec 0 S Rs = 0"
| "stoch_run_trace_gain_evals_exec (Suc t) S [] = 0"
| "stoch_run_trace_gain_evals_exec (Suc t) S (R # Rs) =
     stoch_step_gain_evals_exec S R +
     stoch_run_trace_gain_evals_exec t (stochastic_step_list f_cov S R) Rs"

definition stochastic_greedy_trace_gain_evals_exec :: "Item list list \<Rightarrow> nat" where
  "stochastic_greedy_trace_gain_evals_exec Rs =
     stoch_run_trace_gain_evals_exec k [] Rs"

definition stochastic_greedy_trace_oracle_calls_exec :: "Item list list \<Rightarrow> nat" where
  "stochastic_greedy_trace_oracle_calls_exec Rs =
     gain_call_cost * stochastic_greedy_trace_gain_evals_exec Rs"

subsection \<open>One fixed stochastic trace\<close>

definition stoch_s :: nat where
  "stoch_s = 2"

definition stoch_trace :: "Item list list" where
  "stoch_trace = [[A, B], [C, E]]"

subsection \<open>Executable outputs and budgets\<close>

definition stoch_sol_list :: "Item list" where
  "stoch_sol_list = stochastic_greedy_trace_list stoch_trace"

definition stoch_sol :: "Item set" where
  "stoch_sol = set stoch_sol_list"

definition stoch_gain_evals :: nat where
  "stoch_gain_evals = stochastic_greedy_trace_gain_evals_exec stoch_trace"

definition stoch_oracle_calls :: nat where
  "stoch_oracle_calls = stochastic_greedy_trace_oracle_calls_exec stoch_trace"

definition stoch_gain_budget :: nat where
  "stoch_gain_budget = k * stoch_s"

definition stoch_oracle_budget :: nat where
  "stoch_oracle_budget = gain_call_cost * k * stoch_s"

definition greedy_oracle_calls :: nat where
  "greedy_oracle_calls = gain_call_cost * greedy_marginal_evals"

lemma stoch_gain_evals_le_budget:
  "stoch_gain_evals \<le> stoch_gain_budget"
  unfolding stoch_gain_evals_def stoch_gain_budget_def
            stochastic_greedy_trace_gain_evals_exec_def
            stoch_s_def stoch_trace_def
            stoch_step_gain_evals_exec_def
            sampled_candidates_list_def
            stochastic_greedy_trace_list_def
            stochastic_step_list_def
            greedy_oracle_calls_def
  by eval

lemma stoch_oracle_calls_le_budget:
  "stoch_oracle_calls \<le> stoch_oracle_budget"
  unfolding stoch_oracle_calls_def stoch_oracle_budget_def
            stochastic_greedy_trace_oracle_calls_exec_def
            stoch_gain_evals_def stoch_gain_budget_def
            stochastic_greedy_trace_gain_evals_exec_def
            stoch_s_def stoch_trace_def
            stoch_step_gain_evals_exec_def
            sampled_candidates_list_def
            stochastic_greedy_trace_list_def
            stochastic_step_list_def
  by eval

subsection \<open>Paper-facing report format\<close>

definition sol_as_list :: "Item set \<Rightarrow> Item list" where
  "sol_as_list S = filter (\<lambda>e. e \<in> S) Vlist"

type_synonym run_report = "string * Item list * nat * nat * nat"

definition greedy_report :: run_report where
  "greedy_report =
     ( ''GREEDY'',
       sol_as_list greedy_sol,
       f_cov greedy_sol,
       greedy_marginal_evals,
       greedy_oracle_calls )"

definition stoch_report :: run_report where
  "stoch_report =
     ( ''STOCHASTIC'',
       stoch_sol_list,
       f_cov stoch_sol,
       stoch_gain_evals,
       stoch_oracle_calls )"

definition toy_summary :: "run_report list" where
  "toy_summary = [greedy_report, stoch_report]"

definition reference_values :: "(string * nat) list" where
  "reference_values =
     [ (''GREEDY_value'', f_cov greedy_sol),
       (''STOCHASTIC_value'', f_cov stoch_sol),
       (''OPT_value'', f_cov opt_sol) ]"

subsection \<open>Very small sanity checks\<close>

definition toy_checks :: "(string * bool) list" where
  "toy_checks =
     [ (''trace_size_ok'',
         (\<forall>xs \<in> set stoch_trace. length xs = stoch_s)),
       (''stoch_feasible'',
         distinct stoch_sol_list \<and> card stoch_sol \<le> k),
       (''stoch_value_le_opt'',
         f_cov stoch_sol \<le> f_cov opt_sol),
       (''stoch_value_eq_opt'',
         f_cov stoch_sol = f_cov opt_sol),
       (''stoch_gain_evals_le_budget'',
         stoch_gain_evals \<le> stoch_gain_budget),
       (''stoch_oracle_calls_le_budget'',
         stoch_oracle_calls \<le> stoch_oracle_budget),
       (''stoch_gain_evals_le_greedy'',
         stoch_gain_evals \<le> greedy_marginal_evals),
       (''stoch_oracle_calls_le_greedy'',
         stoch_oracle_calls \<le> greedy_oracle_calls)
     ]"

value stoch_sol_list
value toy_summary
value reference_values
value toy_checks

end