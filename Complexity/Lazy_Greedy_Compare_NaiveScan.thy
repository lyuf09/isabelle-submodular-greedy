theory Lazy_Greedy_Compare_NaiveScan
  imports
    Lazy_Greedy_TotalOracleCost
    "../Core/Oracle_Cost"
    "../Proofs/Lazy_Greedy_Stateful_StepSpec"
begin

context Cardinality_Constraint
begin

lemma step_gain_evals_le_card_remaining:
  "step_gain_evals i \<le> card (remaining (lazy_state i))"
proof -
  let ?st = "lazy_state i"
  let ?A  = "remaining ?st"
  show ?thesis
  proof (cases "?A = {}")
    case True
    then show ?thesis
      by (simp add: step_gain_evals_def Let_def)
  next
    case False
    have "step_gain_evals i = lazy_select_gain_evals (Sg ?st) ?A (ubg ?st)"
      using False by (simp add: step_gain_evals_def Let_def)
    also have "... \<le> card ?A"
      using lazy_select_gain_evals_le_cardA by simp
    finally show ?thesis by simp
  qed
qed

lemma card_lazy_set_eq_index_upto:
  assumes m_le: "m \<le> card V"
  shows "\<And>i. i \<le> m \<Longrightarrow> card (lazy_set i) = i"
proof -
  fix i
  assume i_le: "i \<le> m"
  show "card (lazy_set i) = i"
    using i_le
  proof (induction i)
    case 0
    then show ?case
      by (simp add: lazy_set_def init_state_def)
  next
    case (Suc i)
    have i_le_m: "i \<le> m"
      using Suc.prems by simp

    have IH: "card (lazy_set i) = i"
      using Suc.IH[OF i_le_m] .

    have i_lt_m: "i < m"
      using Suc.prems by simp

    have i_lt_cardV: "i < card V"
      using less_le_trans[OF i_lt_m m_le] .

    have subV: "lazy_set i \<subseteq> V"
      using lazy_state_subset_V[of i]
      by (simp add: lazy_set_def)

    have finS: "finite (lazy_set i)"
      using finite_subset[OF subV finite_V] .

    have rem_ne: "V - lazy_set i \<noteq> {}"
    proof
      assume empty: "V - lazy_set i = {}"
      have V_sub: "V \<subseteq> lazy_set i"
        using empty by auto
      have eqV: "lazy_set i = V"
        using subset_antisym[OF subV V_sub] by simp
      have cardEq: "card (lazy_set i) = card V"
        using eqV finite_V by simp
      have i_eqV: "i = card V"
        using IH cardEq by simp
      show False
        using i_eqV i_lt_cardV by simp
    qed

    have ins: "lazy_set (Suc i) = insert (lazy_choice i) (lazy_set i)"
      using lazy_set_Suc_insert_V_minus_S[OF rem_ne] .

    have xin: "lazy_choice i \<in> V - lazy_set i"
      using lazy_choice_in_V_minus_S[OF rem_ne] .

    have xnot: "lazy_choice i \<notin> lazy_set i"
      using xin by simp

    have cardSuc: "card (lazy_set (Suc i)) = Suc (card (lazy_set i))"
      using ins finS xnot by simp

    show ?case
      using cardSuc IH by simp
  qed
qed

(* C. Exact alignment with the standard scan baseline: remaining size = card V - i. *)
lemma card_remaining_eq_cardV_minus_i:
  assumes m_le: "m \<le> card V" and i_lt: "i < m"
  shows "card (remaining (lazy_state i)) = card V - i"
proof -
  have subV: "lazy_set i \<subseteq> V"
    using lazy_state_subset_V[of i] by (simp add: lazy_set_def)
  have finS: "finite (lazy_set i)"
    using finite_V subV by (meson finite_subset)
  have cardS: "card (lazy_set i) = i"
    using card_lazy_set_eq_index_upto[OF m_le] i_lt by simp

  have "remaining (lazy_state i) = V - lazy_set i"
    by (simp add: remaining_def lazy_set_def)

  moreover have "card (V - lazy_set i) = card V - card (lazy_set i)"
    using finite_V finS subV by (simp add: card_Diff_subset)

  ultimately show ?thesis
    using cardS by simp
qed

theorem total_gain_evals_le_naive_scan:
  assumes m_le: "m \<le> card V"
  shows "total_gain_evals m \<le> naive_greedy_gain_evals (card V) m"
proof -
  have step_le:
    "\<And>i. i < m \<Longrightarrow> step_gain_evals i \<le> card V - i"
  proof -
    fix i assume i_lt: "i < m"
    have "step_gain_evals i \<le> card (remaining (lazy_state i))"
      by (rule step_gain_evals_le_card_remaining)
    also have "... = card V - i"
      using card_remaining_eq_cardV_minus_i[OF m_le i_lt] .
    finally show "step_gain_evals i \<le> card V - i" .
  qed

  have tot_m: "total_gain_evals m \<le> (\<Sum>i<m. card V - i)"
    by (rule tot_le[of m], simp)
    by (induction m) (simp_all add: sum.lessThan_Suc)
  also have "... = naive_greedy_gain_evals (card V) m"
    by (simp add: naive_greedy_gain_evals_def)
  finally show ?thesis .
qed

theorem total_oracle_calls_le_naive_scan:
  assumes m_le: "m \<le> card V"
  shows "total_oracle_calls m \<le> naive_greedy_oracle_calls (card V) m"
proof -
  have "gain_call_cost * total_gain_evals m \<le> gain_call_cost * naive_greedy_gain_evals (card V) m"
    using total_gain_evals_le_naive_scan[OF m_le] by (simp add: mult_left_mono)
  thus ?thesis
    by (simp add: total_oracle_calls_def naive_greedy_oracle_calls_def)
qed

theorem total_oracle_calls_le_sum_untight:
  "total_oracle_calls m \<le> gain_call_cost * (\<Sum>i<m. step_gain_bound_untight i)"
  using total_gain_evals_le_sum_untight
  by (simp add: total_oracle_calls_def mult_left_mono)

end
end