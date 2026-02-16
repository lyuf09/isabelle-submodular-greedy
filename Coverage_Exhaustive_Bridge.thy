theory Coverage_Exhaustive_Bridge
  imports Coverage_Interpretation_Toy Experiments_Exhaustive_Correctness
begin

(* Bridge: the executable exhaustive optimum equals OPT_k in the toy instance. *)

lemma distinct_Vlist[simp]: "distinct Vlist"
  by (simp add: Vlist_def)

lemma enum_opt_set_is_OPT_k:
  shows "f_cov_real (enum_opt_set f_cov_real Vlist k) = CovToy.OPT_k"
proof -
  have enum_in: "enum_opt_set f_cov_real Vlist k \<in> CovToy.feasible_set_k"
    unfolding CovToy.feasible_set_k_def CovToy.feasible_def
    using enum_opt_set_subset[of f_cov_real Vlist k]
          enum_opt_set_card_le_k[of f_cov_real Vlist k]
    by (auto simp: V_def)

  have enum_le: "f_cov_real (enum_opt_set f_cov_real Vlist k) \<le> CovToy.OPT_k"
    using CovToy.OPT_k_upper_bound[OF enum_in] .

  obtain X where X_in: "X \<in> CovToy.feasible_set_k"
    and X_opt: "f_cov_real X = CovToy.OPT_k"
    using CovToy.exists_opt_set by blast

  have X_subV: "X \<subseteq> V"
    using CovToy.feasible_set_k_subset(1)[OF X_in] .
  have X_card: "card X \<le> k"
    using CovToy.feasible_set_k_subset(2)[OF X_in] .
  have X_sub: "X \<subseteq> set Vlist"
    using X_subV by (simp add: V_def)

  have X_le_enum: "f_cov_real X \<le> f_cov_real (enum_opt_set f_cov_real Vlist k)"
    using enum_opt_set_optimal_set[OF distinct_Vlist X_sub X_card] .

  have opt_le: "CovToy.OPT_k \<le> f_cov_real (enum_opt_set f_cov_real Vlist k)"
    using X_le_enum X_opt by simp

  show ?thesis
    using enum_le opt_le by (rule order_antisym)
qed

theorem CovToy_greedy_vs_enum:
  shows "f_cov_real (CovToy.greedy_set k)
        \<ge> (1 - 1 / exp 1) * f_cov_real (enum_opt_set f_cov_real Vlist k)"
proof -
  have main: "f_cov_real (CovToy.greedy_set k) \<ge> (1 - 1 / exp 1) * CovToy.OPT_k"
    using CovToy_greedy_approximation by simp
  have opt_id: "CovToy.OPT_k = f_cov_real (enum_opt_set f_cov_real Vlist k)"
    using enum_opt_set_is_OPT_k by simp
  show ?thesis
    using main by (simp add: opt_id)
qed

end