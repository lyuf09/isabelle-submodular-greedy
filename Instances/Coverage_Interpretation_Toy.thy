theory Coverage_Interpretation_Toy
  imports
    "Coverage_Setup"
    "../Proofs/Greedy_Submodular_Approx"
    "../Experiments/Experiments_Coverage_Example"
begin

(*
  We interpret the abstract locale Greedy_Setup with the toy coverage function.
  NOTE: the executable greedy_list used in experiments is a separate refinement layer.
  Here we connect the coverage objective to the abstract theorem layer.
*)

(* g is finite for every Item, hence also for x \<in> V *)
lemma finite_g_all[simp]: "finite (g x)"
  by (cases x; simp)

definition V :: "Item set" where
  "V = set Vlist"

(* Instantiate the generic coverage setup on the toy ground set *)
interpretation Cov: Coverage_Setup V g
proof
  show "finite V"
    by (simp add: V_def Vlist_def)
 show "\<And>x. x \<in> V \<Longrightarrow> finite (g x)"
    by simp
qed

abbreviation f_cov_real :: "Item set \<Rightarrow> real" where
  "f_cov_real \<equiv> Cov.coverage"

lemma f_cov_real_mono_obl:
  assumes "S \<subseteq> T" and "T \<subseteq> V"
  shows "f_cov_real S \<le> f_cov_real T"
  using assms by (rule Cov.coverage_mono)

lemma f_cov_real_submod_obl:
  assumes "S \<subseteq> V" and "T \<subseteq> V"
  shows "f_cov_real (S \<union> T) + f_cov_real (S \<inter> T) \<le> f_cov_real S + f_cov_real T"
  using assms by (rule Cov.coverage_submodular)

lemma Submodular_Func_covtoy:
  "Submodular_Func V f_cov_real"
  by (rule Cov.Submodular_Func_coverage)

interpretation CovToy: Greedy_Setup V f_cov_real k
  "Submodular_Func.argmax_gain_some f_cov_real"
proof (unfold_locales)

  show "finite V"
    by (rule Cov.finite_V)
next
  show "f_cov_real {} = 0"
    by simp
next
  show "k \<le> card V"
    by (simp add: k_def V_def Vlist_def)
next
  show "\<And>S T. S \<subseteq> T \<Longrightarrow> T \<subseteq> V \<Longrightarrow> f_cov_real S \<le> f_cov_real T"
    by (rule f_cov_real_mono_obl)
next
  show "\<And>S T. S \<subseteq> V \<Longrightarrow> T \<subseteq> V \<Longrightarrow>
        f_cov_real (S \<union> T) + f_cov_real (S \<inter> T) \<le> f_cov_real S + f_cov_real T"
    by (rule f_cov_real_submod_obl)

next
  show "\<And>A::Item set. \<And>S::Item set.
        finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow>
        Submodular_Func.argmax_gain_some f_cov_real S A \<in> A"
  proof -
    fix A :: "Item set"
    fix S :: "Item set"
    assume finA: "finite A" and A0: "A \<noteq> {}"
    have SF: "Submodular_Func V f_cov_real"
      by (rule Submodular_Func_covtoy)
    show "Submodular_Func.argmax_gain_some f_cov_real S A \<in> A"
      using Greedy_Submodular_Construct.Submodular_Func.argmax_gain_some_mem
            [OF SF finA A0] .
  qed
next
  show "\<And>A::Item set. \<And>S::Item set.
        finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow>
        (\<forall>y\<in>A. Submodular_Func.gain f_cov_real S y
              \<le> Submodular_Func.gain f_cov_real S
                  (Submodular_Func.argmax_gain_some f_cov_real S A))"
  proof (intro ballI)
    fix A :: "Item set"
    fix S :: "Item set"
    fix y :: Item
    assume finA: "finite A" and A0: "A \<noteq> {}" and yA: "y \<in> A"
    have SF: "Submodular_Func V f_cov_real"
      by (rule Submodular_Func_covtoy)
    show "Submodular_Func.gain f_cov_real S y
          \<le> Submodular_Func.gain f_cov_real S
              (Submodular_Func.argmax_gain_some f_cov_real S A)"
      using Greedy_Submodular_Construct.Submodular_Func.argmax_gain_some_max
            [OF SF finA A0 yA] .
  qed

qed

(* --- What we get for free after interpretation --- *)

(* Use these to locate the exact theorem name in your development. *)
(* find_theorems name:CovToy "greedy_set" *)
(* find_theorems name:CovToy "OPT" *)
(* find_theorems name:"CovToy.*" "_ \<ge> ((1::real) - 1 / exp 1) * _" *)
(* find_theorems name:CovToy "approx" *)


lemma CovToy_main_bound:
  shows "f_cov_real (CovToy.greedy_set k) \<ge> ((1::real) - 1 / exp 1) * CovToy.OPT_k"
proof -
  have kpos: "0 < k"
    by (simp add: k_def)
  have kcard: "k \<le> card V"
    by (rule CovToy.k_le_cardV)
  show ?thesis
    using CovToy.greedy_approximation[OF kpos kcard]
    by simp
qed

(* Expose the main (1 - 1/e) approximation theorem for the toy coverage instance. *)
theorem CovToy_greedy_approximation:
  shows "(1 - 1 / exp 1) * CovToy.OPT_k \<le> f_cov_real (CovToy.greedy_set k)"
proof -
  have k_pos: "k > 0"
    by (simp add: k_def)
  have k_le: "k \<le> card V"
    by (rule CovToy.k_le_cardV)
  show ?thesis
    using CovToy.greedy_approximation[OF k_pos k_le]
    by simp
qed

end