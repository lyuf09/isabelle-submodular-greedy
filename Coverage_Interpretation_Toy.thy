theory Coverage_Interpretation_Toy
  imports
    Greedy_Submodular_Approx
    Experiments_Coverage_Example
begin

(*
  We interpret the abstract locale Greedy_Setup with the toy coverage function.
  NOTE: the executable greedy_list used in experiments is a separate refinement layer.
  Here we connect the coverage objective to the abstract theorem layer.
*)

definition V :: "Item set" where
  "V = set Vlist"

definition f_cov_real :: "Item set \<Rightarrow> real" where
  "f_cov_real S = real (f_cov S)"

lemma finite_V: "finite V"
  by (simp add: V_def Vlist_def)

lemma finite_g[simp]: "finite (g x)"
  by (cases x; simp)

lemma finite_subset_V:
  assumes "S \<subseteq> V"
  shows "finite S"
  using finite_V assms by (meson finite_subset)

lemma finite_union_g:
  assumes "S \<subseteq> V"
  shows "finite (\<Union>x\<in>S. g x)"
  using finite_subset_V[OF assms] by simp

lemma f_cov_real_empty[simp]: "f_cov_real {} = 0"
  by (simp add: f_cov_real_def f_cov_def)

lemma f_cov_real_nonneg:
  assumes "S \<subseteq> V"
  shows "0 \<le> f_cov_real S"
  by (simp add: f_cov_real_def f_cov_def)

lemma f_cov_real_mono_on:
  assumes SV: "S \<subseteq> V" and TV: "T \<subseteq> V" and ST: "S \<subseteq> T"
  shows "f_cov_real S \<le> f_cov_real T"
proof -
  have subset: "(\<Union>x\<in>S. g x) \<subseteq> (\<Union>x\<in>T. g x)"
    using ST by auto
  have finT: "finite (\<Union>x\<in>T. g x)"
    using TV by (rule finite_union_g)
  have "card (\<Union>x\<in>S. g x) \<le> card (\<Union>x\<in>T. g x)"
    using subset finT by (simp add: card_mono)
  thus ?thesis
    by (simp add: f_cov_real_def f_cov_def)
qed

lemma f_cov_real_mono_obl:
  assumes ST: "S \<subseteq> T"
  assumes TV: "T \<subseteq> V"
  shows "f_cov_real S \<le> f_cov_real T"
proof -
  have SV: "S \<subseteq> V"
    using ST TV by auto
  show ?thesis
    by (rule f_cov_real_mono_on[OF SV TV ST])
qed

lemma f_cov_real_submod_on:
  assumes SV: "S \<subseteq> V" and TV: "T \<subseteq> V"
  shows "f_cov_real S + f_cov_real T \<ge> f_cov_real (S \<union> T) + f_cov_real (S \<inter> T)"
proof -
  let ?X = "\<Union>x\<in>S. g x"
  let ?Y = "\<Union>x\<in>T. g x"

  have finS: "finite S"
    using finite_V SV by (meson finite_subset)
  have finT: "finite T"
    using finite_V TV by (meson finite_subset)

  have finX: "finite ?X"
    using finS by simp
  have finY: "finite ?Y"
    using finT by simp

  have Un_eq: "(\<Union>x\<in>(S \<union> T). g x) = ?X \<union> ?Y"
    by auto

  have subset_int: "(\<Union>x\<in>S \<inter> T. g x )\<subseteq> ?X \<inter> ?Y"
    by auto

  have fin_inter: "finite (?X \<inter> ?Y)"
    using finX by simp

  have card_int_le: "card (\<Union>x\<in>S \<inter> T. g x) \<le> card (?X \<inter> ?Y)"
    by (rule card_mono[OF fin_inter subset_int])

  have cardUI: "card (?X \<union> ?Y) + card (?X \<inter> ?Y) = card ?X + card ?Y"
    by (metis finX finY card_Un_Int)

  have ineq_nat:
    "card (?X \<union> ?Y) + card (\<Union>x\<in>S \<inter> T. g x) \<le> card ?X + card ?Y"
  proof -
    have "card (?X \<union> ?Y) + card (\<Union>x\<in>S \<inter> T. g x)
          \<le> card (?X \<union> ?Y) + card (?X \<inter> ?Y)"
      using card_int_le by simp
    also have "... = card ?X + card ?Y"
      using cardUI by simp
    finally show ?thesis .
  qed

  have ineq_real:
    "real (card (?X \<union> ?Y)) + real (card (\<Union>x\<in>S \<inter> T. g x))
     \<le> real (card ?X) + real (card ?Y)"
    using ineq_nat by simp

  show ?thesis
    using ineq_real
    by (simp add: f_cov_real_def f_cov_def Un_eq algebra_simps)
qed

lemma f_cov_real_submod_obl:
  assumes "S \<subseteq> V" and "T \<subseteq> V"
  shows "f_cov_real (S \<union> T) + f_cov_real (S \<inter> T) \<le> f_cov_real S + f_cov_real T"
  using f_cov_real_submod_on[OF assms] by simp

(*
  Interpretation:
  This should generate locale obligations. We discharge them using the lemmas above.
  If Isabelle shows a remaining goal, it will usually be one of:
    - k > 0 / k >= 1 / k <= card V
    - monotonicity/submodularity stated in a slightly different interface
  In that case, the fix is a small wrapper lemma (we can add it immediately).
*)
lemma Submodular_Func_covtoy:
  shows "Submodular_Func V f_cov_real"
proof
  show "finite V" by (rule finite_V)
  show "f_cov_real {} = 0" by simp
  show "\<And>S T. S \<subseteq> T \<Longrightarrow> T \<subseteq> V \<Longrightarrow> f_cov_real S \<le> f_cov_real T"
    by (rule f_cov_real_mono_obl)
  show "\<And>S T. S \<subseteq> V \<Longrightarrow> T \<subseteq> V \<Longrightarrow>
        f_cov_real (S \<union> T) + f_cov_real (S \<inter> T) \<le> f_cov_real S + f_cov_real T"
    by (rule f_cov_real_submod_obl)
qed


interpretation CovToy: Greedy_Setup V f_cov_real k
  "Submodular_Func.argmax_gain_some f_cov_real"
proof (unfold_locales)

  show "finite V"
    by (rule finite_V)
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

(* Once you see the theorem name, expose it explicitly: *)
(* thm CovToy.<THEOREM_NAME> *)

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

end