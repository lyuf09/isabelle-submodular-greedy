theory Coverage_Setup
  imports "../Core/Submodular_Base"
begin

text \<open>
Reusable setup for (unweighted) coverage objectives of the form
  S \<mapsto> card (\<Union>x\<in>S. g x).
We prove that the induced real-valued function is monotone and submodular
on a finite ground set V, hence it instantiates the locale Submodular_Func.
\<close>

locale Coverage_Setup =
  fixes V :: "'a set"
    and g :: "'a \<Rightarrow> 'b set"
  assumes finite_V: "finite V"
    and finite_g: "\<And>x. x \<in> V \<Longrightarrow> finite (g x)"
begin

definition coverage_nat :: "'a set \<Rightarrow> nat" where
  "coverage_nat S = card (\<Union>x\<in>S. g x)"

definition coverage :: "'a set \<Rightarrow> real" where
  "coverage S = real (coverage_nat S)"

lemma coverage_empty[simp]: "coverage {} = 0"
  by (simp add: coverage_def coverage_nat_def)

lemma finite_union_g:
  assumes "S \<subseteq> V"
  shows "finite (\<Union>x\<in>S. g x)"
proof -
  have finS: "finite S"
    using finite_V assms by (meson finite_subset)
  have fin_g: "\<And>x. x \<in> S \<Longrightarrow> finite (g x)"
    using assms finite_g by auto
  show ?thesis
    using finS fin_g by (rule finite_UN_I)
qed

lemma coverage_mono:
  assumes "S \<subseteq> T" and "T \<subseteq> V"
  shows "coverage S \<le> coverage T"
proof -
  have subset: "(\<Union>x\<in>S. g x) \<subseteq> (\<Union>x\<in>T. g x)"
    using assms(1) by auto
  have finT: "finite (\<Union>x\<in>T. g x)"
    using finite_union_g assms(2) .
  have "coverage_nat S \<le> coverage_nat T"
    unfolding coverage_nat_def
    using card_mono[OF finT subset] .
  thus ?thesis
    by (simp add: coverage_def)
qed

lemma coverage_submodular:
  assumes SV: "S \<subseteq> V" and TV: "T \<subseteq> V"
  shows "coverage (S \<union> T) + coverage (S \<inter> T) \<le> coverage S + coverage T"
proof -
  let ?X = "\<Union>x\<in>S. g x"
  let ?Y = "\<Union>x\<in>T. g x"

  have finX: "finite ?X" using finite_union_g SV .
  have finY: "finite ?Y" using finite_union_g TV .
  have finInt: "finite (?X \<inter> ?Y)" using finX by simp

  have subset_int: "(\<Union>x\<in>(S \<inter> T). g x) \<subseteq> (?X \<inter> ?Y)"
    by auto

  have card_int_le: "card (\<Union>x\<in>(S \<inter> T). g x) \<le> card (?X \<inter> ?Y)"
    using card_mono[OF finInt subset_int] .

  have card_UI': "card ?X + card ?Y = card (?X \<union> ?Y) + card (?X \<inter> ?Y)"
    using card_Un_Int[OF finX finY] .

  have card_UI: "card (?X \<union> ?Y) + card (?X \<inter> ?Y) = card ?X + card ?Y"
    using card_UI' by simp

  have ineq:
    "real (card (?X \<union> ?Y)) + real (card (\<Union>x\<in>(S \<inter> T). g x))
      \<le> real (card ?X) + real (card ?Y)"
  proof -
    have "real (card (?X \<union> ?Y)) + real (card (\<Union>x\<in>(S \<inter> T). g x))
          \<le> real (card (?X \<union> ?Y)) + real (card (?X \<inter> ?Y))"
      using card_int_le by simp
    also have "... = real (card ?X) + real (card ?Y)"
      using card_UI by simp
    finally show ?thesis .
  qed

  show ?thesis
    unfolding coverage_def coverage_nat_def
    using ineq by simp
qed

lemma Submodular_Func_coverage:
  "Submodular_Func V coverage"
proof
  show "finite V" by (rule finite_V)
  show "\<And>S T. S \<subseteq> T \<Longrightarrow> T \<subseteq> V \<Longrightarrow> coverage S \<le> coverage T"
    by (rule coverage_mono)
  show "\<And>S T. S \<subseteq> V \<Longrightarrow> T \<subseteq> V
        \<Longrightarrow> coverage (S \<union> T) + coverage (S \<inter> T) \<le> coverage S + coverage T"
    by (rule coverage_submodular)
  show "coverage {} = 0" by simp
qed

end

end

