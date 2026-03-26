theory Submodular_Base
  imports Complex_Main
begin

locale Submodular_Func =
  fixes V :: "'a set" and f :: "'a set \<Rightarrow> real"
  assumes finite_V: "finite V"
      and monotone_f: "\<And>S T. S \<subseteq> T \<Longrightarrow> T \<subseteq> V \<Longrightarrow> f S \<le> f T"
      and submodular_f:
        "\<And>S T. S \<subseteq> V \<Longrightarrow> T \<subseteq> V \<Longrightarrow> f (S \<union> T) + f (S \<inter> T) \<le> f S + f T"
      and f_empty: "f {} = 0"
begin

text \<open>Marginal gain of adding a single element to a set.\<close>
definition gain :: "'a set \<Rightarrow> 'a \<Rightarrow> real" where
  "gain S e = f (S \<union> {e}) - f S"

lemma f_nonneg:
  assumes "S \<subseteq> V"
  shows "0 \<le> f S"
proof -
  have "{} \<subseteq> S" by auto
  from monotone_f[OF this assms] have "f {} \<le> f S" .
  thus ?thesis by (simp add: f_empty)
qed

lemma monotone_on_PowV:
  shows "monotone_on (Pow V) (\<subseteq>) (\<le>) f"
  unfolding monotone_on_def
  using monotone_f by auto

lemma monotone_f_from_monotone_on_PowV:
  assumes mono: "monotone_on (Pow V) (\<subseteq>) (\<le>) f"
  assumes "S \<subseteq> T" "T \<subseteq> V"
  shows "f S \<le> f T"
proof -
  have SV: "S \<in> Pow V" using assms(3) assms(2) by auto
  have TV: "T \<in> Pow V" using assms(3) by auto
  from mono have
    "\<forall>x\<in>Pow V. \<forall>y\<in>Pow V. x \<subseteq> y \<longrightarrow> f x \<le> f y"
    unfolding monotone_on_def by simp
  thus ?thesis
    using SV TV assms(2) by blast
qed

lemma gain_nonneg:
  assumes "S \<subseteq> V" and "x \<in> V - S"
  shows "0 \<le> gain S x"
proof -
  have "S \<subseteq> S \<union> {x}" by auto
  moreover from assms have "S \<union> {x} \<subseteq> V" by auto
  ultimately have "f S \<le> f (S \<union> {x})" using monotone_f by auto
  thus ?thesis by (simp add: gain_def)
qed

end


locale Cardinality_Constraint = Submodular_Func +
  fixes k :: nat
  assumes k_le_cardV: "k \<le> card V"
begin

definition feasible :: "'a set \<Rightarrow> bool" where
  "feasible S \<longleftrightarrow> S \<subseteq> V \<and> card S \<le> k"

definition feasible_set_k :: "'a set set" where
  "feasible_set_k = {S. feasible S}"

lemma feasible_iff_mem_feasible_set_k:
  "feasible S \<longleftrightarrow> S \<in> feasible_set_k"
  by (simp add: feasible_def feasible_set_k_def)

end

end