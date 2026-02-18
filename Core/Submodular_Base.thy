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

text \<open>
  Diminishing-returns (DR) form of submodularity.

  This definition is included as an alternative interface to the lattice-based
  submodularity assumption used throughout the current development.
  At present, we do not establish the equivalence between the two formulations.

  The DR form is often more convenient when reasoning about algorithmic variants
  such as LazyGreedy or StochasticGreedy, while the lattice-based formulation
  aligns more naturally with classical submodular calculus on sets.

  Proving equivalence between these formulations is deferred and left as a
  potential future extension of the framework.
\<close>
definition dr_submodular_on :: "'a set \<Rightarrow> ('a set \<Rightarrow> real) \<Rightarrow> bool" where
  "dr_submodular_on W g \<longleftrightarrow>
     (\<forall>A\<subseteq>W. \<forall>B\<subseteq>W. A \<subseteq> B \<longrightarrow>
        (\<forall>i\<in>W - B. g (A \<union> {i}) - g A \<ge> g (B \<union> {i}) - g B))"

abbreviation dr_submodular_f :: bool where
  "dr_submodular_f \<equiv> dr_submodular_on V f"

lemma dr_submodular_fD:
  assumes dr: "dr_submodular_f"
      and A: "A \<subseteq> V" and B: "B \<subseteq> V" and AB: "A \<subseteq> B"
      and i: "i \<in> V - B"
  shows "gain A i \<ge> gain B i"
  using dr A B AB i
  unfolding dr_submodular_on_def gain_def
  by simp

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