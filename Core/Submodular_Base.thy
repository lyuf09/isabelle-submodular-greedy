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

lemma gain_nonneg:
  assumes "S \<subseteq> V" and "x \<in> V - S"
  shows "0 \<le> gain S x"
proof -
  have "S \<subseteq> S \<union> {x}" by auto
  moreover from assms have "S \<union> {x} \<subseteq> V" by auto
  ultimately have "f S \<le> f (S \<union> {x})" using monotone_f by auto
  thus ?thesis by (simp add: gain_def)
qed

text \<open>Diminishing returns for single-element marginal gains.\<close>
lemma gain_decreasing:
  assumes "S \<subseteq> T" "T \<subseteq> V" "x \<in> V" "x \<notin> T"
  shows "gain S x \<ge> gain T x"
proof -
  have Sx_sub_V: "insert x S \<subseteq> V"
    using assms by auto

  have subm:
    "f (insert x (S \<union> T)) + f (insert x S \<inter> T) \<le> f (insert x S) + f T"
    using submodular_f[OF Sx_sub_V assms(2)]
    by simp

  have inter_eq: "insert x S \<inter> T = S"
    using assms by auto

  have union_eq: "insert x (S \<union> T) = insert x T"
    using assms by auto

  from subm have "f S + f (insert x T) \<le> f T + f (insert x S)"
    by (simp add: inter_eq union_eq)

  hence "f (insert x S) - f S \<ge> f (insert x T) - f T"
    by linarith

  thus ?thesis
    by (simp add: gain_def)
qed

end

locale Cardinality_Constraint = Submodular_Func +
  fixes k :: nat
  assumes k_le_cardV: "k \<le> card V"
begin

definition feasible :: "'a set \<Rightarrow> bool" where
  "feasible S \<longleftrightarrow> S \<subseteq> V \<and> card S \<le> k"

lemma feasibleI:
  assumes "S \<subseteq> V" "card S \<le> k"
  shows "feasible S"
  using assms unfolding feasible_def by auto

lemma feasibleD:
  assumes "feasible S"
  shows "S \<subseteq> V" "card S \<le> k"
  using assms unfolding feasible_def by auto

lemma feasible_empty[simp]: "feasible {}"
  unfolding feasible_def by auto

lemma feasible_family_nonempty: "Collect feasible \<noteq> {}"
proof -
  have "\<exists>S. feasible S"
  proof
    show "feasible {}" by (rule feasible_empty)
  qed
  then show ?thesis by auto
qed

lemma finite_feasible_family: "finite {S. feasible S}"
proof -
  have "{S. feasible S} \<subseteq> Pow V"
    by (auto simp: feasible_def)
  moreover have "finite (Pow V)"
    using finite_V by simp
  ultimately show ?thesis
    by (rule finite_subset)
qed

subsection \<open>Finite maximizers and optimal feasible sets\<close>

lemma finite_has_maximal:
  assumes fin: "finite A"
    and nonempty: "A \<noteq> {}"
  shows "\<exists>x\<in>A. \<forall>y\<in>A. f y \<le> f x"
proof -
  have fin_image: "finite (f ` A)"
    using fin by simp
  have nonempty_image: "f ` A \<noteq> {}"
    using nonempty by auto

  have max_in_image: "Max (f ` A) \<in> f ` A"
    using Max_in[OF fin_image nonempty_image] .

  then obtain x where xA: "x \<in> A" and x_eq: "f x = Max (f ` A)"
    by auto

  have "\<forall>y\<in>A. f y \<le> f x"
  proof
    fix y
    assume yA: "y \<in> A"
    have fy_image: "f y \<in> f ` A"
      using yA by auto
    have "f y \<le> Max (f ` A)"
      using Max_ge[OF fin_image fy_image] .
    also have "... = f x"
      using x_eq by simp
    finally show "f y \<le> f x" .
  qed

  then show ?thesis
    using xA by blast
qed

subsection \<open>Optimal feasible sets\<close>

text \<open>
  We select a canonical optimal feasible set \<open>OPT_set\<close> using Hilbert choice
  and define \<open>OPT_k\<close> as its value. These are problem-level objects for the
  cardinality-constrained maximization problem, independent of any particular
  greedy implementation.
\<close>

definition OPT_set :: "'a set" where
  "OPT_set =
     (SOME X. feasible X \<and> (\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f X))"

lemma exists_max_feasible:
  "\<exists>X. feasible X \<and> (\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f X)"
proof -
  from finite_has_maximal[OF finite_feasible_family feasible_family_nonempty]
  obtain X where X_feas: "X \<in> Collect feasible"
    and X_max: "\<forall>Y \<in> Collect feasible. f Y \<le> f X"
    by blast
  have "feasible X \<and> (\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f X)"
    using X_feas X_max by auto
  thus ?thesis ..
qed

lemma OPT_set_props:
  shows OPT_set_in: "feasible OPT_set"
    and OPT_set_max: "\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f OPT_set"
proof -
  from exists_max_feasible
  obtain X where X_in: "feasible X"
    and X_max: "\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f X"
    by blast
  then have ex_spec:
    "\<exists>X. feasible X \<and> (\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f X)"
    by blast
  from someI_ex[OF ex_spec]
  have "feasible OPT_set \<and> (\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f OPT_set)"
    unfolding OPT_set_def by simp
  then show "feasible OPT_set"
    and "\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f OPT_set"
    by auto
qed

definition OPT_k :: real where
  "OPT_k = f OPT_set"

lemma exists_opt_set:
  "\<exists>X. feasible X \<and> f X = OPT_k"
proof -
  have "feasible OPT_set"
    by (rule OPT_set_in)
  moreover have "f OPT_set = OPT_k"
    unfolding OPT_k_def by simp
  ultimately show ?thesis
    by blast
qed

lemma OPT_k_upper_bound:
  assumes "feasible S"
  shows "f S \<le> OPT_k"
proof -
  have "\<forall>Y. feasible Y \<longrightarrow> f Y \<le> f OPT_set"
    by (rule OPT_set_max)
  with assms have "f S \<le> f OPT_set"
    by auto
  thus ?thesis
    unfolding OPT_k_def by simp
qed

lemma OPT_k_nonneg: "0 \<le> OPT_k"
proof -
  have "feasible {}"
    by (rule feasible_empty)
  then have "f {} \<le> OPT_k"
    by (rule OPT_k_upper_bound)
  thus ?thesis
    by (simp add: f_empty)
qed

end

section \<open>Acknowledgements\<close>

text \<open>
  The author is grateful to Wenda Li for careful reviews, comments, and
  guidance from the early stages of this project through the preparation of
  this AFP entry.
\<close>

end