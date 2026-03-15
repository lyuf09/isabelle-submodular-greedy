theory Stochastic_Greedy_Uniform_WR
  imports Stochastic_Greedy_Weighted_Sampling "HOL-Analysis.Analysis"
begin

section \<open>Uniform with-replacement sampling over the remaining set\<close>

text \<open>
This theory develops the concrete uniform with-replacement list model over the
remaining set V - S.

Important note.
In the current version of Stochastic_Greedy_Weighted_Sampling, the axioms
sample_space_mem and sample_mass_1 are quantified over all S and s. For a
genuine with-replacement model over V - S, these two requirements are
incompatible when V - S = {} and s > 0: there is no list of positive length
whose elements all lie in the empty set.

Accordingly, this theory focuses on:
  (1) the concrete list space,
  (2) the uniform probability assignment on that space,
  (3) exact hit / miss event formulas,
  (4) the intended lower-bound theorems.
\<close>

context Cardinality_Constraint
begin

subsection \<open>Concrete with-replacement list space\<close>

fun wr_space_on :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set" where
  "wr_space_on A 0 = {[]}" |
  "wr_space_on A (Suc s) = (\<Union>x\<in>A. (Cons x) ` wr_space_on A s)"

lemma wr_space_on_mem_iff:
  "xs \<in> wr_space_on A s \<longleftrightarrow> length xs = s \<and> set xs \<subseteq> A"
proof (induction s arbitrary: xs)
  case 0
  then show ?case
    by (cases xs) auto
next
  case (Suc s)
  then show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      by auto
  next
    case (Cons x ys)
    have
      "x # ys \<in> wr_space_on A (Suc s)
       \<longleftrightarrow> (\<exists>y\<in>A. \<exists>zs\<in>wr_space_on A s. x # ys = y # zs)"
      by auto
    also have "... \<longleftrightarrow> x \<in> A \<and> ys \<in> wr_space_on A s"
      by auto
    also have "... \<longleftrightarrow> length (x # ys) = Suc s \<and> set (x # ys) \<subseteq> A"
      using Suc.IH[of ys] by auto
    finally show ?thesis
      using Cons by simp
  qed
qed

lemma wr_space_on_length:
  assumes "xs \<in> wr_space_on A s"
  shows "length xs = s"
  using assms wr_space_on_mem_iff by auto

lemma wr_space_on_subset:
  assumes "xs \<in> wr_space_on A s"
  shows "set xs \<subseteq> A"
  using assms wr_space_on_mem_iff by auto

lemma finite_wr_space_on [simp]:
  assumes "finite A"
  shows "finite (wr_space_on A s)"
proof (induction s)
  case 0
  then show ?case by simp
next
  case (Suc s)
  have "finite (\<Union>x\<in>A. (Cons x) ` wr_space_on A s)"
  proof (rule finite_UN_I)
    show "finite A"
      by fact
    fix x
    assume "x \<in> A"
    have "finite (wr_space_on A s)"
      using Suc.IH assms by simp
    then show "finite ((Cons x) ` wr_space_on A s)"
      by simp
  qed
  then show ?case
    by simp
qed

lemma wr_space_on_nonempty_iff:
  "wr_space_on A s \<noteq> {} \<longleftrightarrow> A \<noteq> {} \<or> s = 0"
proof (induction s)
  case 0
  then show ?case by simp
next
  case (Suc s)
  show ?case
  proof
    assume "wr_space_on A (Suc s) \<noteq> {}"
    then obtain xs where "xs \<in> wr_space_on A (Suc s)"
      by blast
    then obtain x ys where "x \<in> A" "ys \<in> wr_space_on A s" "xs = x # ys"
      by auto
    then show "A \<noteq> {} \<or> Suc s = 0"
      by auto
  next
    assume "A \<noteq> {} \<or> Suc s = 0"
    then obtain x where "x \<in> A"
      by auto
    have len_rep: "length (replicate (Suc s) x) = Suc s"
      by simp
    have set_rep: "set (replicate (Suc s) x) \<subseteq> A"
      using \<open>x \<in> A\<close> by auto
    have "replicate (Suc s) x \<in> wr_space_on A (Suc s)"
      using len_rep set_rep wr_space_on_mem_iff by blast
    then show "wr_space_on A (Suc s) \<noteq> {}"
      by blast
  qed
qed

lemma card_wr_space_on:
  assumes "finite A"
  shows "card (wr_space_on A s) = card A ^ s"
proof (induction s)
  case 0
  then show ?case by simp
next
  case (Suc s)
  have repr:
    "wr_space_on A (Suc s) = (\<Union>x\<in>A. (Cons x) ` wr_space_on A s)"
    by simp

  have pairwise_disjoint:
    "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x \<noteq> y
      \<Longrightarrow> (Cons x) ` wr_space_on A s \<inter> (Cons y) ` wr_space_on A s = {}"
    by auto

  have card_union:
    "card (wr_space_on A (Suc s))
      = (\<Sum>x\<in>A. card ((Cons x) ` wr_space_on A s))"
    unfolding repr
    using assms pairwise_disjoint
    by (subst card_UN_disjoint) auto

  also have
    "... = (\<Sum>x\<in>A. card (wr_space_on A s))"
  proof (rule sum.cong[OF refl])
    fix x
    assume "x \<in> A"
    show "card ((Cons x) ` wr_space_on A s) = card (wr_space_on A s)"
      by (simp add: card_image)
  qed

  also have "... = card A * card (wr_space_on A s)"
    using assms by simp

  also have "... = card A * card A ^ s"
    using Suc.IH assms by simp

  also have "... = card A ^ Suc s"
    by simp

  finally show ?case .
qed


subsection \<open>Uniform space and uniform probability over V - S\<close>

definition uniform_wr_space :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list set" where
  "uniform_wr_space S s = wr_space_on (V - S) s"

definition uniform_wr_prob :: "'a set \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> real" where
  "uniform_wr_prob S s xs =
     (if xs \<in> uniform_wr_space S s
      then inverse (real (card (uniform_wr_space S s)))
      else 0)"

lemma uniform_wr_space_mem_iff:
  "xs \<in> uniform_wr_space S s \<longleftrightarrow> length xs = s \<and> set xs \<subseteq> V - S"
  unfolding uniform_wr_space_def
  using wr_space_on_mem_iff by simp

lemma finite_uniform_wr_space [simp]:
  "finite (uniform_wr_space S s)"
  unfolding uniform_wr_space_def
  using finite_V by simp

lemma uniform_wr_space_nonempty:
  assumes "S \<subseteq> V"
  assumes "V - S \<noteq> {} \<or> s = 0"
  shows "uniform_wr_space S s \<noteq> {}"
  using assms
  unfolding uniform_wr_space_def
  by (simp add: wr_space_on_nonempty_iff)

lemma uniform_wr_space_card:
  assumes "S \<subseteq> V"
  shows "card (uniform_wr_space S s) = card (V - S) ^ s"
  unfolding uniform_wr_space_def
  using card_wr_space_on[of "V - S" s] finite_V
  by simp

lemma uniform_wr_prob_nonneg:
  "0 \<le> uniform_wr_prob S s xs"
  unfolding uniform_wr_prob_def
  by simp

lemma uniform_wr_prob_outside:
  assumes "xs \<notin> uniform_wr_space S s"
  shows "uniform_wr_prob S s xs = 0"
  using assms
  unfolding uniform_wr_prob_def by simp

lemma uniform_wr_prob_inside:
  assumes "xs \<in> uniform_wr_space S s"
  shows "uniform_wr_prob S s xs = inverse (real (card (uniform_wr_space S s)))"
  using assms
  unfolding uniform_wr_prob_def by simp

lemma uniform_wr_mass_1:
  assumes "S \<subseteq> V"
  assumes feas: "V - S \<noteq> {} \<or> s = 0"
  shows "(\<Sum>xs\<in>uniform_wr_space S s. uniform_wr_prob S s xs) = 1"
proof -
  let ?U = "uniform_wr_space S s"
  let ?n = "card (V - S)"

  have finU: "finite ?U"
    by simp

  have cardU: "card ?U = ?n ^ s"
    using uniform_wr_space_card[OF assms(1)] by simp

  have cardU_nz: "card ?U \<noteq> 0"
  proof (cases "s = 0")
    case True
    with cardU show ?thesis
      by simp
  next
    case False
    with feas have diff_ne: "V - S \<noteq> {}"
      by auto
    have fin_diff: "finite (V - S)"
      using finite_V by simp
    have n_nz: "?n \<noteq> 0"
      using fin_diff diff_ne
      by (simp add: card_eq_0_iff)
    with False cardU show ?thesis
      by simp
  qed

  have "(\<Sum>xs\<in>?U. uniform_wr_prob S s xs)
      = (\<Sum>xs\<in>?U. inverse (real (card ?U)))"
    by (rule sum.cong) (auto simp: uniform_wr_prob_def)

  also have "... = real (card ?U) * inverse (real (card ?U))"
    using finU by simp

  also have "... = 1"
    using cardU_nz by simp

  finally show ?thesis .
qed


subsection \<open>Raw hit / miss events and probabilities\<close>

definition uniform_wr_hit_event :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a list set" where
  "uniform_wr_hit_event OPT S s =
     {xs. xs \<in> uniform_wr_space S s \<and> hits_residual OPT S xs}"

definition uniform_wr_miss_event :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a list set" where
  "uniform_wr_miss_event OPT S s =
     {xs. xs \<in> uniform_wr_space S s \<and> misses_residual OPT S xs}"

definition uniform_wr_hit_prob :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> real" where
  "uniform_wr_hit_prob OPT S s =
     (\<Sum>xs\<in>uniform_wr_hit_event OPT S s. uniform_wr_prob S s xs)"

definition uniform_wr_miss_prob :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> real" where
  "uniform_wr_miss_prob OPT S s =
     (\<Sum>xs\<in>uniform_wr_miss_event OPT S s. uniform_wr_prob S s xs)"

lemma finite_uniform_wr_hit_event [simp]:
  "finite (uniform_wr_hit_event OPT S s)"
proof -
  have "uniform_wr_hit_event OPT S s \<subseteq> uniform_wr_space S s"
    unfolding uniform_wr_hit_event_def by auto
  then show ?thesis
    using finite_uniform_wr_space finite_subset by blast
qed

lemma finite_uniform_wr_miss_event [simp]:
  "finite (uniform_wr_miss_event OPT S s)"
proof -
  have "uniform_wr_miss_event OPT S s \<subseteq> uniform_wr_space S s"
    unfolding uniform_wr_miss_event_def by auto
  then show ?thesis
    using finite_uniform_wr_space finite_subset by blast
qed

lemma uniform_wr_hit_event_iff:
  "xs \<in> uniform_wr_hit_event OPT S s
   \<longleftrightarrow> xs \<in> uniform_wr_space S s \<and> hits_residual OPT S xs"
  unfolding uniform_wr_hit_event_def by auto

lemma uniform_wr_miss_event_iff:
  "xs \<in> uniform_wr_miss_event OPT S s
   \<longleftrightarrow> xs \<in> uniform_wr_space S s \<and> misses_residual OPT S xs"
  unfolding uniform_wr_miss_event_def by auto

lemma uniform_wr_hit_miss_disjoint:
  "uniform_wr_hit_event OPT S s \<inter> uniform_wr_miss_event OPT S s = {}"
  unfolding uniform_wr_hit_event_def uniform_wr_miss_event_def
            hits_residual_def misses_residual_def
  by auto

lemma uniform_wr_hit_miss_union:
  "uniform_wr_hit_event OPT S s \<union> uniform_wr_miss_event OPT S s
     = uniform_wr_space S s"
  unfolding uniform_wr_hit_event_def uniform_wr_miss_event_def
            hits_residual_def misses_residual_def
  by auto

lemma uniform_wr_hit_prob_nonneg:
  "0 \<le> uniform_wr_hit_prob OPT S s"
  unfolding uniform_wr_hit_prob_def
proof (rule sum_nonneg)
  fix xs
  assume "xs \<in> uniform_wr_hit_event OPT S s"
  then show "0 \<le> uniform_wr_prob S s xs"
    using uniform_wr_prob_nonneg by blast
qed

lemma uniform_wr_miss_prob_nonneg:
  "0 \<le> uniform_wr_miss_prob OPT S s"
  unfolding uniform_wr_miss_prob_def
proof (rule sum_nonneg)
  fix xs
  assume "xs \<in> uniform_wr_miss_event OPT S s"
  then show "0 \<le> uniform_wr_prob S s xs"
    using uniform_wr_prob_nonneg by blast
qed

lemma uniform_wr_hit_prob_plus_miss_prob:
  assumes "S \<subseteq> V"
  assumes "V - S \<noteq> {} \<or> s = 0"
  shows "uniform_wr_hit_prob OPT S s + uniform_wr_miss_prob OPT S s = 1"
proof -
  have
    "(\<Sum>xs\<in>uniform_wr_hit_event OPT S s. uniform_wr_prob S s xs) +
     (\<Sum>xs\<in>uniform_wr_miss_event OPT S s. uniform_wr_prob S s xs)
     = (\<Sum>xs\<in>uniform_wr_hit_event OPT S s \<union> uniform_wr_miss_event OPT S s.
          uniform_wr_prob S s xs)"
    using uniform_wr_hit_miss_disjoint
    by (simp add: sum.union_disjoint)

  also have
    "... = (\<Sum>xs\<in>uniform_wr_space S s. uniform_wr_prob S s xs)"
    using uniform_wr_hit_miss_union by simp

  also have
    "... = 1"
    using uniform_wr_mass_1[OF assms] .

  finally show ?thesis
    unfolding uniform_wr_hit_prob_def uniform_wr_miss_prob_def .
qed

lemma uniform_wr_hit_prob_eq_1_minus_miss_prob:
  assumes "S \<subseteq> V"
  assumes "V - S \<noteq> {} \<or> s = 0"
  shows "uniform_wr_hit_prob OPT S s = 1 - uniform_wr_miss_prob OPT S s"
proof -
  have h: "uniform_wr_hit_prob OPT S s + uniform_wr_miss_prob OPT S s = 1"
    using uniform_wr_hit_prob_plus_miss_prob[OF assms] .
  then show ?thesis
    by linarith
qed

lemma uniform_wr_miss_prob_eq_1_minus_hit_prob:
  assumes "S \<subseteq> V"
  assumes "V - S \<noteq> {} \<or> s = 0"
  shows "uniform_wr_miss_prob OPT S s = 1 - uniform_wr_hit_prob OPT S s"
proof -
  have h: "uniform_wr_hit_prob OPT S s + uniform_wr_miss_prob OPT S s = 1"
    using uniform_wr_hit_prob_plus_miss_prob[OF assms] .
  then show ?thesis
    by linarith
qed


subsection \<open>Exact miss-event counting\<close>

lemma uniform_wr_miss_event_alt:
  assumes "OPT \<subseteq> V"
  assumes "S \<subseteq> V"
  shows "uniform_wr_miss_event OPT S s
       = wr_space_on ((V - S) - residual_opt OPT S) s"
proof
  show "uniform_wr_miss_event OPT S s \<subseteq> wr_space_on ((V - S) - residual_opt OPT S) s"
  proof
    fix xs
    assume hx: "xs \<in> uniform_wr_miss_event OPT S s"
    then have hspace: "xs \<in> uniform_wr_space S s"
      unfolding uniform_wr_miss_event_def by auto
    then have len: "length xs = s" and xs_sub: "set xs \<subseteq> V - S"
      using uniform_wr_space_mem_iff by auto
    from hx have miss: "misses_residual OPT S xs"
      unfolding uniform_wr_miss_event_def by auto
    have "set xs \<inter> residual_opt OPT S = {}"
      using miss xs_sub
      unfolding misses_residual_def uniform_wr_space_def sampled_candidates_def
      by auto
    then have "set xs \<subseteq> (V - S) - residual_opt OPT S"
      using xs_sub by auto
    then show "xs \<in> wr_space_on ((V - S) - residual_opt OPT S) s"
      using len wr_space_on_mem_iff by auto
  qed
next
  show "wr_space_on ((V - S) - residual_opt OPT S) s
        \<subseteq> uniform_wr_miss_event OPT S s"
  proof
    fix xs
    assume hx: "xs \<in> wr_space_on ((V - S) - residual_opt OPT S) s"
    then have len: "length xs = s"
      and xs_sub_diff: "set xs \<subseteq> (V - S) - residual_opt OPT S"
      using wr_space_on_mem_iff by auto
    then have xs_sub: "set xs \<subseteq> V - S"
      by auto
    have hspace: "xs \<in> uniform_wr_space S s"
      using len xs_sub
      unfolding uniform_wr_space_def
      by (simp add: wr_space_on_mem_iff)
    have miss: "misses_residual OPT S xs"
      using xs_sub_diff
      unfolding misses_residual_def sampled_candidates_def
      by auto
    show "xs \<in> uniform_wr_miss_event OPT S s"
      using hspace miss
      unfolding uniform_wr_miss_event_def by auto
  qed
qed

lemma uniform_wr_miss_event_card:
  assumes "OPT \<subseteq> V"
  assumes "S \<subseteq> V"
  shows "card (uniform_wr_miss_event OPT S s)
       = (card (V - S) - residual_card OPT S) ^ s"
proof -
  have sub_res: "residual_opt OPT S \<subseteq> V - S"
    using assms(1) residual_opt_subset_remaining by blast

  have fin_res: "finite (residual_opt OPT S)"
  proof (rule finite_subset[of "residual_opt OPT S" V])
    show "residual_opt OPT S \<subseteq> V"
      using assms(1) residual_opt_subset_OPT by blast
  next
    show "finite V"
      using finite_V .
  qed

  have card_diff:
    "card ((V - S) - residual_opt OPT S) = card (V - S) - residual_card OPT S"
    unfolding residual_card_def
    using finite_V sub_res fin_res
    by (simp add: card_Diff_subset)

  have fin_diff_set: "finite ((V - S) - residual_opt OPT S)"
    using finite_V by simp

  have "card (uniform_wr_miss_event OPT S s)
      = card (wr_space_on ((V - S) - residual_opt OPT S) s)"
    using uniform_wr_miss_event_alt[OF assms] by simp
  also have "... = card ((V - S) - residual_opt OPT S) ^ s"
    using card_wr_space_on[OF fin_diff_set] .
  also have "... = (card (V - S) - residual_card OPT S) ^ s"
    using card_diff by simp
  finally show ?thesis .
qed


subsection \<open>Exact hit / miss probabilities\<close>

lemma uniform_wr_miss_prob_exact:
  assumes "OPT \<subseteq> V"
  assumes "S \<subseteq> V"
  assumes "V - S \<noteq> {} \<or> s = 0"
  shows "uniform_wr_miss_prob OPT S s
       = (real (card (V - S) - residual_card OPT S) / real (card (V - S))) ^ s"
proof -
  have fin_miss: "finite (uniform_wr_miss_event OPT S s)"
    by simp

  have const_on_miss:
    "\<And>xs. xs \<in> uniform_wr_miss_event OPT S s
       \<Longrightarrow> uniform_wr_prob S s xs = inverse (real (card (uniform_wr_space S s)))"
    unfolding uniform_wr_miss_event_def
    by (simp add: uniform_wr_prob_def)

  have miss_as_card_ratio:
    "uniform_wr_miss_prob OPT S s
     = real (card (uniform_wr_miss_event OPT S s))
       * inverse (real (card (uniform_wr_space S s)))"
  proof -
    have "(\<Sum>xs\<in>uniform_wr_miss_event OPT S s. uniform_wr_prob S s xs)
        = (\<Sum>xs\<in>uniform_wr_miss_event OPT S s.
             inverse (real (card (uniform_wr_space S s))))"
      using const_on_miss by auto
    also have "... =
        real (card (uniform_wr_miss_event OPT S s))
        * inverse (real (card (uniform_wr_space S s)))"
      using fin_miss by simp
    finally show ?thesis
      unfolding uniform_wr_miss_prob_def .
  qed

  have card_space:
    "card (uniform_wr_space S s) = card (V - S) ^ s"
    using uniform_wr_space_card[OF assms(2)] .

  have card_miss:
    "card (uniform_wr_miss_event OPT S s)
     = (card (V - S) - residual_card OPT S) ^ s"
    using uniform_wr_miss_event_card[OF assms(1,2)] .

  have "uniform_wr_miss_prob OPT S s
      = real ((card (V - S) - residual_card OPT S) ^ s)
        * inverse (real ((card (V - S)) ^ s))"
    using miss_as_card_ratio card_space card_miss
    by simp
  also have "... =
      (real (card (V - S) - residual_card OPT S)) ^ s
      * inverse ((real (card (V - S))) ^ s)"
    by simp
  also have "... =
      (real (card (V - S) - residual_card OPT S)) ^ s
      * (inverse (real (card (V - S)))) ^ s"
    by (simp add: power_inverse)
  also have "... =
      (real (card (V - S) - residual_card OPT S)
       * inverse (real (card (V - S)))) ^ s"
    by (simp add: power_mult_distrib)
  also have "... =
      (real (card (V - S) - residual_card OPT S) / real (card (V - S))) ^ s"
    by (simp add: divide_inverse)
  finally show ?thesis .
qed

lemma uniform_wr_hit_prob_exact:
  assumes "OPT \<subseteq> V"
  assumes "S \<subseteq> V"
  assumes "V - S \<noteq> {} \<or> s = 0"
  shows "uniform_wr_hit_prob OPT S s
       = 1 - (real (card (V - S) - residual_card OPT S) / real (card (V - S))) ^ s"
proof -
  have "uniform_wr_hit_prob OPT S s = 1 - uniform_wr_miss_prob OPT S s"
    using uniform_wr_hit_prob_eq_1_minus_miss_prob[OF assms(2,3)] .
  also have "... =
      1 - (real (card (V - S) - residual_card OPT S) / real (card (V - S))) ^ s"
    using uniform_wr_miss_prob_exact[OF assms] by simp
  finally show ?thesis .
qed


subsection \<open>Target lower bounds for the abstract hit layer\<close>

text \<open>
The next two lemmas are the concrete analytic bridge needed to interpret the
abstract hit-probability interface.

Expected proof route:
  1. exact formula from uniform_wr_hit_prob_exact;
  2. use (1 - r/m)^s \<le> exp (- s r / m) for m > 0;
  3. relax m = card (V - S) to card V;
  4. use the concavity linearisation on [0, k].
\<close>

lemma uniform_wr_hit_prob_ge_hit_lb_exp:
  assumes "OPT \<subseteq> V"
  assumes "S \<subseteq> V"
  assumes feas: "V - S \<noteq> {} \<or> s = 0"
  shows "uniform_wr_hit_prob OPT S s \<ge> hit_lb_exp s (residual_card OPT S)"
proof (cases "s = 0")
  case True
  then show ?thesis
    using uniform_wr_hit_prob_exact[OF assms]
    unfolding hit_lb_exp_def
    by simp
next
  case False
  let ?m = "card (V - S)"
  let ?r = "residual_card OPT S"

  have diff_ne: "V - S \<noteq> {}"
    using feas False by auto

  have m_pos: "0 < ?m"
    using diff_ne finite_V
    by (simp add: card_gt_0_iff)

  have V_ne: "V \<noteq> {}"
    using diff_ne by auto

  have V_pos: "0 < card V"
    using V_ne finite_V
    by (simp add: card_gt_0_iff)

  have sub_res: "residual_opt OPT S \<subseteq> V - S"
    using assms(1) residual_opt_subset_remaining by blast

  have r_le_m: "?r \<le> ?m"
    unfolding residual_card_def
    using sub_res finite_V
    by (intro card_mono) auto

  show ?thesis
  proof (cases "?r = ?m")
    case True
    have miss_zero: "uniform_wr_miss_prob OPT S s = 0"
      using uniform_wr_miss_prob_exact[OF assms] True False
      by simp
    have hit_one: "uniform_wr_hit_prob OPT S s = 1"
      using uniform_wr_hit_prob_eq_1_minus_miss_prob[OF assms(2) feas]
            miss_zero
      by simp
    also have "... \<ge> hit_lb_exp s (residual_card OPT S)"
      using hit_lb_exp_le_1[of s "?r"] by simp
    finally show ?thesis .
  next
    case False
    then have r_lt_m: "?r < ?m"
      using r_le_m by auto

    have x_nonneg: "0 \<le> real ?r / real ?m"
      using m_pos by simp

    have x_lt_1: "real ?r / real ?m < 1"
      using r_lt_m m_pos by simp

    have one_minus_le_exp:
      "1 - real ?r / real ?m \<le> exp (-(real ?r / real ?m))"
    proof -
      have ln_bound:
        "ln (1 - real ?r / real ?m) \<le> - (real ?r / real ?m)"
        using x_nonneg x_lt_1
        by (rule ln_one_minus_pos_upper_bound)

      have pos_one_minus: "0 < 1 - real ?r / real ?m"
        using x_lt_1 by simp

      have "1 - real ?r / real ?m = exp (ln (1 - real ?r / real ?m))"
        using pos_one_minus
        by (simp only: exp_ln_iff [symmetric])
      also have "... \<le> exp (-(real ?r / real ?m))"
        using ln_bound
        by (simp only: exp_le_cancel_iff)
      finally show ?thesis .
    qed

    have miss_eq:
      "uniform_wr_miss_prob OPT S s = (1 - real ?r / real ?m) ^ s"
      using uniform_wr_miss_prob_exact[OF assms]
            r_le_m m_pos
      by (simp add: field_simps)

    have exp_pow:
      "(exp (-(real ?r / real ?m))) ^ s = exp (-(real s * real ?r / real ?m))"
    proof (induction s)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      have "(exp (-(real ?r / real ?m))) ^ Suc n
          = exp (-(real ?r / real ?m)) * (exp (-(real ?r / real ?m))) ^ n"
        by simp
      also have "... = exp (-(real ?r / real ?m)) * exp (-(real n * real ?r / real ?m))"
        using Suc.IH by simp
      also have "... = exp (-(real ?r / real ?m) + -(real n * real ?r / real ?m))"
        by (simp only: exp_add[symmetric])
      also have "... = exp (- ((1 + real n) * real ?r / real ?m))"
        using m_pos by (simp add: field_simps)
      also have "... = exp (-(real (Suc n) * real ?r / real ?m))"
        by simp
      finally show ?case .
    qed

    have miss_le_m:
      "uniform_wr_miss_prob OPT S s \<le> exp (-(real s * real ?r / real ?m))"
    proof -
      have "(1 - real ?r / real ?m) ^ s
            \<le> (exp (-(real ?r / real ?m))) ^ s"
        using one_minus_le_exp x_lt_1
        by (intro power_mono) auto
      also have "... = exp (-(real s * real ?r / real ?m))"
        using exp_pow by simp
      finally show ?thesis
        using miss_eq by simp
    qed

    have m_le_V: "?m \<le> card V"
      using finite_V by (intro card_mono) auto

    have num_nonneg: "0 \<le> real s * real ?r"
      by simp

    have frac_mono:
      "real s * real ?r / real (card V) \<le> real s * real ?r / real ?m"
    proof -
      have m_le_V_real: "real ?m \<le> real (card V)"
        using m_le_V by simp
      have "real s * real ?r * real ?m \<le> real s * real ?r * real (card V)"
        using num_nonneg m_le_V_real by (intro mult_left_mono) simp_all
      then show ?thesis
        using m_pos V_pos by (simp add: field_simps)
    qed

    have exp_mono:
      "exp (-(real s * real ?r / real ?m))
       \<le> exp (-(real s * real ?r / real (card V)))"
      using frac_mono
      by (simp only: exp_le_cancel_iff)

    have miss_le_V:
      "uniform_wr_miss_prob OPT S s
       \<le> exp (-(real s * real ?r / real (card V)))"
      using miss_le_m exp_mono
      by linarith

    have hit_eq:
      "uniform_wr_hit_prob OPT S s = 1 - uniform_wr_miss_prob OPT S s"
      using uniform_wr_hit_prob_eq_1_minus_miss_prob[OF assms(2) feas] .

    from hit_eq miss_le_V
    show ?thesis
      unfolding hit_lb_exp_def
      by linarith
  qed
qed

lemma uniform_wr_hit_prob_ge_hit_lb_linear_if_feasible:
  assumes "OPT \<subseteq> V"
  assumes "finite OPT"
  assumes "card OPT \<le> k"
  assumes "S \<subseteq> V"
  assumes feas: "V - S \<noteq> {} \<or> s = 0"
  shows "uniform_wr_hit_prob OPT S s \<ge> hit_lb_linear s (residual_card OPT S)"
proof (cases "k = 0")
  case True
  have lb0: "hit_lb_linear s (residual_card OPT S) = 0"
  proof -
    have "hit_lb_linear s (residual_card OPT S) =
            (if k = 0 then 0
             else alpha_stoch s * real (residual_card OPT S) / real k)"
      unfolding hit_lb_linear_def
      by simp
    with True show ?thesis
      by simp
  qed
  show ?thesis
  using uniform_wr_hit_prob_nonneg[of OPT S s] lb0
  by linarith
next
  case False
  note k_nz = False

  let ?m = "residual_card OPT S"

  have k_pos: "0 < k"
    using k_nz by simp

  have m_le_k: "?m \<le> k"
    using residual_card_le_k[OF assms(2,3)] .

  have prob_ge_exp:
    "uniform_wr_hit_prob OPT S s \<ge> hit_lb_exp s ?m"
    using uniform_wr_hit_prob_ge_hit_lb_exp[OF assms(1) assms(4) feas] .

  have exp_ge_linear:
    "hit_lb_exp s ?m \<ge> hit_lb_linear s ?m"
  proof (cases "?m = 0")
    case True
    then show ?thesis
      by simp
  next
    case False
    note m_nz = False
    have m_pos: "0 < ?m"
      using m_nz by simp

    show ?thesis
    proof (cases "s = 0")
      case True
      then show ?thesis
        by simp
    next
      case False
      note s_nz = False
      have s_pos: "0 < s"
        using s_nz by simp

      have diff_ne: "V - S \<noteq> {}"
        using feas s_nz by auto

      have V_ne: "V \<noteq> {}"
        using diff_ne by auto

      have cardV_pos: "0 < card V"
        using V_ne finite_V
        by (simp add: card_gt_0_iff)

      let ?q = "exp (- (real s / real (card V)))"
      let ?A = "sum (\<lambda>i. ?q ^ i) {..< ?m}"
      let ?B = "sum (\<lambda>i. ?q ^ i) {?m..< k}"

      have q_nonneg: "0 \<le> ?q"
        by simp

      have q_lt_1: "?q < 1"
        using s_pos cardV_pos
        by simp

      have q_le_1: "?q \<le> 1"
        using q_lt_1 by simp

      have q_ne_1: "?q \<noteq> 1"
        using q_lt_1 by linarith

      have exp_pow_nat:
        "(exp x)^n = exp (real n * x)"
        for n :: nat and x :: real
      proof (induction n)
        case 0
        show ?case by simp
      next
        case (Suc n)
        have "(exp x) ^ Suc n = exp x * (exp x)^n"
          by simp
        also have "... = exp x * exp (real n * x)"
          using Suc.IH by simp
        also have "... = exp (x + real n * x)"
          by (simp only: exp_add[symmetric])
        also have "... = exp ((1 + real n) * x)"
          by (simp add: algebra_simps)
        also have "... = exp (real (Suc n) * x)"
          by simp
        finally show ?case .
      qed

      have qpow_m:
        "?q ^ ?m = exp (-(real s * real ?m / real (card V)))"
      proof -
        have "?q ^ ?m = exp (real ?m * (-(real s / real (card V))))"
          using exp_pow_nat[where n = ?m and x = "- (real s / real (card V))"]
          by simp
        also have "... = exp (-(real s * real ?m / real (card V)))"
          using cardV_pos
          by (simp add: field_simps)
        finally show ?thesis .
      qed

      have qpow_k:
        "?q ^ k = exp (-(real s * real k / real (card V)))"
      proof -
        have "?q ^ k = exp (real k * (-(real s / real (card V))))"
          using exp_pow_nat[where n = k and x = "- (real s / real (card V))"]
          by simp
        also have "... = exp (-(real s * real k / real (card V)))"
          using cardV_pos
          by (simp add: field_simps)
        finally show ?thesis .
      qed

     have sum_split0:
        "sum (\<lambda>i. ?q ^ i) {0..< ?m} + sum (\<lambda>i. ?q ^ i) {?m..<k}
         = sum (\<lambda>i. ?q ^ i) {0..<k}"
        using m_le_k
        by (intro sum.atLeastLessThan_concat) simp_all

      have sum_split:
        "?A + ?B = sum (\<lambda>i. ?q ^ i) {..<k}"
        using sum_split0
        by (simp add: atLeast0LessThan [symmetric])

      have B_le:
        "?B \<le> real (k - ?m) * ?q ^ (?m - 1)"
      proof -
        have "?B \<le> sum (\<lambda>i. ?q ^ (?m - 1)) {?m..<k}"
        proof (rule sum_mono)
          fix i
          assume i: "i \<in> {?m..<k}"
          then have le: "?m - 1 \<le> i"
            using m_pos by auto
          show "?q ^ i \<le> ?q ^ (?m - 1)"
            using le q_nonneg q_le_1
            by (intro power_decreasing) auto
        qed
        then show ?thesis
          by simp
      qed

      have A_ge:
        "real ?m * ?q ^ (?m - 1) \<le> ?A"
      proof -
        have "sum (\<lambda>i. ?q ^ (?m - 1)) {..< ?m} \<le> ?A"
        proof (rule sum_mono)
          fix i
          assume i: "i \<in> {..< ?m}"
          then have le: "i \<le> ?m - 1"
            using m_pos by auto
          show "?q ^ (?m - 1) \<le> ?q ^ i"
            using le q_nonneg q_le_1
            by (intro power_decreasing) auto
        qed
        then show ?thesis
          by simp
      qed

      have mB_le:
        "real ?m * ?B \<le> real (k - ?m) * ?A"
      proof -
        have "real ?m * ?B \<le> real ?m * (real (k - ?m) * ?q ^ (?m - 1))"
          using B_le m_pos
          by (intro mult_left_mono) simp_all
        also have "... = real (k - ?m) * (real ?m * ?q ^ (?m - 1))"
          by (simp add: algebra_simps)
        also have "... \<le> real (k - ?m) * ?A"
          using A_ge
          by (intro mult_left_mono) simp_all
        finally show ?thesis .
      qed

      have avg:
        "real ?m * sum (\<lambda>i. ?q ^ i) {..<k} \<le> real k * ?A"
      proof -
        have "real ?m * sum (\<lambda>i. ?q ^ i) {..<k}
            = real ?m * (?A + ?B)"
          using sum_split[symmetric]
          by simp
        also have "... = real ?m * ?A + real ?m * ?B"
          by (simp add: algebra_simps)
        also have "... \<le> real ?m * ?A + real (k - ?m) * ?A"
          using mB_le by linarith
        also have "... = real k * ?A"
          using m_le_k
          by (simp add: algebra_simps)
        finally show ?thesis .
      qed

      have geom_m:
        "(1 - ?q) * ?A = 1 - ?q ^ ?m"
        using q_ne_1
        by (simp add: geometric_sum field_simps)

      have geom_k:
        "(1 - ?q) * sum (\<lambda>i. ?q ^ i) {..<k} = 1 - ?q ^ k"
        using q_ne_1
        by (simp add: geometric_sum field_simps)

      have one_minus_q_pos: "0 < 1 - ?q"
        using q_lt_1 by simp

      have scaled:
        "real ?m * (1 - ?q ^ k) \<le> real k * (1 - ?q ^ ?m)"
      proof -
        have h0:
          "(1 - ?q) * (real ?m * sum (\<lambda>i. ?q ^ i) {..<k})
           \<le> (1 - ?q) * (real k * ?A)"
          using avg one_minus_q_pos
          by (intro mult_left_mono) simp_all

        have h1:
          "real ?m * ((1 - ?q) * sum (\<lambda>i. ?q ^ i) {..<k})
           \<le> real k * ((1 - ?q) * ?A)"
          using h0
          by (simp add: algebra_simps)

        show ?thesis
          using h1 geom_m geom_k
          by simp
      qed

      have secant_q:
        "1 - ?q ^ ?m \<ge> (real ?m / real k) * (1 - ?q ^ k)"
        using scaled k_pos
        by (simp add: field_simps)

      have lhs_rewrite:
        "hit_lb_exp s ?m = 1 - ?q ^ ?m"
      proof -
        have "hit_lb_exp s ?m = 1 - exp (-(real s * real ?m / real (card V)))"
          unfolding hit_lb_exp_def
          by simp
        also have "... = 1 - ?q ^ ?m"
          using qpow_m[symmetric]
          by simp
        finally show ?thesis .
      qed

      have rhs_rewrite:
        "hit_lb_linear s ?m = (real ?m / real k) * (1 - ?q ^ k)"
      proof -
        have "hit_lb_linear s ?m
            = (1 - exp (-(real s * real k / real (card V)))) * real ?m / real k"
          using k_pos
          unfolding hit_lb_linear_def alpha_stoch_def
          by simp
        also have "... = (1 - ?q ^ k) * real ?m / real k"
          using qpow_k[symmetric]
          by simp
        also have "... = (real ?m / real k) * (1 - ?q ^ k)"
          using k_pos
          by simp
        finally show ?thesis .
      qed

      show ?thesis
        using secant_q lhs_rewrite rhs_rewrite
        by simp
      qed
    qed

  from prob_ge_exp exp_ge_linear
  show ?thesis
    by linarith
qed


lemma uniform_wr_hit_prob_ge_hit_lb_linear:
  assumes "OPT \<subseteq> V"
  assumes "finite OPT"
  assumes "card OPT \<le> k"
  assumes "S \<subseteq> V"
  shows "uniform_wr_hit_prob OPT S s \<ge> hit_lb_linear s (residual_card OPT S)"
proof (cases "V - S \<noteq> {} \<or> s = 0")
  case True
  show ?thesis
    by (rule uniform_wr_hit_prob_ge_hit_lb_linear_if_feasible[OF assms True])
next
  case False
  have diff_empty: "V - S = {}"
    using False by auto

  have V_subset_S: "V \<subseteq> S"
    using diff_empty by auto

  have OPT_subset_S: "OPT \<subseteq> S"
    using assms(1) V_subset_S by auto

  have diff0: "OPT - S = {}"
    using OPT_subset_S by auto

  have fin_diff: "finite (OPT - S)"
    using assms(2) by simp

  have card_diff0: "card (OPT - S) = 0"
    using diff0 fin_diff
    by (simp add: card_eq_0_iff)

  have res_card_0: "residual_card OPT S = 0"
    unfolding residual_card_def residual_opt_def
    using card_diff0
    by simp

  have lb0: "hit_lb_linear s (residual_card OPT S) = 0"
    using res_card_0
    by simp

  show ?thesis
    using uniform_wr_hit_prob_nonneg[of OPT S s] lb0
    by linarith
qed

end
end