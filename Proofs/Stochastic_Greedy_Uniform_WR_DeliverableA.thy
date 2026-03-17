theory Stochastic_Greedy_Uniform_WR_DeliverableA
  imports
    Stochastic_Greedy_Expected_OneStep
    Stochastic_Greedy_Uniform_WR_Interpretation
    Greedy_Submodular_Approx
begin

section \<open>Concrete one-step bridge for Deliverable A (uniform WR model)\<close>

text \<open>
This theory supplies the missing concrete one-step bridge for the uniform
with-replacement stochastic greedy line.

The key idea is to avoid the too-strong pointwise assumption used by the
abstract gap-bridge locale.  Instead, we work with the first residual-optimal
hit in the sampled list, prove a symmetry lemma specific to the uniform
with-replacement model, and then derive the expected one-step lower bound

  expected_step_gain S s \<ge> (alpha_stoch s / k) * (f OPT - f S).

This is the mathematically central part of Deliverable A.
\<close>

context Cardinality_Constraint
begin

subsection \<open>First-hit selector on the residual optimal set\<close>

fun first_in :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "first_in A [] = None"
| "first_in A (x # xs) = (if x \<in> A then Some x else first_in A xs)"

definition first_residual_hit :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "first_residual_hit OPT S xs = first_in (residual_opt OPT S) xs"

definition first_residual_hit_gain :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> real" where
  "first_residual_hit_gain OPT S xs =
     (case first_residual_hit OPT S xs of
        None \<Rightarrow> 0
      | Some x \<Rightarrow> gain S x)"

lemma first_in_SomeD_conj:
  assumes h: "first_in A xs = Some x"
  shows "x \<in> A \<and> x \<in> set xs"
  using h
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "a \<in> A")
    case True
    with Cons.prems show ?thesis by simp
  next
    case False
    from Cons.prems False have hxs: "first_in A xs = Some x" by simp
    from Cons.IH[OF hxs] show ?thesis by simp
  qed
qed

lemma first_in_None_iff:
  "first_in A xs = None \<longleftrightarrow> set xs \<inter> A = {}"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "x \<in> A")
    case True
    then show ?thesis by simp
  next
    case False
    with Cons.IH show ?thesis by auto
  qed
qed

lemma first_in_SomeD:
  assumes "first_in A xs = Some x"
  shows "x \<in> A" and "x \<in> set xs"
proof -
  from first_in_SomeD_conj[OF assms]
  show "x \<in> A" and "x \<in> set xs" by blast+
qed

lemma first_residual_hit_SomeD:
  assumes "first_residual_hit OPT S xs = Some x"
  shows "x \<in> residual_opt OPT S" and "x \<in> set xs"
proof -
  have "x \<in> residual_opt OPT S \<and> x \<in> set xs"
    using assms
    unfolding first_residual_hit_def
    using first_in_SomeD_conj by blast
  then show "x \<in> residual_opt OPT S" and "x \<in> set xs"
    by blast+
qed

lemma first_residual_hit_None_iff:
  "first_residual_hit OPT S xs = None \<longleftrightarrow> set xs \<inter> residual_opt OPT S = {}"
  unfolding first_residual_hit_def
  using first_in_None_iff[of "residual_opt OPT S" xs]
  by simp

lemma hit_event_imp_first_residual_hit_Some:
  assumes hit: "xs \<in> uniform_wr_weighted.hit_event OPT S s"
  obtains x where "first_residual_hit OPT S xs = Some x"
proof -
  have hres: "hits_residual OPT S xs"
    using hit unfolding uniform_wr_weighted.hit_event_def by auto
  then have "sampled_candidates (V - S) xs \<inter> residual_opt OPT S \<noteq> {}"
    unfolding hits_residual_def by simp
  then obtain x where hx: "x \<in> sampled_candidates (V - S) xs \<inter> residual_opt OPT S"
    by blast
  hence "x \<in> set xs \<inter> residual_opt OPT S"
    unfolding sampled_candidates_def by auto
  hence "set xs \<inter> residual_opt OPT S \<noteq> {}" by blast
  hence "first_residual_hit OPT S xs \<noteq> None"
    using first_residual_hit_None_iff by blast
  then obtain x where "first_residual_hit OPT S xs = Some x"
    by (cases "first_residual_hit OPT S xs") auto
  then show ?thesis using that by blast
qed

lemma first_residual_hit_mem_residual_hit_pool:
  assumes hOPT: "OPT \<subseteq> V"
  assumes hS:   "S \<subseteq> V"
  assumes hit:  "xs \<in> uniform_wr_weighted.hit_event OPT S s"
  assumes hx:   "first_residual_hit OPT S xs = Some x"
  shows "x \<in> residual_hit_pool OPT S xs"
proof -
  have x_res: "x \<in> residual_opt OPT S" and x_set: "x \<in> set xs"
    using first_residual_hit_SomeD[OF hx] by blast+
  have x_rem: "x \<in> V - S"
    using x_res hOPT
    unfolding residual_opt_def by auto
  have "x \<in> sampled_candidates (V - S) xs"
    using x_set x_rem unfolding sampled_candidates_def by auto
  with x_res show ?thesis
    unfolding residual_hit_pool_def by blast
qed

lemma first_residual_hit_gain_le_sampled_step_gain:
  assumes hOPT: "OPT \<subseteq> V"
  assumes hS:   "S \<subseteq> V"
  assumes hit:  "xs \<in> uniform_wr_weighted.hit_event OPT S s"
  shows "first_residual_hit_gain OPT S xs
       \<le> uniform_wr_weighted.sampled_step_gain S xs"
proof -
  obtain x where hx: "first_residual_hit OPT S xs = Some x"
    using hit_event_imp_first_residual_hit_Some[OF hit] by blast

  have hit_res: "hits_residual OPT S xs"
    using hit unfolding uniform_wr_weighted.hit_event_def by auto

  have x_pool: "x \<in> residual_hit_pool OPT S xs"
    using first_residual_hit_mem_residual_hit_pool[OF hOPT hS hit hx] .

  have gx_le: "gain S x \<le> gain S (sampled_argmax S xs)"
    using sampled_argmax_ge_residual_hit_pool[OF hit_res x_pool] by simp

  have step_eq: "uniform_wr_weighted.sampled_step_gain S xs = gain S (sampled_argmax S xs)"
    using uniform_wr_weighted.sampled_step_gain_eq_if_hit[OF hit_res] .

  show ?thesis
    unfolding first_residual_hit_gain_def
    using gx_le hx step_eq by simp
qed


subsection \<open>Residual total-gain lower bound\<close>

text \<open>
This is the deterministic bridge from the full residual optimal set to the
current value gap.  Importantly, we use the full residual set OPT - S here,
not the random hit-pool.
\<close>

lemma gain_decreasing_cc:
  assumes ST: "S \<subseteq> T"
  assumes TV: "T \<subseteq> V"
  assumes xV: "x \<in> V"
  assumes xnotT: "x \<notin> T"
  shows "gain T x \<le> gain S x"
proof -
  have SUx_sub_V: "S \<union> {x} \<subseteq> V"
    using ST TV xV by auto

  from submodular_f[OF SUx_sub_V TV]
  have subm0:
    "f ((S \<union> {x}) \<union> T) + f ((S \<union> {x}) \<inter> T) \<le> f (S \<union> {x}) + f T" .

  have subm:
    "f ((S \<union> {x}) \<inter> T) + f ((S \<union> {x}) \<union> T) \<le> f (S \<union> {x}) + f T"
    using subm0
    by (simp add: add.commute)

  have inter_eq: "(S \<union> {x}) \<inter> T = S"
    using ST xnotT by auto

  have union_eq: "(S \<union> {x}) \<union> T = T \<union> {x}"
  proof
    show "(S \<union> {x}) \<union> T \<subseteq> T \<union> {x}"
      using ST by auto
    show "T \<union> {x} \<subseteq> (S \<union> {x}) \<union> T"
      by auto
  qed

  from subm have "f S + f (T \<union> {x}) \<le> f (S \<union> {x}) + f T"
    unfolding inter_eq union_eq
    by simp

  then show ?thesis
    unfolding gain_def
    by linarith
qed

lemma submod_sum_upper_cc:
  assumes finA:  "finite A"
      and A_sub: "A \<subseteq> V"
      and S_sub: "S \<subseteq> V"
      and disj:  "A \<inter> S = {}"
  shows "f (S \<union> A) - f S \<le> (\<Sum>x\<in>A. gain S x)"
  using finA A_sub S_sub disj
proof (induction A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a A)
  have finA: "finite A"
    using insert.hyps by auto
  have a_notin: "a \<notin> A"
    using insert.hyps by auto

  have A_sub: "A \<subseteq> V"
    using insert.prems by auto
  have S_sub: "S \<subseteq> V"
    using insert.prems by auto
  have disjA: "A \<inter> S = {}"
    using insert.prems by auto
  have aV: "a \<in> V"
    using insert.prems by auto
  have a_notS: "a \<notin> S"
    using insert.prems by auto

  have SSUA: "S \<subseteq> S \<union> A"
    by auto
  have SUA_subV: "S \<union> A \<subseteq> V"
    using S_sub A_sub by auto
  have a_notin_SUA: "a \<notin> S \<union> A"
    using a_notS a_notin by auto

  have dec_gain:
    "gain (S \<union> A) a \<le> gain S a"
    using gain_decreasing_cc[OF SSUA SUA_subV aV a_notin_SUA] .

  have step:
    "f (S \<union> insert a A) - f S
      = gain (S \<union> A) a + (f (S \<union> A) - f S)"
    by (simp add: gain_def algebra_simps)

  have step':
    "f (insert a (S \<union> A)) - f S
      = gain (S \<union> A) a + (f (S \<union> A) - f S)"
    by (simp add: gain_def algebra_simps)

  have IH:
    "f (S \<union> A) - f S \<le> (\<Sum>x\<in>A. gain S x)"
    using insert.IH[OF A_sub S_sub disjA] .

  have
    "gain (S \<union> A) a + (f (S \<union> A) - f S)
      \<le> gain S a + (\<Sum>x\<in>A. gain S x)"
   using dec_gain IH by linarith
  then have
    "f (insert a (S \<union> A)) - f S
      \<le> gain S a + (\<Sum>x\<in>A. gain S x)"
    by (simp add: step')
  also have
    "... = (\<Sum>x\<in>insert a A. gain S x)"
    using finA a_notin by simp
  finally show ?case
    by auto
qed

lemma residual_total_gain_ge_gap:
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes S_sub:    "S \<subseteq> V"
  shows "f OPT - f S \<le> real (residual_card OPT S) * avg_gain_on S (residual_opt OPT S)"
proof (cases "residual_opt OPT S = {}")
  case True
  have OPT_sub_S: "OPT \<subseteq> S"
    using True
    by auto

  have opt_le: "f OPT \<le> f S"
    using monotone_f[rule_format, of OPT S] OPT_sub_S S_sub
    by auto

  have rhs0:
    "real (residual_card OPT S) * avg_gain_on S (residual_opt OPT S) = 0"
    using True
    unfolding residual_card_def avg_gain_on_def
    by simp

  show ?thesis
    using opt_le rhs0
    by linarith
next
  case False
  let ?R = "residual_opt OPT S"

  have finR: "finite ?R"
    unfolding residual_opt_def
    using OPT_fin
    by simp

  have R_subV: "?R \<subseteq> V"
    unfolding residual_opt_def
    using OPT_sub
    by auto

  have disj: "?R \<inter> S = {}"
    unfolding residual_opt_def
    by auto

  have step_sum:
    "f (S \<union> ?R) - f S \<le> (\<Sum>x\<in>?R. gain S x)"
    by (rule submod_sum_upper_cc[OF finR R_subV S_sub disj])

  have OPT_sub_union: "OPT \<subseteq> S \<union> ?R"
    unfolding residual_opt_def
    by auto

  have union_subV: "S \<union> ?R \<subseteq> V"
    using S_sub R_subV by auto

  have opt_le_union: "f OPT \<le> f (S \<union> ?R)"
    using monotone_f[rule_format, of OPT "S \<union> ?R"] OPT_sub_union union_subV
    by auto

  have sum_ge_gap:
    "f OPT - f S \<le> (\<Sum>x\<in>?R. gain S x)"
    using opt_le_union step_sum
    by linarith

  have cardR_eq: "residual_card OPT S = card ?R"
    unfolding residual_card_def
    by simp

  have avg_eq:
    "avg_gain_on S ?R = (\<Sum>x\<in>?R. gain S x) / real (card ?R)"
    using finR False
    by (simp add: avg_gain_on_def)

  have card_pos: "card ?R > 0"
    using finR False
    by (simp add: card_gt_0_iff)

  have rhs_eq:
    "real (residual_card OPT S) * avg_gain_on S ?R = (\<Sum>x\<in>?R. gain S x)"
    using avg_eq card_pos cardR_eq
    by simp

  show ?thesis
    using sum_ge_gap rhs_eq
    by simp
qed

lemma avg_gain_on_residual_opt_nonneg:
  assumes OPT_sub: "OPT \<subseteq> V"
  assumes S_sub:   "S \<subseteq> V"
  shows "0 \<le> avg_gain_on S (residual_opt OPT S)"
proof (cases "residual_opt OPT S = {}")
  case True
  then show ?thesis
    unfolding avg_gain_on_def
    by simp
next
  case False
  let ?R = "residual_opt OPT S"

  have finR: "finite ?R"
    unfolding residual_opt_def
    using OPT_sub finite_V
    by (meson Diff_subset finite_subset)

  have sum_nonneg_R: "0 \<le> (\<Sum>x\<in>?R. gain S x)"
  proof (rule sum_nonneg)
    fix x
    assume hx: "x \<in> ?R"
    have xVS: "x \<in> V - S"
      using hx OPT_sub
      unfolding residual_opt_def
      by auto
    show "0 \<le> gain S x"
      using gain_nonneg[OF S_sub xVS] .
  qed

  have avg_eq:
    "avg_gain_on S ?R = (\<Sum>x\<in>?R. gain S x) / real (card ?R)"
    using finR False
    by (simp add: avg_gain_on_def)

  have card_pos: "0 < real (card ?R)"
    using finR False
    by (simp add: card_gt_0_iff)

  show ?thesis
    unfolding avg_eq
    using sum_nonneg_R card_pos
    by (simp add: divide_nonneg_pos)
qed


subsection \<open>The only genuinely new symmetry lemma\<close>

text \<open>
This is the one place where the uniform with-replacement combinatorics must be
used in earnest.

Intended proof idea:
  * partition hit-event lists by the position of the first residual-optimal hit,
  * count lists where that first hit equals a fixed y \<in> residual_opt OPT S,
  * observe that this count is independent of y,
  * conclude that, conditional on hitting, the first residual hit is uniform
    over residual_opt OPT S,
  * therefore the weighted first-hit gain equals hit_prob \<times> average residual gain.
\<close>

definition first_residual_hit_event :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list set" where
  "first_residual_hit_event OPT S s x =
     {xs \<in> uniform_wr_weighted.hit_event OPT S s.
        first_residual_hit OPT S xs = Some x}"

lemma finite_first_residual_hit_event [simp]:
  "finite (first_residual_hit_event OPT S s x)"
  unfolding first_residual_hit_event_def
  by simp

lemma first_residual_hit_event_memD:
  assumes "xs \<in> first_residual_hit_event OPT S s x"
  shows "xs \<in> uniform_wr_weighted.hit_event OPT S s"
    and "first_residual_hit OPT S xs = Some x"
    and "x \<in> residual_opt OPT S"
proof -
  from assms have h1: "xs \<in> uniform_wr_weighted.hit_event OPT S s"
    and h2: "first_residual_hit OPT S xs = Some x"
    unfolding first_residual_hit_event_def
    by auto
  from first_residual_hit_SomeD[OF h2] have "x \<in> residual_opt OPT S"
    by simp
  from h1 h2 this show
    "xs \<in> uniform_wr_weighted.hit_event OPT S s"
    "first_residual_hit OPT S xs = Some x"
    "x \<in> residual_opt OPT S"
    by simp_all
qed

lemma first_residual_hit_event_disjoint:
  assumes xy: "x \<noteq> y"
  shows "first_residual_hit_event OPT S s x \<inter> first_residual_hit_event OPT S s y = {}"
proof (rule equalityI)
  show "first_residual_hit_event OPT S s x \<inter> first_residual_hit_event OPT S s y \<subseteq> {}"
  proof
    fix xs
    assume hxs: "xs \<in> first_residual_hit_event OPT S s x \<inter> first_residual_hit_event OPT S s y"
    then have hx: "first_residual_hit OPT S xs = Some x"
      and hy: "first_residual_hit OPT S xs = Some y"
      unfolding first_residual_hit_event_def by auto
    from hx hy xy show "xs \<in> {}"
      by simp
  qed
next
  show "{} \<subseteq> first_residual_hit_event OPT S s x \<inter> first_residual_hit_event OPT S s y"
    by simp
qed

lemma hit_event_partition_first_residual:
  assumes OPT_sub: "OPT \<subseteq> V"
  shows
    "uniform_wr_weighted.hit_event OPT S s
      = (\<Union>x\<in>residual_opt OPT S. first_residual_hit_event OPT S s x)"
proof
  show "uniform_wr_weighted.hit_event OPT S s
        \<subseteq> (\<Union>x\<in>residual_opt OPT S. first_residual_hit_event OPT S s x)"
  proof
    fix xs
    assume hxs: "xs \<in> uniform_wr_weighted.hit_event OPT S s"
    then obtain x where hx: "first_residual_hit OPT S xs = Some x"
      using hit_event_imp_first_residual_hit_Some by blast
    from first_residual_hit_SomeD[OF hx] have xR: "x \<in> residual_opt OPT S"
      by simp
    have "xs \<in> first_residual_hit_event OPT S s x"
      using hxs hx unfolding first_residual_hit_event_def by auto
    with xR show "xs \<in> (\<Union>x\<in>residual_opt OPT S. first_residual_hit_event OPT S s x)"
      by blast
  qed
next
  show "(\<Union>x\<in>residual_opt OPT S. first_residual_hit_event OPT S s x)
        \<subseteq> uniform_wr_weighted.hit_event OPT S s"
  proof
    fix xs
    assume "xs \<in> (\<Union>x\<in>residual_opt OPT S. first_residual_hit_event OPT S s x)"
    then obtain x where "x \<in> residual_opt OPT S"
      and "xs \<in> first_residual_hit_event OPT S s x"
      by blast
    then show "xs \<in> uniform_wr_weighted.hit_event OPT S s"
      unfolding first_residual_hit_event_def by auto
  qed
qed

lemma uniform_wr_first_hit_weighted_gain_decompose:
  assumes OPT_sub: "OPT \<subseteq> V"
  assumes OPT_fin: "finite OPT"
  shows
    "(\<Sum>xs\<in>uniform_wr_weighted.hit_event OPT S s.
        uniform_wr_prob S s xs * first_residual_hit_gain OPT S xs)
     =
     (\<Sum>x\<in>residual_opt OPT S.
        gain S x *
        (\<Sum>xs\<in>first_residual_hit_event OPT S s x. uniform_wr_prob S s xs))"
proof -
  let ?R = "residual_opt OPT S"
  let ?H = "uniform_wr_weighted.hit_event OPT S s"

  have finR: "finite ?R"
    unfolding residual_opt_def
    using OPT_fin
    by simp

  have H_partition:
    "?H = (\<Union>x\<in>?R. first_residual_hit_event OPT S s x)"
    using hit_event_partition_first_residual[OF OPT_sub] .

  have disj:
    "\<And>x y. x \<in> ?R \<Longrightarrow> y \<in> ?R \<Longrightarrow> x \<noteq> y \<Longrightarrow>
       first_residual_hit_event OPT S s x \<inter> first_residual_hit_event OPT S s y = {}"
    using first_residual_hit_event_disjoint by blast

  have sum_union:
    "(\<Sum>xs\<in>?H. uniform_wr_prob S s xs * first_residual_hit_gain OPT S xs)
     =
     (\<Sum>x\<in>?R.
        \<Sum>xs\<in>first_residual_hit_event OPT S s x.
          uniform_wr_prob S s xs * first_residual_hit_gain OPT S xs)"
    unfolding H_partition
    using finR disj
    by (subst sum.UNION_disjoint) auto

  also have "... =
     (\<Sum>x\<in>?R.
        gain S x *
        (\<Sum>xs\<in>first_residual_hit_event OPT S s x. uniform_wr_prob S s xs))"
  proof (rule sum.cong[OF refl])
    fix x
    assume hx: "x \<in> ?R"
    have
      "(\<Sum>xs\<in>first_residual_hit_event OPT S s x.
          uniform_wr_prob S s xs * first_residual_hit_gain OPT S xs)
       =
       (\<Sum>xs\<in>first_residual_hit_event OPT S s x.
          uniform_wr_prob S s xs * gain S x)"
    proof (rule sum.cong[OF refl])
      fix xs
      assume hxs: "xs \<in> first_residual_hit_event OPT S s x"
      from first_residual_hit_event_memD[OF hxs]
      have "first_residual_hit OPT S xs = Some x"
        by simp
      then show
        "uniform_wr_prob S s xs * first_residual_hit_gain OPT S xs
         = uniform_wr_prob S s xs * gain S x"
        unfolding first_residual_hit_gain_def
        by simp
    qed
    also have "... = gain S x * (\<Sum>xs\<in>first_residual_hit_event OPT S s x. uniform_wr_prob S s xs)"
      by (simp add: sum_distrib_left mult.commute mult.left_commute mult.assoc)
    finally show
      "(\<Sum>xs\<in>first_residual_hit_event OPT S s x.
          uniform_wr_prob S s xs * first_residual_hit_gain OPT S xs)
       =
       gain S x * (\<Sum>xs\<in>first_residual_hit_event OPT S s x. uniform_wr_prob S s xs)" .
  qed
  finally show ?thesis .
qed

fun swap_xy :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "swap_xy x y z =
     (if z = x then y else if z = y then x else z)"

lemma swap_xy_self [simp]: "swap_xy x y (swap_xy x y z) = z"
  by auto

lemma map_swap_xy_self [simp]:
  "map (swap_xy x y) (map (swap_xy x y) xs) = xs"
  by (induction xs) auto

lemma residual_opt_subset_rem:
  assumes OPT_sub: "OPT \<subseteq> V"
  shows "residual_opt OPT S \<subseteq> V - S"
  using OPT_sub
  unfolding residual_opt_def
  by auto

lemma swap_xy_preserves_rem:
  assumes OPT_sub: "OPT \<subseteq> V"
  assumes hx: "x \<in> residual_opt OPT S"
  assumes hy: "y \<in> residual_opt OPT S"
  assumes zU: "z \<in> V - S"
  shows "swap_xy x y z \<in> V - S"
proof -
  have xU: "x \<in> V - S" and yU: "y \<in> V - S"
    using hx hy residual_opt_subset_rem[OF OPT_sub] by auto
  show ?thesis
    using xU yU zU by auto
qed

lemma map_swap_xy_uniform_wr_space:
  assumes OPT_sub: "OPT \<subseteq> V"
  assumes hx: "x \<in> residual_opt OPT S"
  assumes hy: "y \<in> residual_opt OPT S"
  assumes xsU: "xs \<in> uniform_wr_space S s"
  shows "map (swap_xy x y) xs \<in> uniform_wr_space S s"
proof -
  have len: "length (map (swap_xy x y) xs) = s"
    using xsU by (auto simp: uniform_wr_space_mem_iff)
  have set_sub: "set (map (swap_xy x y) xs) \<subseteq> V - S"
  proof
    fix z
    assume "z \<in> set (map (swap_xy x y) xs)"
    then obtain w where wmem: "w \<in> set xs" and zdef: "z = swap_xy x y w"
      by auto
    have "w \<in> V - S"
      using xsU wmem by (auto simp: uniform_wr_space_mem_iff)
    then show "z \<in> V - S"
      using zdef swap_xy_preserves_rem[OF OPT_sub hx hy] by simp
  qed
  show ?thesis
    using len set_sub
    by (auto simp: uniform_wr_space_mem_iff)
qed

lemma swap_xy_sym [simp]:
  "swap_xy x y z = swap_xy y x z"
  by auto

lemma first_in_map_swap_some:
  assumes xA: "x \<in> A"
  assumes yA: "y \<in> A"
  assumes h:  "first_in A xs = Some x"
  shows "first_in A (map (swap_xy x y) xs) = Some y"
  using h
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case
  proof (cases "a \<in> A")
    case True
    from Cons.prems True have "a = x"
      by simp
    with True yA show ?thesis
      by simp
  next
    case False
    have ax: "a \<noteq> x"
      using False xA by auto
    have ay: "a \<noteq> y"
      using False yA by auto
    from Cons.prems False have hxs: "first_in A xs = Some x"
      by simp
    from Cons.IH[OF hxs] have ih:
      "first_in A (map (swap_xy x y) xs) = Some y" .

    have swap_a: "swap_xy x y a = a"
      using ax ay by simp

    have "first_in A (map (swap_xy x y) (a # xs))
        = first_in A (swap_xy x y a # map (swap_xy x y) xs)"
      by simp
    also have "... = first_in A (a # map (swap_xy x y) xs)"
      using swap_a by simp
    also have "... = first_in A (map (swap_xy x y) xs)"
      using False by simp
    also have "... = Some y"
      using ih by simp
    finally show ?thesis .
  qed
qed

lemma first_residual_hit_map_swap_some:
  assumes hx: "x \<in> residual_opt OPT S"
  assumes hy: "y \<in> residual_opt OPT S"
  assumes h:  "first_residual_hit OPT S xs = Some x"
  shows "first_residual_hit OPT S (map (swap_xy x y) xs) = Some y"
  using first_in_map_swap_some[OF hx hy]
  using h
  unfolding first_residual_hit_def
  by simp

lemma swap_xy_first_hit_event_bij:
  assumes OPT_sub: "OPT \<subseteq> V"
  assumes hx: "x \<in> residual_opt OPT S"
  assumes hy: "y \<in> residual_opt OPT S"
  shows
    "bij_betw (map (swap_xy x y))
       (first_residual_hit_event OPT S s x)
       (first_residual_hit_event OPT S s y)"
proof (unfold bij_betw_def, intro conjI)
  show "inj_on (map (swap_xy x y)) (first_residual_hit_event OPT S s x)"
  proof (rule inj_onI)
    fix xs ys
    assume xsA: "xs \<in> first_residual_hit_event OPT S s x"
    assume ysA: "ys \<in> first_residual_hit_event OPT S s x"
    assume eq:  "map (swap_xy x y) xs = map (swap_xy x y) ys"

    have dbl_eq:
      "map (swap_xy x y) (map (swap_xy x y) xs)
       = map (swap_xy x y) (map (swap_xy x y) ys)"
      using eq
      by (rule arg_cong[where f = "map (swap_xy x y)"])

    have comp_id: "(swap_xy x y \<circ> swap_xy x y) = id"
      by (rule ext) simp

    have "map id xs = map id ys"
      using dbl_eq comp_id
      by simp
    then show "xs = ys"
      by simp
  qed

  show "map (swap_xy x y) ` first_residual_hit_event OPT S s x
      = first_residual_hit_event OPT S s y"
  proof (rule equalityI)
    show "map (swap_xy x y) ` first_residual_hit_event OPT S s x
        \<subseteq> first_residual_hit_event OPT S s y"
    proof
      fix zs
      assume hz: "zs \<in> map (swap_xy x y) ` first_residual_hit_event OPT S s x"
      then obtain xs where
        xsE: "xs \<in> first_residual_hit_event OPT S s x"
        and zs_def: "zs = map (swap_xy x y) xs"
        by blast

      from xsE have xs_hit: "xs \<in> uniform_wr_weighted.hit_event OPT S s"
        and firstx: "first_residual_hit OPT S xs = Some x"
        unfolding first_residual_hit_event_def by auto

      have xsU: "xs \<in> uniform_wr_space S s"
        using xs_hit by (rule uniform_wr_weighted.hit_event_memD)

      have zsU: "zs \<in> uniform_wr_space S s"
        using zs_def map_swap_xy_uniform_wr_space[OF OPT_sub hx hy xsU]
        by simp

      have firsty: "first_residual_hit OPT S zs = Some y"
        using zs_def first_residual_hit_map_swap_some[OF hx hy firstx]
        by simp

      from first_residual_hit_SomeD[OF firsty]
      have yset: "y \<in> set zs"
        by simp

      have yU: "y \<in> V - S"
        using hy residual_opt_subset_rem[OF OPT_sub]
        by auto

      have zs_hit: "zs \<in> uniform_wr_weighted.hit_event OPT S s"
        unfolding uniform_wr_weighted.hit_event_def
                  hits_residual_def
                  sampled_candidates_def
        using zsU hy yset yU
        by auto

      show "zs \<in> first_residual_hit_event OPT S s y"
        unfolding first_residual_hit_event_def
        using zs_hit firsty
        by auto
    qed

  next
    show "first_residual_hit_event OPT S s y
        \<subseteq> map (swap_xy x y) ` first_residual_hit_event OPT S s x"
    proof
      fix zs
      assume hz: "zs \<in> first_residual_hit_event OPT S s y"

      have zsE: "map (swap_xy x y) zs \<in> first_residual_hit_event OPT S s x"
      proof -
        from hz have zs_hit: "zs \<in> uniform_wr_weighted.hit_event OPT S s"
          and firsty: "first_residual_hit OPT S zs = Some y"
          unfolding first_residual_hit_event_def by auto

        have zsU: "zs \<in> uniform_wr_space S s"
          using zs_hit by (rule uniform_wr_weighted.hit_event_memD)

        have mapU: "map (swap_xy x y) zs \<in> uniform_wr_space S s"
          using map_swap_xy_uniform_wr_space[OF OPT_sub hx hy zsU]
          by simp

        have firstx0:
          "first_residual_hit OPT S (map (swap_xy y x) zs) = Some x"
          using first_residual_hit_map_swap_some[OF hy hx firsty] .

        have map_swap_sym:
          "map (swap_xy y x) zs = map (swap_xy x y) zs"
          by (induction zs) simp_all

        have firstx:
          "first_residual_hit OPT S (map (swap_xy x y) zs) = Some x"
          using firstx0 map_swap_sym
          by simp

        from first_residual_hit_SomeD[OF firstx]
        have xset: "x \<in> set (map (swap_xy x y) zs)"
          by simp

        have xU: "x \<in> V - S"
          using hx residual_opt_subset_rem[OF OPT_sub]
          by auto

        have map_hit: "map (swap_xy x y) zs \<in> uniform_wr_weighted.hit_event OPT S s"
          unfolding uniform_wr_weighted.hit_event_def
                    hits_residual_def
                    sampled_candidates_def
          using mapU hx xset xU
          by auto

        show ?thesis
          unfolding first_residual_hit_event_def
          using map_hit firstx
          by auto
      qed

      have comp_id: "(swap_xy x y \<circ> swap_xy x y) = id"
        by (rule ext) simp

      have "zs = map (swap_xy x y \<circ> swap_xy x y) zs"
        using comp_id by simp
      also have "... = map (swap_xy x y) (map (swap_xy x y) zs)"
        by simp
      also have "... \<in> map (swap_xy x y) ` first_residual_hit_event OPT S s x"
        using zsE by blast
      finally show "zs \<in> map (swap_xy x y) ` first_residual_hit_event OPT S s x" .
    qed
  qed
qed

lemma first_hit_event_card_eq:
  assumes OPT_sub: "OPT \<subseteq> V"
  assumes hx: "x \<in> residual_opt OPT S"
  assumes hy: "y \<in> residual_opt OPT S"
  shows
    "card (first_residual_hit_event OPT S s x)
     = card (first_residual_hit_event OPT S s y)"
  using swap_xy_first_hit_event_bij[OF OPT_sub hx hy]
  by (rule bij_betw_same_card)

lemma first_hit_event_prob_as_card:
  assumes OPT_sub: "OPT \<subseteq> V"
  assumes hx: "x \<in> residual_opt OPT S"
  shows
    "(\<Sum>xs\<in>first_residual_hit_event OPT S s x. uniform_wr_prob S s xs)
     =
     real (card (first_residual_hit_event OPT S s x))
       * inverse (real (card (uniform_wr_space S s)))"
proof -
  have subU: "first_residual_hit_event OPT S s x \<subseteq> uniform_wr_space S s"
    unfolding first_residual_hit_event_def uniform_wr_weighted.hit_event_def
    by auto
  have finE: "finite (first_residual_hit_event OPT S s x)"
    by simp
  have
    "(\<Sum>xs\<in>first_residual_hit_event OPT S s x. uniform_wr_prob S s xs)
     =
     (\<Sum>xs\<in>first_residual_hit_event OPT S s x.
        inverse (real (card (uniform_wr_space S s))))"
  proof (rule sum.cong[OF refl])
    fix xs
    assume "xs \<in> first_residual_hit_event OPT S s x"
    hence "xs \<in> uniform_wr_space S s"
      using subU by auto
    thus "uniform_wr_prob S s xs
        = inverse (real (card (uniform_wr_space S s)))"
      by (rule uniform_wr_prob_inside)
  qed
  also have "... =
     real (card (first_residual_hit_event OPT S s x))
       * inverse (real (card (uniform_wr_space S s)))"
    using finE by simp
  finally show ?thesis .
qed

lemma hit_prob_as_card:
  shows
    "uniform_wr_weighted.hit_prob_of OPT S s
     =
     real (card (uniform_wr_weighted.hit_event OPT S s))
       * inverse (real (card (uniform_wr_space S s)))"
proof -
  have
    "uniform_wr_weighted.hit_prob_of OPT S s
     =
     (\<Sum>xs\<in>uniform_wr_weighted.hit_event OPT S s.
        inverse (real (card (uniform_wr_space S s))))"
    unfolding uniform_wr_weighted.hit_prob_of_def
  proof (rule sum.cong[OF refl])
    fix xs
    assume hxs: "xs \<in> uniform_wr_weighted.hit_event OPT S s"
    hence "xs \<in> uniform_wr_space S s"
      by (rule uniform_wr_weighted.hit_event_memD)
    thus "uniform_wr_prob S s xs
        = inverse (real (card (uniform_wr_space S s)))"
      by (rule uniform_wr_prob_inside)
  qed
  also have "... =
     real (card (uniform_wr_weighted.hit_event OPT S s))
       * inverse (real (card (uniform_wr_space S s)))"
    by simp
  finally show ?thesis .
qed

lemma uniform_wr_first_hit_prob_uniform:
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes S_sub:    "S \<subseteq> V"
  assumes hx:       "x \<in> residual_opt OPT S"
  shows
    "(\<Sum>xs\<in>first_residual_hit_event OPT S s x. uniform_wr_prob S s xs)
      = uniform_wr_weighted.hit_prob_of OPT S s / real (card (residual_opt OPT S))"
proof -
  let ?R = "residual_opt OPT S"

  have finR: "finite ?R"
    unfolding residual_opt_def
    using OPT_fin by simp

  have R_nonempty: "?R \<noteq> {}"
    using hx by blast

  have cardR_pos: "card ?R > 0"
    using finR R_nonempty
    by (simp add: card_gt_0_iff)

  have part:
    "uniform_wr_weighted.hit_event OPT S s
      = (\<Union>y\<in>?R. first_residual_hit_event OPT S s y)"
    using hit_event_partition_first_residual[OF OPT_sub] .

  have disj:
    "\<And>y z. y \<in> ?R \<Longrightarrow> z \<in> ?R \<Longrightarrow> y \<noteq> z
      \<Longrightarrow> first_residual_hit_event OPT S s y \<inter> first_residual_hit_event OPT S s z = {}"
    using first_residual_hit_event_disjoint by blast

  have card_union:
    "card (uniform_wr_weighted.hit_event OPT S s)
      = (\<Sum>y\<in>?R. card (first_residual_hit_event OPT S s y))"
    unfolding part
    using finR disj
    by (subst card_UN_disjoint) auto

  have all_eq:
    "\<And>y. y \<in> ?R
      \<Longrightarrow> card (first_residual_hit_event OPT S s y)
         = card (first_residual_hit_event OPT S s x)"
    using hx first_hit_event_card_eq[OF OPT_sub]
    by blast

  have card_share:
    "card (uniform_wr_weighted.hit_event OPT S s)
      = card ?R * card (first_residual_hit_event OPT S s x)"
  proof -
    have "(\<Sum>y\<in>?R. card (first_residual_hit_event OPT S s y))
        = (\<Sum>y\<in>?R. card (first_residual_hit_event OPT S s x))"
      using all_eq by (intro sum.cong) simp_all
    also have "... = card ?R * card (first_residual_hit_event OPT S s x)"
      using finR by simp
    finally show ?thesis
      using card_union by simp
  qed

  have px:
    "(\<Sum>xs\<in>first_residual_hit_event OPT S s x. uniform_wr_prob S s xs)
     =
     real (card (first_residual_hit_event OPT S s x))
       * inverse (real (card (uniform_wr_space S s)))"
    using first_hit_event_prob_as_card[OF OPT_sub hx] .

  have ph:
    "uniform_wr_weighted.hit_prob_of OPT S s
     =
     real (card (uniform_wr_weighted.hit_event OPT S s))
       * inverse (real (card (uniform_wr_space S s)))"
    by (rule hit_prob_as_card)

  have card_share_real:
    "real (card (first_residual_hit_event OPT S s x))
     =
     real (card (uniform_wr_weighted.hit_event OPT S s)) / real (card ?R)"
    using card_share cardR_pos
    by (simp add: field_simps)

  show ?thesis
    unfolding ph px
    using card_share_real cardR_pos
    by (simp add: divide_inverse algebra_simps)
qed

lemma uniform_wr_first_hit_weighted_gain_eq:
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes S_sub:    "S \<subseteq> V"
  shows
    "(\<Sum>xs\<in>uniform_wr_weighted.hit_event OPT S s.
        uniform_wr_prob S s xs * first_residual_hit_gain OPT S xs)
     =
     uniform_wr_weighted.hit_prob_of OPT S s
       * avg_gain_on S (residual_opt OPT S)"
proof (cases "residual_opt OPT S = {}")
  case True
  have hit_empty: "uniform_wr_weighted.hit_event OPT S s = {}"
  proof (rule equalityI)
    show "uniform_wr_weighted.hit_event OPT S s \<subseteq> {}"
    proof
      fix xs
      assume hxs: "xs \<in> uniform_wr_weighted.hit_event OPT S s"
      then obtain x where hx: "first_residual_hit OPT S xs = Some x"
        using hit_event_imp_first_residual_hit_Some
        by blast
      from first_residual_hit_SomeD[OF hx]
      have xR: "x \<in> residual_opt OPT S"
        by simp
      from True xR have False
        by blast
      then show "xs \<in> {}"
        by simp
    qed
  next
    show "{} \<subseteq> uniform_wr_weighted.hit_event OPT S s"
      by simp
  qed

  show ?thesis
    using hit_empty True
    by (simp add: avg_gain_on_def)
next
  case False
  let ?R = "residual_opt OPT S"

  have finR: "finite ?R"
    unfolding residual_opt_def
    using OPT_fin
    by simp

  have cardR_pos: "card ?R > 0"
    using finR False
    by (simp add: card_gt_0_iff)

  have decomp:
    "(\<Sum>xs\<in>uniform_wr_weighted.hit_event OPT S s.
        uniform_wr_prob S s xs * first_residual_hit_gain OPT S xs)
     =
     (\<Sum>x\<in>?R.
        gain S x *
        (\<Sum>xs\<in>first_residual_hit_event OPT S s x. uniform_wr_prob S s xs))"
    using uniform_wr_first_hit_weighted_gain_decompose[OF OPT_sub OPT_fin] .

  also have "... =
     (\<Sum>x\<in>?R.
        gain S x *
        (uniform_wr_weighted.hit_prob_of OPT S s / real (card ?R)))"
  proof (rule sum.cong[OF refl])
    fix x
    assume hx: "x \<in> ?R"
    show
      "gain S x * (\<Sum>xs\<in>first_residual_hit_event OPT S s x. uniform_wr_prob S s xs)
       =
       gain S x * (uniform_wr_weighted.hit_prob_of OPT S s / real (card ?R))"
      using uniform_wr_first_hit_prob_uniform[OF OPT_sub OPT_fin OPT_card S_sub hx]
      by simp
  qed

  also have "... =
     (\<Sum>x\<in>?R. (gain S x * uniform_wr_weighted.hit_prob_of OPT S s) / real (card ?R))"
    by (simp add: algebra_simps)
  also have "... =
     (\<Sum>x\<in>?R. gain S x * uniform_wr_weighted.hit_prob_of OPT S s) / real (card ?R)"
    by (simp add: sum_divide_distrib)
  also have "... =
     uniform_wr_weighted.hit_prob_of OPT S s *
       ((\<Sum>x\<in>?R. gain S x) / real (card ?R))"
    by (simp add: sum_distrib_right algebra_simps)

  also have "... =
     uniform_wr_weighted.hit_prob_of OPT S s * avg_gain_on S ?R"
    using finR False
    by (simp add: avg_gain_on_def)

  finally show ?thesis
    by simp
qed

subsection \<open>Concrete one-step inequality for uniform WR\<close>

theorem uniform_wr_expected_step_gain_ge_hit_prob_times_avg_residual:
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes S_sub:    "S \<subseteq> V"
  shows
    "uniform_wr_weighted.expected_step_gain S s
      \<ge> uniform_wr_weighted.hit_prob_of OPT S s
          * avg_gain_on S (residual_opt OPT S)"
proof -
  let ?Hit =
    "uniform_wr_weighted.hit_event OPT S s"

  let ?Miss =
    "uniform_wr_weighted.miss_event OPT S s"

  let ?Hsample =
    "(\<Sum>xs\<in>?Hit.
        uniform_wr_prob S s xs * uniform_wr_weighted.sampled_step_gain S xs)"

  let ?Hfirst =
    "(\<Sum>xs\<in>?Hit.
        uniform_wr_prob S s xs * first_residual_hit_gain OPT S xs)"

  let ?M =
    "(\<Sum>xs\<in>?Miss.
        uniform_wr_prob S s xs * uniform_wr_weighted.sampled_step_gain S xs)"

  have split:
    "uniform_wr_weighted.expected_step_gain S s = ?Hsample + ?M"
    by (rule uniform_wr_weighted.expected_step_gain_split_hit_miss)

  have miss_nonneg: "0 \<le> ?M"
  proof (rule sum_nonneg)
    fix xs
    assume hxs: "xs \<in> ?Miss"
    have xs_space: "xs \<in> uniform_wr_space S s"
      using hxs by (rule uniform_wr_weighted.miss_event_memD)
    have p_nonneg: "0 \<le> uniform_wr_prob S s xs"
      using uniform_wr_prob_nonneg xs_space by blast
    have g_nonneg: "0 \<le> uniform_wr_weighted.sampled_step_gain S xs"
      using uniform_wr_weighted.sampled_step_gain_nonneg[OF S_sub xs_space] .
    show "0 \<le> uniform_wr_prob S s xs * uniform_wr_weighted.sampled_step_gain S xs"
      using p_nonneg g_nonneg
      by simp
  qed

  have step1:
    "uniform_wr_weighted.expected_step_gain S s \<ge> ?Hsample"
    using split miss_nonneg
    by linarith

  have hit_mono:
    "?Hfirst \<le> ?Hsample"
  proof (rule sum_mono)
    fix xs
    assume hxs: "xs \<in> ?Hit"
    have p_nonneg: "0 \<le> uniform_wr_prob S s xs"
      using hxs uniform_wr_weighted.hit_event_memD uniform_wr_prob_nonneg
      by blast
    have step_dom:
      "first_residual_hit_gain OPT S xs
        \<le> uniform_wr_weighted.sampled_step_gain S xs"
      using first_residual_hit_gain_le_sampled_step_gain[OF OPT_sub S_sub hxs] .
    show
      "uniform_wr_prob S s xs * first_residual_hit_gain OPT S xs
        \<le> uniform_wr_prob S s xs * uniform_wr_weighted.sampled_step_gain S xs"
      using mult_left_mono[OF step_dom p_nonneg]
      by simp
  qed

  have step2:
    "?Hsample \<ge> ?Hfirst"
    using hit_mono by simp

  have step3:
    "?Hfirst =
      uniform_wr_weighted.hit_prob_of OPT S s
        * avg_gain_on S (residual_opt OPT S)"
    using uniform_wr_first_hit_weighted_gain_eq[OF OPT_sub OPT_fin OPT_card S_sub] .

  have step12:
    "uniform_wr_weighted.expected_step_gain S s \<ge> ?Hfirst"
    using step1 step2
    by linarith

  show ?thesis
    using step12 step3
    by simp
qed


theorem uniform_wr_expected_step_gain_ge_alpha_gap_over_k:
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes S_sub:    "S \<subseteq> V"
  assumes k_pos:    "0 < k"
  shows
    "uniform_wr_weighted.expected_step_gain S s
      \<ge> (alpha_stoch s / real k) * (f OPT - f S)"
proof -
  let ?m = "residual_card OPT S"
  let ?avg = "avg_gain_on S (residual_opt OPT S)"

  have step_ge:
    "uniform_wr_weighted.expected_step_gain S s
      \<ge> uniform_wr_weighted.hit_prob_of OPT S s * ?avg"
    using uniform_wr_expected_step_gain_ge_hit_prob_times_avg_residual
      [OF OPT_sub OPT_fin OPT_card S_sub] .

  have hit_ge:
    "uniform_wr_weighted.hit_prob_of OPT S s \<ge> hit_lb_linear s ?m"
    using uniform_wr_weighted_hit_prob_eq
          uniform_wr_hit_prob_ge_hit_lb_linear[OF OPT_sub OPT_fin OPT_card S_sub]
    by simp

  have avg_nonneg: "0 \<le> ?avg"
    using avg_gain_on_residual_opt_nonneg[OF OPT_sub S_sub] .

  have step_ge':
    "uniform_wr_weighted.expected_step_gain S s
      \<ge> hit_lb_linear s ?m * ?avg"
    using step_ge hit_ge avg_nonneg
    by (meson mult_right_mono order_trans)

  have total_ge_gap:
    "f OPT - f S \<le> real ?m * ?avg"
    using residual_total_gain_ge_gap[OF OPT_sub OPT_fin OPT_card S_sub] .

  have coeff_nonneg: "0 \<le> alpha_stoch s / real k"
    using alpha_stoch_ge_0 k_pos by simp

  have lin_rewrite:
    "hit_lb_linear s ?m * ?avg
      = (alpha_stoch s / real k) * (real ?m * ?avg)"
    using k_pos
    unfolding hit_lb_linear_def
    by (simp add: algebra_simps)

  have coeff_mono:
    "(alpha_stoch s / real k) * (real ?m * ?avg)
      \<ge> (alpha_stoch s / real k) * (f OPT - f S)"
    using total_ge_gap coeff_nonneg
    by (intro mult_left_mono) simp_all

  have step_ge'':
    "uniform_wr_weighted.expected_step_gain S s
      \<ge> (alpha_stoch s / real k) * (real ?m * ?avg)"
    using step_ge' lin_rewrite
    by simp

  show ?thesis
    using step_ge'' coeff_mono
    by linarith
qed


subsection \<open>A ceiling-based sample-size parameter for the \<epsilon>-corollary\<close>

text \<open>
The existing sample_size_eps in the sampling file is floor-like (via nat).
For the clean Deliverable-A corollary we introduce a ceiling-based variant here.
\<close>

definition sample_size_eps_ceil :: "real \<Rightarrow> nat" where
  "sample_size_eps_ceil eps =
     nat (ceiling ((real (card V) / real k) * ln (1 / eps)))"

lemma alpha_stoch_sample_size_eps_ceil_ge_one_minus_eps:
  assumes k_pos: "0 < k"
  assumes k_le_V: "k \<le> card V"
  assumes eps:   "0 < eps" "eps < 1"
  shows "alpha_stoch (sample_size_eps_ceil eps) \<ge> 1 - eps"
proof -
  let ?N = "real (card V)"
  let ?K = "real k"
  let ?L = "ln (1 / eps)"
  let ?A = "(?N / ?K) * ?L"
  let ?s = "sample_size_eps_ceil eps"

  have cardV_pos: "0 < card V"
    using k_pos k_le_V by auto
  hence N_pos: "0 < ?N"
    by simp
  have K_pos: "0 < ?K"
    using k_pos by simp

  have inv_eps_pos: "0 < 1 / eps"
    using eps by simp
  have inv_eps_ge_1: "1 \<le> 1 / eps"
    using eps by (simp add: field_simps)

  have L_nonneg: "0 \<le> ?L"
    using inv_eps_pos inv_eps_ge_1
    by (simp add: ln_ge_iff)

  have A_nonneg: "0 \<le> ?A"
    using N_pos K_pos L_nonneg by simp

  have ceil_nonneg: "0 \<le> ceiling ?A"
    using A_nonneg by linarith

  have real_s_eq:
    "real ?s = real_of_int (ceiling ?A)"
    unfolding sample_size_eps_ceil_def
    using ceil_nonneg by simp

  have A_le_real_s:
    "?A \<le> real ?s"
  proof -
    have "?A \<le> real_of_int (ceiling ?A)"
      by (rule le_of_int_ceiling)
    also have "... = real ?s"
      using real_s_eq by simp
    finally show ?thesis .
  qed

  have factor_pos: "0 \<le> ?K / ?N"
    using K_pos N_pos by simp

  have A_times_factor:
    "?A * (?K / ?N) = ?L"
  proof -
    have "?A * (?K / ?N) = ((?N / ?K) * (?K / ?N)) * ?L"
      by (simp add: algebra_simps)
    also have "((?N / ?K) * (?K / ?N)) = 1"
      using K_pos N_pos by (simp add: field_simps)
    finally show ?thesis by simp
  qed

  have scaled_ge_ln:
    "real ?s * (?K / ?N) \<ge> ?L"
  proof -
    have h1: "real ?s * (?K / ?N) \<ge> ?A * (?K / ?N)"
      using A_le_real_s factor_pos
      by (intro mult_right_mono) simp_all
    have h2: "?A * (?K / ?N) = ?L"
      using A_times_factor .
    from h1 h2 show ?thesis
      by simp
  qed

  have neg_le:
    "- (real ?s * (?K / ?N)) \<le> - ?L"
    using scaled_ge_ln by linarith

  have exp_le:
    "exp (- (real ?s * (?K / ?N))) \<le> exp (- ?L)"
    using neg_le
    by simp

  have minus_ln_eq:
    "- ln (1 / eps) = ln eps"
    using eps
    by (simp add: ln_div)

  have exp_ln_eq:
    "exp (- ?L) = eps"
  proof -
    have "exp (- ?L) = exp (ln eps)"
      unfolding minus_ln_eq[symmetric]
      by simp
    also have "... = eps"
      using eps
      by simp
    finally show ?thesis .
  qed

  have exp_le_eps:
    "exp (- (real ?s * (?K / ?N))) \<le> eps"
    using exp_le exp_ln_eq by simp

  have alpha_eq:
    "alpha_stoch ?s = 1 - exp (- (real ?s * (?K / ?N)))"
    unfolding alpha_stoch_def
    by simp

  show ?thesis
    using alpha_eq exp_le_eps
    by linarith
qed

corollary uniform_wr_expected_step_gain_ge_one_minus_eps_gap_over_k:
  assumes OPT_sub:  "OPT \<subseteq> V"
  assumes OPT_fin:  "finite OPT"
  assumes OPT_card: "card OPT \<le> k"
  assumes S_sub:    "S \<subseteq> V"
  assumes k_pos:    "0 < k"
  assumes k_le_V:   "k \<le> card V"
  assumes gap_nonneg: "f S \<le> f OPT"
  assumes eps:      "0 < eps" "eps < 1"
  shows
    "uniform_wr_weighted.expected_step_gain S (sample_size_eps_ceil eps)
      \<ge> ((1 - eps) / real k) * (f OPT - f S)"
proof -
  have base:
    "uniform_wr_weighted.expected_step_gain S (sample_size_eps_ceil eps)
      \<ge> (alpha_stoch (sample_size_eps_ceil eps) / real k) * (f OPT - f S)"
    using uniform_wr_expected_step_gain_ge_alpha_gap_over_k
      [OF OPT_sub OPT_fin OPT_card S_sub k_pos, of "sample_size_eps_ceil eps"] .

  have alpha_ge:
    "alpha_stoch (sample_size_eps_ceil eps) \<ge> 1 - eps"
    using alpha_stoch_sample_size_eps_ceil_ge_one_minus_eps
      [OF k_pos k_le_V eps] .

  have gap_ge0: "0 \<le> f OPT - f S"
    using gap_nonneg by linarith

  have coeff_ge:
    "(1 - eps) / real k \<le> alpha_stoch (sample_size_eps_ceil eps) / real k"
  proof -
    have k_real_pos: "0 < real k"
      using k_pos by simp
    have inv_nonneg: "0 \<le> inverse (real k)"
      using k_real_pos by simp
    have "(1 - eps) * inverse (real k)
          \<le> alpha_stoch (sample_size_eps_ceil eps) * inverse (real k)"
      using alpha_ge inv_nonneg
      by (intro mult_right_mono) simp_all
    then show ?thesis
      by (simp add: divide_inverse)
  qed

  have coeff_mono:
    "((1 - eps) / real k) * (f OPT - f S)
      \<le> (alpha_stoch (sample_size_eps_ceil eps) / real k) * (f OPT - f S)"
    using coeff_ge gap_ge0
    by (intro mult_right_mono) simp_all

  show ?thesis
    using base coeff_mono
    by linarith
  qed

end

end