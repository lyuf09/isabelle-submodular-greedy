theory Greedy_Submodular_Approx
  imports Greedy_Submodular_Construct
begin

text \<open>
  This theory derives analytic bounds for the coefficient
  \<open>1 - (1 - 1/k)^k\<close> appearing in the Nemhauser–Wolsey approximation ratio.
  In particular we show that it is bounded below by \<open>1 - 1/exp 1\<close>.
\<close>

text \<open>
  First, we relate the discrete quantity \<open>(1 - 1/k)^k\<close> to the exponential
  function via a standard limit inequality.
\<close>

lemma pow_one_minus_inv_le_exp_neg1:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "(1 - 1 / real k) ^ k \<le> exp (-1 :: real)"
proof -
  have f1: "0 < k"
    using assms by auto
  have "1 \<le> real k"
    using assms one_of_nat_le_iff by blast
  then show ?thesis
    using f1 exp_ge_one_minus_x_over_n_power_n by presburger
qed

text \<open>
  As a corollary, we obtain a uniform lower bound
  \<open>1 - (1 - 1/k)^k \<ge> 1 - 1/exp 1\<close> for all \<open>k \<ge> 1\<close>.
\<close>

lemma coeff_ge_1_minus_inv_exp:
  fixes k :: nat
  assumes "k \<ge> 1"
  shows "1 - (1 - 1 / real k) ^ k \<ge> 1 - 1 / exp 1"
proof -
  from pow_one_minus_inv_le_exp_neg1[OF assms]
  have "(1 - 1 / real k) ^ k \<le> exp (-1 :: real)" .
  then have "1 - (1 - 1 / real k) ^ k \<ge> 1 - exp (-1 :: real)"
    by simp
  also have "exp (-1 :: real) = 1 / exp 1"
    by (simp add: exp_minus field_simps)
  finally show ?thesis .
qed


context Greedy_Setup
begin

section \<open>Greedy approximation for monotone submodular maximization\<close>

text \<open>
  In this section we formalize the classical Nemhauser–Wolsey guarantee:
  for a non-negative, monotone, submodular function on a finite ground set,
  the greedy algorithm that selects \<open>k\<close> elements achieves at least
  \<open>1 - (1 - 1/k)^k\<close> times the optimal value. Combining this with the analytic
  bound above yields the familiar \<open>1 - 1/e\<close> approximation factor.
\<close>

text \<open>Elementary algebraic identity used in the gap recurrence.\<close>
lemma one_minus_inv_times:
  fixes x :: real
  shows "(1 - 1 / real k) * x = x - x / real k"
  by (simp add: left_diff_distrib)

section \<open>Submodular setting\<close>

subsection \<open>Non-emptiness lemmas\<close>

text \<open>
  Two basic non-emptiness facts:
  \<midarrow> if \<open>S \<subseteq> V\<close> and \<open>|S| < k \<le> |V|\<close>, then the candidate set \<open>V - S\<close> is non-empty;
  \<midarrow> if \<open>S, Opt \<subseteq> V\<close> and \<open>f S < f Opt\<close>, then the gap set \<open>Opt - S\<close> is non-empty.
\<close>

lemma nonempty_candidates:
  assumes "S \<subseteq> V" "card S < k" "k \<le> card V"
  shows "V - S \<noteq> {}"
proof
  assume "V - S = {}"
  hence "V \<subseteq> S" by auto
  with assms(1) have "V = S" by auto
  with assms(2,3) show False by simp
qed

lemma nonempty_gap:
  assumes "S \<subseteq> V" "Opt \<subseteq> V" "f S < f Opt"
  shows "Opt - S \<noteq> {}"
proof
  assume "Opt - S = {}"
  hence "Opt \<subseteq> S" by auto
  with assms(1,2) have "f Opt \<le> f S" using monotone_f by auto
  with assms(3) show False by linarith
qed

subsection \<open>Submodular calculus\<close>

text \<open>
  We next derive a diminishing-returns inequality for marginal gains and
  a telescoping upper bound over a finite disjoint set.
\<close>

text \<open>Diminishing returns: marginal gain decreases as the base set grows.\<close>
lemma gain_decreasing:
  assumes "S \<subseteq> T" "T \<subseteq> V" "x \<in> V" "x \<notin> T"
  shows "gain S x \<ge> gain T x"
proof -
  have Sx_sub_V: "S \<union> {x} \<subseteq> V"
    using assms(1,2,3) by auto

  from submodular_f[OF Sx_sub_V assms(2)]
  have subm:
    "f ((S \<union> {x}) \<union> T) + f ((S \<union> {x}) \<inter> T)
       \<le> f (S \<union> {x}) + f T" .

  have "(S \<union> {x}) \<union> T = T \<union> {x}"
    using assms(1) by auto
  moreover have "(S \<union> {x}) \<inter> T = S"
    using assms(1,4) by auto
  ultimately have
    "f (T \<union> {x}) + f S \<le> f (S \<union> {x}) + f T"
    using subm by simp

  hence "f (S \<union> {x}) - f S \<ge> f (T \<union> {x}) - f T"
    by linarith

  thus ?thesis
    by (simp add: gain_def)
qed

subsection \<open>Main averaging lemma\<close>

text \<open>
  We now establish the averaging argument underlying the greedy guarantee.
  Intuitively, as long as \<open>|S| < k\<close> and \<open>|Opt| \<le> k\<close>, there exists
  some element in \<open>V - S\<close> whose marginal gain is at least the average
  contribution of elements in an optimal solution.
\<close>

text \<open>Submodular telescoping: sum of marginals upper-bounds the joint gain.\<close>
lemma submod_sum_upper:
  assumes "finite A" "A \<subseteq> V" "S \<subseteq> V" "A \<inter> S = {}"
  shows "f (S \<union> A) - f S \<le> (\<Sum>x\<in>A. gain S x)"
  using assms
proof (induction rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a A)
  from insert.hyps have a_notin: "a \<notin> A" and finA: "finite A" by auto

  from insert.prems have S_sub: "S \<subseteq> V" by auto
  from insert.prems have ins_subV: "insert a A \<subseteq> V" by auto
  from insert.prems have ins_disj: "insert a A \<inter> S = {}" by auto

  have A_sub: "A \<subseteq> V" using ins_subV by auto
  have aV   : "a \<in> V"  using ins_subV by auto
  have disjA: "A \<inter> S = {}" using ins_disj by auto
  have a_notS: "a \<notin> S" using ins_disj by auto

  have step:
    "f (S \<union> insert a A) - f S
     = (f ((S \<union> A) \<union> {a}) - f (S \<union> A)) + (f (S \<union> A) - f S)"
    by (simp add: insert_commute Un_assoc)

  have SSUA: "S \<subseteq> S \<union> A" by auto
  have SUA_subV: "S \<union> A \<subseteq> V" using S_sub A_sub by auto
  have a_notin_SUA: "a \<notin> S \<union> A" using a_notS a_notin by auto
  have dec:
    "f ((S \<union> A) \<union> {a}) - f (S \<union> A) \<le> gain S a"
    using gain_decreasing[OF SSUA SUA_subV aV a_notin_SUA]
    by (simp add: gain_def)

  from insert.IH[OF A_sub S_sub disjA]
  have IH: "f (S \<union> A) - f S \<le> (\<Sum>x\<in>A. gain S x)" .

  have "(f ((S \<union> A) \<union> {a}) - f (S \<union> A)) + (f (S \<union> A) - f S)
        \<le> gain S a + (\<Sum>x\<in>A. gain S x)"
    using dec IH by linarith
  thus ?case
    by (simp add: step insert_commute finA a_notin)
qed

text \<open>
  Average marginal bound against any feasible \<open>Opt\<close> with \<open>|Opt| \<le> k\<close>:
  there exists an element \<open>e \<in> V - S\<close> such that
  \<open>gain S e \<ge> (f Opt - f S) / real k\<close>.
\<close>
lemma marginal_gain_lower_bound:
  fixes Opt S :: "'a set"
  assumes S_sub: "S \<subseteq> V"
    and O_sub: "Opt \<subseteq> V"
    and k_le_V: "k \<le> card V"
    and cardS_lt_k: "card S < k"
    and cardO_le_k: "card Opt \<le> k"
  shows "\<exists>e\<in>V - S. gain S e \<ge> (f Opt - f S) / real k"
proof -
  have finV: "finite V" by (rule finite_V)
  have k_pos: "0 < k" using cardS_lt_k by (simp add: not_less)

  consider (le) "f Opt \<le> f S" | (gt) "f S < f Opt" by linarith
  then show ?thesis
  proof cases
    case le
    have VS_ne: "V - S \<noteq> {}"
      using nonempty_candidates[OF S_sub cardS_lt_k k_le_V] .

    then obtain e where eVS: "e \<in> V - S" by blast
    hence ge0: "0 \<le> gain S e" using S_sub gain_nonneg by auto

    moreover have "(f Opt - f S) / real k \<le> 0"
    proof -
      have "f Opt - f S \<le> 0" using le by linarith
      thus ?thesis
        using k_pos by (simp add: divide_nonpos_pos)
    qed

    ultimately have "(f Opt - f S) / real k \<le> gain S e"
      by linarith

    thus ?thesis
      using eVS by (intro bexI[of _ e]) auto
  next
    case gt
    have OS_ne: "Opt - S \<noteq> {}"
      using nonempty_gap[OF S_sub O_sub gt] .

    have finOS: "finite (Opt - S)"
      using finV O_sub by (meson Diff_subset finite_subset)
    have OS_subV: "Opt - S \<subseteq> V" using O_sub by auto
    have disj: "(Opt - S) \<inter> S = {}" by auto
    have finO: "finite Opt" using finV O_sub finite_subset by blast

    have step_sum:
      "f (S \<union> (Opt - S)) - f S \<le> (\<Sum>x\<in>Opt - S. gain S x)"
      using submod_sum_upper[OF finOS OS_subV S_sub disj] .

    have SUO_subV: "S \<union> Opt \<subseteq> V" using S_sub O_sub by auto
    have sum_upper: "f Opt - f S \<le> (\<Sum>x\<in>Opt - S. gain S x)"
    proof -
      have "f Opt \<le> f (S \<union> Opt)"
        using monotone_f[rule_format, of Opt "S \<union> Opt"] SUO_subV by auto
      then have "f Opt - f S \<le> f (S \<union> Opt) - f S" by linarith
      also have "S \<union> Opt = S \<union> (Opt - S)" by auto
      also have "f (S \<union> (Opt - S)) - f S
                   \<le> (\<Sum>x\<in>Opt - S. gain S x)"
        using step_sum .
      finally show ?thesis .
    qed

    obtain e where e_in: "e \<in> Opt - S"
      and e_arg: "is_arg_max (gain S) (\<lambda>y. y \<in> Opt - S) e"
      using finite_is_arg_max_in[of "Opt - S" "gain S"] finOS OS_ne
      by blast

    have e_max: "\<forall>y\<in>Opt - S. gain S y \<le> gain S e"
    proof
      fix y assume yA: "y \<in> Opt - S"
      show "gain S y \<le> gain S e"
        using is_arg_maxD_le[OF e_arg yA] .
    qed

    have "(\<Sum>x\<in>Opt - S. gain S x) \<le> (\<Sum>x\<in>Opt - S. gain S e)"
      using e_max by (intro sum_mono) simp_all
    also have "... = real (card (Opt - S)) * gain S e"
      by simp
    finally have sum_le_card_max:
      "(\<Sum>x\<in>Opt - S. gain S x) \<le> real (card (Opt - S)) * gain S e" .

    have base: "f Opt - f S \<le> real (card (Opt - S)) * gain S e"
      using sum_upper sum_le_card_max by linarith

    have cardOS_le_k: "card (Opt - S) \<le> k"
    proof -
      have "card (Opt - S) \<le> card Opt"
        using finO Diff_subset by (rule card_mono)
      also have "... \<le> k" using cardO_le_k .
      finally show ?thesis .
    qed

    have eVS: "e \<in> V - S" using e_in O_sub by auto
    have ge0: "0 \<le> gain S e" using S_sub eVS gain_nonneg by auto

    have "real (card (Opt - S)) * gain S e \<le> real k * gain S e"
      using cardOS_le_k ge0 by (simp add: mult_right_mono)
    hence main_ineq: "f Opt - f S \<le> real k * gain S e"
      using base by linarith

    have "gain S e \<ge> (f Opt - f S) / real k"
      using main_ineq k_pos by (simp add: mult.commute pos_divide_le_eq)
    thus ?thesis using eVS by blast
  qed
qed


subsection \<open>Feasible sets and the optimal value OPT\<close>

text \<open>
  We collect all feasible sets of cardinality at most \<open>k\<close> and define
  \<open>OPT_k\<close> as the maximum value of \<open>f\<close> over this family.
\<close>

lemma feasible_set_k_nonempty:
  "{} \<in> feasible_set_k"
  by (simp add: feasible_set_k_def feasible_def)

lemma feasible_set_k_finite:
  "finite feasible_set_k"
proof -
  have "feasible_set_k \<subseteq> Pow V"
    by (auto simp: feasible_set_k_def feasible_def)
  moreover have "finite (Pow V)"
    using finite_V by simp
  ultimately show ?thesis
    by (rule finite_subset)
qed

subsection \<open>Existence of maximal element in finite sets\<close>

text \<open>
  Set-function version of the finite arg-max lemma: there is a maximizer
  of \<open>f\<close> over any finite non-empty family of sets.
\<close>
lemma finite_has_maximal_is_arg:
  assumes "finite A" "A \<noteq> {}"
  shows "\<exists>x\<in>A. is_arg_max f (\<lambda>x. x \<in> A) x"
  using finite_is_arg_max_in[of A f] assms by blast

corollary finite_has_maximal:
  assumes "finite A" "A \<noteq> {}"
  shows "\<exists>x\<in>A. \<forall>y\<in>A. f y \<le> f x"
proof -
  from finite_has_maximal_is_arg[OF assms]
  obtain x where xA: "x \<in> A" and xarg: "is_arg_max f (\<lambda>x. x \<in> A) x"
    by blast
  have "\<forall>y\<in>A. f y \<le> f x"
  proof
    fix y assume "y \<in> A"
    thus "f y \<le> f x"
      using is_arg_maxD_le[OF xarg] by blast
  qed
  thus ?thesis using xA by blast
qed


subsection \<open>OPT as a maximizer over feasible sets\<close>

text \<open>
  Using the choice operator \<open>SOME\<close>, we select a canonical optimal set
  \<open>OPT_set\<close> and define \<open>OPT_k = f OPT_set\<close>. All subsequent bounds
  are expressed in terms of this quantity.
\<close>

definition OPT_set :: "'a set" where
  "OPT_set =
     (SOME X. X \<in> feasible_set_k \<and> (\<forall>Y\<in>feasible_set_k. f Y \<le> f X))"

lemma exists_max_feasible:
  "\<exists>X. X \<in> feasible_set_k \<and> (\<forall>Y\<in>feasible_set_k. f Y \<le> f X)"
proof -
  have nonempty: "feasible_set_k \<noteq> {}"
    using feasible_set_k_nonempty by auto
  from finite_has_maximal[OF feasible_set_k_finite nonempty]
  show ?thesis
    by blast
qed

lemma OPT_set_props:
  shows OPT_set_in: "OPT_set \<in> feasible_set_k"
    and OPT_set_max: "\<forall>Y\<in>feasible_set_k. f Y \<le> f OPT_set"
proof -
  from exists_max_feasible
  obtain X where X_in: "X \<in> feasible_set_k"
    and X_max: "\<forall>Y\<in>feasible_set_k. f Y \<le> f X"
    by blast
  then have ex_spec:
    "\<exists>X. X \<in> feasible_set_k \<and> (\<forall>Y\<in>feasible_set_k. f Y \<le> f X)"
    by blast
  from someI_ex[OF ex_spec]
  have "OPT_set \<in> feasible_set_k \<and> (\<forall>Y\<in>feasible_set_k. f Y \<le> f OPT_set)"
    unfolding OPT_set_def by simp
  then show "OPT_set \<in> feasible_set_k"
    and "\<forall>Y\<in>feasible_set_k. f Y \<le> f OPT_set"
    by auto
qed

definition OPT_k :: real where
  "OPT_k = f OPT_set"

lemma exists_opt_set:
  "\<exists>X\<in>feasible_set_k. f X = OPT_k"
proof -
  have "OPT_set \<in> feasible_set_k"
    by (rule OPT_set_in)
  moreover have "f OPT_set = OPT_k"
    unfolding OPT_k_def by simp
  ultimately show ?thesis
    by blast
qed

lemma OPT_k_upper_bound:
  assumes "S \<in> feasible_set_k"
  shows "f S \<le> OPT_k"
proof -
  have "\<forall>Y\<in>feasible_set_k. f Y \<le> f OPT_set"
    by (rule OPT_set_max)
  with assms have "f S \<le> f OPT_set"
    by auto
  thus ?thesis
    unfolding OPT_k_def by simp
qed

subsection \<open>Gap sequence\<close>

text \<open>
  We introduce the gap sequence \<open>gap i = OPT_k - f (greedy_set i)\<close> and
  show that it satisfies a simple linear recurrence under the greedy update.
\<close>

definition gap :: "nat \<Rightarrow> real" where
  "gap i = OPT_k - f (greedy_set i)"

text \<open>
  One-step inequality: the marginal gain of the greedy choice lower-bounds
  the average improvement towards \<open>OPT_k\<close>.
\<close>
lemma greedy_step_ineq:
  assumes "i < k"
      and S_sub: "greedy_set i \<subseteq> V"
      and R_nonempty: "V - greedy_set i \<noteq> {}"
      and k_le_V: "k \<le> card V"
  shows "gain (greedy_set i)
           (argmax_gain (greedy_set i) (V - greedy_set i))
         \<ge> (OPT_k - f (greedy_set i)) / real k"
proof -
  let ?S = "greedy_set i"
  let ?R = "V - ?S"

  obtain X where X_in: "X \<in> feasible_set_k" and X_opt: "f X = OPT_k"
    using exists_opt_set by blast
  from X_in have X_sub: "X \<subseteq> V" and cardX_le_k: "card X \<le> k"
    unfolding feasible_set_k_def feasible_def by auto

  have S_sub': "?S \<subseteq> V"
    using S_sub .

  have cardS_lt_k: "card ?S < k"
  proof -
    have "card ?S \<le> i"
      by (rule card_greedy_le_i)
    with assms(1) show ?thesis
      by (meson le_less_trans)
  qed

  from marginal_gain_lower_bound[
        OF S_sub' X_sub k_le_V cardS_lt_k cardX_le_k]
  obtain e where e_inR: "e \<in> V - ?S"
    and e_lb: "gain ?S e \<ge> (f X - f ?S) / real k"
    by blast

  have finV: "finite V"
    by (rule finite_V)

  have finR: "finite ?R"
    using finV by auto
  have R_nonempty': "?R \<noteq> {}"
    using R_nonempty by simp

  have argmax_dom:
    "argmax_gain ?S ?R \<in> ?R"
    using argmax_gain_mem[OF finR R_nonempty'] .

  have argmax_max:
    "\<forall>y\<in>?R. gain ?S y \<le> gain ?S (argmax_gain ?S ?R)"
    using argmax_gain_max[OF finR R_nonempty'] .

  from argmax_max e_inR
  have e_le_argmax:
    "gain ?S e \<le> gain ?S (argmax_gain ?S ?R)"
    by auto

  have argmax_lb:
    "gain ?S (argmax_gain ?S ?R)
       \<ge> (f X - f ?S) / real k"
    using e_lb e_le_argmax by linarith

  have "(f X - f ?S) / real k = (OPT_k - f ?S) / real k"
    using X_opt by simp

  with argmax_lb
  have "gain ?S (argmax_gain ?S ?R)
        \<ge> (OPT_k - f ?S) / real k"
    by simp

  thus ?thesis
    by simp
qed

text \<open>Greedy sets are feasible whenever their size is at most \<open>k\<close>.\<close>
lemma feasible_set_k_subset:
  assumes "S \<in> feasible_set_k"
  shows "S \<subseteq> V" "card S \<le> k"
  using assms unfolding feasible_set_k_def feasible_def by auto

lemma greedy_set_feasible:
  assumes S_sub: "greedy_set i \<subseteq> V"
      and card_le_i: "card (greedy_set i) \<le> i"
      and i_le_k: "i \<le> k"
  shows "greedy_set i \<in> feasible_set_k"
proof -
  have "card (greedy_set i) \<le> k"
    using card_le_i i_le_k by (meson order_trans)
  with S_sub show ?thesis
    unfolding feasible_set_k_def feasible_def by auto
qed

text \<open>The gap is non-negative along the greedy sequence.\<close>
lemma gap_nonneg:
  assumes S_sub: "greedy_set i \<subseteq> V"
      and card_le_i: "card (greedy_set i) \<le> i"
      and i_le_k: "i \<le> k"
  shows "0 \<le> gap i"
proof -
  have S_feas: "greedy_set i \<in> feasible_set_k"
    using greedy_set_feasible[OF S_sub card_le_i i_le_k] .
  have "f (greedy_set i) \<le> OPT_k"
    using OPT_k_upper_bound[OF S_feas] .
  then have "0 \<le> OPT_k - f (greedy_set i)"
    by simp
  thus ?thesis
    unfolding gap_def by simp
qed

text \<open>
  Gap recurrence: each step reduces the gap by at least a \<open>1/k\<close> fraction.
\<close>
lemma gap_step_diff:
  assumes "i < k"
      and S_sub: "greedy_set i \<subseteq> V"
      and R_nonempty: "V - greedy_set i \<noteq> {}"
      and k_le_V: "k \<le> card V"
  shows "gap (Suc i) \<le> gap i - gap i / real k"
proof -
  let ?S = "greedy_set i"

  have base:
    "gain ?S (argmax_gain ?S (V - ?S))
       \<ge> (OPT_k - f ?S) / real k"
    using greedy_step_ineq[OF assms] by simp

  have gap_Suc_eq:
    "gap (Suc i)
       = OPT_k - f ?S
         - gain ?S (argmax_gain ?S (V - ?S))"
  proof -
    have "gap (Suc i) = OPT_k - f (greedy_set (Suc i))"
      by (simp add: gap_def)
    also have "\<dots> = OPT_k
                 - (f ?S
                    + gain ?S (argmax_gain ?S (V - ?S)))"
      using greedy_step_f_eq[OF R_nonempty] by simp
    also have "\<dots> = OPT_k - f ?S
                   - gain ?S (argmax_gain ?S (V - ?S))"
      by simp
    finally show ?thesis .
  qed

  have "OPT_k - f ?S
        - gain ?S (argmax_gain ?S (V - ?S))
      \<le> OPT_k - f ?S
        - (OPT_k - f ?S) / real k"
    using base by linarith
  hence "gap (Suc i)
         \<le> OPT_k - f ?S - (OPT_k - f ?S) / real k"
    using gap_Suc_eq by simp

  also have "OPT_k - f ?S - (OPT_k - f ?S) / real k
             = gap i - gap i / real k"
    by (simp add: gap_def)

  finally show ?thesis .
qed

text \<open>
  In multiplicative form, the gap shrinks by a factor of at most
  \<open>1 - 1/real k\<close> per step.
\<close>
lemma gap_step:
  assumes "i < k"
      and "greedy_set i \<subseteq> V"
      and "V - greedy_set i \<noteq> {}"
      and "k \<le> card V"
  shows "gap (Suc i) \<le> (1 - 1 / real k) * gap i"
proof -
  have "gap (Suc i) \<le> gap i - gap i / real k"
    using gap_step_diff[OF assms] .
  also have "gap i - gap i / real k
             = (1 - 1 / real k) * gap i"
    using one_minus_inv_times[of "gap i"] by simp
  finally show ?thesis .
qed

lemma gap_0[simp]: "gap 0 = OPT_k"
proof -
  have "gap 0 = OPT_k - f (greedy_set 0)"
    by (simp add: gap_def)
  also have "greedy_set 0 = {}" by simp
  also have "f {} = 0" by (rule f_empty)
  finally show ?thesis by simp
qed

text \<open>
  Geometric decay of the gap: after \<open>i\<close> greedy steps the remaining gap is
  bounded by \<open>(1 - 1/real k)^i * OPT_k\<close>.
\<close>
lemma gap_geometric:
  assumes k_pos: "k > 0"
      and k_le_V: "k \<le> card V"
      and i_le_k: "i \<le> k"
  shows "gap i \<le> (1 - 1 / real k) ^ i * OPT_k"
using i_le_k
proof (induction i)
  case 0
  have "gap 0 = OPT_k" by simp
  thus ?case by simp
next
  case (Suc i)
  have i_le_k: "i \<le> k" using Suc.prems by simp
  have i_lt_k: "i < k" using Suc.prems by simp

  have S_sub: "greedy_set i \<subseteq> V"
    by (rule greedy_subset_V)
  have cardSi_le_i: "card (greedy_set i) \<le> i"
    by (rule card_greedy_le_i)

  have gap_i_nonneg: "0 \<le> gap i"
    using gap_nonneg[OF S_sub cardSi_le_i i_le_k] .

  have cardSi_lt_V: "card (greedy_set i) < card V"
  proof -
    have "card (greedy_set i) \<le> i"
      by (rule card_greedy_le_i)
    also have "... < k" using i_lt_k by simp
    also have "... \<le> card V" using k_le_V by simp
    finally show ?thesis .
  qed

  have R_nonempty: "V - greedy_set i \<noteq> {}"
    using remainder_nonempty_if_card_ltV[OF cardSi_lt_V] .

  have step:
    "gap (Suc i) \<le> (1 - 1 / real k) * gap i"
    using gap_step[OF i_lt_k S_sub R_nonempty k_le_V] .

  have coef_nonneg: "0 \<le> (1 - 1 / real k)"
  proof -
    have "1 \<le> real k" using k_pos by simp
    then have "1 / real k \<le> 1"
      by (simp add: field_simps)
    then show ?thesis
      by simp
  qed

  have mult_mono:
    "(1 - 1 / real k) * gap i
      \<le> (1 - 1 / real k) * ((1 - 1 / real k) ^ i * OPT_k)"
  proof -
    have IH: "gap i \<le> (1 - 1 / real k) ^ i * OPT_k"
      using Suc.IH i_le_k by simp
    from IH coef_nonneg show ?thesis
      by (rule mult_left_mono)
  qed

  have pow_Suc:
   "(1 - 1 / real k) * ((1 - 1 / real k) ^ i * OPT_k)
     = (1 - 1 / real k) ^ Suc i * OPT_k"
   by (simp add: mult_ac)

  from step mult_mono have
    "gap (Suc i)
       \<le> (1 - 1 / real k) * ((1 - 1 / real k) ^ i * OPT_k)"
    by (rule order_trans)
  hence "gap (Suc i)
         \<le> (1 - 1 / real k) ^ Suc i * OPT_k"
    by (simp add: pow_Suc)
  thus ?case
    by simp
qed

text \<open>
  As a consequence, the value of the greedy solution after \<open>k\<close> steps is
  at least \<open>(1 - (1 - 1/real k)^k) * OPT_k\<close>.
\<close>
lemma greedy_sequence_bound:
  assumes k_pos: "k > 0"
      and k_le_V: "k \<le> card V"
  shows "f (greedy_set k) \<ge> (1 - (1 - 1 / real k) ^ k) * OPT_k"
proof -
  have gap_bound:
    "gap k \<le> (1 - 1 / real k) ^ k * OPT_k"
    using gap_geometric[OF k_pos k_le_V le_refl] .

  have f_eq:
    "f (greedy_set k) = OPT_k - gap k"
    by (simp add: gap_def)

  have lower_bound:
    "OPT_k - gap k \<ge> OPT_k - (1 - 1 / real k) ^ k * OPT_k"
  proof -
    have "- gap k \<ge> - ((1 - 1 / real k) ^ k * OPT_k)"
      using gap_bound by simp
    thus ?thesis
      by simp
  qed

  have "f (greedy_set k) \<ge> OPT_k - (1 - 1 / real k) ^ k * OPT_k"
    using f_eq lower_bound by simp

  also have "OPT_k - (1 - 1 / real k) ^ k * OPT_k
             = (1 - (1 - 1 / real k) ^ k) * OPT_k"
  proof -
    have "OPT_k - (1 - 1 / real k) ^ k * OPT_k
          = 1 * OPT_k - (1 - 1 / real k) ^ k * OPT_k"
      by simp
    also have "... = (1 - (1 - 1 / real k) ^ k) * OPT_k"
      by (simp add: left_diff_distrib)
    finally show ?thesis .
  qed

  finally show ?thesis .
qed

subsection \<open>Non-negativity of OPT and approximation ratio\<close>

text \<open>\<open>OPT_k\<close> is non-negative because \<open>f {} = 0\<close> is a feasible value.\<close>
lemma OPT_k_nonneg: "0 \<le> OPT_k"
proof -
  have "{} \<in> feasible_set_k"
    by (rule feasible_set_k_nonempty)
  then have "f {} \<le> OPT_k"
    by (rule OPT_k_upper_bound)
  thus ?thesis
    by (simp add: f_empty)
qed

text \<open>
  Combining the discrete bound with the analytic inequality for
  \<open>1 - (1 - 1/k)^k\<close> yields the standard \<open>1 - 1/e\<close> approximation factor.
\<close>
theorem greedy_approximation:
  assumes k_pos: "k > 0"
      and k_le_V: "k \<le> card V"
  shows "f (greedy_set k) \<ge> (1 - 1 / exp 1) * OPT_k"
proof -
  have base_bound:
    "f (greedy_set k) \<ge> (1 - (1 - 1 / real k) ^ k) * OPT_k"
    using greedy_sequence_bound[OF k_pos k_le_V] .

  have k_ge1: "k \<ge> 1"
    using k_pos by simp

  have coeff_bound:
    "1 - (1 - 1 / real k) ^ k \<ge> 1 - 1 / exp 1"
    using coeff_ge_1_minus_inv_exp[OF k_ge1] .

  have nonneg: "0 \<le> OPT_k"
    by (rule OPT_k_nonneg)

  have coeff_mono:
    "(1 - (1 - 1 / real k) ^ k) * OPT_k
      \<ge> (1 - 1 / exp 1) * OPT_k"
    using coeff_bound nonneg
    by (rule mult_right_mono)

  from base_bound coeff_mono
  have "f (greedy_set k) \<ge> (1 - 1 / exp 1) * OPT_k"
    by (meson order_trans)
  thus ?thesis .
qed

subsection \<open>Corollaries\<close>

text \<open>
  Define the approximation ratio of the greedy algorithm for a given \<open>k\<close>
  (with the convention that the ratio is \<open>1\<close> when \<open>OPT_k = 0\<close>), and show
  that it is always at least \<open>1 - 1/exp 1\<close>.
\<close>
definition approx_ratio :: "nat \<Rightarrow> real" where
  "approx_ratio \<equiv>
     (\<lambda>k. if OPT_k = 0 then 1 else f (greedy_set k) / OPT_k)"

corollary approx_ratio_ge_1_minus_inv_exp:
  assumes "k > 0" "k \<le> card V"
  shows   "approx_ratio k \<ge> 1 - 1 / exp 1"
proof (cases "OPT_k = 0")
  case True
  then show ?thesis
    unfolding approx_ratio_def
    by simp
next
  case False
  then have OPT_pos: "OPT_k > 0"
    using OPT_k_nonneg by auto

  have main: "f (greedy_set k) \<ge> (1 - 1 / exp 1) * OPT_k"
    using greedy_approximation[OF assms] .

  show ?thesis
    unfolding approx_ratio_def
    using main False OPT_pos
    by (simp add: field_simps)
qed

end

end
