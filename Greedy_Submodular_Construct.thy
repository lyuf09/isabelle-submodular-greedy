theory Greedy_Submodular_Construct
  imports Submodular_Base
begin

section \<open>Greedy construction\<close>

text \<open>
  This theory sets up the greedy construction for monotone submodular
  maximization under a cardinality constraint. We fix a finite ground set
  \<open>V\<close>, a budget \<open>k\<close>, and a non-negative monotone submodular function
  \<open>f\<close> over subsets of \<open>V\<close>. The greedy sequence starts from the empty set
  and repeatedly adds an element with the largest marginal gain
  (ties broken arbitrarily).
\<close>

text \<open>
  Locale \<open>Greedy_Setup\<close> encapsulates this standard setting. All subsequent
  definitions and lemmas are expressed relative to a fixed ground set \<open>V\<close>,
  budget \<open>k\<close>, and set function \<open>f\<close> satisfying the usual assumptions
  (finiteness, non-negativity, monotonicity, and submodularity).
\<close>

subsection \<open>Preliminaries on finite maximizers\<close>

text \<open>Finite arg-max via the standard predicate is_arg_max.\<close>

lemma finite_is_arg_max_in:
  fixes g :: "'a \<Rightarrow> 'b::linorder"
  assumes fin: "finite A" and ne: "A \<noteq> {}"
  shows "\<exists>x\<in>A. is_arg_max g (\<lambda>x. x \<in> A) x"
proof -
  have img_fin: "finite (g ` A)"
    using fin by simp
  have img_ne: "g ` A \<noteq> {}"
    using ne by auto

  let ?M = "Max (g ` A)"
  have M_in: "?M \<in> g ` A"
    using Max_in[OF img_fin img_ne] .
  then obtain x where xA: "x \<in> A" and gx: "g x = ?M"
    by auto

    have no_better: "\<not> (\<exists>y. y \<in> A \<and> g y > g x)"
    proof
      assume ex: "\<exists>y. y \<in> A \<and> g y > g x"
      then obtain y where yA: "y \<in> A" and gy: "g y > g x" by auto

      have "g y \<le> Max (g ` A)"
        using Max_ge_iff[OF img_fin img_ne] yA by auto
      hence gy_le_gx: "g y \<le> g x"
        by (simp add: gx)

      have gx_lt_gy: "g x < g y" using gy by simp
      show False
        using gx_lt_gy gy_le_gx by (meson less_le_not_le)
    qed

  have "is_arg_max g (\<lambda>z. z \<in> A) x"
    unfolding is_arg_max_def
    using xA no_better by auto
  thus ?thesis
    using xA by blast
qed

lemma is_arg_maxD_le:
  fixes g :: "'a \<Rightarrow> 'b::linorder"
  assumes H: "is_arg_max g (\<lambda>x. x \<in> A) x"
      and yA: "y \<in> A"
  shows "g y \<le> g x"
proof -
  from H have no_better: "\<not> (\<exists>z. z \<in> A \<and> g z > g x)"
    unfolding is_arg_max_def by auto
  hence "\<not> (g y > g x)"
    using yA by blast
  thus ?thesis
    by (simp add: not_less)
qed

text \<open>
  Abstract setup for the greedy algorithm:
  \<midarrow> finite ground set \<open>V\<close>
  \<midarrow> budget \<open>k\<close>
  \<midarrow> non-negative, monotone, submodular function \<open>f\<close> with \<open>f {} = 0\<close>.

  This theory focuses on the greedy construction and basic structural
  properties (subset relations, cardinality bounds, and a sequence view),
  without yet proving any approximation guarantees.
\<close>

locale Greedy_Setup = Submodular_Setup V k f
  for V :: "'a set" and k :: nat and f :: "'a set \<Rightarrow> real"
begin

text \<open>
  Arg-max of the marginal gain over a finite non-empty candidate set \<open>A\<close>
  at a given state \<open>S\<close>. The choice operator \<open>SOME\<close> is justified by the
  finite arg-max lemma above.
\<close>
definition argmax_gain :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a" where
  "argmax_gain S A =
     (SOME x. x \<in> A \<and> is_arg_max (gain S) (\<lambda>y. y \<in> A) x)"

text \<open>Existence of a maximizer ensures that \<open>argmax_gain\<close> is well-defined.\<close>
lemma argmax_gain_exists:
  assumes fin: "finite A" and ne: "A \<noteq> {}"
  shows "\<exists>x\<in>A. is_arg_max (gain S) (\<lambda>y. y \<in> A) x"
  using fin ne
  by (rule finite_is_arg_max_in[of A "gain S"])

text \<open>
  Basic properties: the chosen element lies in \<open>A\<close>, and its gain dominates
  all other candidates in \<open>A\<close>.
\<close>
lemma argmax_gain_in:
  assumes fin: "finite A" and ne: "A \<noteq> {}"
  shows
    "argmax_gain S A \<in> A"
    "\<forall>y\<in>A. gain S y \<le> gain S (argmax_gain S A)"
proof -
  from argmax_gain_exists[OF fin ne]
  obtain x where xA: "x \<in> A"
    and xarg: "is_arg_max (gain S) (\<lambda>y. y \<in> A) x"
    by blast

  have max: "\<forall>y\<in>A. gain S y \<le> gain S x"
  proof
    fix y assume yA: "y \<in> A"
    show "gain S y \<le> gain S x"
      using is_arg_maxD_le[OF xarg yA] .
  qed

  have ex: "\<exists>x. x \<in> A \<and> is_arg_max (gain S) (\<lambda>y. y \<in> A) x"
    using xA xarg by blast

  have chosen:
    "argmax_gain S A \<in> A \<and>
     is_arg_max (gain S) (\<lambda>y. y \<in> A) (argmax_gain S A)"
    unfolding argmax_gain_def
    using someI_ex[OF ex] by blast

  show "argmax_gain S A \<in> A"
    using chosen by blast

  have "\<forall>y\<in>A. gain S y \<le> gain S (argmax_gain S A)"
  proof
    fix y assume yA: "y \<in> A"
    from chosen have arg:
      "is_arg_max (gain S) (\<lambda>y. y \<in> A) (argmax_gain S A)"
      by blast
    show "gain S y \<le> gain S (argmax_gain S A)"
      using is_arg_maxD_le[OF arg yA] .
  qed
  thus "\<forall>y\<in>A. gain S y \<le> gain S (argmax_gain S A)" .
qed


lemma argmax_gain_mem:
  assumes fin: "finite A" and ne: "A \<noteq> {}"
  shows "argmax_gain S A \<in> A"
proof -
  have ex: "\<exists>x. x \<in> A \<and> is_arg_max (gain S) (\<lambda>y. y \<in> A) x"
    using argmax_gain_exists[OF fin ne] by blast
  show ?thesis
    unfolding argmax_gain_def
    using someI_ex[OF ex] by blast
qed

lemma argmax_gain_max:
  assumes fin: "finite A" and ne: "A \<noteq> {}"
  shows "\<forall>y\<in>A. gain S y \<le> gain S (argmax_gain S A)"
proof
  fix y assume yA: "y \<in> A"
  have ex: "\<exists>x. x \<in> A \<and> is_arg_max (gain S) (\<lambda>z. z \<in> A) x"
    using argmax_gain_exists[OF fin ne] by blast
  have chosen:
    "argmax_gain S A \<in> A \<and> is_arg_max (gain S) (\<lambda>z. z \<in> A) (argmax_gain S A)"
    unfolding argmax_gain_def
    using someI_ex[OF ex] by blast
  then show "gain S y \<le> gain S (argmax_gain S A)"
    using is_arg_maxD_le[of "gain S" A "argmax_gain S A" y] yA by blast
qed


text \<open>
  Greedy construction: start from \<open>{}\<close> and, as long as there are remaining
  elements, add one with maximum marginal gain.
\<close>
primrec greedy_set :: "nat \<Rightarrow> 'a set" where
  "greedy_set 0 = {}"
| "greedy_set (Suc i) =
     (let S = greedy_set i in
      if V - S = {} then S else S \<union> {argmax_gain S (V - S)})"


text \<open>Greedy sets are always subsets of the ground set \<open>V\<close>.\<close>
lemma greedy_subset_V: "greedy_set i \<subseteq> V"
proof (induction i)
  case 0
  show ?case by simp
next
  case (Suc i)
  have IH: "greedy_set i \<subseteq> V" by fact
  show ?case
  proof (cases "V - greedy_set i = {}")
    case True
    have "greedy_set (Suc i) = greedy_set i"
      using True by (simp add: Let_def)
    thus ?thesis
      using IH by simp

  next
    case False
    have finA: "finite (V - greedy_set i)"
      using finite_V by simp
    from argmax_gain_in(1)[OF finA False]
    have inA: "argmax_gain (greedy_set i) (V - greedy_set i)
               \<in> V - greedy_set i" .
    hence inV: "argmax_gain (greedy_set i) (V - greedy_set i) \<in> V"
      by simp

    from IH inV
    have "greedy_set i \<union> {argmax_gain (greedy_set i) (V - greedy_set i)} \<subseteq> V"
      by auto
    with False show ?thesis
      by (simp add: Let_def)
  qed
qed


text \<open>If a genuinely new element is inserted, the cardinality increases by one.\<close>
lemma greedy_card_step:
  assumes ne: "V - greedy_set i \<noteq> {}"
  shows   "card (greedy_set (Suc i)) = card (greedy_set i) + 1"
proof -
  let ?S = "greedy_set i"
  let ?A = "V - ?S"
  let ?x = "argmax_gain ?S ?A"

  have finS: "finite ?S"
    using greedy_subset_V finite_V
    by (meson finite_subset)

  have finA: "finite ?A"
    using finite_V by simp

  from argmax_gain_in(1)[OF finA ne]
  have x_in_A: "?x \<in> ?A" .
  hence x_notin_S: "?x \<notin> ?S"
    by simp

  have suc_def:
    "greedy_set (Suc i) =
       (let S = ?S in
        if V - S = {} then S else S \<union> {argmax_gain S (V - S)})"
    by simp

  from ne have "greedy_set (Suc i) = ?S \<union> {?x}"
    unfolding suc_def by (simp add: Let_def)
  hence "greedy_set (Suc i) = insert ?x ?S"
    by simp

  thus ?thesis
    using finS x_notin_S by simp
qed

text \<open>If the remainder is empty, the greedy set stays unchanged.\<close>
lemma greedy_card_idle:
  assumes "V - greedy_set i = {}"
  shows   "card (greedy_set (Suc i)) = card (greedy_set i)"
  using assms by (simp add: Let_def)

text \<open>
  State transition: when the remainder is non-empty, \<open>Sᵢ\<close> evolves by adding
  the arg-max element.
\<close>
lemma state_transition_nonempty:
  assumes "0 < i" and "V - greedy_set (i - 1) \<noteq> {}"
  shows   "greedy_set i =
           greedy_set (i - 1)
           \<union> {argmax_gain (greedy_set (i - 1)) (V - greedy_set (i - 1))}"
proof -
  obtain j where ij: "i = Suc j"
    using assms(1) by (cases i) auto

  from assms(2) ij have rem_ne: "V - greedy_set j \<noteq> {}"
    by simp

  have def_suc:
    "greedy_set (Suc j) =
       (let S = greedy_set j in
        if V - S = {} then S else S \<union> {argmax_gain S (V - S)})"
    by simp

  from rem_ne have
    "greedy_set (Suc j) =
       greedy_set j \<union> {argmax_gain (greedy_set j) (V - greedy_set j)}"
    by (simp add: def_suc Let_def)

  with ij show ?thesis
    by simp
qed


text \<open>At most one new element is added in each greedy step.\<close>
lemma card_greedy_le_i: "card (greedy_set i) \<le> i"
proof (induction i)
  case 0
  show ?case by simp
next
  case (Suc i)
  show ?case
  proof (cases "V - greedy_set i = {}")
    case True
    have "card (greedy_set (Suc i)) = card (greedy_set i)"
      using True by (rule greedy_card_idle)
    with Suc.IH show ?thesis by simp
  next
    case False
    have "card (greedy_set (Suc i)) = card (greedy_set i) + 1"
      using False by (rule greedy_card_step)
    with Suc.IH show ?thesis by simp
  qed
qed

text \<open>If \<open>i \<le> k\<close> then \<open>card (greedy_set i) \<le> k\<close> (used later in the gap bound).\<close>
lemma card_greedy_le_k:
  assumes "i \<le> k"
  shows   "card (greedy_set i) \<le> k"
  using card_greedy_le_i assms by (meson le_trans)

text \<open>
  If \<open>card (greedy_set t) < card V\<close>, then the remainder \<open>V - greedy_set t\<close>
  is non-empty.
\<close>
lemma remainder_nonempty_if_card_ltV:
  assumes "card (greedy_set t) < card V"
  shows   "V - greedy_set t \<noteq> {}"
proof
  assume "V - greedy_set t = {}"
  then have vsub: "V \<subseteq> greedy_set t" by auto
  have ssub: "greedy_set t \<subseteq> V" by (rule greedy_subset_V)
  from ssub vsub have "greedy_set t = V" by (rule subset_antisym)
  with assms show False by simp
qed

text \<open>
  Under \<open>k \<le> card V\<close>, the greedy transition up to step \<open>k\<close> always adds a new
  element.
\<close>
 lemma state_transition_upto_k:
  assumes "0 < i" "i \<le> k" "k \<le> card V"
  shows   "greedy_set i =
           greedy_set (i - 1)
           \<union> {argmax_gain (greedy_set (i - 1)) (V - greedy_set (i - 1))}"
proof -
  have "card (greedy_set (i - 1)) \<le> i - 1"
    using card_greedy_le_i by simp
  also have "... < k"
    using assms(1,2) by simp
  also have "... \<le> card V"
    using assms(3) by simp
  finally have ltV: "card (greedy_set (i - 1)) < card V" .

  have rem_ne: "V - greedy_set (i - 1) \<noteq> {}"
    using remainder_nonempty_if_card_ltV[OF ltV] .

  show ?thesis
    by (rule state_transition_nonempty[OF assms(1) rem_ne])
qed

text \<open>Intermediate greedy states as a list \<open>[S₀,\<dots>,Sₙ]\<close>.\<close>
definition greedy_sequence :: "nat \<Rightarrow> 'a set list" where
  "greedy_sequence n = map greedy_set [0..<Suc n]"

text \<open>Indexing lemma for the sequence representation.\<close>
lemma greedy_sequence_nth[simp]:
  assumes "i \<le> n"
  shows   "greedy_sequence n ! i = greedy_set i"
proof -
  have i_lt: "i < Suc n" using assms by simp
  have "(map greedy_set [0..<Suc n]) ! i = greedy_set ([0..<Suc n] ! i)"
    using i_lt by (simp only: nth_map length_upt)
  also have "... = greedy_set i"
    using i_lt by (simp only: nth_upt add_0_left)
  finally show ?thesis
    by (simp only: greedy_sequence_def)
qed

text \<open>Every greedy state is finite.\<close>
lemma greedy_set_finite [simp]: "finite (greedy_set i)"
  using greedy_subset_V finite_V by (meson finite_subset)

text \<open>One-step monotonicity: \<open>Sᵢ \<subseteq> Sᵢ₊₁\<close>.\<close>
lemma greedy_mono_Suc: "greedy_set i \<subseteq> greedy_set (Suc i)"
proof (cases "V - greedy_set i = {}")
  case True
  then show ?thesis by (simp add: Let_def)
next
  case False
  then show ?thesis by (auto simp: Let_def)
qed

text \<open>Chain monotonicity: if \<open>i \<le> j\<close> then \<open>Sᵢ \<subseteq> Sⱼ\<close>.\<close>
lemma greedy_chain_mono:
  assumes "i \<le> j"
  shows   "greedy_set i \<subseteq> greedy_set j"
using assms
proof (induction j arbitrary: i)
  case 0
  then show ?case
    by simp
next
  case (Suc j i)
  show ?case
  proof (cases "i \<le> j")
    case True
    with Suc.IH have "greedy_set i \<subseteq> greedy_set j" .
    also have "... \<subseteq> greedy_set (Suc j)"
      by (rule greedy_mono_Suc)
    finally show ?thesis .
  next
    case False
    hence "i = Suc j" using Suc.prems by simp
    thus ?thesis by simp
  qed
qed

text \<open>Cardinality is non-decreasing along the greedy sequence.\<close>
lemma greedy_card_mono:
  "i \<le> j \<Longrightarrow> card (greedy_set i) \<le> card (greedy_set j)"
  by (meson greedy_chain_mono greedy_set_finite finite_subset card_mono)

text \<open>
  A compact bound in one line: \<open>card Sᵢ \<le> min i (card V)\<close> for all \<open>i\<close>.
\<close>
lemma greedy_card_min:
  "card (greedy_set i) \<le> min i (card V)"
proof -
  have A1: "card (greedy_set i) \<le> i"
    by (rule card_greedy_le_i)
  have A2: "card (greedy_set i) \<le> card V"
  proof -
    have fin: "finite V" using finite_V .
    have sub: "greedy_set i \<subseteq> V" by (rule greedy_subset_V)
    from fin sub show ?thesis by (rule card_mono)
  qed
  show ?thesis
  proof (cases "i \<le> card V")
    case True
    then show ?thesis using A1 by (simp add: min_def)
  next
    case False
    then show ?thesis using A2 by (simp add: min_def)
  qed
qed

text \<open>Length and endpoints of the intermediate sequence.\<close>
lemma greedy_sequence_length [simp]:
  "length (greedy_sequence n) = Suc n"
  by (simp add: greedy_sequence_def)

lemma greedy_sequence_0 [simp]:
  "greedy_sequence n ! 0 = {}"
  using greedy_sequence_nth[of 0 n] by simp

lemma greedy_sequence_last [simp]:
  "greedy_sequence n ! n = greedy_set n"
  using greedy_sequence_nth by simp

text \<open>
  At a non-empty remainder, the chosen element is new and lies in \<open>V - S\<close>.
\<close>
lemma chosen_in_remainder_nonempty:
  assumes rem_ne: "V - greedy_set i \<noteq> {}"
  defines x_def:  "x \<equiv> argmax_gain (greedy_set i) (V - greedy_set i)"
  shows   "x \<in> V - greedy_set i" "x \<notin> greedy_set i"
proof -
  have finA: "finite (V - greedy_set i)"
    using finite_V by simp
  have xinA:
    "argmax_gain (greedy_set i) (V - greedy_set i) \<in> V - greedy_set i"
    by (rule argmax_gain_in(1)[OF finA rem_ne])
  show "x \<in> V - greedy_set i"
    unfolding x_def by (rule xinA)
  then show "x \<notin> greedy_set i" by simp
qed

text \<open>
  Increment shape at a non-empty step: \<open>Sᵢ₊₁\<close> is obtained by inserting
  the arg-max element into \<open>Sᵢ\<close>. This is often useful in counting arguments.
\<close>
lemma greedy_increment_nonempty[simp]:
  assumes "V - greedy_set i \<noteq> {}"
  shows   "greedy_set (Suc i) =
           insert (argmax_gain (greedy_set i) (V - greedy_set i)) (greedy_set i)"
proof -
  have def:
    "greedy_set (Suc i) =
       (let S = greedy_set i in
        if V - S = {} then S else S \<union> {argmax_gain S (V - S)})"
    by simp
  from assms show ?thesis
    unfolding def
    by (simp add: Let_def)
qed

text \<open>
  One-step update of the objective value along the greedy sequence.
\<close>
lemma greedy_step_f_eq:
  assumes "V - greedy_set i \<noteq> {}"
  shows
    "f (greedy_set (Suc i)) =
       f (greedy_set i) +
       gain (greedy_set i)
         (argmax_gain (greedy_set i) (V - greedy_set i))"
proof -
  let ?S = "greedy_set i"
  let ?x = "argmax_gain ?S (V - ?S)"

  have gs_Suc:
    "greedy_set (Suc i) =
       insert (argmax_gain (greedy_set i) (V - greedy_set i)) (greedy_set i)"
    using assms by (rule greedy_increment_nonempty)

  hence "greedy_set (Suc i) = ?S \<union> {?x}"
    by simp

  hence "f (greedy_set (Suc i)) = f (?S \<union> {?x})"
    by simp
  also have "\<dots> = f ?S + gain ?S ?x"
    by (simp add: gain_def)
  finally show ?thesis
    by simp
qed

end
end
