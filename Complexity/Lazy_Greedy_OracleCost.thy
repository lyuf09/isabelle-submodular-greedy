theory Lazy_Greedy_OracleCost
  imports
    "../Algorithms/Lazy_Greedy_Stateful"
    "../Core/Oracle_Cost"
begin

text \<open>
This theory provides a lightweight oracle-cost bound for the inner
lazy selection procedure, in terms of the number of times we "tighten"
an upper bound (i.e., recompute gain S x for a chosen candidate x).

We model:
  - tighten-steps: number of iterations taking the "else" branch
  - gain-evals:   number of gain computations performed by the loop
                  (one per iteration with positive fuel)

The key bound is:
  tighten_steps \<le> card (untight S A ub)
and hence
  gain_evals \<le> card (untight S A ub) + 1
Moreover, gain_evals is always \<le> fuel, so with fuel = card A we get
  gain_evals \<le> card A.
\<close>

context Submodular_Func
begin

fun lazy_tighten_steps_fuel :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> nat" where
  "lazy_tighten_steps_fuel 0 S A ub = 0"
| "lazy_tighten_steps_fuel (Suc n) S A ub =
     (let x = pick_ub_some A ub in
        if ub x = gain S x
        then 0
        else Suc (lazy_tighten_steps_fuel n S A (tighten S ub x)))"

fun lazy_gain_evals_fuel :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> nat" where
  "lazy_gain_evals_fuel 0 S A ub = 0"
| "lazy_gain_evals_fuel (Suc n) S A ub =
     (let x = pick_ub_some A ub in
        if ub x = gain S x
        then 1
        else Suc (lazy_gain_evals_fuel n S A (tighten S ub x)))"

lemma lazy_gain_evals_fuel_le_fuel:
  "lazy_gain_evals_fuel n S A ub \<le> n"
proof (induction n arbitrary: ub)
  case 0
  then show ?case by simp
next
  case (Suc n ub)
  let ?x = "pick_ub_some A ub"
  show ?case
  proof (cases "ub ?x = gain S ?x")
    case True
    then show ?thesis by (simp add: Let_def)
  next
    case False
    have "lazy_gain_evals_fuel n S A (tighten S ub ?x) \<le> n"
      using Suc.IH by simp
    then show ?thesis
      using False by (simp add: Let_def)
  qed
qed

lemma lazy_tighten_steps_fuel_le_card_untightI:
  assumes finA: "finite A" and neA: "A \<noteq> {}"
  shows "ub_valid S A ub \<Longrightarrow>
         lazy_tighten_steps_fuel n S A ub \<le> card (untight S A ub)"
  using assms
proof (induction n arbitrary: ub)
  case 0
  then show ?case by simp
next
  case (Suc n ub)
  assume ubv: "ub_valid S A ub"

  define x where "x = pick_ub_some A ub"
  have xA: "x \<in> A"
    using pick_ub_some_mem[OF finA neA] by (simp add: x_def)

  show ?case
  proof (cases "ub x = gain S x")
    case True
    then show ?thesis
      by (simp add: Let_def x_def[symmetric] True)
  next
    case False
    have ubv_ball: "\<forall>z\<in>A. gain S z \<le> ub z"
      using ubv unfolding ub_valid_def by simp
    have le_gx: "gain S x \<le> ub x"
      using ubv_ball xA by (rule bspec)

    have gt: "ub x > gain S x"
      using le_gx False by (meson eq_iff not_le order_le_less)
    have xU: "x \<in> untight S A ub"
      using xA gt unfolding untight_def by auto

    have finU: "finite (untight S A ub)"
      using finite_untight[OF finA] .
    have Ueq: "untight S A (tighten S ub x) = untight S A ub - {x}"
      using xA gt by (simp add: untight_tighten)
    have card_drop:
      "card (untight S A (tighten S ub x)) = card (untight S A ub) - 1"
      using finU xU by (simp add: Ueq card_Diff_singleton)

    have ubv': "ub_valid S A (tighten S ub x)"
      using ub_valid_tighten[OF ubv] .
    have IH:
      "lazy_tighten_steps_fuel n S A (tighten S ub x)
       \<le> card (untight S A (tighten S ub x))"
      using Suc.IH[of "tighten S ub x"] finA neA ubv'
      by blast

    have IH': "lazy_tighten_steps_fuel n S A (tighten S ub x)
               \<le> card (untight S A ub) - 1"
      using IH by (simp add: card_drop)

        let ?m = "card (untight S A ub)"
        let ?t = "lazy_tighten_steps_fuel n S A (tighten S ub x)"

        have Une: "untight S A ub \<noteq> {}"
          using xU by auto
        have mpos: "0 < card (untight S A ub)"
          using finU Une by (simp add: card_gt_0_iff)

        have pred_lt: "?m - 1 < ?m"
          using mpos by (cases ?m) auto

        have t_lt: "?t < ?m"
          using IH' pred_lt by (rule le_less_trans)

        have step: "Suc ?t \<le> ?m"
          using t_lt by (simp add: Suc_le_eq)

    then show ?thesis
      by (simp add: Let_def x_def[symmetric] False)
  qed
qed

lemma lazy_tighten_steps_fuel_le_card_untight:
  assumes finA: "finite A" and neA: "A \<noteq> {}" and ubv: "ub_valid S A ub"
  shows "lazy_tighten_steps_fuel n S A ub \<le> card (untight S A ub)"
  using lazy_tighten_steps_fuel_le_card_untightI[OF finA neA] ubv .

lemma lazy_gain_evals_fuel_le_card_untight_plus1I:
  assumes finA: "finite A" and neA: "A \<noteq> {}"
  shows "ub_valid S A ub \<Longrightarrow>
         lazy_gain_evals_fuel n S A ub \<le> card (untight S A ub) + 1"
  using assms
proof (induction n arbitrary: ub)
  case 0
  then show ?case by simp
next
  case (Suc n ub)
  assume ubv: "ub_valid S A ub"

  define x where "x = pick_ub_some A ub"
  have xA: "x \<in> A"
    using pick_ub_some_mem[OF finA neA] by (simp add: x_def)

  show ?case
  proof (cases "ub x = gain S x")
    case True
    then show ?thesis
      by (simp add: Let_def x_def[symmetric])
  next
    case False
    have ubv_ball: "\<forall>z\<in>A. gain S z \<le> ub z"
      using ubv unfolding ub_valid_def by simp
    have le_gx: "gain S x \<le> ub x"
      using ubv_ball xA by (rule bspec)

    have gt: "ub x > gain S x"
      using le_gx False by (meson eq_iff not_le order_le_less)
    have xU: "x \<in> untight S A ub"
      using xA gt unfolding untight_def by auto

    have finU: "finite (untight S A ub)"
      using finite_untight[OF finA] .

    have Ueq: "untight S A (tighten S ub x) = untight S A ub - {x}"
      using xA gt by (simp add: untight_tighten)

    have card_drop:
      "card (untight S A (tighten S ub x)) = card (untight S A ub) - 1"
      using finU xU by (simp add: Ueq card_Diff_singleton)

    have ubv': "ub_valid S A (tighten S ub x)"
      using ub_valid_tighten[OF ubv] .

    have IH:
      "lazy_gain_evals_fuel n S A (tighten S ub x)
       \<le> card (untight S A (tighten S ub x)) + 1"
      using Suc.IH[of "tighten S ub x"] ubv' finA neA
      by blast

    have Une: "untight S A ub \<noteq> {}"
      using xU by auto
    have cardU_pos: "0 < card (untight S A ub)"
      using finU Une by (simp add: card_gt_0_iff)

    have IH0:
      "lazy_gain_evals_fuel n S A (tighten S ub x) \<le> card (untight S A ub)"
    proof -
      have "lazy_gain_evals_fuel n S A (tighten S ub x)
            \<le> (card (untight S A ub) - 1) + 1"
        using IH by (simp add: card_drop)
      also have "(card (untight S A ub) - 1) + 1 = card (untight S A ub)"
        using cardU_pos by (cases "card (untight S A ub)") auto
      finally show ?thesis .
    qed

    have step:
      "Suc (lazy_gain_evals_fuel n S A (tighten S ub x))
       \<le> card (untight S A ub) + 1"
    proof -
      have "Suc (lazy_gain_evals_fuel n S A (tighten S ub x))
            \<le> Suc (card (untight S A ub))"
        using IH0 by simp
      then show ?thesis by simp
    qed

    then show ?thesis
      using False by (simp add: Let_def x_def[symmetric])
  qed
qed

lemma lazy_gain_evals_fuel_le_card_untight_plus1:
  assumes finA: "finite A" and neA: "A \<noteq> {}" and ubv: "ub_valid S A ub"
  shows "lazy_gain_evals_fuel n S A ub \<le> card (untight S A ub) + 1"
  using lazy_gain_evals_fuel_le_card_untight_plus1I[OF finA neA] ubv .

definition lazy_select_gain_evals :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> nat" where
  "lazy_select_gain_evals S A ub = lazy_gain_evals_fuel (card A) S A ub"

definition lazy_select_oracle_calls :: "'a set \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> nat" where
  "lazy_select_oracle_calls S A ub = gain_call_cost * lazy_select_gain_evals S A ub"

lemma lazy_select_gain_evals_le_cardA:
  "lazy_select_gain_evals S A ub \<le> card A"
  unfolding lazy_select_gain_evals_def
  using lazy_gain_evals_fuel_le_fuel[of "card A" S A ub] by simp

lemma lazy_select_gain_evals_le_card_untight_plus1:
  assumes finA: "finite A" and neA: "A \<noteq> {}" and ubv: "ub_valid S A ub"
  shows "lazy_select_gain_evals S A ub \<le> card (untight S A ub) + 1"
  unfolding lazy_select_gain_evals_def
  using lazy_gain_evals_fuel_le_card_untight_plus1[OF finA neA ubv] .

lemma lazy_select_oracle_calls_le_cardA:
  "lazy_select_oracle_calls S A ub \<le> gain_call_cost * card A"
  unfolding lazy_select_oracle_calls_def
  using mult_left_mono[OF lazy_select_gain_evals_le_cardA] by simp

lemma lazy_select_oracle_calls_le_untight_plus1:
  assumes finA: "finite A" and neA: "A \<noteq> {}" and ubv: "ub_valid S A ub"
  shows "lazy_select_oracle_calls S A ub
       \<le> gain_call_cost * (card (untight S A ub) + 1)"
  unfolding lazy_select_oracle_calls_def
  using mult_left_mono[OF lazy_select_gain_evals_le_card_untight_plus1[OF finA neA ubv]] by simp

end

end