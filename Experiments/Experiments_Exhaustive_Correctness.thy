theory Experiments_Exhaustive_Correctness
  imports Experiments_Exhaustive "HOL-Library.Sublist"
begin

(* -------------------------------------------------------------------------- *)
(* Small helper: foldl that always chooses either the accumulator or current. *)
(* -------------------------------------------------------------------------- *)

lemma foldl_choose_in_insert:
  assumes choose: "\<And>b a. step b a = b \<or> step b a = a"
  shows "foldl step init xs \<in> insert init (set xs)"
  using choose
proof (induction xs arbitrary: init)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  have IH: "\<And>init. foldl step init xs \<in> insert init (set xs)"
   using Cons.IH[OF Cons.prems] by simp
  have step_mem: "step init a \<in> {init, a}"
    using Cons.prems by auto

  have "foldl step (step init a) xs \<in> insert (step init a) (set xs)"
    using IH by simp
  moreover have "insert (step init a) (set xs) \<subseteq> insert init (set (a # xs))"
    using step_mem by auto
  ultimately show ?case
    by auto
qed

lemma foldl_choose_mem:
  assumes choose: "\<And>b a. step b a = b \<or> step b a = a"
  shows "foldl step init xs = init \<or> foldl step init xs \<in> set xs"
  using foldl_choose_in_insert[OF choose]
  by auto

lemma argmax_list_mem:
  "argmax_list f cands = [] \<or> argmax_list f cands \<in> set cands"
  unfolding argmax_list_def
  by (rule foldl_choose_mem) auto

(* -------------------------------------------------------------------------- *)
(* subseqs_upto_k: basic facts                                                *)
(* -------------------------------------------------------------------------- *)

lemma set_mono_subseq:
  assumes "subseq xs ys"
  shows "set xs <= set ys"
  using assms
  by (induction rule: list_emb.induct) auto

lemma in_subseqs_upto_kD:
  assumes "ys \<in> set (subseqs_upto_k xs k)"
  shows "length ys \<le> k" and "set ys \<subseteq> set xs"
proof -
  have len: "length ys <= k"
    using assms by (auto simp: subseqs_upto_k_def)
  have sub: "subseq ys xs"
    using assms by (auto simp: subseqs_upto_k_def)
  have setsub: "set ys <= set xs"
    using set_mono_subseq[OF sub] .
  show "length ys <= k" using len .
  show "set ys <= set xs" using setsub .
qed

(* -------------------------------------------------------------------------- *)
(* Feasibility of enum_opt_set                                                *)
(* -------------------------------------------------------------------------- *)

lemma enum_opt_set_subset:
  "enum_opt_set f xs k \<subseteq> set xs"
proof -
  let ?best = "argmax_list f (subseqs_upto_k xs k)"
  have mem: "?best = [] \<or> ?best \<in> set (subseqs_upto_k xs k)"
    using argmax_list_mem[of f "subseqs_upto_k xs k"] by simp
  show ?thesis
  proof (cases "?best = []")
    case True
    then show ?thesis by (simp add: enum_opt_set_def)
  next
    case False
    then have inC: "?best \<in> set (subseqs_upto_k xs k)"
      using mem by auto
    then have "set ?best \<subseteq> set xs"
      using in_subseqs_upto_kD(2) by blast
    then show ?thesis
      by (simp add: enum_opt_set_def)
  qed
qed

lemma enum_opt_set_card_le_k:
  "card (enum_opt_set f xs k) \<le> k"
proof -
  let ?best = "argmax_list f (subseqs_upto_k xs k)"
  have mem: "?best = [] \<or> ?best \<in> set (subseqs_upto_k xs k)"
    using argmax_list_mem[of f "subseqs_upto_k xs k"] by simp
  have len_le: "length ?best \<le> k"
  proof (cases "?best = []")
    case True
    then show ?thesis by simp
  next
    case False
    then have inC: "?best \<in> set (subseqs_upto_k xs k)"
      using mem by auto
    then show ?thesis
      using in_subseqs_upto_kD(1) by blast
  qed
  have "card (set ?best) \<le> length ?best"
    by (rule card_length)
  then have "card (enum_opt_set f xs k) \<le> length ?best"
    by (simp add: enum_opt_set_def)
  also have "... \<le> k"
    using len_le .
  finally show ?thesis .
qed

(* -------------------------------------------------------------------------- *)
(* Optimality over enumerated candidates                                      *)
(* -------------------------------------------------------------------------- *)

lemma foldl_step_ge_init:
  fixes val :: "'a \<Rightarrow> 'b::linorder"
  shows "val init \<le> val (foldl (\<lambda>best cand. if val best \<le> val cand then cand else best) init xs)"
proof (induction xs arbitrary: init)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  let ?step = "\<lambda>best cand. if val best \<le> val cand then cand else best"
  have step_ge: "val init \<le> val (?step init a)"
    by (simp split: if_splits)
  have IH: "val (?step init a) \<le> val (foldl ?step (?step init a) xs)"
    using Cons.IH[of "?step init a"] by simp
  have "val init \<le> val (foldl ?step (?step init a) xs)"
    using order_trans[OF step_ge IH] .
  then show ?case by simp
qed


lemma foldl_max_ge:
  fixes val :: "'a \<Rightarrow> 'b::linorder"
  shows "\<forall>y\<in>set xs. val y \<le>
        val (foldl (\<lambda>best cand. if val best \<le> val cand then cand else best) init xs)"
proof (induction xs arbitrary: init)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  let ?step  = "\<lambda>best cand. if val best \<le> val cand then cand else best"
  let ?init' = "?step init a"

  have IH: "\<forall>y\<in>set xs. val y \<le> val (foldl ?step ?init' xs)"
    using Cons.IH[of ?init'] by simp

  have init'_le: "val ?init' \<le> val (foldl ?step ?init' xs)"
    using foldl_step_ge_init[of val ?init' xs] by simp

  have a_le_init': "val a \<le> val ?init'"
  proof (cases "val init \<le> val a")
    case True
    then show ?thesis by simp
  next
    case False
    then have "val a < val init"
      by (simp add: not_le)
    then show ?thesis
      using False by simp
  qed

  have a_le_foldl: "val a \<le> val (foldl ?step ?init' xs)"
    using order_trans[OF a_le_init' init'_le] .

  show ?case
  proof
    fix y assume "y \<in> set (a # xs)"
    then consider (A) "y = a" | (X) "y \<in> set xs" by auto
    then show "val y \<le> val (foldl ?step init (a # xs))"
    proof cases
      case A
      then show ?thesis using a_le_foldl by simp
    next
      case X
      then have "val y \<le> val (foldl ?step ?init' xs)"
        using IH by auto
      then show ?thesis by simp
    qed
  qed
qed


lemma argmax_list_ge:
  fixes f :: "'a set \<Rightarrow> 'b::linorder"
  assumes cand: "cand \<in> set cands"
  shows "f (set cand) \<le> f (set (argmax_list f cands))"
proof -
  have all:
    "\<forall>y\<in>set cands.
       f (set y) \<le>
       f (set (foldl (\<lambda>best z. if f (set best) \<le> f (set z) then z else best)
                     ([]::'a list) cands))"
    by (rule foldl_max_ge[
          where val="\<lambda>ys. f (set ys)"
            and init="([]::'a list)"
            and xs=cands])

  have "f (set cand) \<le>
        f (set (foldl (\<lambda>best z. if f (set best) \<le> f (set z) then z else best)
                      ([]::'a list) cands))"
    using all cand by auto

  thus ?thesis
    by (simp add: argmax_list_def)
qed

lemma enum_opt_set_optimal_subseq:
  assumes "ys \<in> set (subseqs_upto_k xs k)"
  shows "f (set ys) \<le> f (enum_opt_set f xs k)"
  using argmax_list_ge[of ys "subseqs_upto_k xs k" f] assms
  by (simp add: enum_opt_set_def)

(* -------------------------------------------------------------------------- *)
(* Stronger: true optimality over all sets, if xs is distinct                 *)
(* -------------------------------------------------------------------------- *)

lemma filter_mem_subseqs:
  "filter P xs \<in> set (subseqs xs)"
  by simp


lemma enum_opt_set_optimal_set:
  fixes f :: "'a set \<Rightarrow> 'b::linorder"
  assumes dist: "distinct xs"
      and Ssub: "S \<subseteq> set xs"
      and Sk:   "card S \<le> k"
  shows "f S \<le> f (enum_opt_set f xs k)"
proof -
  let ?ys = "filter (%x. x \<in> S) xs"

  have set_ys: "set ?ys = S"
    using Ssub by auto

  have len_ys: "length ?ys \<le> k"
  proof -
    have d_ys: "distinct ?ys"
      using dist by simp
    have card_len: "card (set ?ys) = length ?ys"
      using d_ys by (rule distinct_card)
    have "length ?ys = card (set ?ys)"
      using card_len by simp
    also have "... = card S"
      using set_ys by simp
    finally show ?thesis
      using Sk by simp
  qed

  have ys_in: "?ys \<in> set (subseqs_upto_k xs k)"
  proof -
    have "?ys \<in> set (subseqs xs)"
      by simp
    thus ?thesis
      using len_ys by (simp add: subseqs_upto_k_def)
  qed

  have "f (set ?ys) \<le> f (enum_opt_set f xs k)"
    using enum_opt_set_optimal_subseq[OF ys_in] .
  thus ?thesis
    using set_ys by simp
qed

end