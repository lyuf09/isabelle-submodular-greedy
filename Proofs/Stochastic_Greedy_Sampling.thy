theory Stochastic_Greedy_Sampling
  imports "../Algorithms/Stochastic_Greedy"
begin

section \<open>Sampling parameters for the StochasticGreedy analysis\<close>

text \<open>
This theory records the paper-facing parameters used in the later approximation
proof. The probabilistic lemmas themselves are deferred to the next stage; for
the first week we only freeze the notation and the target statements.

The intended parameter story is:
  • s is the per-round sample size;
  • alpha_stoch s packages the exponential hit-probability term;
  • sample_size_eps eps is the standard paper-facing choice used to derive
    a (1 - 1 / exp 1 - eps)-style approximation bound.
\<close>

context Cardinality_Constraint
begin

definition alpha_stoch :: "nat \<Rightarrow> real" where
  "alpha_stoch s = 1 - exp (- (real s * real k / real (card V)))"

definition sample_size_eps :: "real \<Rightarrow> nat" where
  "sample_size_eps eps =
     nat \<lceil>(real (card V) / real k) * ln (1 / eps)\<rceil>"

text \<open>
Planned theorem line for later files:

  1. A hit-probability lower bound for sampled candidates intersecting the
     residual optimal set.
  2. A linearised bound of the form
       hit_prob \<ge> alpha_stoch s * |OPT - S| / k.
  3. Substitution of sample_size_eps eps to obtain
       alpha_stoch (sample_size_eps eps) \<ge> 1 - eps.

The current file only fixes the notation so that later approximation and
complexity theories can share the same parameter layer.
\<close>

lemma alpha_stoch_le_1:
  "alpha_stoch s \<le> 1"
proof -
  have "0 < exp (- (real s * real k / real (card V)))"
    by simp
  then show ?thesis
    unfolding alpha_stoch_def by linarith
qed

lemma sample_size_eps_nonneg:
  "0 \<le> real (sample_size_eps eps)"
  by simp

end

end