/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Certainty Equivalents and Risk Premia for a CARA Agent

A risk-averse decision maker evaluates a money lottery not by its expected payoff but by its
expected *utility*. The **certainty equivalent** is the sure amount of money that the agent would
accept in exchange for the gamble: It is the value `c` whose utility equals the gamble's expected
utility. Because a risk-averse agent dislikes spread, the certainty equivalent of a non-degenerate
lottery falls strictly below the lottery's expected value, and the shortfall — the **risk
premium** — is what the agent pays to shed the risk. This file does not prove that principle in
general; it works the whole story out on one concrete fifty-fifty bet under exponential (CARA)
utility, where every step (non-degeneracy, the strict Jensen gap, the positive premium) is an
exported theorem.

## The model

The agent has constant-absolute-risk-aversion (CARA, exponential) utility `u(x) = -exp(-α·x)` with
coefficient `α := 1 > 0`, packaged as the Econlib `ConstantAbsoluteRiskAversionUtility`. The
lottery is a bundled `FinLottery 2` — a fair coin over `Fin 2`:

* outcomes `![0, 1]` — win nothing or win one unit of money;
* probabilities `![1/2, 1/2]` — each outcome equally likely, supplied as a `FinDist (Fin 2)` via the
  `finDist%` literal builder, so the probability axioms are discharged automatically.

Its expected value is `𝔼[X] = 1/2 · 0 + 1/2 · 1 = 1/2`.

## The mathematics

CARA utility is the canonical utility that is strictly concave on all of `ℝ`, so the example is
honest: The Jensen gap is strict. Concretely, `u' (x) = α·exp(-α·x) > 0` (monotone) and
`u''(x) = -α²·exp(-α·x) < 0` everywhere, so `strictConcaveOn_of_deriv2_neg` yields strict
concavity. The lottery is non-degenerate — both outcomes carry positive probability and
have distinct values — so the strict finite-lottery API delivers the full strict story:

* a certainty equivalent exists (intermediate value theorem, via `certainty_equivalent_exists`) and
  is unique (strict monotonicity, via `certainty_equivalent_unique`), so the certainty equivalent
  is well defined;
* it is `< 𝔼[X]` (strict finite Jensen, via
  `certainty_equivalent_lt_expected_value_of_strict_concave`);
* the risk premium `𝔼[X] - c` is `> 0` (`risk_premium_pos_of_strict_concave`).

Finally the Arrow–Pratt coefficient of absolute risk aversion — the formal
`TwiceDiffUtility.absoluteRiskAversion`, i.e. `A(x) = -u''(x)/u'(x)` with the derivatives supplied
by the `TwiceDiffUtility` structure — is the constant `α`, the defining feature of the CARA family.

## Main definitions and theorems

* `agent` — the CARA agent with `α = 1`.
* `lottery` — the fair fifty-fifty money lottery over `Fin 2`, bundled as a `FinLottery 2`.
* `lottery_nondegenerate` — the lottery has two distinct outcomes of positive probability.
* `u_strictMono` — the utility `u(x) = -exp(-x)` is strictly increasing.
* `u_strictConcave` — `u` is strictly concave on all of `ℝ`.
* `ce_exists` / `ce_unique` — a certainty equivalent exists and is unique.
* `expectedValue_eq` — the lottery's expected value is `1/2`.
* `ce_lt_expectedValue` — the certainty equivalent is strictly below `𝔼[X] = 1/2`.
* `riskPremium_pos` — the risk premium is strictly positive.
* `arrowPratt_eq_alpha` — the Arrow–Pratt coefficient `absoluteRiskAversion` equals `α = 1` at
  every wealth level.
-/

noncomputable section

namespace EconlibExamples.Preferences.CertaintyEquivalent

open Econlib.Preferences

/-! ## The CARA agent and the fifty-fifty lottery -/

/-- The risk-averse agent: CARA (exponential) utility with `α = 1`, i.e. `u(x) = -exp(-x)`. -/
def agent : ConstantAbsoluteRiskAversionUtility where
  α := 1
  α_pos := one_pos

/-- The fair fifty-fifty money lottery over `Fin 2`, bundled as a `FinLottery 2`: outcomes
`![0, 1]` — win nothing or win one — under the fair-coin distribution `![1/2, 1/2]`. The
probabilities are supplied through the `finDist%` literal builder, so nonnegativity and total mass
one are discharged automatically and invalid weights are inexpressible. -/
def lottery : FinLottery 2 where
  outcome := ![0, 1]
  prob := finDist% ![1 / 2, 1 / 2]

/-- The lottery is non-degenerate: Both outcomes carry positive probability and have distinct
values. This is what makes the Jensen gap strict — a sure thing has no risk premium. -/
lemma lottery_nondegenerate :
    ∃ i j, 0 < lottery.prob.pmf i ∧ 0 < lottery.prob.pmf j ∧
      lottery.outcome i ≠ lottery.outcome j :=
  ⟨0, 1, by norm_num [lottery], by norm_num [lottery], by norm_num [lottery]⟩

/-! ## Monotonicity and strict concavity of the utility -/

/-- The CARA utility `u(x) = -exp(-x)` is strictly increasing: More money is strictly better. -/
lemma u_strictMono : StrictMono agent.u :=
  agent.u_strictMono

/-- The CARA utility `u(x) = -exp(-x)` is continuous. -/
lemma u_continuous : Continuous agent.u :=
  agent.continuous_u

/-- The CARA utility is strictly concave on all of `ℝ`. CARA is the canonical utility that is
strictly concave everywhere, so the certainty-equivalent gap below is strict. We read the
strict concavity off the everywhere-negative second derivative `u''(x) = -α²·exp(-α·x) < 0`. -/
lemma u_strictConcave : StrictConcaveOn ℝ Set.univ agent.u := by
  -- The first derivative is `u'(x) = α·exp(-α·x)`, so `deriv agent.u` is this function.
  have hderiv : deriv agent.u = fun y => agent.α * Real.exp (-agent.α * y) :=
    funext fun y => (agent.hasDerivAt_u y).deriv
  refine strictConcaveOn_of_deriv2_neg convex_univ u_continuous.continuousOn ?_
  · -- The second derivative is `u''(x) = -α²·exp(-α·x)`, strictly negative everywhere.
    intro y _
    simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id_eq]
    rw [hderiv, (agent.hasDerivAt_deriv_u y).deriv]
    have hα2 : 0 < agent.α ^ 2 := pow_pos agent.α_pos 2
    have hexp : 0 < Real.exp (-agent.α * y) := Real.exp_pos _
    nlinarith [mul_pos hα2 hexp]

/-! ## Certainty equivalent: Existence, the Jensen gap, and the risk premium -/

/-- A certainty equivalent of the lottery exists. This is the intermediate-value theorem applied to
the continuous utility: Its expected utility is attained at some sure outcome `c`. -/
lemma ce_exists : ∃ c, IsCertaintyEquivalent agent.u lottery c :=
  certainty_equivalent_exists u_continuous

/-- The certainty equivalent is unique, because the utility is strictly increasing: Distinct sure
amounts have distinct utilities, and a certainty equivalent determines the utility value. Together
with `ce_exists` this makes the certainty equivalent of the lottery a well-defined number. -/
lemma ce_unique {c₁ c₂ : ℝ} (hc₁ : IsCertaintyEquivalent agent.u lottery c₁)
    (hc₂ : IsCertaintyEquivalent agent.u lottery c₂) : c₁ = c₂ :=
  certainty_equivalent_unique (u_strictMono.strictMonoOn Set.univ)
    (Set.mem_univ _) (Set.mem_univ _) hc₁ hc₂

/-- The lottery's expected value is `1/2`. -/
lemma expectedValue_eq : lottery.expectedValue = 1 / 2 := by
  simp [lottery, Fin.sum_univ_two]

/-- The certainty equivalent lies strictly below the lottery's expected value
`lottery.expectedValue` (which equals `1/2`, see `expectedValue_eq`) — the strict Jensen gap of a
risk-averse agent facing risk. Strict concavity of the CARA utility and non-degeneracy of the
lottery are both load-bearing: An affine utility or a sure thing would collapse the gap to
equality. -/
lemma ce_lt_expectedValue {c : ℝ} (hc : IsCertaintyEquivalent agent.u lottery c) :
    c < lottery.expectedValue :=
  certainty_equivalent_lt_expected_value_of_strict_concave (u_strictMono.strictMonoOn Set.univ)
    u_strictConcave (fun _ => Set.mem_univ _) (Set.mem_univ _) lottery_nondegenerate hc

/-- The risk premium `𝔼[X] - c` is strictly positive: The agent strictly prefers `𝔼[X]` for sure
over the gamble, so shedding the risk commands a positive price. -/
lemma riskPremium_pos {c : ℝ} (hc : IsCertaintyEquivalent agent.u lottery c) :
    0 < riskPremium lottery c :=
  risk_premium_pos_of_strict_concave (u_strictMono.strictMonoOn Set.univ) u_strictConcave
    (fun _ => Set.mem_univ _) (Set.mem_univ _) lottery_nondegenerate hc

/-! ## The Arrow–Pratt coefficient of absolute risk aversion -/

/-- The Arrow–Pratt measure of absolute risk aversion — the formal
`TwiceDiffUtility.absoluteRiskAversion`, i.e. `A(y) = -u''(y)/u'(y)` with `u'` and `u''` the
derivative fields of `agent.toTwiceDiffUtility` — is the constant `α = 1` at every wealth level
`y`. This constancy is exactly what defines the CARA family. -/
lemma arrowPratt_eq_alpha (y : ℝ) :
    (agent.toTwiceDiffUtility).absoluteRiskAversion y (Set.mem_univ y) = 1 :=
  agent.absoluteRiskAversion_eq_alpha y (Set.mem_univ y)

end EconlibExamples.Preferences.CertaintyEquivalent
