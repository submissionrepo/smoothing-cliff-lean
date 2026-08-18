/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Precautionary saving under prudence

*Prudence* — convexity of marginal utility, `Econlib.Preferences.Prudent` — is the canonical
condition (Kimball, 1990) under which a consumer responds to **income risk** by saving more than
under certainty. This file works the economics out as a two-period saving model, exhibiting the
mechanism that the bare `Prudent` predicate encodes.

## The model

A consumer lives two periods with wealth `w` and a unit gross return (`R = β = 1`, so the algebra
isolates prudence). In period 0 they consume `w - s` and save `s`; in period 1 they consume
`s + yᵢ`, where future income is a finite lottery `L : FinLottery n` — income realizations
`L.outcome` paired with probabilities `L.prob`. Because `L.prob` lives in `FinDist (Fin n)`, which
bundles nonnegativity and total mass one, no separate "is a distribution" hypothesis is needed:
invalid weights are inexpressible. **Lifetime utility** is the objective
`lifetimeUtility s = u(w - s) + 𝔼[u(s + ỹ)]`, maximized over the open feasible set `FeasibleSaving`
of saving levels with strictly positive consumption in both periods. The defining fact
(`hasDerivAt_lifetimeUtility`) is that the derivative of this objective is exactly the Euler
residual: `V'(s) = -u'(w - s) + 𝔼[u'(s + ỹ)] = eulerResidualRisky s`. Hence the Euler equation
`u'(w - s) = 𝔼[u'(s + ỹ)]` is the *first-order condition* of the maximization, not an assumed
relation — it is a **theorem** about maximizers (`eulerResidualRisky_eq_zero_of_isLocalMax`), and,
conversely, under concavity a stationary point is a global maximizer
(`isMaxOn_lifetimeUtility_of_euler`).

We compare two economies with the same mean income `ȳ = 𝔼[ỹ]`: one where income is the sure mean
(objective `lifetimeUtilityCertain`), one where it is the lottery.

The lottery here distributes income, not consumption: the agent takes utility of `s + L.outcome i`
and `w - s`, so `FinLottery` serves only to bundle the income distribution. The certainty-equivalent
and risk-premium lemmas of `Risk/CertaintyEquivalent.lean` are therefore not reused — this file
reimplements the relevant Jensen step directly via `ConvexOn.map_sum_le`. The structural derivative
and first-order-condition lemmas (`hasDerivAt_lifetimeUtility`, the FOC theorems,
`strictAntiOn_eulerResidualRisky_of_strictConcave`) use the weights only through `FinDist.nonneg` /
`FinDist.sum_one`; they nominally carry the `FinDist` validity even where mere weights would do.

## The mechanism

The whole comparative static rides on one inequality, and that inequality is exactly prudence.
Because the marginal utility `u'` is convex (prudence), Jensen's inequality gives

  `u'(s + 𝔼[ỹ]) ≤ 𝔼[u'(s + ỹ)]`   (`marginalUtility_mean_le_expected`).

Risk raises the expected marginal utility of saving above its certainty value. So at any saving
level the Euler residual (marginal benefit minus marginal cost) is larger under risk than under
certainty; with a strictly decreasing residual (the standard concavity/regularity condition, which
strict concavity of the lifetime objective supplies via `StrictConcaveOn.strictAntiOn_deriv`,
packaged here as `strictAntiOn_eulerResidualRisky_of_strictConcave`), the risky economy's Euler
equation is solved at a higher saving level. The bare-residual statement is
`precautionary_saving`; the version about **actual maximizers** of the two-period problem — with the
Euler equations derived as FOCs rather than assumed — is `precautionary_saving_optimal`. A prudent
consumer self-insures against income risk by saving more.

## Main definitions and theorems

* `meanIncome`, `expectedMarginalUtility` — `𝔼[ỹ]` and `𝔼[u'(s + ỹ)]`. `meanIncome` coincides with
  the lottery's expected value `∑ L.prob.pmf i * L.outcome i` (the quantity `riskPremium`
  differences against).
* `eulerResidualCertain`, `eulerResidualRisky` — marginal benefit minus marginal cost of saving,
  under sure mean income and under the lottery.
* `marginalUtility_mean_le_expected` — the precautionary inequality, Jensen for the convex `u'`.
* `precautionary_saving` — comparing two assumed Euler roots: a strictly-decreasing risky residual
  plus prudence gives `sCert ≤ sRisky`.
* `lifetimeUtility`, `lifetimeUtilityCertain` — the two-period objectives
  `u(w-s) + 𝔼[u(s+ỹ)]` and its certainty counterpart.
* `FeasibleSaving`, `FeasibleSavingCertain` — feasible-saving predicates (strictly positive
  consumption in both periods); `isOpen_feasibleSaving` / `isOpen_feasibleSavingCertain` show the
  feasible sets are open.
* `hasDerivAt_lifetimeUtility` / `deriv_lifetimeUtility` (and certainty analogues) — **the crux**:
  the derivative of the lifetime objective is the Euler residual.
* `eulerResidualRisky_eq_zero_of_isLocalMax` / `eulerResidualCertain_eq_zero_of_isLocalMax` — **FOC
  necessity**: a feasible local maximizer solves its Euler equation (derived, not assumed).
* `isMaxOn_lifetimeUtility_of_euler` / `isMaxOn_lifetimeUtilityCertain_of_euler` — **FOC
  sufficiency**: under concavity, an Euler-stationary feasible point is a global maximizer.
* `precautionary_saving_optimal` — **the comparative static for actual maximizers**: with `sCert`,
  `sRisky` local maximizers of the certainty resp. risky two-period problems, a prudent
  agent saves at least as much under risk (`sCert ≤ sRisky`). The strict antitonicity of the risky
  residual is retained as an explicit regularity hypothesis.
* `strictAntiOn_eulerResidualRisky_of_strictConcave` — strict concavity of the lifetime objective
  on the feasible set makes the risky Euler residual strictly antitone there (the second-order
  condition behind the regularity hypothesis).
* `log_precautionary_inequality` — the precautionary inequality made concrete for logarithmic
  utility (a `Prudent` witness) on a fair `{1, 3}` income gamble: `1/2 ≤ 2/3`.
* `log_eulerResidualCertain_root` / `log_eulerResidualRisky_root` — for log utility with `w = 11/3`
  and the fair `{1, 3}` gamble, the certain Euler equation is solved at `sᶜ = 5/6` and the risky one
  at `s⋆ = 1`.
* `log_strictConcaveOn_lifetimeUtility` / `log_strictConcaveOn_lifetimeUtilityCertain` — the two
  log objectives are strictly concave on their feasible sets (`Real.log` precomposed with the
  consumption affine maps, via `strictConcaveOn_log_Ioi`).
* `log_isMaxOn_lifetimeUtility_risky` / `log_isMaxOn_lifetimeUtilityCertain` — `s⋆ = 1` and
  `sᶜ = 5/6` are global maximizers of the respective two-period objectives over the
  feasible set, with the Euler equations derived as FOCs rather than assumed.
* `log_isMaxOn_lifetimeUtility_risky_unique` / `log_isMaxOn_lifetimeUtilityCertain_unique` —
  strict concavity makes each optimum the unique maximizer, so "the optimal saving" is
  well-defined.
* `log_saves_more_under_risk` — **the concrete punchline**: bundling the two optimality facts with
  `5/6 < 1`, a log agent saves strictly more (a precautionary wedge of `1/6`) when future income is
  the `{1, 3}` lottery than when it is replaced by its certain mean `2` — a comparison of
  actual optima of the saving problem.
-/

noncomputable section

namespace EconlibExamples.Preferences.PrecautionarySaving

open Econlib.Preferences
open Econlib.Probability
open Set

variable {n : ℕ} (u : ℝ → ℝ) (w : ℝ) (L : FinLottery n)

/-- Mean future income `𝔼[ỹ] = ∑ pᵢ yᵢ`. This is the lottery's expected value
`∑ L.prob.pmf i * L.outcome i`. -/
def meanIncome : ℝ := ∑ i, L.prob.pmf i * L.outcome i

/-- Expected period-1 marginal utility of a saving level `s`, `𝔼[u'(s + ỹ)] = ∑ pᵢ u'(s + yᵢ)`. -/
def expectedMarginalUtility (s : ℝ) : ℝ := ∑ i, L.prob.pmf i * deriv u (s + L.outcome i)

/-- Euler residual under **certain** income `ȳ`: marginal benefit `u'(s + ȳ)` minus marginal cost
`u'(w - s)` of saving. The certainty-economy optimal saving solves this `= 0`. -/
def eulerResidualCertain (s : ℝ) : ℝ := deriv u (s + meanIncome L) - deriv u (w - s)

/-- Euler residual under **risky** income: expected marginal benefit `𝔼[u'(s + ỹ)]` minus marginal
cost `u'(w - s)` of saving. The risky-economy optimal saving solves this `= 0`. -/
def eulerResidualRisky (s : ℝ) : ℝ := expectedMarginalUtility u L s - deriv u (w - s)

/-- **The precautionary motive.** For a prudent agent — marginal utility `u' = deriv u` convex on
`(0, ∞)` — risky income raises the expected marginal utility of saving above its certainty value:
`u'(s + 𝔼[ỹ]) ≤ 𝔼[u'(s + ỹ)]`. This is Jensen's inequality for the convex marginal utility, and it
is the entire formal reason a prudent consumer values saving more when the future is uncertain. -/
theorem marginalUtility_mean_le_expected (hu : Prudent u) (s : ℝ)
    (hpos : ∀ i, s + L.outcome i ∈ Ioi (0 : ℝ)) :
    deriv u (s + meanIncome L) ≤ expectedMarginalUtility u L s := by
  -- The mean future consumption is the `p`-average of the realized future consumptions.
  have hmean : ∑ i, L.prob.pmf i • (s + L.outcome i) = s + meanIncome L := by
    unfold meanIncome
    simp only [smul_eq_mul, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, L.prob.sum_one, one_mul]
  -- Jensen for the convex marginal utility `deriv u` at the future-consumption points.
  have hjensen : deriv u (∑ i, L.prob.pmf i • (s + L.outcome i)) ≤
      ∑ i, L.prob.pmf i • deriv u (s + L.outcome i) :=
    ConvexOn.map_sum_le hu (fun i _ => L.prob.nonneg i) L.prob.sum_one (fun i _ => hpos i)
  rw [hmean] at hjensen
  simpa only [smul_eq_mul, expectedMarginalUtility] using hjensen

/-- **Precautionary saving (Euler-residual form).** A prudent agent saves at least as much when
future income is a lottery as when it is replaced by its certain mean. The economic input is
prudence, entering through `marginalUtility_mean_le_expected`.

This statement takes `sCert` and `sRisky` as given solutions of their respective Euler equations
(`hCert`, `hRisky`) and a strictly decreasing risky Euler residual (`hΦ_anti`, the
second-order/regularity condition). It is the bare algebraic core. The economically complete
statement — where `sCert`, `sRisky` are actual local maximizers of the two-period objectives and
the Euler equations are derived as first-order conditions rather than assumed — is
`precautionary_saving_optimal`, which feeds this lemma the FOC-necessity theorems. The conclusion is
`sCert ≤ sRisky`. -/
theorem precautionary_saving (hu : Prudent u) {S : Set ℝ} {sCert sRisky : ℝ}
    (hpos : ∀ i, sCert + L.outcome i ∈ Ioi (0 : ℝ))
    (hΦ_anti : StrictAntiOn (eulerResidualRisky u w L) S)
    (hsCert : sCert ∈ S) (hsRisky : sRisky ∈ S)
    (hCert : eulerResidualCertain u w L sCert = 0)
    (hRisky : eulerResidualRisky u w L sRisky = 0) :
    sCert ≤ sRisky := by
  -- At the certainty optimum the risky residual is at least the (zero) certain residual.
  have hpre : eulerResidualCertain u w L sCert ≤ eulerResidualRisky u w L sCert := by
    have := marginalUtility_mean_le_expected u L hu sCert hpos
    unfold eulerResidualCertain eulerResidualRisky
    linarith
  have h0 : eulerResidualRisky u w L sRisky ≤ eulerResidualRisky u w L sCert := by
    rw [hRisky, ← hCert]; exact hpre
  -- A strictly decreasing residual (at the two feasible points) turns that ordering into the
  -- saving comparison.
  exact (hΦ_anti.le_iff_ge hsRisky hsCert).mp h0

/-! ## A concrete prudent agent: logarithmic utility

Logarithmic utility is a `Prudent` witness (`prudent_log`), and on a fair `{1, 3}` income gamble it
makes the precautionary motive fully computable. We first record the precautionary inequality at
log utility, and then — once the two-period optimization machinery is in place below — the economic
**punchline** as a comparison of optima: with wealth `w = 11/3` the certainty problem is
solved at `sᶜ = 5/6` and the risky problem at `s⋆ = 1`, both unique global maximizers of their
two-period objectives, and `5/6 < 1`. A log agent therefore saves strictly more (a precautionary
wedge of `1/6`) when income is the lottery than when it is replaced by its certain mean
(`log_saves_more_under_risk`). -/

/-- Future income gamble: a fair coin over `{1, 3}` units (mean `𝔼[ỹ] = 2`), bundled as a
`FinLottery 2`. The `FinDist` literal `finDist% ![1/2, 1/2]` discharges the probability axioms
automatically. -/
def logLottery : FinLottery 2 where
  outcome := ![1, 3]
  prob := finDist% ![(1 : ℝ) / 2, 1 / 2]

/-- The mean income of `logLottery` is `2`: `½·1 + ½·3 = 2`. -/
lemma logLottery_meanIncome : meanIncome logLottery = 2 := by
  simp [meanIncome, logLottery, Fin.sum_univ_two]; norm_num

/-- **Concrete precautionary inequality for log utility.** Logarithmic utility is prudent
(`prudent_log`), so at zero baseline saving the expected marginal utility of period-1 consumption
under the fair `{1, 3}` gamble exceeds the marginal utility at the mean consumption `2`:
`u'(2) = 1/2 ≤ 1/2·u'(1) + 1/2·u'(3) = 1/2·1 + 1/2·(1/3) = 2/3`. -/
theorem log_precautionary_inequality :
    deriv Real.log (0 + meanIncome logLottery) ≤ expectedMarginalUtility Real.log logLottery 0 := by
  have hpos : ∀ i, (0 : ℝ) + logLottery.outcome i ∈ Ioi (0 : ℝ) := by
    intro i; fin_cases i <;> norm_num [logLottery]
  exact marginalUtility_mean_le_expected Real.log logLottery prudent_log 0 hpos

/-- The two sides of `log_precautionary_inequality` are `1/2` and `2/3`. -/
theorem log_precautionary_values :
    deriv Real.log (0 + meanIncome logLottery) = 1 / 2 ∧
      expectedMarginalUtility Real.log logLottery 0 = 2 / 3 := by
  refine ⟨?_, ?_⟩
  · -- mean income is `2`, and `u'(2) = 1/2`.
    rw [logLottery_meanIncome, zero_add, Real.deriv_log]
    norm_num
  · -- `1/2·(1/1) + 1/2·(1/3) = 2/3`.
    simp only [expectedMarginalUtility, logLottery, Fin.sum_univ_two, zero_add,
      Real.deriv_log, FinDist.ofVec_pmf, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num

/-! ## The two-period saving problem: objective, FOC, and the comparative static for maximizers

The results above compare two assumed solutions of the Euler equations. We now build the
two-period optimization the Euler equation is the first-order condition of, and re-derive the
comparative static for actual maximizers. The spine is that `eulerResidualRisky` is exactly the
derivative of the lifetime objective, so the Euler equations become consequences of optimality
rather than assumptions. -/

/-- **Lifetime utility under risky income.** Period-0 utility from consuming `w - s` plus expected
period-1 utility from consuming `s + ỹ`: `V(s) = u(w - s) + 𝔼[u(s + ỹ)]`. This is the objective
whose maximizer the risky-economy Euler equation characterizes. -/
def lifetimeUtility (s : ℝ) : ℝ := u (w - s) + ∑ i, L.prob.pmf i * u (s + L.outcome i)

/-- **Lifetime utility under certain income.** The certainty-economy objective, with future income
replaced by its sure mean `ȳ = 𝔼[ỹ]`: `Vᶜ(s) = u(w - s) + u(s + ȳ)`. -/
def lifetimeUtilityCertain (s : ℝ) : ℝ := u (w - s) + u (s + meanIncome L)

/-- **Feasible saving (risky economy).** A saving level is feasible when consumption is strictly
positive in both periods and in every income state: `0 < w - s` (period-0) and `0 < s + yᵢ` for
all `i` (period-1). The feasible set is open, which is what makes an interior maximizer a local
maximizer. -/
def FeasibleSaving (s : ℝ) : Prop := 0 < w - s ∧ ∀ i, 0 < s + L.outcome i

/-- **Feasible saving (certainty economy).** As `FeasibleSaving`, with the single period-1 state
`s + ȳ`: `0 < w - s` and `0 < s + ȳ`. -/
def FeasibleSavingCertain (s : ℝ) : Prop := 0 < w - s ∧ 0 < s + meanIncome L

variable {u w L}

/-- The feasible set `{s | FeasibleSaving w L s}` is open: it is a finite intersection of open
half-lines in `s`. Openness is what upgrades an interior maximizer to a `IsLocalMax`. -/
theorem isOpen_feasibleSaving : IsOpen {s : ℝ | FeasibleSaving w L s} := by
  -- `0 < w - s` is open, and each `0 < s + yᵢ` is open; a finite `∀`-intersection of opens is open.
  have h0 : IsOpen {s : ℝ | 0 < w - s} :=
    isOpen_lt continuous_const (continuous_const.sub continuous_id)
  have hi : ∀ i : Fin n, IsOpen {s : ℝ | 0 < s + L.outcome i} := fun i =>
    isOpen_lt continuous_const (continuous_id.add continuous_const)
  have hset : {s : ℝ | FeasibleSaving w L s}
      = {s : ℝ | 0 < w - s} ∩ ⋂ i, {s : ℝ | 0 < s + L.outcome i} := by
    ext s; simp [FeasibleSaving]
  rw [hset]
  exact h0.inter (isOpen_iInter_of_finite hi)

/-- The certainty feasible set `{s | FeasibleSavingCertain w L s}` is open. -/
theorem isOpen_feasibleSavingCertain :
    IsOpen {s : ℝ | FeasibleSavingCertain w L s} := by
  have h0 : IsOpen {s : ℝ | 0 < w - s} :=
    isOpen_lt continuous_const (continuous_const.sub continuous_id)
  have h1 : IsOpen {s : ℝ | 0 < s + meanIncome L} :=
    isOpen_lt continuous_const (continuous_id.add continuous_const)
  have hset : {s : ℝ | FeasibleSavingCertain w L s} =
      {s : ℝ | 0 < w - s} ∩ {s : ℝ | 0 < s + meanIncome L} := by
    ext s; simp [FeasibleSavingCertain]
  rw [hset]; exact h0.inter h1

/-- **The derivative of lifetime utility is the risky Euler residual** (Stage B, the crux). Under a
differentiability hypothesis on `u` over `(0, ∞)` and at a feasible saving level `s`, the lifetime
objective `V(s) = u(w - s) + 𝔼[u(s + ỹ)]` has derivative
`V'(s) = -u'(w - s) + 𝔼[u'(s + ỹ)] = eulerResidualRisky u w L s`. The `u(w - s)` term contributes
`-u'(w - s)` (chain rule with `s ↦ w - s`), and each `pᵢ·u(s + yᵢ)` contributes `pᵢ·u'(s + yᵢ)`. -/
theorem hasDerivAt_lifetimeUtility
    (hu_diff : ∀ x : ℝ, 0 < x → HasDerivAt u (deriv u x) x) {s : ℝ}
    (hs : FeasibleSaving w L s) :
    HasDerivAt (lifetimeUtility u w L) (eulerResidualRisky u w L s) s := by
  obtain ⟨hw, hy⟩ := hs
  -- Period-0 term: `u(w - s)` has derivative `-u'(w - s)` by the chain rule.
  have hlin0 : HasDerivAt (fun s : ℝ => w - s) (-1) s := by
    simpa using (hasDerivAt_const s w).sub (hasDerivAt_id s)
  have hcomp0 : HasDerivAt (fun s : ℝ => u (w - s)) (deriv u (w - s) * (-1)) s :=
    (hu_diff (w - s) hw).comp s hlin0
  -- Period-1 terms: each `pᵢ·u(s + yᵢ)` has derivative `pᵢ·u'(s + yᵢ)`.
  have hsum :
      HasDerivAt (fun s : ℝ => ∑ i, L.prob.pmf i * u (s + L.outcome i))
        (∑ i, L.prob.pmf i * (deriv u (s + L.outcome i) * 1)) s := by
    apply HasDerivAt.fun_sum
    intro i _
    have hlini : HasDerivAt (fun s : ℝ => s + L.outcome i) (1 : ℝ) s :=
      (hasDerivAt_id s).add_const (L.outcome i)
    have hcompi : HasDerivAt (fun s : ℝ => u (s + L.outcome i)) (deriv u (s + L.outcome i) * 1) s :=
      (hu_diff (s + L.outcome i) (hy i)).comp s hlini
    exact hcompi.const_mul (L.prob.pmf i)
  -- Add the two pieces and identify the derivative with the Euler residual.
  have hV : HasDerivAt (lifetimeUtility u w L)
      (deriv u (w - s) * (-1) + ∑ i, L.prob.pmf i * (deriv u (s + L.outcome i) * 1)) s :=
    hcomp0.add hsum
  have hval : deriv u (w - s) * (-1) + ∑ i, L.prob.pmf i * (deriv u (s + L.outcome i) * 1)
      = eulerResidualRisky u w L s := by
    simp only [eulerResidualRisky, expectedMarginalUtility, mul_one, mul_neg_one]
    ring
  rwa [hval] at hV

/-- **The derivative of certainty lifetime utility is the certain Euler residual** (Stage B,
certainty analogue). `Vᶜ(s) = u(w - s) + u(s + ȳ)` has derivative
`-u'(w - s) + u'(s + ȳ) = eulerResidualCertain u w L s`. -/
theorem hasDerivAt_lifetimeUtilityCertain
    (hu_diff : ∀ x : ℝ, 0 < x → HasDerivAt u (deriv u x) x) {s : ℝ}
    (hs : FeasibleSavingCertain w L s) :
    HasDerivAt (lifetimeUtilityCertain u w L) (eulerResidualCertain u w L s) s := by
  obtain ⟨hw, hmean⟩ := hs
  have hlin0 : HasDerivAt (fun s : ℝ => w - s) (-1) s := by
    simpa using (hasDerivAt_const s w).sub (hasDerivAt_id s)
  have hcomp0 : HasDerivAt (fun s : ℝ => u (w - s)) (deriv u (w - s) * (-1)) s :=
    (hu_diff (w - s) hw).comp s hlin0
  have hlin1 : HasDerivAt (fun s : ℝ => s + meanIncome L) (1 : ℝ) s :=
    (hasDerivAt_id s).add_const (meanIncome L)
  have hcomp1 : HasDerivAt (fun s : ℝ => u (s + meanIncome L))
      (deriv u (s + meanIncome L) * 1) s :=
    (hu_diff (s + meanIncome L) hmean).comp s hlin1
  have hV : HasDerivAt (lifetimeUtilityCertain u w L)
      (deriv u (w - s) * (-1) + deriv u (s + meanIncome L) * 1) s :=
    hcomp0.add hcomp1
  have hval : deriv u (w - s) * (-1) + deriv u (s + meanIncome L) * 1
      = eulerResidualCertain u w L s := by
    simp only [eulerResidualCertain, mul_one, mul_neg_one]; ring
  rwa [hval] at hV

/-- Consequently, the (unconditional) derivative of the lifetime objective at a feasible point is
the risky Euler residual. -/
theorem deriv_lifetimeUtility
    (hu_diff : ∀ x : ℝ, 0 < x → HasDerivAt u (deriv u x) x) {s : ℝ}
    (hs : FeasibleSaving w L s) :
    deriv (lifetimeUtility u w L) s = eulerResidualRisky u w L s :=
  (hasDerivAt_lifetimeUtility hu_diff hs).deriv

/-- And the certainty analogue. -/
theorem deriv_lifetimeUtilityCertain
    (hu_diff : ∀ x : ℝ, 0 < x → HasDerivAt u (deriv u x) x) {s : ℝ}
    (hs : FeasibleSavingCertain w L s) :
    deriv (lifetimeUtilityCertain u w L) s = eulerResidualCertain u w L s :=
  (hasDerivAt_lifetimeUtilityCertain hu_diff hs).deriv

/-- **FOC necessity, risky economy** (Stage C). If a feasible saving level `s⋆` is a local
maximizer of the lifetime objective `V`, then the risky Euler equation holds at `s⋆`:
`eulerResidualRisky u w L s⋆ = 0`. This converts the Euler-root hypothesis of
`precautionary_saving` into a theorem about maximizers. The argument is `IsLocalMax.deriv_eq_zero`
(a local max has zero derivative) composed with the Stage-B identification of the derivative. -/
theorem eulerResidualRisky_eq_zero_of_isLocalMax
    (hu_diff : ∀ x : ℝ, 0 < x → HasDerivAt u (deriv u x) x) {sStar : ℝ}
    (hfeas : FeasibleSaving w L sStar)
    (hmax : IsLocalMax (lifetimeUtility u w L) sStar) :
    eulerResidualRisky u w L sStar = 0 := by
  have := hmax.deriv_eq_zero
  rwa [deriv_lifetimeUtility hu_diff hfeas] at this

/-- **FOC necessity, certainty economy** (Stage C). If a feasible saving level `s⋆` is a local
maximizer of the certainty objective `Vᶜ`, then `eulerResidualCertain u w L s⋆ = 0`. -/
theorem eulerResidualCertain_eq_zero_of_isLocalMax
    (hu_diff : ∀ x : ℝ, 0 < x → HasDerivAt u (deriv u x) x) {sStar : ℝ}
    (hfeas : FeasibleSavingCertain w L sStar)
    (hmax : IsLocalMax (lifetimeUtilityCertain u w L) sStar) :
    eulerResidualCertain u w L sStar = 0 := by
  have := hmax.deriv_eq_zero
  rwa [deriv_lifetimeUtilityCertain hu_diff hfeas] at this

/-- **FOC sufficiency, risky economy** (Stage D). If the lifetime objective `V` is concave on the
(open) feasible set and the risky Euler equation holds at a feasible `s⋆`, then `s⋆` is a global
maximizer of `V` over the feasible set. Strict concavity is not needed for maximality (only for
uniqueness): this is `ConcaveOn.isMaxOn_of_deriv_eq_zero` fed the Stage-B derivative. -/
theorem isMaxOn_lifetimeUtility_of_euler
    (hu_diff : ∀ x : ℝ, 0 < x → HasDerivAt u (deriv u x) x) {sStar : ℝ}
    (hfeas : FeasibleSaving w L sStar)
    (hconc : ConcaveOn ℝ {s : ℝ | FeasibleSaving w L s} (lifetimeUtility u w L))
    (heuler : eulerResidualRisky u w L sStar = 0) :
    IsMaxOn (lifetimeUtility u w L) {s : ℝ | FeasibleSaving w L s} sStar :=
  hconc.isMaxOn_of_deriv_eq_zero isOpen_feasibleSaving hfeas
    (hasDerivAt_lifetimeUtility hu_diff hfeas).differentiableAt
    (by rw [deriv_lifetimeUtility hu_diff hfeas]; exact heuler)

/-- **FOC sufficiency, certainty economy** (Stage D). Concavity of `Vᶜ` plus the certain Euler
equation at a feasible `s⋆` makes `s⋆` a global maximizer of `Vᶜ` over the certainty feasible
set. -/
theorem isMaxOn_lifetimeUtilityCertain_of_euler
    (hu_diff : ∀ x : ℝ, 0 < x → HasDerivAt u (deriv u x) x) {sStar : ℝ}
    (hfeas : FeasibleSavingCertain w L sStar)
    (hconc : ConcaveOn ℝ {s : ℝ | FeasibleSavingCertain w L s}
      (lifetimeUtilityCertain u w L))
    (heuler : eulerResidualCertain u w L sStar = 0) :
    IsMaxOn (lifetimeUtilityCertain u w L) {s : ℝ | FeasibleSavingCertain w L s} sStar :=
  hconc.isMaxOn_of_deriv_eq_zero isOpen_feasibleSavingCertain hfeas
    (hasDerivAt_lifetimeUtilityCertain hu_diff hfeas).differentiableAt
    (by rw [deriv_lifetimeUtilityCertain hu_diff hfeas]; exact heuler)

/-- **Precautionary saving, for actual maximizers** (Stage D capstone). The comparative
static: with `sCert` an actual local maximizer of the certainty two-period objective `Vᶜ` and
`sRisky` an actual local maximizer of the risky objective `V` — both feasible, not assumed Euler
roots — a prudent agent saves at least as much under income risk as under certainty:
`sCert ≤ sRisky`.

The FOC necessity (`eulerResidual…_eq_zero_of_isLocalMax`) turns each maximizer into a solution of
its Euler equation, and these are fed into `precautionary_saving`. The economic content is prudence,
entering through `marginalUtility_mean_le_expected`. The strict antitonicity of the risky Euler
residual (`hΦ_anti`) is retained as the explicit second-order/regularity hypothesis: it is the
derivative of `V` being strictly decreasing, which a strictly concave `V` supplies (see
`StrictConcaveOn.strictAntiOn_deriv`, packaged as
`strictAntiOn_eulerResidualRisky_of_strictConcave`). -/
theorem precautionary_saving_optimal
    (hu : Prudent u)
    (hu_diff : ∀ x : ℝ, 0 < x → HasDerivAt u (deriv u x) x) {S : Set ℝ} {sCert sRisky : ℝ}
    (hposCert : ∀ i, sCert + L.outcome i ∈ Ioi (0 : ℝ))
    (hΦ_anti : StrictAntiOn (eulerResidualRisky u w L) S)
    (hsCert : sCert ∈ S) (hsRisky : sRisky ∈ S)
    (hfeasCert : FeasibleSavingCertain w L sCert)
    (hmaxCert : IsLocalMax (lifetimeUtilityCertain u w L) sCert)
    (hfeasRisky : FeasibleSaving w L sRisky)
    (hmaxRisky : IsLocalMax (lifetimeUtility u w L) sRisky) :
    sCert ≤ sRisky :=
  precautionary_saving u w L hu hposCert hΦ_anti hsCert hsRisky
    (eulerResidualCertain_eq_zero_of_isLocalMax hu_diff hfeasCert hmaxCert)
    (eulerResidualRisky_eq_zero_of_isLocalMax hu_diff hfeasRisky hmaxRisky)

/-- **Strict antitonicity of the risky Euler residual from strict concavity.** If the risky
lifetime objective `V` is strictly concave on a convex feasible set `S` over which `u` is
differentiable (so `V` is differentiable), then its derivative — which equals
`eulerResidualRisky u w L` on `S` (Stage B) — is strictly antitone on `S`. This is the
second-order condition supplying the `StrictAntiOn` hypothesis of the capstone over the
feasible set. -/
theorem strictAntiOn_eulerResidualRisky_of_strictConcave
    (hu_diff : ∀ x : ℝ, 0 < x → HasDerivAt u (deriv u x) x)
    {S : Set ℝ} (hSfeas : ∀ s ∈ S, FeasibleSaving w L s)
    (hconc : StrictConcaveOn ℝ S (lifetimeUtility u w L)) :
    StrictAntiOn (eulerResidualRisky u w L) S := by
  -- `V` is differentiable on `S` (Stage B gives `HasDerivAt` at every feasible point).
  have hdiff : ∀ s ∈ S, DifferentiableAt ℝ (lifetimeUtility u w L) s := fun s hs =>
    (hasDerivAt_lifetimeUtility hu_diff (hSfeas s hs)).differentiableAt
  -- Strict concavity ⇒ derivative strictly antitone on `S`; rewrite the derivative as the residual.
  have hanti : StrictAntiOn (deriv (lifetimeUtility u w L)) S := hconc.strictAntiOn_deriv hdiff
  intro a ha b hb hab
  have hda : deriv (lifetimeUtility u w L) a = eulerResidualRisky u w L a :=
    deriv_lifetimeUtility hu_diff (hSfeas a ha)
  have hdb : deriv (lifetimeUtility u w L) b = eulerResidualRisky u w L b :=
    deriv_lifetimeUtility hu_diff (hSfeas b hb)
  have := hanti ha hb hab
  rwa [hda, hdb] at this

/-! ## Convexity and concavity of the two-period objective

To turn a stationary point into a global maximizer we need the lifetime objective to be concave on
the feasible set, and that set to be convex. The objective is a nonnegative-weight combination of
`Real.log` precomposed with the affine maps `s ↦ w - s` (period-0 consumption) and `s ↦ s + yᵢ`
(period-1 consumption). Strict concavity of `Real.log` on `(0, ∞)` (`strictConcaveOn_log_Ioi`)
transports through these affine substitutions, and the feasible set is a finite intersection of open
half-lines, hence convex. -/

/-- The period-0 half-line `{s | 0 < w - s}` is convex. -/
theorem convex_setOf_pos_sub : Convex ℝ {s : ℝ | 0 < w - s} := by
  have : {s : ℝ | 0 < w - s} = Iio w := by
    ext s; simp only [Set.mem_setOf_eq, Set.mem_Iio, sub_pos]
  rw [this]; exact convex_Iio w

/-- The period-1 half-line `{s | 0 < s + c}` is convex (here `c` is an income realization or its
mean). -/
theorem convex_setOf_pos_add (c : ℝ) : Convex ℝ {s : ℝ | 0 < s + c} := by
  have : {s : ℝ | 0 < s + c} = Ioi (-c) := by
    ext s; simp only [Set.mem_setOf_eq, Set.mem_Ioi]; constructor <;> intro h <;> linarith
  rw [this]; exact convex_Ioi (-c)

/-- The risky feasible set `{s | FeasibleSaving w L s}` is convex: a finite intersection of the
convex half-lines `{0 < w - s}` and `{0 < s + yᵢ}`. -/
theorem convex_feasibleSaving : Convex ℝ {s : ℝ | FeasibleSaving w L s} := by
  have hset : {s : ℝ | FeasibleSaving w L s}
      = {s : ℝ | 0 < w - s} ∩ ⋂ i, {s : ℝ | 0 < s + L.outcome i} := by
    ext s; simp [FeasibleSaving]
  rw [hset]
  exact convex_setOf_pos_sub.inter (convex_iInter fun i => convex_setOf_pos_add (L.outcome i))

/-- The certainty feasible set `{s | FeasibleSavingCertain w L s}` is convex. -/
theorem convex_feasibleSavingCertain :
    Convex ℝ {s : ℝ | FeasibleSavingCertain w L s} := by
  have hset : {s : ℝ | FeasibleSavingCertain w L s} =
      {s : ℝ | 0 < w - s} ∩ {s : ℝ | 0 < s + meanIncome L} := by
    ext s; simp [FeasibleSavingCertain]
  rw [hset]
  exact convex_setOf_pos_sub.inter (convex_setOf_pos_add (meanIncome L))

/-- `s ↦ Real.log (w - s)` is **strictly concave** on any convex set of feasible savings (where
`0 < w - s`): strict concavity of `Real.log` on `(0, ∞)` transported through the affine
substitution `s ↦ w - s`. -/
theorem strictConcaveOn_log_sub {S : Set ℝ} (hSconv : Convex ℝ S)
    (hSpos : ∀ s ∈ S, 0 < w - s) :
    StrictConcaveOn ℝ S (fun s : ℝ => Real.log (w - s)) := by
  refine ⟨hSconv, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : (w - x) ∈ Ioi (0 : ℝ) := hSpos x hx
  have hy' : (w - y) ∈ Ioi (0 : ℝ) := hSpos y hy
  have hxy' : w - x ≠ w - y := fun h => hxy (by linarith)
  have key := strictConcaveOn_log_Ioi.2 hx' hy' hxy' ha hb hab
  simp only [smul_eq_mul]
  have hcombo : a * (w - x) + b * (w - y) = w - (a * x + b * y) := by
    linear_combination w * hab
  rw [← hcombo]
  simpa only [smul_eq_mul] using key

/-- `s ↦ Real.log (s + c)` is **concave** on any convex set where `0 < s + c`: concavity of
`Real.log` on `(0, ∞)` transported through the affine substitution `s ↦ s + c`. -/
theorem concaveOn_log_add (c : ℝ) {S : Set ℝ} (hSconv : Convex ℝ S)
    (hSpos : ∀ s ∈ S, 0 < s + c) :
    ConcaveOn ℝ S (fun s : ℝ => Real.log (s + c)) := by
  refine ⟨hSconv, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (x + c) ∈ Ioi (0 : ℝ) := hSpos x hx
  have hy' : (y + c) ∈ Ioi (0 : ℝ) := hSpos y hy
  have key := strictConcaveOn_log_Ioi.concaveOn.2 hx' hy' ha hb hab
  simp only [smul_eq_mul]
  have hcombo : a * (x + c) + b * (y + c) = (a * x + b * y) + c := by
    linear_combination c * hab
  rw [← hcombo]
  simpa only [smul_eq_mul] using key

/-! ## The concrete optimum: a log agent saves strictly more under risk

We now exhibit the precautionary motive as a comparison of actual optima of the two-period
problem. Fix wealth `w = 11/3`, the fair `{1, 3}` gamble (mean `𝔼[ỹ] = 2`), and log utility. The
certainty optimum is `sᶜ = 5/6`; the risky optimum is `s⋆ = 1`. Each is the **unique** global
maximizer of its two-period objective over the feasible set (the objective is strictly concave), and
`5/6 < 1`: the prudent log agent self-insures by saving strictly more when future income is risky
than when it is replaced by its certain mean. -/

/-- Log utility is differentiable on `(0, ∞)`: `HasDerivAt Real.log (deriv Real.log x) x` for
`x > 0`. This discharges the `hu_diff` hypothesis of the maximizer theorems for `Real.log`. -/
theorem hasDerivAt_log_of_pos :
    ∀ x : ℝ, 0 < x → HasDerivAt Real.log (deriv Real.log x) x := by
  intro x hx
  rw [Real.deriv_log]
  exact Real.hasDerivAt_log (ne_of_gt hx)

/-- **Certainty Euler root for log utility.** At `sᶜ = 5/6` the certain Euler residual vanishes:
period-1 consumption `5/6 + 𝔼[ỹ] = 5/6 + 2 = 17/6` equals period-0 consumption
`11/3 - 5/6 = 17/6`, so the two marginal utilities `u'(17/6)` cancel. -/
theorem log_eulerResidualCertain_root :
    eulerResidualCertain Real.log (11 / 3) logLottery (5 / 6) = 0 := by
  simp only [eulerResidualCertain, logLottery_meanIncome, Real.deriv_log]
  norm_num

/-- **Risky Euler root for log utility.** At `s⋆ = 1` the risky Euler residual vanishes: the
expected period-1 marginal utility `½·u'(2) + ½·u'(4) = ½·½ + ½·¼ = 3/8` equals the period-0
marginal utility `u'(11/3 - 1) = u'(8/3) = 3/8`. -/
theorem log_eulerResidualRisky_root :
    eulerResidualRisky Real.log (11 / 3) logLottery 1 = 0 := by
  simp only [eulerResidualRisky, expectedMarginalUtility, logLottery, Fin.sum_univ_two,
    Real.deriv_log, FinDist.ofVec_pmf, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- **Strict concavity of the risky lifetime objective for log utility.** On the feasible set, the
risky objective `V(s) = log(11/3 - s) + ∑ᵢ pᵢ·log(s + yᵢ)` is strictly concave: the period-0 term
`log(11/3 - s)` is strictly concave and each period-1 term `pᵢ·log(s + yᵢ)` is concave
(`pᵢ ≥ 0`). -/
theorem log_strictConcaveOn_lifetimeUtility :
    StrictConcaveOn ℝ {s : ℝ | FeasibleSaving (11 / 3) logLottery s}
      (lifetimeUtility Real.log (11 / 3) logLottery) := by
  set S := {s : ℝ | FeasibleSaving (11 / 3) logLottery s} with hS
  have hconvS : Convex ℝ S := convex_feasibleSaving
  have hpos0 : ∀ s ∈ S, (0 : ℝ) < 11 / 3 - s := fun s hs => hs.1
  have hpY : ∀ i, ∀ s ∈ S, 0 < s + logLottery.outcome i := fun i s hs => hs.2 i
  -- Period-0 term `log(11/3 - s)` is strictly concave.
  have hf : StrictConcaveOn ℝ S (fun s => Real.log (11 / 3 - s)) :=
    strictConcaveOn_log_sub hconvS hpos0
  -- Period-1 sum `∑ᵢ pᵢ·log(s + yᵢ)` is concave (nonnegative-weight sum of concave terms).
  have hg : ConcaveOn ℝ S
      (fun s => ∑ i, logLottery.prob.pmf i * Real.log (s + logLottery.outcome i)) := by
    have h0 : ConcaveOn ℝ S
        (fun s => logLottery.prob.pmf 0 * Real.log (s + logLottery.outcome 0)) := by
      have hc := (concaveOn_log_add (logLottery.outcome 0) hconvS (hpY 0)).smul
        (by norm_num [logLottery] : (0 : ℝ) ≤ logLottery.prob.pmf 0)
      exact hc.congr (fun s _ => by simp [smul_eq_mul])
    have h1 : ConcaveOn ℝ S
        (fun s => logLottery.prob.pmf 1 * Real.log (s + logLottery.outcome 1)) := by
      have hc := (concaveOn_log_add (logLottery.outcome 1) hconvS (hpY 1)).smul
        (by norm_num [logLottery] : (0 : ℝ) ≤ logLottery.prob.pmf 1)
      exact hc.congr (fun s _ => by simp [smul_eq_mul])
    refine (h0.add h1).congr (fun s _ => ?_)
    simp [Pi.add_apply, Fin.sum_univ_two]
  exact (hf.add_concaveOn hg).congr (fun s _ => rfl)

/-- **Strict concavity of the certainty lifetime objective for log utility.** Both terms of
`Vᶜ(s) = log(11/3 - s) + log(s + 2)` are strictly concave, so `Vᶜ` is strictly concave on its
feasible set. -/
theorem log_strictConcaveOn_lifetimeUtilityCertain :
    StrictConcaveOn ℝ {s : ℝ | FeasibleSavingCertain (11 / 3) logLottery s}
      (lifetimeUtilityCertain Real.log (11 / 3) logLottery) := by
  set S := {s : ℝ | FeasibleSavingCertain (11 / 3) logLottery s} with hS
  have hconvS : Convex ℝ S := convex_feasibleSavingCertain
  have hpos0 : ∀ s ∈ S, (0 : ℝ) < 11 / 3 - s := fun s hs => hs.1
  have hpos1 : ∀ s ∈ S, (0 : ℝ) < s + meanIncome logLottery := fun s hs => hs.2
  have hf : StrictConcaveOn ℝ S (fun s => Real.log (11 / 3 - s)) :=
    strictConcaveOn_log_sub hconvS hpos0
  -- Use `concaveOn_log_add` at `c = 𝔼[ỹ] = 2`; it is strictly concave but plain concavity suffices
  -- for the second term, and the sum is strictly concave via the period-0 term.
  have hg : ConcaveOn ℝ S (fun s => Real.log (s + meanIncome logLottery)) :=
    concaveOn_log_add (meanIncome logLottery) hconvS hpos1
  exact (hf.add_concaveOn hg).congr (fun s _ => rfl)

/-- The risky optimum `s⋆ = 1` is feasible: `0 < 11/3 - 1 = 8/3` and `0 < 1 + yᵢ` for both income
states `y₀ = 1, y₁ = 3`. -/
theorem log_feasibleSaving_risky : FeasibleSaving (11 / 3) logLottery 1 := by
  refine ⟨by norm_num, fun i => ?_⟩
  fin_cases i <;> norm_num [logLottery]

/-- The certainty optimum `sᶜ = 5/6` is feasible: `0 < 11/3 - 5/6 = 17/6` and
`0 < 5/6 + 𝔼[ỹ] = 5/6 + 2 = 17/6`. -/
theorem log_feasibleSavingCertain :
    FeasibleSavingCertain (11 / 3) logLottery (5 / 6) := by
  refine ⟨by norm_num, ?_⟩
  rw [logLottery_meanIncome]; norm_num

/-- **The risky optimum is a global maximizer.** At `s⋆ = 1` the risky two-period objective
`V` attains its maximum over the feasible set: feasibility, the risky Euler equation
(`log_eulerResidualRisky_root`), and concavity of `V` make `1` a global maximizer via the file's FOC
sufficiency theorem `isMaxOn_lifetimeUtility_of_euler`. -/
theorem log_isMaxOn_lifetimeUtility_risky :
    IsMaxOn (lifetimeUtility Real.log (11 / 3) logLottery)
      {s : ℝ | FeasibleSaving (11 / 3) logLottery s} 1 :=
  isMaxOn_lifetimeUtility_of_euler hasDerivAt_log_of_pos log_feasibleSaving_risky
    log_strictConcaveOn_lifetimeUtility.concaveOn log_eulerResidualRisky_root

/-- **The certainty optimum is a global maximizer.** At `sᶜ = 5/6` the certainty two-period
objective `Vᶜ` attains its maximum over the feasible set. -/
theorem log_isMaxOn_lifetimeUtilityCertain :
    IsMaxOn (lifetimeUtilityCertain Real.log (11 / 3) logLottery)
      {s : ℝ | FeasibleSavingCertain (11 / 3) logLottery s} (5 / 6) :=
  isMaxOn_lifetimeUtilityCertain_of_euler hasDerivAt_log_of_pos log_feasibleSavingCertain
    log_strictConcaveOn_lifetimeUtilityCertain.concaveOn log_eulerResidualCertain_root

/-- **Uniqueness of the risky optimum.** Because the risky objective is strictly concave on the
feasible set, `s⋆ = 1` is the unique global maximizer: any feasible global maximizer equals `1`. -/
theorem log_isMaxOn_lifetimeUtility_risky_unique {s : ℝ}
    (hs : FeasibleSaving (11 / 3) logLottery s)
    (hmax : IsMaxOn (lifetimeUtility Real.log (11 / 3) logLottery)
      {s : ℝ | FeasibleSaving (11 / 3) logLottery s} s) :
    s = 1 :=
  log_strictConcaveOn_lifetimeUtility.eq_of_isMaxOn hmax log_isMaxOn_lifetimeUtility_risky hs
    log_feasibleSaving_risky

/-- **Uniqueness of the certainty optimum.** Strict concavity of `Vᶜ` makes `sᶜ = 5/6` the unique
global maximizer over the feasible set. -/
theorem log_isMaxOn_lifetimeUtilityCertain_unique {s : ℝ}
    (hs : FeasibleSavingCertain (11 / 3) logLottery s)
    (hmax : IsMaxOn (lifetimeUtilityCertain Real.log (11 / 3) logLottery)
      {s : ℝ | FeasibleSavingCertain (11 / 3) logLottery s} s) :
    s = 5 / 6 :=
  log_strictConcaveOn_lifetimeUtilityCertain.eq_of_isMaxOn hmax
    log_isMaxOn_lifetimeUtilityCertain hs log_feasibleSavingCertain

/-- **A log agent saves strictly more under risk (the punchline).** For log utility with wealth
`w = 11/3` and a fair `{1, 3}` income gamble (mean `𝔼[ỹ] = 2`):

* `sᶜ = 5/6` is the global maximizer of the **certainty** two-period objective `Vᶜ` over the
  certainty feasible set;
* `s⋆ = 1` is the global maximizer of the **risky** two-period objective `V` over the risky feasible
  set;
* and `5/6 < 1`.

So the prudent consumer self-insures against income risk by saving strictly more (a *precautionary*
saving wedge of `1 - 5/6 = 1/6`) than when future income is replaced by its certain mean. The
maximizers are unique (`log_isMaxOn_lifetimeUtility_risky_unique` and its certainty analogue), so
"the optimal saving" is literally well-defined, and the strict inequality is between actual optima
of the saving problem, not assumed Euler roots. -/
theorem log_saves_more_under_risk :
    IsMaxOn (lifetimeUtilityCertain Real.log (11 / 3) logLottery)
        {s : ℝ | FeasibleSavingCertain (11 / 3) logLottery s} (5 / 6) ∧
    IsMaxOn (lifetimeUtility Real.log (11 / 3) logLottery)
        {s : ℝ | FeasibleSaving (11 / 3) logLottery s} 1 ∧
    (5 / 6 : ℝ) < 1 :=
  ⟨log_isMaxOn_lifetimeUtilityCertain, log_isMaxOn_lifetimeUtility_risky, by norm_num⟩

end EconlibExamples.Preferences.PrecautionarySaving

end
