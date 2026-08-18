/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Order.Core.NegPut
public import Econlib.Probability.Order.SOSD.Mollifier.ExpectConcave

/-!
# SOSD equivalence

This file states the **second-order stochastic dominance** equivalence for the monotone concave
utility class of linear growth: `F` dominates `G` in the second order iff `E_G[u] ≤ E_F[u]` for
every monotone concave `u` satisfying a linear-growth bound. The forward direction is supplied by
`sosd_expect_concave_mono_general` (in `Order/SOSD/Mollifier/ExpectConcave.lean`); the reverse
direction tests against the truncated kernels `negPut`.

## Main statements

* `CDF.SOSD.expect_concave_mono` — SOSD forward direction for linear-growth monotone concave
  utilities.
* `CDF.SOSD.iff_expect_concave` — the equivalence over that utility class.

## Notes

The quantifier ranges over linear-growth utilities only — it is not "every risk-averse agent": The
superlinear utilities `log` and CRRA fall outside this class and are handled separately, under a
positive bounded support hypothesis, by `CDF.SOSD.expect_log` and `CDF.SOSD.expect_crra` in
`Order/SOSD/PositiveSupport.lean`.

## References

* Hadar, Josef, and William R. Russell. 1969. “Rules for Ordering Uncertain Prospects.” *The
  American Economic Review* 59 (1): 25–34.
* Hanoch, G., and H. Levy. 1969. “The Efficiency Analysis of Choices Involving Risk.” *The Review
  of Economic Studies* 36 (3): 335–46. [https://doi.org/10.2307/2296431](https://doi.org/10.2307/2296431).
* Rothschild, Michael, and Joseph E. Stiglitz. 1970. “Increasing Risk: I. A Definition.” *Journal
  of Economic Theory* 2 (3): 225–43. [https://doi.org/10.1016/0022-0531(70)90038-4](https://doi.org/10.1016/0022-0531(70)90038-4).

## Tags

second-order stochastic dominance, sosd, concave order, increasing risk
-/

@[expose] public section

open MeasureTheory Set BigOperators Function Filter
open scoped Topology ENNReal Real

namespace Econlib.Probability

/-- SOSD forward direction, for monotone concave utilities of **linear growth**: If `F` dominates
`G` in the second-order sense, then every monotone concave `u` satisfying the linear-growth bound
`|u x| ≤ C·(1 + |x|)` and the stated integrability conditions has `E_G[u] ≤ E_F[u]`.

The linear-growth bound is a substantive restriction: It covers bounded, affine, and sublinear
concave utilities, but excludes the canonical risk-averse utilities `log` and CRRA, which are
superlinear near `0` (and are not even real-valued on all of `ℝ`). Those cases are recovered, under
a positive bounded support hypothesis, by `CDF.SOSD.expect_log` and `CDF.SOSD.expect_crra` in
`Order/SOSD/PositiveSupport.lean`, which apply the compact-support concave step
`CDF.SOSD.expect_concave_compactSupport` (in `Order/SOSD/CompactSupport.lean`) to `u` directly on
its support — no linear-growth bound and no global extension. -/
lemma CDF.SOSD.expect_concave_mono (dF dG : ContDist) (u : ℝ → ℝ)
    (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (hu_conc : ConcaveOn ℝ univ u)
    (hu_mono : Monotone u)
    (h_linear : ∃ C : ℝ, 0 < C ∧ ∀ x, |u x| ≤ C * (1 + |x|))
    (h_intF : Integrable (fun x => dF.density x * u x))
    (h_intG : Integrable (fun x => dG.density x * u x))
    (h_meanF : Integrable (fun x => dF.density x * |x|))
    (h_meanG : Integrable (fun x => dG.density x * |x|)) :
    dG.expect u ≤ dF.expect u :=
  sosd_expect_concave_mono_general h_sosd u hu_conc hu_mono h_linear
    h_intF h_intG h_meanF h_meanG

/-- SOSD equivalence, for the monotone concave linear-growth utility class: `F` dominates `G` in
the second order iff `E_G[u] ≤ E_F[u]` for every monotone concave `u` carrying the linear-growth
bound `|u x| ≤ C·(1 + |x|)` and the stated integrability. The quantifier ranges over this
restricted class only — not "every risk-averse agent": Superlinear utilities such as `log`/CRRA are
outside it (see `CDF.SOSD.expect_log`/`expect_crra` for their positive-support specializations).
Finite first moments are required for the reverse direction's test function. -/
lemma CDF.SOSD.iff_expect_concave (dF dG : ContDist)
    (h_int_xF : Integrable (fun x => dF.density x * x))
    (h_int_xG : Integrable (fun x => dG.density x * x))
    (h_meanF : Integrable (fun x => dF.density x * |x|))
    (h_meanG : Integrable (fun x => dG.density x * |x|)) :
    CDF.SOSD dF.cdf dG.cdf ↔
    (∀ u : ℝ → ℝ, ConcaveOn ℝ univ u → Monotone u →
     (∃ C : ℝ, 0 < C ∧ ∀ x, |u x| ≤ C * (1 + |x|)) →
     Integrable (fun x => dF.density x * u x) →
     Integrable (fun x => dG.density x * u x) →
     dG.expect u ≤ dF.expect u) := by
  constructor
  · -- Forward: SOSD → expectation ordering (via mollifier bridge)
    exact fun h_sosd u hu_conc hu_mono h_linear h_intF h_intG =>
      CDF.SOSD.expect_concave_mono dF dG u h_sosd hu_conc hu_mono h_linear
        h_intF h_intG h_meanF h_meanG
  · -- Reverse: test against negPut, use Tonelli identity. The finite first moments give the
    -- integrable-tails witnesses; the negPut test gives the integrated-CDF inequality.
    refine fun h_expect => CDF.SOSD.mk' (fun x => cdf_integrableOn_Iic dF x h_int_xF)
      (fun x => cdf_integrableOn_Iic dG x h_int_xG) ?_
    intro x
    have h_negPut_linear : ∃ C : ℝ, 0 < C ∧ ∀ t, |negPut x t| ≤ C * (1 + |t|) := by
      refine ⟨1 + |x|, by positivity, fun t => ?_⟩
      simp only [negPut]
      -- |min(0, t - x)| ≤ (1 + |x|) * (1 + |t|)
      -- Case split: t ≤ x → min = t - x, |t - x| ≤ |t| + |x|; t > x → min = 0
      rcases le_or_gt t x with h | h
      · rw [min_eq_right (sub_nonpos.mpr h)]
        calc |t - x| ≤ |t| + |x| := abs_sub t x
          _ ≤ (1 + |x|) * (1 + |t|) := by nlinarith [abs_nonneg t, abs_nonneg x]
      · rw [min_eq_left (le_of_lt (sub_pos.mpr h)), abs_zero]
        positivity
    -- Apply the forward direction to negPut: E_G[negPut x] ≤ E_F[negPut x]
    have h_concave : ConcaveOn ℝ univ (negPut x) := negPut_concave x
    have h_mono : Monotone (negPut x) := negPut_monotone x
    have h_intF : Integrable (fun t => dF.density t * negPut x t) :=
      integrable_negPut dF x h_int_xF
    have h_intG : Integrable (fun t => dG.density t * negPut x t) :=
      integrable_negPut dG x h_int_xG
    have h_ineq := h_expect (negPut x) h_concave h_mono h_negPut_linear h_intF h_intG
    -- E_d[negPut x] = -∫_{Iic x} F(s) ds for each d
    rw [expect_negPut_eq_neg_integral_cdf dF x h_int_xF,
        expect_negPut_eq_neg_integral_cdf dG x h_int_xG] at h_ineq
    -- -∫_{Iic x} G ≤ -∫_{Iic x} F  ⟺  ∫_{Iic x} F ≤ ∫_{Iic x} G  ⟺  SOSD
    simpa using neg_le_neg_iff.mp h_ineq

end Econlib.Probability
