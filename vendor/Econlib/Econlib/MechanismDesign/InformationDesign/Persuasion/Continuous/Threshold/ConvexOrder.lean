/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Threshold.Basic

/-!
# Threshold persuasion: Convex-order properties of two-point laws

The two-point law derived from a continuous prior and a cutoff is convex-order dominated by the
prior (Gentzkow and Kamenica 2016): Collapsing each side of the cutoff to its conditional mean is a
mean-preserving contraction. This makes the two-point law a feasible (Bayes-plausible) signal.

## Main statements

* `threshold_weighted_conditionalExpect_eq_expect` — the probability-weighted conditional
  expectations on the two cells of the cutoff partition sum to the total expectation.
* `thresholdTwoPointLaw_expect_id_eq_prior` — the two-point law has the same mean as the prior.
* `thresholdTwoPointLaw_convexOrderOnIcc` — convex-order domination on `[a, b]`.
* `thresholdTwoPointLaw_convexOrder` — convex-order domination on `[0, 1]`.

## Notes

Everything here is the `K = 2` instance of the conditional-mean partition law
(`Econlib.Probability.ConditionalMeanPartition`), transported along the bridge
`thresholdTwoPointLaw_eq_conditionalMeanPartitionLaw`.

## References

* Gentzkow, Matthew, and Emir Kamenica. 2016. “A Rothschild-Stiglitz Approach to Bayesian
  Persuasion.” *American Economic Review* 106 (5): 597–601. [https://doi.org/10.1257/aer.p20161049](https://doi.org/10.1257/aer.p20161049).

## Tags

persuasion, threshold persuasion, convex order, posterior mean
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous

/-- The probability-weighted conditional expectations below and above the threshold sum to the
total expectation. `K = 2` instance of
`Econlib.Probability.weighted_conditionalExpect_eq_expect`. -/
theorem threshold_weighted_conditionalExpect_eq_expect (d : Econlib.Probability.ContDist)
    {a u b : ℝ} (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_cont : ContinuousOn d.density (Icc a b))
    {φ : ℝ → ℝ} (hφ_cont : ContinuousOn φ (Icc a b)) :
    d.prob_interval a u * d.conditionalExpectOrZero φ (Icc a u) +
      d.prob_interval u b * d.conditionalExpectOrZero φ (Icc u b) =
        d.toProbDist.expect φ := by
  have hd_support : d.toProbDist.supportsOn (Icc a b) :=
    contDist_toProbDist_supportsOn_Icc_of_density_eq_zero_outside d hsupport
  have h := Econlib.Probability.weighted_conditionalExpect_eq_expect d
    (thresholdPartition hau hub) φ hφ_cont hd_cont hd_support
  rwa [Fin.sum_univ_two, thresholdPartition_cellMass_zero d hau hub,
    thresholdPartition_cellMass_one d hau hub, thresholdPartition_cellClosed_zero hau hub,
    thresholdPartition_cellClosed_one hau hub] at h

/-- The probability-weighted conditional means below and above the cutoff sum to the total mean:
The `id` instance of `threshold_weighted_conditionalExpect_eq_expect`. -/
theorem threshold_two_point_mean_identity (d : Econlib.Probability.ContDist)
    {a u b : ℝ} (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    d.prob_interval a u * d.conditionalExpectOrZero id (Icc a u) +
      d.prob_interval u b * d.conditionalExpectOrZero id (Icc u b) =
        d.toProbDist.expect id :=
  -- The mean identity is the weighted-conditional-expectation identity at the test function `id`.
  threshold_weighted_conditionalExpect_eq_expect d hau hub hsupport hd_cont
    (φ := id) continuousOn_id

/-- The two-point law preserves the prior mean: `𝔼[X]` is unchanged by collapsing each side of the
cutoff to its conditional mean. -/
theorem thresholdTwoPointLaw_expect_id_eq_prior (d : Econlib.Probability.ContDist)
    {a u b : ℝ} (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    (thresholdTwoPointLaw d a u b hub.le).expect id = d.toProbDist.expect id := by
  have hsum : d.prob_interval a u + d.prob_interval u b = 1 :=
    threshold_prob_intervals_sum_one d hau hub hsupport
  have hleft : 1 - d.prob_interval u b = d.prob_interval a u := by
    linarith
  rw [thresholdTwoPointLaw_expect d a u b hub.le id aestronglyMeasurable_id]
  simpa [hleft] using threshold_two_point_mean_identity d hau hub hsupport hd_cont

/-- The two-point law is convex-order dominated by the prior on `[a, b]`: A mean-preserving
contraction of the prior under continuity and positive density. -/
theorem thresholdTwoPointLaw_convexOrderOnIcc (d : Econlib.Probability.ContDist)
    {a u b : ℝ} (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    Econlib.Probability.ConvexOrderOnIcc a b
      (thresholdTwoPointLaw d a u b hub.le) d.toProbDist := by
  have hd_support : d.toProbDist.supportsOn (Icc a b) :=
    contDist_toProbDist_supportsOn_Icc_of_density_eq_zero_outside d hsupport
  rw [thresholdTwoPointLaw_eq_conditionalMeanPartitionLaw d hau hub hsupport hd_pos hd_cont]
  exact Econlib.Probability.conditionalMeanPartitionLaw_convexOrderOnIcc d
    (thresholdPartition hau hub) _ hd_cont hd_support

/-- The two-point law is convex-order dominated by the prior on `[0, 1]`: The unit-interval
specialization of `thresholdTwoPointLaw_convexOrderOnIcc`. -/
theorem thresholdTwoPointLaw_convexOrder (d : Econlib.Probability.ContDist)
    {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hsupport : ∀ x ∉ Icc (0 : ℝ) 1, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc (0 : ℝ) 1, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc (0 : ℝ) 1)) :
    thresholdTwoPointLaw d 0 u 1 hu1.le ≼cx d.toProbDist := by
  simpa [Econlib.Probability.ConvexOrder] using
    thresholdTwoPointLaw_convexOrderOnIcc d hu0 hu1 hsupport hd_pos hd_cont

end Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous
