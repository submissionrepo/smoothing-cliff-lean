/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Optimality
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous.Threshold.ConvexOrder
public import Econlib.Probability.Order.Convex.StopLoss

/-!
# Threshold persuasion: Optimality of the cutoff disclosure

For a natural class of sender objectives the threshold two-point law is optimal among all
Bayes-plausible signals, not merely feasible. This file supplies the optimality theorem advertised
by the threshold module, via the convex-price certificate `isOptimalSignal_of_convexMajorant`
(Dworczak and Martini 2019; Dworczak and Kolotilin 2024).

The worked objective is the **excess-over-threshold** ("call option") payoff
`fun m => max (m - u) 0`: The sender is paid the posterior mean's excess over the action threshold
`u`. Its convex hinge shape (flat below `u`, slope one above) is its own convex majorant, and the
tightness identity `d.expect φ = thresholdTwoPointLaw.expect φ` holds because `φ` is affine on each
cell of the cutoff partition, so pooling each cell to its conditional mean preserves the
expectation. The cutoff two-point law is therefore optimal.

## Main statements

* `thresholdTwoPointLaw_expect_hinge` — the two-point law's payoff under the excess-over-threshold
  objective is `P(X ≥ u) · (𝔼[X | X ≥ u] − u)`.
* `contDist_expect_hinge_eq` — the prior's payoff under the same objective equals the same value
  (the tightness identity).
* `thresholdTwoPointLaw_isOptimal_excessOverThreshold` — the cutoff two-point law maximizes the
  sender's expected excess-over-threshold payoff over all feasible signals.

## References

* Dworczak, Piotr, and Giorgio Martini. 2019. “The Simple Economics of Optimal Persuasion.”
  *Journal of Political Economy* 127 (5): 1993–2048. [https://doi.org/10.1086/701813](https://doi.org/10.1086/701813).
* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900).

## Tags

persuasion, threshold persuasion, optimal signal, stop-loss, two-point distribution
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous

open Econlib.Probability

variable (d : Econlib.Probability.ContDist) {a u b : ℝ}

/-- The two-point law's expected excess-over-threshold payoff: The upper cell carries all the
payoff, contributing `P(X ≥ u) · (𝔼[X | X ≥ u] − u)`. -/
lemma thresholdTwoPointLaw_expect_hinge (hau : a < u) (hub : u < b)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    (thresholdTwoPointLaw d a u b hub.le).expect (fun m => max (m - u) 0)
      = d.prob_interval u b * (d.conditionalExpectOrZero id (Icc u b) - u) := by
  have hmem := threshold_conditionalExpect_id_mem_subintervals d hau hub hd_pos hd_cont
  have hmL : d.conditionalExpectOrZero id (Icc a u) ≤ u := hmem.1.2
  have hmR : u ≤ d.conditionalExpectOrZero id (Icc u b) := hmem.2.1
  have hφ_cont : Continuous (fun m : ℝ => max (m - u) 0) := continuous_hinge u
  rw [thresholdTwoPointLaw_expect d a u b hub.le _ hφ_cont.aestronglyMeasurable]
  have h0 : max (d.conditionalExpectOrZero id (Icc a u) - u) 0 = 0 := by
    rw [max_eq_right]; linarith
  have h1 : max (d.conditionalExpectOrZero id (Icc u b) - u) 0
      = d.conditionalExpectOrZero id (Icc u b) - u := by
    rw [max_eq_left]; linarith
  rw [h0, h1]; ring

/-- **Tightness identity.** The prior's expected excess-over-threshold payoff equals the two-point
law's: Only the mass above the cutoff contributes, and
`∫_{[u,b]} (x − u) dd = P(X ≥ u)(𝔼[X|X≥u]−u)`. This is the affine-on-each-cell statement underlying
optimality of the cutoff signal. -/
lemma contDist_expect_hinge_eq (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    d.toProbDist.expect (fun m => max (m - u) 0)
      = d.prob_interval u b * (d.conditionalExpectOrZero id (Icc u b) - u) := by
  have hp_pos : 0 < d.prob_interval u b :=
    d.prob_interval_pos_of_pos_density hub
      (fun x hx => hd_pos x (Icc_subset_Icc hau.le le_rfl hx))
      (hd_cont.mono (Icc_subset_Icc hau.le le_rfl))
  have hset_pos : 0 < ∫ x in Icc u b, d.density x := by
    simpa [Econlib.Probability.ContDist.prob_interval, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hub.le] using hp_pos
  rw [Econlib.Probability.ProbDist.expect, Econlib.Probability.ContDist.toProbDist_toMeasure,
    d.integral_toMeasure_eq]
  -- The integrand vanishes off `[u, b]` (below `u` the hinge is zero; above `b` the density is
  -- zero), so it equals the indicator of `density · (x − u)` pointwise.
  have hpt : (fun x => d.density x * max (x - u) 0)
      = (Icc u b).indicator (fun x => d.density x * (x - u)) := by
    funext x
    by_cases hx : x ∈ Icc u b
    · rw [indicator_of_mem hx, max_eq_left (by linarith [hx.1] : (0 : ℝ) ≤ x - u)]
    · rw [Set.indicator_of_notMem hx]
      rcases not_and_or.mp hx with h | h
      · rw [max_eq_right (by linarith [not_le.mp h] : x - u ≤ 0), mul_zero]
      · rw [hsupport x (fun hmem => h hmem.2), zero_mul]
  rw [hpt, integral_indicator measurableSet_Icc,
    d.conditionalExpectOrZero_eq_of_pos id (Icc u b) hset_pos]
  have hp_eq : d.prob_interval u b = ∫ x in Icc u b, d.density x := rfl
  have hd_int : IntegrableOn (fun x => d.density x) (Icc u b) := d.integrable.integrableOn
  have hdx_int : IntegrableOn (fun x => d.density x * x) (Icc u b) :=
    ((hd_cont.mono (Icc_subset_Icc hau.le le_rfl)).mul continuousOn_id).integrableOn_Icc
  have hsplit : ∫ x in Icc u b, d.density x * (x - u)
      = (∫ x in Icc u b, d.density x * x) - u * ∫ x in Icc u b, d.density x := by
    rw [show (∫ x in Icc u b, d.density x * (x - u))
        = ∫ x in Icc u b, (d.density x * x - u * d.density x) from by
          apply integral_congr_ae; filter_upwards with x; ring]
    rw [integral_sub hdx_int (hd_int.const_mul u), integral_const_mul]
  rw [hsplit]
  have hp_ne : d.prob_interval u b ≠ 0 := ne_of_gt hp_pos
  have hid : (∫ x in Icc u b, d.density x * id x) = ∫ x in Icc u b, d.density x * x := by
    simp [id_eq]
  rw [hid, hp_eq]
  field_simp

/-- **The cutoff disclosure is optimal for the excess-over-threshold objective.**

For a sender paid the posterior mean's excess over the threshold `u`, the threshold two-point law
maximizes expected payoff over every feasible (Bayes-plausible) signal. The optimal signal
collapses to a two-point distribution — the two conditional means below and above the cutoff. -/
theorem thresholdTwoPointLaw_isOptimal_excessOverThreshold (hau : a < u) (hub : u < b)
    (hsupport : ∀ x ∉ Icc a b, d.density x = 0)
    (hd_pos : ∀ x ∈ Icc a b, 0 < d.density x)
    (hd_cont : ContinuousOn d.density (Icc a b)) :
    IsOptimalSignal a b d.toProbDist (fun m => max (m - u) 0)
      (thresholdTwoPointLaw d a u b hub.le) := by
  -- The objective is its own bi-affine convex majorant; tightness is the two hinge identities.
  refine isOptimalSignal_of_convexMajorant
    (c := fun m => max (m - u) 0)
    (thresholdTwoPointLaw_convexOrderOnIcc d hau hub hsupport hd_pos hd_cont)
    (convexOn_hinge_on a b u) (continuous_hinge u).continuousOn (continuous_hinge u).continuousOn
    (fun x _ => le_rfl) ?_
  rw [thresholdTwoPointLaw_expect_hinge d hau hub hd_pos hd_cont,
    contDist_expect_hinge_eq d hau hub hsupport hd_pos hd_cont]

end Econlib.MechanismDesign.InformationDesign.Persuasion.Continuous
