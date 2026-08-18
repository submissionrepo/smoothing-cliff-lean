/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Probability.Quantile
public import Econlib.Probability.ContDist.CDF

/-!
# Quantile function of a continuous distribution

This file specializes measure-level quantiles to a `ContDist`. It bridges the measure-theoretic CDF
`(μ (Iic x)).toReal` to the `ContDist`-level `cdf`, establishes the **right-inverse identity**
`F (F⁻¹ u) = u` for `u ∈ (0, 1)`, and records expectation change-of-variables formulas through the
quantile map.

These are the change-of-variables tools the ironing layer needs: It works on the quantile domain
`[0, 1]`, where the virtual-value primitive `H(q) = ∫₀^q ψ(F⁻¹ u) du` lives.

## Main statements

* `ContDist.toReal_measure_Iic_eq_cdf` — the CDF bridge `(d.toMeasure (Iic x)).toReal = d.cdf x`.
* `ContDist.quantile_le_iff` — Galois identity in `ContDist` vocabulary.
* `ContDist.cdf_quantile` — right inverse `d.cdf (quantile u) = u` for `u ∈ Ioo 0 1`.
* `ContDist.expect_eq_integral_quantile` — change of variables `E_d[g] = ∫₀¹ g (F⁻¹ t) dt`.

## Tags

quantile, generalized inverse, cumulative distribution function, change of variables
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Econlib.Probability.ContDist

variable (d : ContDist)

/-- **CDF bridge.** The measure-theoretic CDF `(d.toMeasure (Iic x)).toReal` agrees with the
`ContDist`-level CDF `d.cdf x`. Both are `∫_{Iic x} density`: The left as a real-ized lintegral
against `withDensity`, the right as a Bochner integral. -/
lemma toReal_measure_Iic_eq_cdf (x : ℝ) :
    (d.toMeasure (Iic x)).toReal = d.cdf x := by
  rw [ContDist.toMeasure_eq, withDensity_apply _ measurableSet_Iic, cdf_eq_integral]
  rw [← MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun t => d.nonneg t)
        d.integrable.integrableOn.aestronglyMeasurable]

/-- **Galois identity for the quantile.** The quantile of `u` is at most `x` iff `u ≤ d.cdf x`,
stated in `ContDist` vocabulary. -/
lemma quantile_le_iff {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) {x : ℝ} :
    Measure.quantile d.toMeasure u ≤ x ↔ u ≤ d.cdf x := by
  haveI := d.toMeasure_isProbability
  rw [Measure.quantile_le_iff hu, toReal_measure_Iic_eq_cdf]

/-- For `u ∈ (0, 1)` the quantile lies in the superlevel set: `u ≤ d.cdf (quantile u)`. -/
lemma le_cdf_quantile {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    u ≤ d.cdf (Measure.quantile d.toMeasure u) :=
  (d.quantile_le_iff hu).mp le_rfl

/-- **Right inverse of the CDF.** Because the `ContDist` CDF is everywhere continuous (not merely
right-continuous), for `u ∈ (0, 1)` it actually attains `u` at its quantile: `F (F⁻¹ u) = u`. -/
lemma cdf_quantile {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    d.cdf (Measure.quantile d.toMeasure u) = u := by
  haveI := d.toMeasure_isProbability
  set q := Measure.quantile d.toMeasure u with hq
  refine le_antisymm ?_ (d.le_cdf_quantile hu)
  -- `F` is continuous; for every `x < q`, `x ∉ {F ≥ u}`, so `F x < u`. Pass to the left limit.
  -- `x < q` means `x` is below the superlevel set `{F ≥ u}`, so `F x < u`.
  have hlt : ∀ x < q, d.cdf x < u := fun x hx =>
    lt_of_not_ge fun hle => hx.not_ge ((d.quantile_le_iff hu).mpr hle)
  have htend : Tendsto (fun x => d.cdf x) (𝓝[<] q) (𝓝 (d.cdf q)) :=
    (d.cdf_continuous.continuousAt).continuousWithinAt.tendsto
  haveI : (𝓝[<] q).NeBot := nhdsWithin_Iio_neBot (le_refl q)
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hlt x hx).le

/-- **Change of variables.** For any integrable `g`, the `ContDist` expectation is the integral of
`g ∘ F⁻¹` over the quantile domain `(0, 1)`. -/
lemma expect_eq_integral_quantile {g : ℝ → ℝ} (hg : Integrable g d.toMeasure) :
    d.expect g = ∫ t in Ioo (0 : ℝ) 1, g (Measure.quantile d.toMeasure t) := by
  haveI := d.toMeasure_isProbability
  rw [d.expect_eq_measure_integral]
  exact Measure.integral_eq_integral_quantile g hg.aestronglyMeasurable

end Econlib.Probability.ContDist
