/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.StieltjesRegularization
public import Econlib.Probability.ContDist.CDF

/-!
# Stieltjes bridges between a `ContDist` and its CDF

This file proves the Stieltjes-measure identities attached to the CDF of a `ContDist`: The CDF is
continuous, its Stieltjes measure coincides with the underlying density measure `d.toMeasure`, and
integration against the Stieltjes measure unfolds as `∫ density * g` against Lebesgue measure.

## Main statements

* `contdist_cdf_continuous` — `d.cdf` is continuous, not just right-continuous.
* `contdist_stieltjes_measure_eq` — `stieltjesMeasure d.cdf.mono = d.toMeasure`.
* `contdist_stieltjes_integral_eq` — `∫ g dμ_{F_d} = ∫ density * g`.
* `contdist_ibp_bridge`, `contdist_ibp_bridge_set` — the integration-by-parts rewrite identities
  for the FOSD / SOSD analytic chains.

## Notes

These bridges let integration-by-parts arguments work either against `stieltjesMeasure d.cdf.mono`
or against the density on Lebesgue measure, whichever yields cleaner algebra.

## Tags

continuous distribution, CDF, Stieltjes measure, integration by parts
-/

@[expose] public section

open MeasureTheory Set BigOperators Function Filter
open scoped Topology ENNReal Real

namespace Econlib.Probability

open Monotone

/-- The CDF of a continuous distribution is continuous, not just right-continuous. -/
lemma contdist_cdf_continuous (d : ContDist) : Continuous d.cdf := by
  set C := ∫ t in Iic (0 : ℝ), d.density t
  suffices h : d.cdf = fun x => C + ∫ t in (0 : ℝ)..x, d.density t by
    rw [h]; exact continuous_const.add (d.integrable.continuous_primitive 0)
  ext b; simp only [C, ContDist.cdf_eq_integral]
  linarith [intervalIntegral.integral_Iic_sub_Iic (a := (0 : ℝ)) (b := b)
    d.integrable.integrableOn d.integrable.integrableOn]

/-- **Measure bridge**: The Stieltjes measure of a density-CDF equals `d.toMeasure`. -/
lemma contdist_stieltjes_measure_eq (d : ContDist) :
    stieltjesMeasure d.cdf.mono = d.toMeasure := by
  change stieltjesMeasure d.cdf.mono =
    volume.withDensity (fun x => ENNReal.ofReal (d.density x))
  have hF_cont := contdist_cdf_continuous d
  apply Real.measure_ext_Ioo_rat
  intro a b
  by_cases hab : (a : ℝ) < b
  · have h_fn_eq : ⇑(stieltjes d.cdf.mono) = d.cdf :=
      funext (stieltjes_eq_of_rightCts d.cdf.mono d.cdf.right_continuous)
    have h_lhs : (stieltjesMeasure d.cdf.mono) (Ioo (a : ℝ) b) =
        ENNReal.ofReal (∫ t in Ioc (a : ℝ) b, d.density t) := by
      change (stieltjes d.cdf.mono).measure (Ioo (a : ℝ) b) = _
      rw [StieltjesFunction.measure_Ioo, h_fn_eq,
          leftLim_eq_of_tendsto (nhdsWithin_Iio_neBot le_rfl).ne
            (hF_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds),
          ContDist.cdf_eq_integral, ContDist.cdf_eq_integral]
      congr 1
      linarith [intervalIntegral.integral_Iic_sub_Iic (a := (a : ℝ)) (b := (b : ℝ))
        d.integrable.integrableOn d.integrable.integrableOn,
        intervalIntegral.integral_of_le hab.le (f := d.density) (μ := volume)]
    have h_rhs : (volume.withDensity (fun x => ENNReal.ofReal (d.density x))) (Ioo (a : ℝ) b) =
        ENNReal.ofReal (∫ t in Ioc (a : ℝ) b, d.density t) := by
      rw [withDensity_apply _ measurableSet_Ioo,
          ← ofReal_integral_eq_lintegral_ofReal d.integrable.integrableOn (ae_of_all _ d.nonneg),
          setIntegral_congr_set Ioo_ae_eq_Ioc.symm]
    rw [h_lhs, h_rhs]
  · push Not at hab
    rw [Ioo_eq_empty (not_lt.mpr (by exact_mod_cast hab)), measure_empty, measure_empty]

/-- **Integral bridge**: Integrating `g` against the CDF's Stieltjes measure equals integrating
`density * g` against Lebesgue measure. Direct corollary of the measure bridge. -/
lemma contdist_stieltjes_integral_eq (d : ContDist) (g : ℝ → ℝ) :
    ∫ x, g x ∂(stieltjesMeasure d.cdf.mono) = ∫ x, d.density x * g x := by
  rw [contdist_stieltjes_measure_eq d]; exact d.integral_toMeasure_eq g

/-- **Integration-by-parts bridge**: `∫ leftLim(u_rc) dμ_CDF = E_d[u]`. -/
lemma contdist_ibp_bridge (d : ContDist) (u : ℝ → ℝ) (hu : Monotone u) :
    ∫ x, leftLim (⇑(stieltjes hu)) x ∂(stieltjesMeasure d.cdf.mono) = d.expect u := by
  rw [contdist_stieltjes_measure_eq d, d.integral_toMeasure_eq]
  exact integral_congr_ae ((leftLim_stieltjes_eq_ae u hu).mono fun x hx => by
    change d.density x * leftLim (⇑(stieltjes hu)) x = d.density x * u x; rw [hx])

/-- **Set integral bridge**: Integrating `leftLim(u_rc)` against the CDF's Stieltjes measure on any
measurable set equals integrating `density * u` on that set. -/
lemma contdist_ibp_bridge_set (d : ContDist) (u : ℝ → ℝ) (hu : Monotone u)
    {S : Set ℝ} (hS : MeasurableSet S) :
    ∫ x in S, leftLim (⇑(stieltjes hu)) x ∂(stieltjesMeasure d.cdf.mono) =
    ∫ x in S, d.density x * u x := by
  rw [contdist_stieltjes_measure_eq d, d.setIntegral_toMeasure_eq _ hS]
  exact setIntegral_congr_ae hS ((leftLim_stieltjes_eq_ae u hu).mono fun x hx _ => by rw [hx])

end Econlib.Probability
