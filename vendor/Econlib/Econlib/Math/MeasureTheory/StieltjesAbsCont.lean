/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Econlib.Math.MeasureTheory.StieltjesIBP
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Absolute continuity of C¹ Stieltjes measures

For a monotone C¹ function `u` with continuous nonnegative derivative `u'`, the Stieltjes measure
`hu.stieltjesMeasure` is absolutely continuous with respect to Lebesgue measure, with Radon–Nikodym
density `u'`. Equivalently, `hu.stieltjesMeasure = volume.withDensity u'`, so integration against
the Stieltjes measure reduces to the Lebesgue integral of `f · u'`.

## Main statements

* `Monotone.stieltjes_measure_eq_withDensity` — the Stieltjes measure of a C¹ monotone function
  equals Lebesgue measure weighted by its derivative.
* `Monotone.stieltjes_integral_eq_lebesgue` — integration against the Stieltjes measure equals the
  Lebesgue integral weighted by the derivative.

## Tags

stieltjes measure, absolutely continuous, radon-nikodym derivative, fundamental theorem of calculus
-/

@[expose] public section

open MeasureTheory Set Filter Topology Function
open scoped ENNReal Real

namespace Monotone

/-- The Stieltjes measure of a C¹ monotone function equals Lebesgue measure weighted by its
derivative. -/
theorem stieltjes_measure_eq_withDensity {u u' : ℝ → ℝ} (hu : Monotone u)
    (h_deriv : ∀ x, HasDerivAt u (u' x) x) (hu_nn : ∀ x, 0 ≤ u' x)
    (hu_cont : Continuous u') :
    hu.stieltjesMeasure = volume.withDensity (fun x => ENNReal.ofReal (u' x)) := by
  -- Both measures are σ-finite (Stieltjes on ℝ is σ-finite; withDensity of
  -- locally integrable is σ-finite).
  -- Show they agree on Ioo intervals with rational endpoints.
  apply Real.measure_ext_Ioo_rat
  intro a b
  by_cases hab : (a : ℝ) < b
  · -- Stieltjes side: μ(Ioo a b) via measure_Ioc and Ioo ≈ Ioc
    -- The Stieltjes function of a C¹ function equals the function itself
    -- (since continuous ⟹ right-continuous, so rightLim = identity).
    have h_sf_eq : ∀ x, (hu.stieltjes) x = u x := by
      intro x; change hu.stieltjesFunction x = u x
      rw [Monotone.stieltjesFunction_eq]
      exact rightLim_eq_of_tendsto (nhdsWithin_Ioi_neBot le_rfl).ne
        ((h_deriv x).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    -- u is continuous (differentiable everywhere → continuous)
    have hu_continuous : Continuous u :=
      continuous_iff_continuousAt.mpr (fun x => (h_deriv x).continuousAt)
    -- leftLim of the Stieltjes function = u for continuous u
    have h_leftLim : leftLim (⇑(hu.stieltjes)) (b : ℝ) = u b := by
      rw [leftLim_eq_of_tendsto (nhdsWithin_Iio_neBot le_rfl).ne
        (by rw [show ⇑(hu.stieltjes) = u from funext h_sf_eq]
            exact hu_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)]
    -- Stieltjes measure of Ioo via StieltjesFunction.measure_Ioo
    have h_lhs : (hu.stieltjesMeasure) (Ioo (a : ℝ) b) =
        ENNReal.ofReal (u b - u a) := by
      change (hu.stieltjes).measure (Ioo (a : ℝ) b) = _
      rw [StieltjesFunction.measure_Ioo, h_sf_eq, h_leftLim]
    -- withDensity side: measure of Ioo = ofReal (∫ u')
    have h_rhs : (volume.withDensity (fun x => ENNReal.ofReal (u' x))) (Ioo (a : ℝ) b) =
        ENNReal.ofReal (u b - u a) := by
      rw [withDensity_apply _ measurableSet_Ioo]
      -- ∫_{Ioo a b} u' = u(b) - u(a) by FTC (via Ioc ≈ Ioo a.e.)
      have h_ftc : ∫ x in (a : ℝ)..b, u' x = u b - u a :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => h_deriv x) (hu_cont.intervalIntegrable _ _)
      -- Convert lintegral of ofReal to ofReal of integral (non-negative function)
      have h_intOn : IntegrableOn u' (Ioo (a : ℝ) b) :=
        (hu_cont.intervalIntegrable (a : ℝ) b |>.1).mono_set Ioo_subset_Ioc_self
      rw [← ofReal_integral_eq_lintegral_ofReal h_intOn (ae_of_all _ hu_nn)]
      -- Goal: ofReal (∫ x in Ioo a b, u') = ofReal (u b - u a)
      congr 1
      -- ∫_{Ioo a b} u' = ∫_{Ioc a b} u' = ∫_a^b u' = u(b) - u(a)
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hab.le]
      exact h_ftc
    rw [h_lhs, h_rhs]
  · -- a ≥ b: both sides = 0
    push Not at hab
    rw [Ioo_eq_empty (not_lt.mpr (by exact_mod_cast hab)), measure_empty, measure_empty]

/-- Integration against a C¹ Stieltjes measure converts to the Lebesgue integral weighted by the
derivative: `∫ f dμ_u = ∫ f · u'`. -/
theorem stieltjes_integral_eq_lebesgue {u u' : ℝ → ℝ} (hu : Monotone u)
    (h_deriv : ∀ x, HasDerivAt u (u' x) x) (hu_nn : ∀ x, 0 ≤ u' x)
    (hu_cont : Continuous u')
    (f : ℝ → ℝ) :
    ∫ y, f y ∂(hu.stieltjesMeasure) = ∫ y, f y * u' y := by
  rw [stieltjes_measure_eq_withDensity hu h_deriv hu_nn hu_cont]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hu_cont.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  congr 1; ext x
  rw [smul_eq_mul, ENNReal.toReal_ofReal (hu_nn x), mul_comm]

end Monotone
