/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.IntegralIdentities
public import Econlib.Math.Probability.StopLoss
public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.ContDist.CDF

/-!
# Uniform continuous distribution

This file constructs the uniform distribution on a compact interval `[a, b]` as a `ContDist` and
provides its density, expectation, variance, and CDF in closed form.

## Main definitions

* `ContDist.uniform`: Uniform distribution on `[a, b]` as a continuous distribution.

## Main statements

* `ContDist.uniform_density`: The density equals `1 / (b - a)` on `[a, b]` and `0` outside.
* `ContDist.uniform_isMode`: Every point of `[a, b]` is a mode.
* `ContDist.uniform_expect`: The expectation of the identity is `(a + b) / 2`.
* `ContDist.uniform_variance`: The variance of the identity is `(b - a)² / 12`.
* `ContDist.uniform_cdf`: The CDF equals `0` for `x < a`, `(x - a) / (b - a)` for `a ≤ x ≤ b`, and
  `1` for `x > b`.
* `ContDist.uniform_stopLoss`: The stop-loss at `z ∈ [a, b]` is `(b - z)² / (2 (b - a))`.

## Tags

probability, continuous distributions, uniform
-/

@[expose] public section

open Set MeasureTheory

namespace Econlib.Probability

/-- The uniform density written as a constant indicator on `[a, b]`. -/
private lemma uniform_density_indicator (a b : ℝ) :
    (fun x => if x ∈ Icc a b then 1 / (b - a) else (0 : ℝ)) =
      (Icc a b).indicator (fun _ => 1 / (b - a)) := by
  ext x; simp [indicator_apply]

/-- The first-moment kernel of the uniform density as an indicator. -/
private lemma uniform_density_mul_id_indicator (a b : ℝ) :
    (fun x => (if x ∈ Icc a b then 1 / (b - a) else 0) * x) =
      (Icc a b).indicator (fun x => x / (b - a)) := by
  ext x; simp only [indicator_apply]; split_ifs <;> ring

/-- Uniform distribution on the closed interval `[a, b]`, where `a < b`.

The density is `1 / (b - a)` on `[a, b]` and `0` outside. -/
noncomputable def ContDist.uniform (a b : ℝ) (hab : a < b) : ContDist where
  density x := if x ∈ Icc a b then 1 / (b - a) else 0
  nonneg x := by
    split
    · exact div_nonneg (by norm_num) (sub_nonneg.mpr (le_of_lt hab))
    · exact le_refl 0
  integrable := by
    rw [uniform_density_indicator]
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (hs := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
                          (hC := enorm_ne_top))
  integral_one := by
    rw [uniform_density_indicator, integral_indicator measurableSet_Icc, setIntegral_const]
    rw [Real.volume_real_Icc_of_le (le_of_lt hab)]
    simp only [one_div, smul_eq_mul]
    exact mul_inv_cancel₀ (by linarith : b - a ≠ 0)

/-- The density of the uniform distribution on `[a, b]` is zero at any `x ∉ [a, b]`. -/
lemma ContDist.uniform_density_eq_zero_of_not_mem (a b : ℝ) (hab : a < b) {x : ℝ}
    (hx : x ∉ Set.Icc a b) : (ContDist.uniform a b hab).density x = 0 := if_neg hx

/-- The density of the uniform distribution on `[a, b]` equals `1 / (b - a)` on `[a, b]` and `0`
outside. -/
@[simp] lemma ContDist.uniform_density (a b : ℝ) (hab : a < b) (x : ℝ) :
    (ContDist.uniform a b hab).density x =
      if x ∈ Icc a b then 1 / (b - a) else 0 := rfl

/-- The density of the uniform distribution on `[a, b]` evaluated at a point of `[a, b]`: It equals
`1 / (b - a)`. The on-`Icc` form, without the nested `if`. -/
@[simp] lemma ContDist.uniform_density_of_mem (a b : ℝ) (hab : a < b) {x : ℝ}
    (hx : x ∈ Icc a b) : (ContDist.uniform a b hab).density x = 1 / (b - a) := if_pos hx

/-- Every point of the support `[a, b]` is a mode of the uniform distribution: The density is
constant there and zero outside. -/
lemma ContDist.uniform_isMode (a b : ℝ) (hab : a < b) {c : ℝ} (hc : c ∈ Icc a b) :
    (ContDist.uniform a b hab).IsMode c := by
  intro x
  rw [ContDist.uniform_density, ContDist.uniform_density, if_pos hc]
  split_ifs
  · exact le_refl _
  · exact div_nonneg zero_le_one (by linarith)

/-- The expectation of the identity under the uniform distribution on `[a, b]` is `(a + b) / 2`. -/
lemma ContDist.uniform_expect (a b : ℝ) (hab : a < b) :
    (ContDist.uniform a b hab).expect id = (a + b) / 2 := by
  simp only [ContDist.expect, uniform, id]
  rw [uniform_density_mul_id_indicator, integral_indicator measurableSet_Icc]
  rw [show ∫ x in Icc a b, x / (b - a) = ∫ x in a..b, x / (b - a) from by
    rw [intervalIntegral.integral_of_le hab.le]
    exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  have hba : (b - a : ℝ) ≠ 0 := by linarith
  have h_deriv : ∀ x : ℝ, HasDerivAt (fun y => y ^ 2 / (2 * (b - a))) (x / (b - a)) x := by
    intro x; convert (hasDerivAt_pow 2 x).div_const (2 * (b - a)) using 1
    rw [Nat.cast_ofNat]; field_simp; ring
  have h_ftc : ∫ x in a..b, x / (b - a) =
      b ^ 2 / (2 * (b - a)) - a ^ 2 / (2 * (b - a)) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => h_deriv x)
      ((continuous_id.div_const _).intervalIntegrable _ _)
  rw [h_ftc]; field_simp; ring

/-- The variance of the identity under the uniform distribution on `[a, b]` is `(b - a)² / 12`. -/
lemma ContDist.uniform_variance (a b : ℝ) (hab : a < b) :
    (ContDist.uniform a b hab).variance id = (b - a) ^ 2 / 12 := by
  simp only [ContDist.variance, ContDist.expect, uniform, id]
  have hba : (b - a : ℝ) ≠ 0 := by linarith
  have h_ind2 : (fun x => (if x ∈ Icc a b then 1 / (b - a) else 0) * (x ^ 2)) =
      (Icc a b).indicator (fun x => x ^ 2 / (b - a)) := by
    ext x; simp only [indicator_apply]; split_ifs <;> ring
  rw [h_ind2, integral_indicator measurableSet_Icc]
  rw [show ∫ x in Icc a b, x ^ 2 / (b - a) = ∫ x in a..b, x ^ 2 / (b - a)
     from by
    rw [intervalIntegral.integral_of_le hab.le]
    exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  rw [uniform_density_mul_id_indicator, integral_indicator measurableSet_Icc]
  rw [show ∫ x in Icc a b, x / (b - a) = ∫ x in a..b, x / (b - a) from by
    rw [intervalIntegral.integral_of_le hab.le]
    exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  rw [show ∫ x in a..b, x ^ 2 / (b - a) =
      (b ^ 3 - a ^ 3) / (3 * (b - a)) from by
    rw [show (fun x => x ^ 2 / (b - a)) = fun x => (1 / (b - a)) * x ^ 2
    from by
      ext x; ring]
    rw [intervalIntegral.integral_const_mul, integral_sq_Icc]; field_simp]
  rw [show ∫ x in a..b, x / (b - a) =
      (b ^ 2 - a ^ 2) / (2 * (b - a)) from by
    rw [show (fun x => x / (b - a)) = fun x => (1 / (b - a)) * x from by
    ext x; ring]
    rw [intervalIntegral.integral_const_mul, integral_id_Icc]; field_simp]
  field_simp; ring

/-- The CDF of the uniform distribution on `[a, b]`: It equals `0` for `x < a`, `(x - a) / (b - a)`
for `a ≤ x ≤ b`, and `1` for `x > b`. -/
lemma ContDist.uniform_cdf (a b : ℝ) (hab : a < b) (x : ℝ) :
    (ContDist.uniform a b hab).cdf x =
      if x < a then 0
      else if x ≤ b then (x - a) / (b - a)
      else 1 := by
  simp only [ContDist.cdf_eq_integral, uniform]
  rw [uniform_density_indicator, setIntegral_indicator measurableSet_Icc]
  split_ifs with hxa hxb
  · have : Iic x ∩ Icc a b = ∅ := by
      ext t; simp only [Iic, Icc, mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false,
        not_and, not_le]; intro ht hta; linarith
    rw [this, setIntegral_empty]
  · push Not at hxa
    have : Iic x ∩ Icc a b = Icc a x := by
      ext t; simp only [Iic, Icc, mem_inter_iff, mem_setOf_eq]; constructor
      · rintro ⟨htx, hta, _⟩; exact ⟨hta, htx⟩
      · rintro ⟨hta, htx⟩; exact ⟨htx, hta, le_trans htx hxb⟩
    rw [this, setIntegral_const, Real.volume_real_Icc_of_le hxa]
    simp only [one_div, smul_eq_mul]; rw [div_eq_mul_inv]
  · push Not at hxa hxb
    have : Iic x ∩ Icc a b = Icc a b := by
      ext t
      simp only [Iic, Icc, mem_inter_iff, mem_setOf_eq, and_iff_right_iff_imp, and_imp]
      intro hta htb; linarith
    rw [this, setIntegral_const, Real.volume_real_Icc_of_le (le_of_lt hab)]
    simp only [one_div, smul_eq_mul]
    exact mul_inv_cancel₀ (by linarith)

/-- The CDF of the uniform distribution on `[a, b]` evaluated at a point of `[a, b]`: It equals
`(x - a) / (b - a)`. The on-`Icc` form, without the nested `if`. -/
@[simp] lemma ContDist.uniform_cdf_of_mem (a b : ℝ) (hab : a < b) {x : ℝ}
    (hx : x ∈ Icc a b) :
    (ContDist.uniform a b hab).cdf x = (x - a) / (b - a) := by
  rw [ContDist.uniform_cdf, if_neg (not_lt.mpr hx.1), if_pos hx.2]

/-- The stop-loss of the uniform distribution on `[a, b]` at a threshold `z ∈ [a, b]`: The expected
overshoot above `z` is `(b - z)² / (2 (b - a))`. -/
lemma ContDist.uniform_stopLoss (a b : ℝ) (hab : a < b) {z : ℝ} (hz : z ∈ Icc a b) :
    (ContDist.uniform a b hab).toMeasure.stopLoss z = (b - z) ^ 2 / (2 * (b - a)) := by
  have hba : (b - a : ℝ) ≠ 0 := by linarith [hab]
  simp only [MeasureTheory.Measure.stopLoss]
  rw [(ContDist.uniform a b hab).integral_toMeasure_eq]
  -- The density-weighted hinge is an indicator over `[a, b]`.
  have hind : (fun x => (ContDist.uniform a b hab).density x * max (x - z) 0)
      = (Icc a b).indicator (fun x => max (x - z) 0 / (b - a)) := by
    funext x
    rw [ContDist.uniform_density]
    by_cases hx : x ∈ Icc a b
    · rw [if_pos hx, indicator_of_mem hx]; ring
    · rw [if_neg hx, indicator_of_notMem hx, zero_mul]
  rw [hind, integral_indicator measurableSet_Icc,
    show (∫ x in Icc a b, max (x - z) 0 / (b - a))
      = ∫ x in a..b, max (x - z) 0 / (b - a) from by
        rw [intervalIntegral.integral_of_le hab.le]
        exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  rw [mem_Icc] at hz
  -- Split at `z`: the hinge vanishes below `z` and is affine above.
  have hsplit : (∫ x in a..z, max (x - z) 0 / (b - a)) + (∫ x in z..b, max (x - z) 0 / (b - a))
      = ∫ x in a..b, max (x - z) 0 / (b - a) := by
    apply intervalIntegral.integral_add_adjacent_intervals <;>
      exact (((continuous_id.sub continuous_const).max continuous_const).div_const
        _).intervalIntegrable _ _
  have hlow : (∫ x in a..z, max (x - z) 0 / (b - a)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => 0) (fun x hx => by
      rw [uIcc_of_le hz.1] at hx
      rw [max_eq_right (by linarith [hx.2] : x - z ≤ 0), zero_div])]
    simp
  have hhigh : (∫ x in z..b, max (x - z) 0 / (b - a)) = (b - z) ^ 2 / (2 * (b - a)) := by
    rw [intervalIntegral.integral_congr (g := fun x => (x - z) / (b - a)) (fun x hx => by
      rw [uIcc_of_le hz.2] at hx
      rw [max_eq_left (by linarith [hx.1] : (0 : ℝ) ≤ x - z)])]
    rw [show (fun x : ℝ => (x - z) / (b - a)) = fun x : ℝ => (1 / (b - a)) * (x - z) from
        funext fun x => by ring,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
        intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  linarith [hsplit, hlow, hhigh]

end Econlib.Probability
