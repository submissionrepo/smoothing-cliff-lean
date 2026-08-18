/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.IntegralIdentities
public import Econlib.Math.MeasureTheory.IntegralReal
public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.ContDist.CDF
public import Mathlib.Probability.Distributions.Exponential

/-!
# Exponential distribution

This file constructs exponential distributions as `ContDist` objects and develops their basic
analytic properties: Density, CDF, survival function, expectation, variance, and memorylessness.

## Main definitions

* `ContDist.exponential`: The exponential distribution with rate parameter `rate > 0` as a
  `ContDist`, with density `rate * exp(-rate * x)` for `x ≥ 0` and `0` otherwise.

## Main statements

* `ContDist.exponential_cdf`: The CDF equals `1 - exp(-rate * x)` for `x ≥ 0` and `0` for `x < 0`.
* `ContDist.exponential_survival`: The survival function `1 - F(x) = exp(-rate * x)` for `x ≥ 0`.
* `ContDist.exponential_isMode_zero`: `0` is a mode.
* `ContDist.exponential_expect`: The expectation equals `1 / rate`.
* `ContDist.exponential_variance`: The variance equals `1 / rate ^ 2`.
* `ContDist.exponential_memoryless`: The memorylessness property: For `s, t ≥ 0`,
  `P(X > s + t) / P(X > s) = P(X > t)`.

## Tags

probability, continuous distributions, exponential
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory

namespace Econlib.Probability

/-- The exponential density `rate * exp(-rate * x)` (extended by zero for `x < 0`) equals Mathlib's
`exponentialPDFReal rate`. -/
lemma density_eq_exponentialPDFReal (rate : ℝ) :
    (fun x => if x ≥ 0 then rate * Real.exp (-rate * x) else (0 : ℝ)) =
    exponentialPDFReal rate := by
  ext x; simp only [ge_iff_le, neg_mul]
  by_cases hx : 0 ≤ x <;>
    simp [hx, exponentialPDFReal, gammaPDFReal, Real.rpow_zero]

/-- The `ENNReal.ofReal` lift of `exponentialPDFReal rate` equals Mathlib's `exponentialPDF rate`
as a function `ℝ → ℝ≥0∞`. -/
lemma ofReal_exponentialPDFReal_eq_exponentialPDF (rate : ℝ) :
    (fun x => ENNReal.ofReal (exponentialPDFReal rate x)) = exponentialPDF rate := by
  ext x; rw [exponentialPDF_eq]; simp [exponentialPDFReal, gammaPDFReal]

/-- Exponential distribution with rate parameter `rate > 0`, with density `rate * exp(-rate * x)`
for `x ≥ 0` and `0` otherwise. -/
noncomputable def ContDist.exponential (rate : ℝ) (hrate : 0 < rate) : ContDist where
  density := exponentialPDFReal rate
  nonneg := exponentialPDFReal_nonneg hrate
  integrable := integrable_of_lintegral_ofReal_eq_one
    (exponentialPDFReal_nonneg hrate)
    (stronglyMeasurable_exponentialPDFReal rate)
    (by rw [ofReal_exponentialPDFReal_eq_exponentialPDF, lintegral_exponentialPDF_eq_one hrate])
  integral_one := integral_eq_one_of_lintegral_ofReal_eq_one
    (exponentialPDFReal_nonneg hrate)
    (stronglyMeasurable_exponentialPDFReal rate)
    (by rw [ofReal_exponentialPDFReal_eq_exponentialPDF, lintegral_exponentialPDF_eq_one hrate])

/-- The exponential density vanishes on negative arguments. -/
lemma ContDist.exponential_density_eq_zero_of_neg (rate : ℝ) (hrate : 0 < rate)
    {x : ℝ} (hx : x < 0) : (ContDist.exponential rate hrate).density x = 0 := by
  simp [ContDist.exponential, exponentialPDFReal, gammaPDFReal, show ¬(0 ≤ x) from by linarith]

/-- The density of `ContDist.exponential rate hrate` equals `exponentialPDFReal rate`. -/
@[simp] lemma ContDist.exponential_density (rate : ℝ) (hrate : 0 < rate) (x : ℝ) :
    (ContDist.exponential rate hrate).density x = exponentialPDFReal rate x := rfl

/-- `0` is a mode of the exponential distribution: The density `rate * exp(-rate * x)` is
decreasing on `[0, ∞)` and vanishes on `(-∞, 0)`, so it is maximized at the left endpoint. -/
lemma ContDist.exponential_isMode_zero (rate : ℝ) (hrate : 0 < rate) :
    (ContDist.exponential rate hrate).IsMode 0 := by
  have h := congrFun (density_eq_exponentialPDFReal rate)
  intro x
  rw [ContDist.exponential_density, ContDist.exponential_density, ← h x, ← h 0]
  norm_num
  split_ifs with hx
  · -- `exp(-rate * x) ≤ 1` since the exponent is nonpositive on `0 ≤ x`
    have hexp : Real.exp (-(rate * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    nlinarith
  · positivity

/-- The expected value of an exponential distribution with rate `rate` equals `1 / rate`. -/
lemma ContDist.exponential_expect (rate : ℝ) (hrate : 0 < rate) :
    (ContDist.exponential rate hrate).expect id = 1 / rate := by
  change ∫ x, (ContDist.exponential rate hrate).density x * id x = 1 / rate
  simp only [id_eq, ContDist.exponential_density]
  rw [show exponentialPDFReal rate = fun x => if x ≥ 0 then rate * Real.exp (-rate * x) else 0
    from (density_eq_exponentialPDFReal rate).symm]
  have h_ind : (fun x => (if x ≥ 0 then rate * Real.exp (-rate * x) else 0) * x) =
      (Ici (0 : ℝ)).indicator (fun x => rate * Real.exp (-rate * x) * x) := by
    ext x; simp only [Set.indicator_apply, ge_iff_le, mem_Ici]
    split_ifs with h <;> ring
  rw [h_ind, integral_indicator measurableSet_Ici]
  rw [show ∫ x in Ici (0 : ℝ), rate * Real.exp (-rate * x) * x =
      ∫ x in Ioi (0 : ℝ), rate * Real.exp (-rate * x) * x from
    setIntegral_congr_set Ioi_ae_eq_Ici.symm]
  simp_rw [show ∀ x, rate * Real.exp (-rate * x) * x = rate * (x * Real.exp (-rate * x))
    from fun x => by ring]
  rw [MeasureTheory.integral_const_mul, integral_mul_exp_neg_mul_Ioi rate hrate]
  field_simp

/-- Survival function of the exponential distribution: For `x ≥ 0`, `1 - F(x) = exp(-rate * x)`. -/
lemma ContDist.exponential_survival (rate : ℝ) (hrate : 0 < rate) (x : ℝ) (hx : 0 ≤ x) :
    1 - (ContDist.exponential rate hrate).cdf x = Real.exp (-rate * x) := by
  simp only [ContDist.cdf_eq_integral, ContDist.exponential_density]
  rw [show exponentialPDFReal rate = fun t => if t ≥ 0 then rate * Real.exp (-rate * t) else 0
    from (density_eq_exponentialPDFReal rate).symm]
  have h_ind : (fun t => if t ≥ 0 then rate * Real.exp (-rate * t) else 0) =
      (Ici (0 : ℝ)).indicator (fun t => rate * Real.exp (-rate * t)) := by
    ext t; simp [indicator_apply, ge_iff_le]
  rw [h_ind, setIntegral_indicator measurableSet_Ici,
      show Iic x ∩ Ici 0 = Icc 0 x from by ext t; simp [Iic, Ici, Icc]; tauto]
  rw [show ∫ t in Icc (0 : ℝ) x, rate * Real.exp (-rate * t) =
      ∫ t in (0 : ℝ)..x, rate * Real.exp (-rate * t) from by
    rw [intervalIntegral.integral_of_le hx]; exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  have h_ftc : ∫ t in (0 : ℝ)..x, rate * Real.exp (-rate * t) =
      1 - Real.exp (-rate * x) := by
    have h_deriv : ∀ t : ℝ, HasDerivAt (fun s => -Real.exp (-rate * s))
        (rate * Real.exp (-rate * t)) t := by
      intro t
      have h1 : HasDerivAt (fun s => -rate * s) (-rate) t := by
        simpa using (hasDerivAt_id t).const_mul (-rate)
      have h2 := (Real.hasDerivAt_exp (-rate * t)).comp t h1
      convert h2.neg using 1; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h_deriv t)
      ((continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id'))).intervalIntegrable _ _)]
    simp [Real.exp_zero]; ring
  linarith

/-- The CDF of the exponential distribution with rate `rate`: Equals `0` for `x < 0` and
`1 - exp(-rate * x)` for `x ≥ 0`. -/
lemma ContDist.exponential_cdf (rate : ℝ) (hrate : 0 < rate) (x : ℝ) :
    (ContDist.exponential rate hrate).cdf x =
      if x < 0 then 0 else 1 - Real.exp (-rate * x) := by
  by_cases hx : x < 0
  · rw [if_pos hx, ContDist.cdf_eq_integral]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    have ht_neg : t < 0 := lt_of_le_of_lt (by simpa using ht) hx
    simp [ContDist.exponential_density, exponentialPDFReal, gammaPDFReal, not_le.mpr ht_neg]
  · push Not at hx
    have hs := ContDist.exponential_survival rate hrate x hx
    rw [if_neg (not_lt.mpr hx)]
    linarith

/-- The variance of the exponential distribution with rate `rate` equals `1 / rate ^ 2`. -/
lemma ContDist.exponential_variance (rate : ℝ) (hrate : 0 < rate) :
    (ContDist.exponential rate hrate).variance id = 1 / rate ^ 2 := by
  simp only [ContDist.variance, ContDist.expect, id, ContDist.exponential_density]
  have h_sq : ∫ x, exponentialPDFReal rate x * x ^ 2 = 2 / rate ^ 2 := by
    rw [show exponentialPDFReal rate = fun x => if x ≥ 0 then rate * Real.exp (-rate * x) else 0
      from (density_eq_exponentialPDFReal rate).symm]
    have h_ind : (fun x => (if x ≥ 0 then rate * Real.exp (-rate * x) else 0) * x ^ 2) =
        (Ici (0 : ℝ)).indicator (fun x => rate * Real.exp (-rate * x) * x ^ 2) := by
      ext x
      simp only [Set.indicator_apply, ge_iff_le, mem_Ici]
      split_ifs with hx <;> ring
    rw [h_ind, integral_indicator measurableSet_Ici]
    rw [show ∫ x in Ici (0 : ℝ), rate * Real.exp (-rate * x) * x ^ 2 =
        ∫ x in Ioi (0 : ℝ), rate * Real.exp (-rate * x) * x ^ 2 from
      setIntegral_congr_set Ioi_ae_eq_Ici.symm]
    simp_rw [show ∀ x, rate * Real.exp (-rate * x) * x ^ 2 = rate * (x ^ 2 * Real.exp (-rate * x))
      from fun x => by ring]
    rw [integral_const_mul, integral_sq_mul_exp_neg_mul_Ioi rate hrate]
    field_simp
  rw [h_sq]
  have h_mean : ∫ x, exponentialPDFReal rate x * x = 1 / rate := by
    simpa [ContDist.expect, ContDist.exponential_density] using
      ContDist.exponential_expect rate hrate
  rw [h_mean]
  field_simp
  ring

/-- **Memorylessness of the exponential distribution:** for `s t ≥ 0`,
`P(X > s + t) / P(X > s) = P(X > t)`, where `X ~ Exp(rate)`. -/
lemma ContDist.exponential_memoryless (rate : ℝ) (hrate : 0 < rate) (s t : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) :
    let d := ContDist.exponential rate hrate
    (1 - d.cdf (s + t)) / (1 - d.cdf s) = 1 - d.cdf t := by
  simp only
  rw [ContDist.exponential_survival rate hrate (s + t) (by linarith),
      ContDist.exponential_survival rate hrate s hs,
      ContDist.exponential_survival rate hrate t ht,
      show -rate * (s + t) = -rate * s + -rate * t from by ring, Real.exp_add]
  exact mul_div_cancel_left₀ _ (Real.exp_pos _).ne'

end Econlib.Probability
