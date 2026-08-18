/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.ContDist.CDF
public import Mathlib.Probability.Distributions.Gamma

/-!
# Gamma distribution

This file constructs gamma distributions as continuous and nonnegative-real distributions and
records density, expectation, variance, and CDF facts.

## Main definitions

* `ContDist.gamma`: Gamma distribution as a continuous distribution on `Real`.

## Main statements

* `ContDist.gamma_expect`: Expectation formula.
* `ContDist.gamma_variance`: Variance formula.
* `ContDist.gamma_cdf`: CDF formula.

## Tags

probability, continuous distributions, gamma
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Econlib.Probability

/-- The `ENNReal`-valued lift of `gammaPDFReal` agrees pointwise with `gammaPDF`. -/
lemma ofReal_gammaPDFReal_eq_gammaPDF (shape rate : ℝ) :
    (fun x => ENNReal.ofReal (gammaPDFReal shape rate x)) = gammaPDF shape rate := by
  ext x
  rw [gammaPDF_eq]
  simp [gammaPDFReal]

/-- The Gamma distribution with shape parameter `shape` and rate parameter `rate`, constructed as a
`ContDist` via its probability density function `gammaPDFReal`. -/
noncomputable def ContDist.gamma (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) :
    ContDist :=
  ContDist.ofPDFReal (gammaPDFReal shape rate)
    (gammaPDFReal_nonneg hshape hrate)
    (stronglyMeasurable_gammaPDFReal shape rate)
    (by rw [ofReal_gammaPDFReal_eq_gammaPDF, lintegral_gammaPDF_eq_one hshape hrate])

/-- The density of the Gamma distribution is zero on `(-∞, 0)`. -/
lemma ContDist.gamma_density_eq_zero_of_neg (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate)
    {x : ℝ} (hx : x < 0) : (ContDist.gamma shape rate hshape hrate).density x = 0 := by
  change gammaPDFReal shape rate x = 0
  simp [gammaPDFReal, show ¬0 ≤ x from by linarith]

/-- The density of `ContDist.gamma` is `gammaPDFReal`. -/
@[simp] lemma ContDist.gamma_density (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate)
    (x : ℝ) : (ContDist.gamma shape rate hshape hrate).density x = gammaPDFReal shape rate x := rfl

/-- The Gamma PDF integrates to one over `ℝ`. -/
lemma integral_gammaPDFReal_eq_one (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) :
    ∫ x, gammaPDFReal shape rate x = 1 :=
  (ContDist.gamma shape rate hshape hrate).integral_one

private lemma gamma_ratio (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) :
    rate ^ (shape + 1) / Real.Gamma (shape + 1) =
      (rate / shape) * (rate ^ shape / Real.Gamma shape) := by
  rw [Real.Gamma_add_one (ne_of_gt hshape), Real.rpow_add_one hrate.ne']
  field_simp [ne_of_gt hshape, ne_of_gt hrate]

private lemma gammaPDFReal_mul_id (shape rate x : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) :
    gammaPDFReal shape rate x * x = (shape / rate) * gammaPDFReal (shape + 1) rate x := by
  by_cases hx : 0 ≤ x
  · by_cases hx0 : x = 0
    · subst hx0
      simp [gammaPDFReal, hshape.ne']
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      rw [gammaPDFReal, if_pos hx, gammaPDFReal, if_pos hx]
      have hxpow : x ^ (shape - 1) * x = x ^ shape := by
        rw [← Real.rpow_add_one hx0, sub_add_cancel]
      rw [show (shape + 1 - 1 : ℝ) = shape by ring,
        show rate ^ shape / Real.Gamma shape * x ^ (shape - 1) * Real.exp (-(rate * x)) * x =
          rate ^ shape / Real.Gamma shape * (x ^ (shape - 1) * x) * Real.exp (-(rate * x)) by ring,
        hxpow, gamma_ratio shape rate hshape hrate]
      field_simp [ne_of_gt hshape, ne_of_gt hrate]
  · simp [gammaPDFReal, hx]

private lemma gammaPDFReal_mul_sq (shape rate x : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) :
    gammaPDFReal shape rate x * x ^ 2 =
      (shape * (shape + 1) / rate ^ 2) * gammaPDFReal (shape + 2) rate x := by
  by_cases hx : 0 ≤ x
  · by_cases hx0 : x = 0
    · subst hx0
      have hshape2 : shape + 2 - 1 ≠ 0 := by linarith
      simp [gammaPDFReal, hshape2]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      rw [gammaPDFReal, if_pos hx, gammaPDFReal, if_pos hx]
      have hshape1 : 0 < shape + 1 := by linarith
      have hrpow : x ^ (shape - 1) * x ^ 2 = x ^ (shape + 1) := by
        rw [← Real.rpow_natCast x 2, ← Real.rpow_add hxpos]
        congr 1
        ring
      rw [show (shape + 2 - 1 : ℝ) = shape + 1 by ring,
       show rate ^ shape / Real.Gamma shape * x ^ (shape - 1) * Real.exp (-(rate * x)) * x ^ 2 =
       rate ^ shape / Real.Gamma shape * (x ^ (shape - 1) * x ^ 2) * Real.exp (-(rate * x)) by ring,
       hrpow]
      rw [show rate ^ (shape + 2) / Real.Gamma (shape + 2) =
          (rate ^ 2 / (shape * (shape + 1))) * (rate ^ shape / Real.Gamma shape) from by
        rw [show shape + 2 = (shape + 1) + 1 by ring, Real.Gamma_add_one (ne_of_gt hshape1),
          Real.Gamma_add_one (ne_of_gt hshape)]
        have hrpow2 : rate ^ (shape + 1 + 1) = rate ^ 2 * rate ^ shape := by
          calc
            rate ^ (shape + 1 + 1) = rate ^ (shape + 2) := by congr 1; ring
            _ = rate ^ shape * rate ^ (2 : ℝ) := by rw [Real.rpow_add hrate]
            _ = rate ^ 2 * rate ^ shape := by simp [mul_comm]
        rw [hrpow2]
        field_simp [ne_of_gt hshape, ne_of_gt hshape1, ne_of_gt hrate]
      ]
      field_simp [ne_of_gt hshape, ne_of_gt hshape1, ne_of_gt hrate]
  · simp [gammaPDFReal, hx]

/-- The expectation of the Gamma distribution with shape `shape` and rate `rate` is
`shape / rate`. -/
lemma ContDist.gamma_expect (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) :
    (ContDist.gamma shape rate hshape hrate).expect id = shape / rate := by
  simp only [ContDist.expect, id, ContDist.gamma_density]
  have hshape1 : 0 < shape + 1 := by linarith
  have hmul : (fun x => gammaPDFReal shape rate x * x) =
      fun x => (shape / rate) * gammaPDFReal (shape + 1) rate x :=
    funext (fun x => gammaPDFReal_mul_id shape rate x hshape hrate)
  rw [hmul, integral_const_mul,
    integral_gammaPDFReal_eq_one (shape + 1) rate hshape1 hrate, mul_one]

/-- The variance of the Gamma distribution with shape `shape` and rate `rate` is
`shape / rate ^ 2`. -/
lemma ContDist.gamma_variance (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) :
    (ContDist.gamma shape rate hshape hrate).variance id = shape / rate ^ 2 := by
  simp only [ContDist.variance, ContDist.expect, id, ContDist.gamma_density]
  have hshape2 : 0 < shape + 2 := by linarith
  have hshape1 : 0 < shape + 1 := by linarith
  have hsq : (fun x => gammaPDFReal shape rate x * x ^ 2) =
      fun x => (shape * (shape + 1) / rate ^ 2) * gammaPDFReal (shape + 2) rate x :=
    funext (fun x => gammaPDFReal_mul_sq shape rate x hshape hrate)
  rw [hsq, integral_const_mul, integral_gammaPDFReal_eq_one (shape + 2) rate hshape2 hrate, mul_one]
  have hmul : (fun x => gammaPDFReal shape rate x * x) =
      fun x => (shape / rate) * gammaPDFReal (shape + 1) rate x :=
    funext (fun x => gammaPDFReal_mul_id shape rate x hshape hrate)
  rw [hmul, integral_const_mul,
    integral_gammaPDFReal_eq_one (shape + 1) rate hshape1 hrate, mul_one]
  field_simp [ne_of_gt hrate]
  ring

/-- The CDF of the Gamma distribution at `x` equals the integral of `gammaPDFReal` over
`(-∞, x]`. -/
lemma ContDist.gamma_cdf (shape rate : ℝ) (hshape : 0 < shape) (hrate : 0 < rate) (x : ℝ) :
    (ContDist.gamma shape rate hshape hrate).cdf x = ∫ t in Set.Iic x, gammaPDFReal shape rate t :=
  by simp [ContDist.cdf_eq_integral, ContDist.gamma_density]

end Econlib.Probability
