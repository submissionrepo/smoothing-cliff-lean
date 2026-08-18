/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.ContDist.CDF
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian distribution

This file constructs Gaussian distributions as `ContDist` (continuous distributions on `ℝ`) using
Mathlib's `gaussianPDFReal`, providing the normal distribution with explicit mean and variance
parameters and basic density, measure-compatibility, and moment lemmas.

## Main definitions

* `ContDist.gaussian`: Gaussian distribution with given mean and positive variance, as a `ContDist`.
* `ContDist.normal`: Alias for `ContDist.gaussian`.

## Main statements

* `ContDist.gaussian_toMeasure_eq`: The underlying measure equals Mathlib's `gaussianReal`.
* `ContDist.gaussian_isMode_mean`: The mean is a mode.
* `ContDist.gaussian_expect`: The expectation of the identity equals the mean.
* `ContDist.gaussian_variance`: The variance of the identity equals the variance parameter.
* `ContDist.gaussian_cdf`: The CDF is the integral of the Gaussian PDF over `(-∞, x]`.

## Tags

probability, continuous distributions, gaussian
-/

@[expose] public section

open ProbabilityTheory NNReal

namespace Econlib.Probability

/-- Coerce a positive real variance to `ℝ≥0`, packaging it as a nonneg subtype. -/
noncomputable def gaussianVarianceNNReal (variance : ℝ) (hvariance : 0 < variance) : ℝ≥0 :=
  ⟨variance, le_of_lt hvariance⟩

/-- The coercion of `gaussianVarianceNNReal` back to `ℝ` is the original variance. -/
@[simp] lemma gaussianVarianceNNReal_coe (variance : ℝ) (hvariance : 0 < variance) :
    (gaussianVarianceNNReal variance hvariance : ℝ) = variance := rfl

/-- A positive variance packaged as `gaussianVarianceNNReal` is nonzero. -/
lemma gaussianVarianceNNReal_ne_zero (variance : ℝ) (hvariance : 0 < variance) :
    gaussianVarianceNNReal variance hvariance ≠ 0 := by
  rw [← NNReal.coe_ne_zero, gaussianVarianceNNReal_coe]
  exact hvariance.ne'

/-- **Identifiability of affine coefficients under a nondegenerate Gaussian.** If two affine
functions of a real variable agree almost everywhere with respect to a Gaussian `N(m, s)` of
nonzero variance, their intercepts and slopes coincide. -/
theorem affine_eq_of_ae_eq_gaussianReal {m : ℝ} {s : ℝ≥0} (hs : s ≠ 0) {c₀ c₁ d₀ d₁ : ℝ}
    (h : (fun x : ℝ => c₀ + c₁ * x) =ᵐ[gaussianReal m s] fun x => d₀ + d₁ * x) :
    c₀ = d₀ ∧ c₁ = d₁ := by
  -- A nondegenerate Gaussian is mutually absolutely continuous with Lebesgue measure, so the
  -- a.e. equality transports to `volume`.
  have hvol : (fun x : ℝ => c₀ + c₁ * x) =ᵐ[MeasureTheory.volume] fun x => d₀ + d₁ * x :=
    (gaussianReal_absolutelyContinuous' m hs).ae_eq h
  have hcont₁ : Continuous fun x : ℝ => c₀ + c₁ * x :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hcont₂ : Continuous fun x : ℝ => d₀ + d₁ * x :=
    continuous_const.add (continuous_const.mul continuous_id)
  -- Continuous functions a.e.-equal under the full-support Lebesgue measure are equal everywhere.
  have heq : (fun x : ℝ => c₀ + c₁ * x) = fun x => d₀ + d₁ * x :=
    (hcont₁.ae_eq_iff_eq MeasureTheory.volume hcont₂).mp hvol
  have h0 : c₀ + c₁ * 0 = d₀ + d₁ * 0 := congrFun heq 0
  have h1 : c₀ + c₁ * 1 = d₀ + d₁ * 1 := congrFun heq 1
  exact ⟨by linarith, by linarith⟩

/-- Gaussian distribution with mean `mean` and positive variance `variance`, constructed as a
`ContDist` from the Gaussian PDF. -/
noncomputable def ContDist.gaussian (mean variance : ℝ) (hvariance : 0 < variance) :
    ContDist :=
  ContDist.ofPDFReal (gaussianPDFReal mean (gaussianVarianceNNReal variance hvariance))
    (gaussianPDFReal_nonneg mean (gaussianVarianceNNReal variance hvariance))
    (stronglyMeasurable_gaussianPDFReal mean (gaussianVarianceNNReal variance hvariance))
    (by
      rw [lintegral_gaussianPDFReal_eq_one]
      exact gaussianVarianceNNReal_ne_zero variance hvariance)

/-- `ContDist.normal` is an alias for `ContDist.gaussian`. -/
noncomputable abbrev ContDist.normal (mean variance : ℝ) (hvariance : 0 < variance) : ContDist :=
  ContDist.gaussian mean variance hvariance

/-- The density of the Gaussian distribution equals the Gaussian PDF. -/
@[simp] lemma ContDist.gaussian_density (mean variance : ℝ) (hvariance : 0 < variance) (x : ℝ) :
    (ContDist.gaussian mean variance hvariance).density x =
      gaussianPDFReal mean (gaussianVarianceNNReal variance hvariance) x := rfl

/-- The density of `ContDist.normal` equals the Gaussian PDF. -/
@[simp] lemma ContDist.normal_density (mean variance : ℝ) (hvariance : 0 < variance) (x : ℝ) :
    (ContDist.normal mean variance hvariance).density x =
      gaussianPDFReal mean (gaussianVarianceNNReal variance hvariance) x := rfl

/-- The underlying measure of the Gaussian distribution equals Mathlib's `gaussianReal`. -/
@[simp] lemma ContDist.gaussian_toMeasure_eq (mean variance : ℝ) (hvariance : 0 < variance) :
    (ContDist.gaussian mean variance hvariance).toMeasure =
      gaussianReal mean (gaussianVarianceNNReal variance hvariance) := by
  rw [ContDist.toMeasure_eq,
    gaussianReal_of_var_ne_zero mean (gaussianVarianceNNReal_ne_zero variance hvariance),
    gaussianPDF_def]
  congr 1

/-- The mean is a mode of the Gaussian distribution: The density is maximized where the squared
deviation in the exponent vanishes. -/
lemma ContDist.gaussian_isMode_mean (mean variance : ℝ) (hvariance : 0 < variance) :
    (ContDist.gaussian mean variance hvariance).IsMode mean := by
  intro x
  rw [ContDist.gaussian_density, ContDist.gaussian_density]
  unfold gaussianPDFReal
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Real.exp_le_exp]
  exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (x - mean)]) (by positivity)

/-- The expectation of the identity under the Gaussian distribution equals the mean. -/
lemma ContDist.gaussian_expect (mean variance : ℝ) (hvariance : 0 < variance) :
    (ContDist.gaussian mean variance hvariance).expect id = mean := by
  rw [ContDist.expect_eq_measure_integral, ContDist.gaussian_toMeasure_eq]
  simp [integral_id_gaussianReal]

/-- The variance of the identity under the Gaussian distribution equals the variance parameter. -/
lemma ContDist.gaussian_variance (mean variance : ℝ) (hvariance : 0 < variance) :
    (ContDist.gaussian mean variance hvariance).variance id = variance := by
  rw [ContDist.variance]
  rw [ContDist.expect_eq_measure_integral, ContDist.expect_eq_measure_integral,
    ContDist.gaussian_toMeasure_eq]
  have h_var : Var[id; gaussianReal mean (gaussianVarianceNNReal variance hvariance)] =
      gaussianVarianceNNReal variance hvariance := by
    simp [variance_id_gaussianReal]
  rw [variance_eq_sub (by
    simpa using memLp_id_gaussianReal (μ := mean)
      (v := gaussianVarianceNNReal variance hvariance) 2)] at h_var
  simpa using h_var

/-- The CDF of the Gaussian distribution at `x` equals the integral of the Gaussian PDF over
`(-∞, x]`. -/
lemma ContDist.gaussian_cdf (mean variance : ℝ) (hvariance : 0 < variance) (x : ℝ) :
    (ContDist.gaussian mean variance hvariance).cdf x =
      ∫ t in Set.Iic x, gaussianPDFReal mean (gaussianVarianceNNReal variance hvariance) t := by
  simp [ContDist.cdf_eq_integral, ContDist.gaussian_density]

end Econlib.Probability
