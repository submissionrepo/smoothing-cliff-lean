/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Distributions.Gaussian

/-!
# Log-normal distribution

This file defines the log-normal density, constructs the associated continuous and nonnegative-real
distributions, and proves normalization and moment formulas.

## Main definitions

* `logNormalPDFReal`: Real-valued log-normal density.
* `ContDist.logNormal`: Log-normal distribution as a continuous distribution.

## Main statements

* `integral_logNormalPDFReal_eq_one`: Normalization of the density.
* `ContDist.logNormal_cdf`: The CDF is zero for `x ≤ 0` and the Gaussian CDF at `log x` for `x > 0`.
* `ContDist.logNormal_expect`: Expectation formula `exp(mean + variance / 2)`.
* `ContDist.logNormal_variance`: Variance formula `(exp(variance) - 1) · exp(2·mean + variance)`.

## Tags

probability, continuous distributions, log-normal
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace Econlib.Probability

/-- Coercion of a positive real `variance` to `ℝ≥0`, used as the variance parameter for the
underlying Gaussian density in the log-normal construction. -/
noncomputable def logNormalVarianceNNReal (variance : ℝ) (hvariance : 0 < variance) :
    ℝ≥0 :=
  ⟨variance, le_of_lt hvariance⟩

/-- `logNormalVarianceNNReal variance hvariance` is nonzero whenever `0 < variance`. -/
lemma logNormalVarianceNNReal_ne_zero (variance : ℝ) (hvariance : 0 < variance) :
    logNormalVarianceNNReal variance hvariance ≠ 0 := by
  simp only [ne_eq, ← NNReal.coe_eq_zero, logNormalVarianceNNReal, NNReal.coe_mk]
  exact hvariance.ne'

/-- The positive-branch density of the log-normal distribution. -/
noncomputable def logNormalPDFPos (mean variance : ℝ) (hvariance : 0 < variance) (x : ℝ) :
    ℝ :=
  gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) (Real.log x) / x

/-- Density of the log-normal distribution with log-mean `mean` and log-variance `variance`. -/
noncomputable def logNormalPDFReal (mean variance : ℝ) (hvariance : 0 < variance) (x : ℝ) : ℝ :=
  (Ioi 0).indicator (logNormalPDFPos mean variance hvariance) x

/-- The change-of-variables identity `t = exp x` turns the positive-branch density into the
Gaussian density: `|exp x| • logNormalPDFPos (exp x) = gaussianPDFReal x`. This is the common
Jacobian computation reused by every integral over the log-normal density. -/
private lemma exp_smul_logNormalPDFPos (mean variance : ℝ) (hvariance : 0 < variance) (x : ℝ) :
    |Real.exp x| • logNormalPDFPos mean variance hvariance (Real.exp x) =
      gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) x := by
  rw [abs_of_pos (Real.exp_pos x), smul_eq_mul]
  unfold logNormalPDFPos
  rw [Real.log_exp]
  field_simp [show Real.exp x ≠ 0 by positivity]

/-- The log-normal density `logNormalPDFReal` is everywhere nonneg. -/
lemma logNormalPDFReal_nonneg (mean variance : ℝ) (hvariance : 0 < variance) (x : ℝ) :
    0 ≤ logNormalPDFReal mean variance hvariance x := by
  unfold logNormalPDFReal
  by_cases hx : 0 < x
  · simp [hx, logNormalPDFPos, gaussianPDFReal_nonneg, div_nonneg, le_of_lt hx]
  · simp [hx]

/-- On the positive half-line, `logNormalPDFReal` equals the Gaussian density composed with `log`
divided by `x`. -/
lemma logNormalPDFReal_of_pos (mean variance : ℝ) (hvariance : 0 < variance) {x : ℝ}
    (hx : 0 < x) :
    logNormalPDFReal mean variance hvariance x =
      gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) (Real.log x) / x := by
  simp [logNormalPDFReal, logNormalPDFPos, hx]

/-- `logNormalPDFReal` is zero on the non-positive half-line. -/
lemma logNormalPDFReal_of_nonpos (mean variance : ℝ) (hvariance : 0 < variance) {x : ℝ}
    (hx : x ≤ 0) : logNormalPDFReal mean variance hvariance x = 0 := by
  simp [logNormalPDFReal, not_lt.mpr hx]

/-- The log-normal density is Borel measurable. -/
lemma measurable_logNormalPDFReal (mean variance : ℝ) (hvariance : 0 < variance) :
    Measurable (logNormalPDFReal mean variance hvariance) := by
  unfold logNormalPDFReal logNormalPDFPos
  refine Measurable.indicator ?_ measurableSet_Ioi
  fun_prop

/-- The log-normal density is strongly measurable. -/
lemma stronglyMeasurable_logNormalPDFReal (mean variance : ℝ) (hvariance : 0 < variance) :
    StronglyMeasurable (logNormalPDFReal mean variance hvariance) :=
  (measurable_logNormalPDFReal mean variance hvariance).stronglyMeasurable

private lemma integral_gaussianReal_eq_integral_gaussianPDFReal_mul
    (mean variance : ℝ) (hvariance : 0 < variance) (g : ℝ → ℝ) :
    ∫ x, g x ∂gaussianReal mean (logNormalVarianceNNReal variance hvariance) =
      ∫ x, gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) x * g x := by
  rw [gaussianReal_of_var_ne_zero mean (logNormalVarianceNNReal_ne_zero variance hvariance),
    gaussianPDF_def]
  rw [integral_withDensity_eq_integral_toReal_smul
    (μ := volume)
    (f := fun x => ENNReal.ofReal
      (gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) x))
    (by fun_prop) (ae_of_all _ fun x => by simp)]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal
    (gaussianPDFReal_nonneg mean (logNormalVarianceNNReal variance hvariance) x),
    smul_eq_mul]

private lemma integrableOn_logNormalPDFPos (mean variance : ℝ) (hvariance : 0 < variance) :
    IntegrableOn (logNormalPDFPos mean variance hvariance) (Ioi 0) := by
  have hchange :=
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := (univ : Set ℝ)) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn
      (logNormalPDFPos mean variance hvariance)
  have hfun :
      (fun x : ℝ => |Real.exp x| • logNormalPDFPos mean variance hvariance (Real.exp x)) =
        fun x => gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) x :=
    funext (exp_smul_logNormalPDFPos mean variance hvariance)
  have hgauss :
      Integrable (fun x : ℝ =>
        gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) x) := by
    simpa using integrable_gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance)
  have hright :
      IntegrableOn (fun x : ℝ =>
        |Real.exp x| • logNormalPDFPos mean variance hvariance (Real.exp x))
        univ := by
    rw [integrableOn_univ]
    exact hgauss.congr (Filter.Eventually.of_forall fun x => (congrFun hfun x).symm)
  have hleft := hchange.mpr hright
  simpa [Set.image_univ, Real.range_exp] using hleft

private lemma integrable_logNormalPDFReal (mean variance : ℝ) (hvariance : 0 < variance) :
    Integrable (logNormalPDFReal mean variance hvariance) := by
  unfold logNormalPDFReal
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact integrableOn_logNormalPDFPos mean variance hvariance

private lemma integral_logNormalPDFPos_eq_one (mean variance : ℝ) (hvariance : 0 < variance) :
    ∫ x in Ioi (0 : ℝ), logNormalPDFPos mean variance hvariance x = 1 := by
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      (s := (univ : Set ℝ)) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn
      (logNormalPDFPos mean variance hvariance)
  calc
    ∫ x in Ioi (0 : ℝ), logNormalPDFPos mean variance hvariance x
      = ∫ x, |Real.exp x| • logNormalPDFPos mean variance hvariance (Real.exp x) := by
          simpa [Set.image_univ, Real.range_exp] using hchange
      _ = ∫ x, gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) x := by
          simp_rw [exp_smul_logNormalPDFPos]
      _ = 1 :=
          integral_gaussianPDFReal_eq_one mean
            (logNormalVarianceNNReal_ne_zero variance hvariance)

/-- The log-normal density integrates to one: It is a probability density. -/
theorem integral_logNormalPDFReal_eq_one (mean variance : ℝ) (hvariance : 0 < variance) :
    ∫ x, logNormalPDFReal mean variance hvariance x = 1 := by
  unfold logNormalPDFReal
  rw [integral_indicator measurableSet_Ioi]
  exact integral_logNormalPDFPos_eq_one mean variance hvariance

/-- The lower Lebesgue integral of the log-normal density (lifted to `ℝ≥0∞`) equals one. -/
lemma lintegral_logNormalPDFReal_eq_one (mean variance : ℝ) (hvariance : 0 < variance) :
    ∫⁻ x, ENNReal.ofReal (logNormalPDFReal mean variance hvariance x) = 1 := by
  rw [← ENNReal.ofReal_one, ← integral_logNormalPDFReal_eq_one mean variance hvariance]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_logNormalPDFReal mean variance hvariance)
    (ae_of_all _ (logNormalPDFReal_nonneg mean variance hvariance))).symm

/-- Log-normal distribution with log-mean `mean` and log-variance `variance`. -/
noncomputable def ContDist.logNormal (mean variance : ℝ) (hvariance : 0 < variance) : ContDist :=
  ContDist.ofPDFReal (logNormalPDFReal mean variance hvariance)
    (logNormalPDFReal_nonneg mean variance hvariance)
    (stronglyMeasurable_logNormalPDFReal mean variance hvariance)
    (lintegral_logNormalPDFReal_eq_one mean variance hvariance)

/-- The log-normal density vanishes on negative arguments. -/
lemma ContDist.logNormal_density_eq_zero_of_neg (mean variance : ℝ) (hvariance : 0 < variance)
    {x : ℝ} (hx : x < 0) : (ContDist.logNormal mean variance hvariance).density x = 0 :=
  logNormalPDFReal_of_nonpos mean variance hvariance (le_of_lt hx)

/-- The density function of `ContDist.logNormal` unfolds to `logNormalPDFReal`. -/
@[simp] lemma ContDist.logNormal_density (mean variance : ℝ) (hvariance : 0 < variance) (x : ℝ) :
    (ContDist.logNormal mean variance hvariance).density x =
      logNormalPDFReal mean variance hvariance x :=
  rfl

/-- The density of `ContDist.logNormal` is zero at non-positive arguments. -/
lemma ContDist.logNormal_density_eq_zero_of_nonpos (mean variance : ℝ) (hvariance : 0 < variance)
    {x : ℝ} (hx : x ≤ 0) :
    (ContDist.logNormal mean variance hvariance).density x = 0 := by
  rw [ContDist.logNormal_density]
  exact logNormalPDFReal_of_nonpos mean variance hvariance hx

/-- CDF of the log-normal distribution: It equals zero for `x ≤ 0`, and for `x > 0` it equals the
Gaussian CDF evaluated at `log x`. -/
theorem ContDist.logNormal_cdf (mean variance : ℝ) (hvariance : 0 < variance) (x : ℝ) :
    (ContDist.logNormal mean variance hvariance).cdf x =
      if x ≤ 0 then 0
      else (ContDist.gaussian mean variance hvariance).cdf (Real.log x) := by
  by_cases hx : x ≤ 0
  · rw [if_pos hx, ContDist.cdf_eq_integral]
    change ∫ t in Iic x, logNormalPDFReal mean variance hvariance t = 0
    trans ∫ t in Iic x, (0 : ℝ)
    · apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
      exact logNormalPDFReal_of_nonpos mean variance hvariance (le_trans ht hx)
    · simp
  · have hx_pos : 0 < x := lt_of_not_ge hx
    have hinter : Iic x ∩ Ioi (0 : ℝ) = Ioc (0 : ℝ) x := by
      ext t
      simp [and_comm]
    have himage : Real.exp '' Iic (Real.log x) = Ioc (0 : ℝ) x := by
      rw [show Real.exp = Subtype.val ∘ Real.expOrderIso by
            ext t
            simp [Function.comp, Real.coe_expOrderIso_apply]]
      rw [Set.image_comp]
      rw [OrderIso.image_Iic]
      rw [Set.image_subtype_val_Ioi_Iic (b := Real.expOrderIso (Real.log x))]
      simp [Real.coe_expOrderIso_apply, Real.exp_log hx_pos]
    rw [if_neg hx, ContDist.cdf_eq_integral]
    change ∫ t in Iic x, logNormalPDFReal mean variance hvariance t =
      (ContDist.gaussian mean variance hvariance).cdf (Real.log x)
    calc
      ∫ t in Iic x, logNormalPDFReal mean variance hvariance t
        = ∫ t in Iic x ∩ Ioi (0 : ℝ), logNormalPDFPos mean variance hvariance t := by
            rw [show logNormalPDFReal mean variance hvariance =
                (Ioi (0 : ℝ)).indicator (logNormalPDFPos mean variance hvariance) by rfl]
            rw [setIntegral_indicator measurableSet_Ioi]
        _ = ∫ t in Ioc (0 : ℝ) x, logNormalPDFPos mean variance hvariance t := by
            rw [hinter]
        _ = ∫ t in Real.exp '' Iic (Real.log x), logNormalPDFPos mean variance hvariance t := by
            rw [himage]
        _ = ∫ u in Iic (Real.log x),
              |Real.exp u| • logNormalPDFPos mean variance hvariance (Real.exp u) := by
            simpa using
              (integral_image_eq_integral_abs_deriv_smul
                (s := Iic (Real.log x)) (f := Real.exp) (f' := Real.exp)
                measurableSet_Iic
                (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt)
                Real.exp_injective.injOn
                (logNormalPDFPos mean variance hvariance))
        _ = ∫ u in Iic (Real.log x),
              (ContDist.gaussian mean variance hvariance).density u := by
            simp_rw [exp_smul_logNormalPDFPos]
            rfl
        _ = (ContDist.gaussian mean variance hvariance).cdf (Real.log x) := by
            rw [ContDist.cdf_eq_integral]

/-- The CDF of the log-normal distribution is zero at non-positive arguments. -/
lemma ContDist.logNormal_cdf_of_nonpos (mean variance : ℝ) (hvariance : 0 < variance)
    {x : ℝ} (hx : x ≤ 0) :
    (ContDist.logNormal mean variance hvariance).cdf x = 0 := by
  simp [ContDist.logNormal_cdf, hx]

/-- For positive `x`, the CDF of the log-normal distribution equals the Gaussian CDF at `log x`. -/
lemma ContDist.logNormal_cdf_of_pos (mean variance : ℝ) (hvariance : 0 < variance)
    {x : ℝ} (hx : 0 < x) :
    (ContDist.logNormal mean variance hvariance).cdf x =
      (ContDist.gaussian mean variance hvariance).cdf (Real.log x) := by
  simp [ContDist.logNormal_cdf, not_le.mpr hx]

private lemma integral_logNormalPDFReal_mul_eq (mean variance : ℝ) (hvariance : 0 < variance) :
    ∫ x, logNormalPDFReal mean variance hvariance x * x = Real.exp (mean + variance / 2) := by
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      (s := (univ : Set ℝ)) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn
      (fun x => logNormalPDFPos mean variance hvariance x * x)
  have hfun :
      (fun x : ℝ =>
        |Real.exp x| • (logNormalPDFPos mean variance hvariance (Real.exp x) * Real.exp x)) =
        fun x =>
          gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) x * Real.exp x := by
    funext x
    rw [← smul_mul_assoc, exp_smul_logNormalPDFPos]
  have hpdf_mul :
      (fun x : ℝ => logNormalPDFReal mean variance hvariance x * x) =
        (Ioi 0).indicator (fun x => logNormalPDFPos mean variance hvariance x * x) := by
    funext x
    by_cases hx : 0 < x
    · simp [logNormalPDFReal, logNormalPDFPos, hx]
    · simp [logNormalPDFReal, hx]
  calc
    ∫ x, logNormalPDFReal mean variance hvariance x * x
      = ∫ x in Ioi (0 : ℝ), logNormalPDFPos mean variance hvariance x * x := by
          rw [hpdf_mul, integral_indicator measurableSet_Ioi]
      _ = ∫ x, |Real.exp x| •
            (logNormalPDFPos mean variance hvariance (Real.exp x) * Real.exp x) := by
          simpa [Set.image_univ, Real.range_exp] using hchange
      _ = ∫ x, gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) x *
            Real.exp x := by
          apply integral_congr_ae
          filter_upwards with x
          exact congrFun hfun x
      _ = ∫ x, Real.exp x ∂gaussianReal mean (logNormalVarianceNNReal variance hvariance) := by
          symm
          exact integral_gaussianReal_eq_integral_gaussianPDFReal_mul
            mean variance hvariance Real.exp
      _ = Real.exp (mean + variance / 2) := by
          have hmgf :=
            congrFun (ProbabilityTheory.mgf_id_gaussianReal
              (μ := mean) (v := logNormalVarianceNNReal variance hvariance)) 1
          simpa [ProbabilityTheory.mgf, logNormalVarianceNNReal] using hmgf

private lemma integral_logNormalPDFReal_sq_eq (mean variance : ℝ) (hvariance : 0 < variance) :
    ∫ x, logNormalPDFReal mean variance hvariance x * x ^ 2 =
      Real.exp (2 * mean + 2 * variance) := by
  have hchange :=
    integral_image_eq_integral_abs_deriv_smul
      (s := (univ : Set ℝ)) (f := Real.exp) (f' := Real.exp)
      MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn
      (fun x => logNormalPDFPos mean variance hvariance x * x ^ 2)
  have hfun :
      (fun x : ℝ =>
        |Real.exp x| •
          (logNormalPDFPos mean variance hvariance (Real.exp x) * (Real.exp x) ^ 2)) =
        fun x =>
          gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) x *
            Real.exp (2 * x) := by
    funext x
    rw [← smul_mul_assoc, exp_smul_logNormalPDFPos, ← Real.exp_nat_mul, Nat.cast_ofNat]
  have hpdf_sq :
      (fun x : ℝ => logNormalPDFReal mean variance hvariance x * x ^ 2) =
        (Ioi 0).indicator (fun x => logNormalPDFPos mean variance hvariance x * x ^ 2) := by
    funext x
    by_cases hx : 0 < x
    · simp [logNormalPDFReal, logNormalPDFPos, hx]
    · simp [logNormalPDFReal, hx]
  calc
    ∫ x, logNormalPDFReal mean variance hvariance x * x ^ 2
      = ∫ x in Ioi (0 : ℝ), logNormalPDFPos mean variance hvariance x * x ^ 2 := by
          rw [hpdf_sq, integral_indicator measurableSet_Ioi]
      _ = ∫ x, |Real.exp x| •
              (logNormalPDFPos mean variance hvariance (Real.exp x) * (Real.exp x) ^ 2) := by
          simpa [Set.image_univ, Real.range_exp] using hchange
      _ = ∫ x, gaussianPDFReal mean (logNormalVarianceNNReal variance hvariance) x *
              Real.exp (2 * x) := by
          apply integral_congr_ae
          filter_upwards with x
          exact congrFun hfun x
      _ = ∫ x, Real.exp (2 * x)
            ∂gaussianReal mean (logNormalVarianceNNReal variance hvariance) := by
          symm
          exact integral_gaussianReal_eq_integral_gaussianPDFReal_mul
            mean variance hvariance (fun x => Real.exp (2 * x))
      _ = Real.exp (2 * mean + 2 * variance) := by
          have hmgf :=
            congrFun (ProbabilityTheory.mgf_id_gaussianReal
              (μ := mean) (v := logNormalVarianceNNReal variance hvariance)) 2
          calc
            ∫ x, Real.exp (2 * x) ∂gaussianReal mean (logNormalVarianceNNReal variance hvariance)
              = ProbabilityTheory.mgf id
                  (gaussianReal mean (logNormalVarianceNNReal variance hvariance)) 2 := by
                    simp [ProbabilityTheory.mgf]
              _ = Real.exp (mean * 2 + variance * 2 ^ 2 / 2) := by
                    simpa [logNormalVarianceNNReal] using hmgf
              _ = Real.exp (2 * mean + 2 * variance) := by
                    congr 1
                    ring

/-- **Expectation formula:** The mean of the log-normal distribution with log-mean `mean` and
log-variance `variance` is `exp(mean + variance / 2)`. -/
theorem ContDist.logNormal_expect (mean variance : ℝ) (hvariance : 0 < variance) :
    (ContDist.logNormal mean variance hvariance).expect id = Real.exp (mean + variance / 2) := by
  simpa [ContDist.expect, id, ContDist.logNormal_density] using
    integral_logNormalPDFReal_mul_eq mean variance hvariance

/-- **Variance formula:** The variance of the log-normal distribution with log-mean `mean` and
log-variance `variance` is `(exp(variance) - 1) * exp(2 * mean + variance)`. -/
theorem ContDist.logNormal_variance (mean variance : ℝ) (hvariance : 0 < variance) :
    (ContDist.logNormal mean variance hvariance).variance id =
      (Real.exp variance - 1) * Real.exp (2 * mean + variance) := by
  rw [ContDist.variance, ContDist.logNormal_expect mean variance hvariance]
  change
    (∫ x, logNormalPDFReal mean variance hvariance x * x ^ 2) -
      Real.exp (mean + variance / 2) ^ 2 =
      (Real.exp variance - 1) * Real.exp (2 * mean + variance)
  rw [integral_logNormalPDFReal_sq_eq mean variance hvariance]
  rw [pow_two, ← Real.exp_add]
  have hsquare : (mean + variance / 2) + (mean + variance / 2) = 2 * mean + variance := by
    ring
  rw [hsquare]
  have hexp :
      Real.exp (2 * mean + 2 * variance) =
        Real.exp (2 * mean + variance) * Real.exp variance := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

end Econlib.Probability
