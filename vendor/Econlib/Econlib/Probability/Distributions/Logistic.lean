/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.IntegralIdentities
public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.ContDist.CDF
public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import Mathlib.NumberTheory.ZetaValues

/-!
# Logistic distribution

This file defines logistic CDF and density functions, constructs logistic distributions, and proves
CDF, density, expectation, and variance formulas.

## Main definitions

* `logisticCDFReal`: Real-valued logistic CDF.
* `logisticPDFReal`: Real-valued logistic density.
* `ContDist.logistic`: Logistic distribution as a continuous distribution.

## Main statements

* `ContDist.logistic_isMode_mean`: The mean is a mode.
* `ContDist.logistic_cdf`: CDF formula.
* `ContDist.logistic_expect`: Expectation formula.
* `ContDist.logistic_variance`: Variance formula.

## Tags

probability, continuous distributions, logistic
-/

@[expose] public section

open Set MeasureTheory Real Filter

namespace Econlib.Probability

/-- The CDF of the logistic distribution with location `mean` and scale `scale`, given by
`σ((x - mean) / scale)` where `σ` is the sigmoid (logistic) function. -/
noncomputable def logisticCDFReal (mean scale : ℝ) (x : ℝ) : ℝ :=
  Real.sigmoid ((x - mean) / scale)

/-- The PDF of the logistic distribution with location `mean` and scale `scale`, given by
`σ(z) * (1 - σ(z)) / scale` where `z = (x - mean) / scale` and `σ` is the sigmoid function. -/
noncomputable def logisticPDFReal (mean scale : ℝ) (x : ℝ) : ℝ :=
  (Real.sigmoid ((x - mean) / scale) * (1 - Real.sigmoid ((x - mean) / scale))) / scale

/-- The logistic density is nonneg for positive scale. -/
lemma logisticPDFReal_nonneg (mean scale x : ℝ) (hscale : 0 < scale) :
    0 ≤ logisticPDFReal mean scale x := by
  unfold logisticPDFReal
  refine div_nonneg ?_ (le_of_lt hscale)
  exact mul_nonneg (Real.sigmoid_nonneg _) (sub_nonneg.mpr (Real.sigmoid_le_one _))

/-- The logistic CDF is differentiable, with derivative equal to the logistic density. -/
lemma hasDerivAt_logisticCDFReal (mean scale : ℝ) (hscale : 0 < scale) (x : ℝ) :
    HasDerivAt (logisticCDFReal mean scale) (logisticPDFReal mean scale x) x := by
  have hinner : HasDerivAt (fun y : ℝ => (y - mean) / scale) (1 / scale) x := by
    simpa using ((hasDerivAt_id x).sub_const mean).div_const scale
  have hsig := (Real.hasDerivAt_sigmoid ((x - mean) / scale)).comp x hinner
  have hscale_ne : scale ≠ 0 := by linarith
  simpa [logisticCDFReal, logisticPDFReal, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
    hscale_ne] using hsig

/-- The logistic CDF is continuous. -/
lemma continuous_logisticCDFReal (mean scale : ℝ) :
    Continuous (logisticCDFReal mean scale) := by
  unfold logisticCDFReal
  fun_prop

/-- The logistic distribution's CDF as a `CDF` structure, with location `mean` and scale `scale`. -/
noncomputable def logisticCDF (mean scale : ℝ) (hscale : 0 < scale) : CDF where
  toStieltjesFunction :=
    { toFun := logisticCDFReal mean scale
      mono' := by
        intro a b hab
        unfold logisticCDFReal
        gcongr
      right_continuous' := by
        intro x
        exact (continuous_logisticCDFReal mean scale).continuousAt.continuousWithinAt }
  tendsto_bot := by
    have hsub : Tendsto (fun x : ℝ => x - mean) atBot atBot := by
      simpa [sub_eq_add_neg] using tendsto_atBot_add_const_right atBot (-mean) tendsto_id
    have hdiv : Tendsto (fun x : ℝ => (x - mean) / scale) atBot atBot :=
      (tendsto_div_const_atBot_of_pos hscale).2 hsub
    simpa [logisticCDFReal] using Real.tendsto_sigmoid_atBot.comp hdiv
  tendsto_top := by
    have hsub : Tendsto (fun x : ℝ => x - mean) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-mean) tendsto_id
    have hdiv : Tendsto (fun x : ℝ => (x - mean) / scale) atTop atTop :=
      (tendsto_div_const_atTop_of_pos hscale).2 hsub
    simpa [logisticCDFReal] using Real.tendsto_sigmoid_atTop.comp hdiv

/-- The logistic continuous distribution with location `mean` and scale `scale`. -/
noncomputable def ContDist.logistic (mean scale : ℝ) (hscale : 0 < scale) : ContDist :=
  (logisticCDF mean scale hscale).toDist (logisticPDFReal mean scale)
    (fun x => hasDerivAt_logisticCDFReal mean scale hscale x)

/-- The density of the logistic distribution equals `logisticPDFReal`. -/
@[simp] lemma ContDist.logistic_density (mean scale : ℝ) (hscale : 0 < scale) (x : ℝ) :
    (ContDist.logistic mean scale hscale).density x = logisticPDFReal mean scale x := rfl

/-- The mean is a mode of the logistic distribution: `σ(z)(1 - σ(z))` is maximized where the
sigmoid takes the value `1/2`, i.e. at `z = 0`. -/
lemma ContDist.logistic_isMode_mean (mean scale : ℝ) (hscale : 0 < scale) :
    (ContDist.logistic mean scale hscale).IsMode mean := by
  intro x
  rw [ContDist.logistic_density, ContDist.logistic_density]
  unfold logisticPDFReal
  rw [sub_self, zero_div, Real.sigmoid_zero]
  set s := Real.sigmoid ((x - mean) / scale) with hs
  -- `s (1 - s) ≤ 1/4`, with equality at `s = 1/2`
  have hkey : s * (1 - s) ≤ 2⁻¹ * (1 - 2⁻¹) := by nlinarith [sq_nonneg (s - 2⁻¹)]
  exact div_le_div_of_nonneg_right hkey hscale.le

/-- The CDF of the logistic distribution equals `logisticCDFReal`. -/
lemma ContDist.logistic_cdf (mean scale : ℝ) (hscale : 0 < scale) (x : ℝ) :
    (ContDist.logistic mean scale hscale).cdf x = logisticCDFReal mean scale x := by
  simp only [ContDist.cdf_eq_integral, ContDist.logistic_density]
  have h :=
    integral_Iic_of_hasDerivAt_of_tendsto' (a := x)
      (fun y _ => hasDerivAt_logisticCDFReal mean scale hscale y)
      (ContDist.logistic mean scale hscale).integrable.integrableOn
      (logisticCDF mean scale hscale).tendsto_bot
  simpa [logisticCDFReal] using h

private lemma logisticPDFReal_standard (x : ℝ) :
    logisticPDFReal 0 1 x = Real.exp (-x) / (1 + Real.exp (-x)) ^ 2 := by
  unfold logisticPDFReal
  rw [Real.sigmoid_def]
  have hexp_ne : 1 + Real.exp (-x) ≠ 0 := by positivity
  field_simp [hexp_ne]
  norm_num
  ring

private lemma logisticPDFReal_even (x : ℝ) :
    logisticPDFReal 0 1 (-x) = logisticPDFReal 0 1 x := by
  unfold logisticPDFReal
  have hneg : ((-x - 0) / 1 : ℝ) = -x := by ring
  have hpos : ((x - 0) / 1 : ℝ) = x := by ring
  rw [hneg, hpos]
  rw [Real.sigmoid_neg]
  ring

private lemma logisticPDFReal_translate_scale (mean scale x : ℝ) :
    logisticPDFReal mean scale x = logisticPDFReal 0 1 ((x - mean) / scale) / scale := by
  unfold logisticPDFReal
  simp

private noncomputable def logisticSecondTailTerm (n : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 * Real.exp (-x) * ((n + 1 : ℝ) * (-Real.exp (-x)) ^ n)

private lemma logisticSecondTailTerm_hasSum (x : ℝ) (hx : 0 < x) :
    HasSum (fun n : ℕ => logisticSecondTailTerm n x) (x ^ 2 * logisticPDFReal 0 1 x) := by
  have hr : ‖-Real.exp (-x)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos (Real.exp_pos (-x))]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hgeom :
      HasSum (fun n : ℕ => (-Real.exp (-x)) ^ n) ((1 - (-Real.exp (-x)))⁻¹) :=
    hasSum_geometric_of_norm_lt_one hr
  have hmul :
      HasSum (fun n : ℕ => (n : ℝ) * (-Real.exp (-x)) ^ n)
        ((-Real.exp (-x)) / (1 - (-Real.exp (-x))) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hadd :
      HasSum (fun n : ℕ => ((n + 1 : ℝ) * (-Real.exp (-x)) ^ n))
        (1 / (1 + Real.exp (-x)) ^ 2) := by
    convert hmul.add hgeom using 1
    · ext n
      ring
    · have hexp_ne : 1 + Real.exp (-x) ≠ 0 := by positivity
      field_simp [hexp_ne]
      ring
  have hm := hadd.mul_left (x ^ 2 * Real.exp (-x))
  have hpdf :
      x ^ 2 * logisticPDFReal 0 1 x =
        x ^ 2 * Real.exp (-x) * (1 / (1 + Real.exp (-x)) ^ 2) := by
    rw [logisticPDFReal_standard]
    ring
  rw [hpdf]
  simpa [logisticSecondTailTerm, mul_assoc, mul_left_comm, mul_comm] using hm

private lemma logisticSecondBase_integrableOn :
    IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-x)) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := 3) (by positivity)
  simpa [show (3 : ℝ) - 1 = 2 by norm_num, mul_comm] using h

private lemma logisticSecondTailTerm_eq_scaled (n : ℕ) (x : ℝ) :
    logisticSecondTailTerm n x =
      (((-1 : ℝ) ^ n) / (n + 1 : ℝ)) *
        ((x * (n + 1 : ℝ)) ^ 2 * Real.exp (-(x * (n + 1 : ℝ)))) := by
  rw [logisticSecondTailTerm]
  have hnp1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hexp :
      Real.exp (-(x * (n + 1 : ℝ))) = Real.exp (-x) * (Real.exp (-x)) ^ n := by
    rw [show -(x * (n + 1 : ℝ)) = -x + (n : ℝ) * (-x) by ring, Real.exp_add, Real.exp_nat_mul]
  have hpow : (-Real.exp (-x)) ^ n = (-1 : ℝ) ^ n * (Real.exp (-x)) ^ n := by
    rw [show -Real.exp (-x) = (-1 : ℝ) * Real.exp (-x) by ring, mul_pow]
  rw [hpow, hexp]
  field_simp [hnp1]

private lemma logisticSecondTailTerm_integrable (n : ℕ) :
    IntegrableOn (logisticSecondTailTerm n) (Ioi 0) := by
  have hbase :
      IntegrableOn
        (fun x : ℝ => (x * (n + 1 : ℝ)) ^ 2 * Real.exp (-(x * (n + 1 : ℝ))))
        (Ioi 0) := by
    have hzero :
        IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-x)) (Ioi (0 * (n + 1 : ℝ))) := by
      simpa [zero_mul] using logisticSecondBase_integrableOn
    have h :=
      (integrableOn_Ioi_comp_mul_right_iff (fun x : ℝ => x ^ 2 * Real.exp (-x)) 0
        (show 0 < (n + 1 : ℝ) by positivity)).2 hzero
    simpa [zero_mul, mul_assoc] using h
  simpa [funext (logisticSecondTailTerm_eq_scaled n)] using
    hbase.const_mul (((-1 : ℝ) ^ n) / (n + 1 : ℝ))

private lemma scaledLogisticSecondBase_integral (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), (x * (n + 1 : ℝ)) ^ 2 * Real.exp (-(x * (n + 1 : ℝ))) =
      2 / (n + 1 : ℝ) := by
  have h :=
    integral_comp_mul_right_Ioi (g := fun y : ℝ => y ^ 2 * Real.exp (-y)) 0
      (show 0 < (n + 1 : ℝ) by positivity)
  simp only [smul_eq_mul, zero_mul] at h
  have hbase : ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-x) = 2 := by
    simpa using (integral_sq_mul_exp_neg_mul_Ioi 1 zero_lt_one)
  rw [h, hbase]
  have hnp1 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hnp1]

private lemma logisticSecondTailTerm_integral (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), logisticSecondTailTerm n x = 2 * ((-1 : ℝ) ^ n) / (n + 1 : ℝ) ^ 2 := by
  rw [show (fun x : ℝ => logisticSecondTailTerm n x) =
      fun x : ℝ =>
        (((-1 : ℝ) ^ n) / (n + 1 : ℝ)) *
          ((x * (n + 1 : ℝ)) ^ 2 * Real.exp (-(x * (n + 1 : ℝ)))) by
        funext x; exact logisticSecondTailTerm_eq_scaled n x]
  rw [integral_const_mul, scaledLogisticSecondBase_integral n]
  have hnp1 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hnp1]

private lemma logisticSecondTailTerm_norm_eq (n : ℕ) (x : ℝ) :
    ‖logisticSecondTailTerm n x‖ =
      ((n + 1 : ℝ)⁻¹) * ((x * (n + 1 : ℝ)) ^ 2 * Real.exp (-(x * (n + 1 : ℝ)))) := by
  rw [logisticSecondTailTerm_eq_scaled]
  rw [norm_mul]
  have hcoeff :
      ‖(((-1 : ℝ) ^ n) / (n + 1 : ℝ))‖ = (n + 1 : ℝ)⁻¹ := by
    rw [Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity)]
    ring
  rw [hcoeff, Real.norm_of_nonneg]
  positivity

private lemma logisticSecondTailTerm_norm_integral (n : ℕ) :
    ∫ x in Ioi (0 : ℝ), ‖logisticSecondTailTerm n x‖ = 2 / (n + 1 : ℝ) ^ 2 := by
  rw [show (fun x : ℝ => ‖logisticSecondTailTerm n x‖) =
      fun x => ((n + 1 : ℝ)⁻¹) * ((x * (n + 1 : ℝ)) ^ 2 * Real.exp (-(x * (n + 1 : ℝ)))) by
        funext x; exact logisticSecondTailTerm_norm_eq n x]
  rw [integral_const_mul, scaledLogisticSecondBase_integral n]
  have hnp1 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hnp1]

private lemma summable_logisticSecondTailTerm_norm_integral :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖logisticSecondTailTerm n x‖) := by
  have hsum :
      Summable (fun n : ℕ => 2 / (n + 1 : ℝ) ^ 2) := by
    have hz0 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    have hz : Summable (fun n : ℕ => 1 / (n + 1 : ℝ) ^ 2) := by
      simpa using (summable_nat_add_iff (G := ℝ) 1).2 hz0
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hz.mul_left 2
  exact hsum.congr fun n => (logisticSecondTailTerm_norm_integral n).symm

private lemma hasSum_alternating_inv_natSucc_sq :
    HasSum (fun n : ℕ => ((-1 : ℝ) ^ n) / (n + 1 : ℝ) ^ 2) (π ^ 2 / 12) := by
  have hcos0 :=
    hasSum_one_div_nat_pow_mul_cos (k := 1) one_ne_zero (x := (1 / 2 : ℝ))
      (by constructor <;> norm_num)
  have hcos :
      HasSum (fun n : ℕ => 1 / (n : ℝ) ^ 2 * Real.cos (2 * π * n * (1 / 2 : ℝ)))
        (-(π ^ 2 / 12)) := by
    convert hcos0 using 1
    have hpoly :
        Polynomial.eval (1 / 2 : ℝ)
          (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2)) = (-1 / 12 : ℝ) := by
      rw [Polynomial.eval_map, Polynomial.bernoulli]
      norm_num [Finset.sum_range_succ, bernoulli_zero, bernoulli_one, bernoulli_two]
    norm_num [hpoly]
    ring
  have hshift :
      HasSum (fun n : ℕ => 1 / ((n + 1 : ℝ) ^ 2) * Real.cos (2 * π * (n + 1) * (1 / 2 : ℝ)))
        (-(π ^ 2 / 12)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using (hasSum_nat_add_iff' 1).mpr hcos
  convert hshift.neg using 1
  · ext n
    have hcos_pi : Real.cos ((n + 1 : ℝ) * π) = (-1 : ℝ) ^ (n + 1) := by
      simpa using Real.cos_nat_mul_pi (n + 1)
    rw [show 2 * π * (n + 1) * (1 / 2 : ℝ) = (n + 1 : ℝ) * π by ring, hcos_pi]
    field_simp
    ring
  · ring

private lemma hasSum_logisticSecondTailTerm_integral :
    HasSum (fun n : ℕ => ∫ x in Ioi (0 : ℝ), logisticSecondTailTerm n x) (π ^ 2 / 6) := by
  convert hasSum_alternating_inv_natSucc_sq.mul_left 2 using 1
  · ext n
    rw [logisticSecondTailTerm_integral]
    ring
  · ring

private lemma logistic_standard_tail_second_integral :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * logisticPDFReal 0 1 x = π ^ 2 / 6 := by
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Ioi 0)
  have htsum :
      (∑' n, ∫ x, logisticSecondTailTerm n x ∂ μ) =
        ∫ x, ∑' n, logisticSecondTailTerm n x ∂ μ := by
    simpa [μ] using
      (MeasureTheory.integral_tsum_of_summable_integral_norm (μ := μ)
        (fun n => logisticSecondTailTerm_integrable n)
        summable_logisticSecondTailTerm_norm_integral)
  have hpoint :
      ∫ x, ∑' n, logisticSecondTailTerm n x ∂ μ =
        ∫ x in Ioi (0 : ℝ), x ^ 2 * logisticPDFReal 0 1 x := by
    apply MeasureTheory.integral_congr_ae
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 ?_
    filter_upwards with x hx
    exact (logisticSecondTailTerm_hasSum x hx).tsum_eq
  have hseries :
      (∑' n, ∫ x in Ioi (0 : ℝ), logisticSecondTailTerm n x) =
        ∫ x in Ioi (0 : ℝ), x ^ 2 * logisticPDFReal 0 1 x := by
    simpa [μ] using htsum.trans hpoint
  rw [← hseries]
  exact hasSum_logisticSecondTailTerm_integral.tsum_eq

private lemma logisticPDFReal_abs (x : ℝ) :
    logisticPDFReal 0 1 |x| = logisticPDFReal 0 1 x := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), logisticPDFReal_even]

private lemma logistic_standard_second_integral :
    ∫ x, logisticPDFReal 0 1 x * x ^ 2 = π ^ 2 / 3 := by
  calc
    ∫ x, logisticPDFReal 0 1 x * x ^ 2
      = ∫ x, (fun t : ℝ => logisticPDFReal 0 1 t * t ^ 2) |x| := by
          congr 1
          ext x
          change logisticPDFReal 0 1 x * x ^ 2 = logisticPDFReal 0 1 |x| * |x| ^ 2
          rw [logisticPDFReal_abs, sq_abs]
      _ = 2 * ∫ x in Ioi (0 : ℝ), logisticPDFReal 0 1 x * x ^ 2 := by
          change ∫ x, logisticPDFReal 0 1 |x| * |x| ^ 2 =
            2 * ∫ x in Ioi (0 : ℝ), logisticPDFReal 0 1 x * x ^ 2
          convert (integral_comp_abs (f := fun t : ℝ => logisticPDFReal 0 1 t * t ^ 2)) using 1
      _ = π ^ 2 / 3 := by
          rw [show (∫ x in Ioi (0 : ℝ), logisticPDFReal 0 1 x * x ^ 2) =
              ∫ x in Ioi (0 : ℝ), x ^ 2 * logisticPDFReal 0 1 x by
                congr 1
                ext x
                ring, logistic_standard_tail_second_integral]
          ring

private lemma logistic_standard_second_integrable :
    MeasureTheory.Integrable (fun x : ℝ => logisticPDFReal 0 1 x * x ^ 2) := by
  let f : ℝ → ℝ := fun x => logisticPDFReal 0 1 x * x ^ 2
  have hmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume := by
    have : Measurable f := by
      unfold f logisticPDFReal
      fun_prop
    exact this.aestronglyMeasurable
  have hnonneg : 0 ≤ᵐ[MeasureTheory.volume] f := Filter.Eventually.of_forall fun x =>
    mul_nonneg (logisticPDFReal_nonneg 0 1 x zero_lt_one) (sq_nonneg x)
  refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).1 ?_
  intro htop
  have hreal :
      (∫⁻ a, ENNReal.ofReal (f a) ∂MeasureTheory.volume).toReal = π ^ 2 / 3 := by
    rw [← MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]
    simpa [f] using logistic_standard_second_integral
  have hzero : (∫⁻ a, ENNReal.ofReal (f a) ∂MeasureTheory.volume).toReal = 0 := by
    simp [htop]
  exact (show (0 : ℝ) < π ^ 2 / 3 by positivity).ne' (by linarith)

private lemma logistic_standard_first_integrable :
    MeasureTheory.Integrable (fun x : ℝ => logisticPDFReal 0 1 x * x) := by
  let g : ℝ → ℝ := fun x => logisticPDFReal 0 1 x * x ^ 2 + logisticPDFReal 0 1 x
  have hg2 : MeasureTheory.Integrable (fun x : ℝ => logisticPDFReal 0 1 x * x ^ 2) :=
    logistic_standard_second_integrable
  have hg1 : MeasureTheory.Integrable (fun x : ℝ => logisticPDFReal 0 1 x) :=
    (ContDist.logistic 0 1 zero_lt_one).integrable
  have hg : MeasureTheory.Integrable g := hg2.add hg1
  apply MeasureTheory.Integrable.mono' hg
  · fun_prop
  · filter_upwards with x
    have hpdf : 0 ≤ logisticPDFReal 0 1 x := logisticPDFReal_nonneg 0 1 x zero_lt_one
    have hx : |x| ≤ x ^ 2 + 1 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)]
    change ‖logisticPDFReal 0 1 x * x‖ ≤ logisticPDFReal 0 1 x * x ^ 2 + logisticPDFReal 0 1 x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hpdf]
    calc
      logisticPDFReal 0 1 x * |x| ≤ logisticPDFReal 0 1 x * (x ^ 2 + 1) := by
        exact mul_le_mul_of_nonneg_left hx hpdf
      _ = logisticPDFReal 0 1 x * x ^ 2 + logisticPDFReal 0 1 x := by ring

private lemma logistic_standard_first_integral :
    ∫ x, logisticPDFReal 0 1 x * x = 0 := by
  let f : ℝ → ℝ := fun x => logisticPDFReal 0 1 x * x
  have hcomp : ∫ x, f (-x) = ∫ x, f x := by
    simpa [f, mul_assoc, mul_left_comm, mul_comm] using
      (MeasureTheory.Measure.integral_comp_mul_left (g := f) (-1 : ℝ))
  have hodd : ∀ x : ℝ, f (-x) = -f x := by
    intro x
    dsimp [f]
    rw [logisticPDFReal_even]
    ring
  have hfun : (fun x : ℝ => f (-x)) = fun x => -f x := by
    funext x
    exact hodd x
  have hneg : ∫ x, f (-x) = -∫ x, f x := by
    rw [hfun, MeasureTheory.integral_neg]
  have hself : ∫ x, f x = -∫ x, f x := hcomp.symm.trans hneg
  have hzero : ∫ x, f x = 0 := by linarith
  simpa [f] using hzero

private lemma logistic_centered_first_integrable (mean scale : ℝ) (hscale : 0 < scale) :
    MeasureTheory.Integrable (fun x : ℝ => logisticPDFReal mean scale x * (x - mean)) := by
  have hscale_ne : scale ≠ 0 := by linarith
  have hbase :
      MeasureTheory.Integrable (fun x : ℝ => logisticPDFReal 0 1 (x / scale) * (x / scale)) := by
    simpa using logistic_standard_first_integrable.comp_div hscale_ne
  have hshift := hbase.comp_sub_right mean
  have h_eq :
      (fun x : ℝ => logisticPDFReal mean scale x * (x - mean)) =
        fun x => logisticPDFReal 0 1 ((x - mean) / scale) * (((x - mean) / scale)) := by
    funext x
    rw [logisticPDFReal_translate_scale]
    field_simp [hscale_ne]
  simpa [h_eq] using hshift

private lemma logistic_centered_second_integrable (mean scale : ℝ) (hscale : 0 < scale) :
    MeasureTheory.Integrable (fun x : ℝ => logisticPDFReal mean scale x * (x - mean) ^ 2) := by
  have hscale_ne : scale ≠ 0 := by linarith
  have hbase :
      MeasureTheory.Integrable
          (fun x : ℝ => logisticPDFReal 0 1 (x / scale) * (x / scale) ^ 2) := by
    simpa using logistic_standard_second_integrable.comp_div hscale_ne
  have hshift := hbase.comp_sub_right mean
  have h_eq :
      (fun x : ℝ => logisticPDFReal mean scale x * (x - mean) ^ 2) =
        fun x => scale * (logisticPDFReal 0 1 ((x - mean) / scale) *
          (((x - mean) / scale) ^ 2)) := by
    funext x
    rw [logisticPDFReal_translate_scale]
    field_simp [hscale_ne]
  simpa [h_eq] using hshift.const_mul scale

private lemma logistic_centered_first_integral (mean scale : ℝ) (hscale : 0 < scale) :
    ∫ x, logisticPDFReal mean scale x * (x - mean) = 0 := by
  have hscale_ne : scale ≠ 0 := by linarith
  calc
    ∫ x, logisticPDFReal mean scale x * (x - mean)
      = ∫ x, logisticPDFReal 0 1 ((x - mean) / scale) * (((x - mean) / scale)) := by
          congr 1
          ext x
          rw [logisticPDFReal_translate_scale]
          field_simp [hscale_ne]
      _ = ∫ x, logisticPDFReal 0 1 (x / scale) * (x / scale) := by
          simpa using
            (MeasureTheory.integral_sub_right_eq_self (μ := MeasureTheory.volume)
              (fun y : ℝ => logisticPDFReal 0 1 (y / scale) * (y / scale)) mean)
      _ = scale * ∫ x, logisticPDFReal 0 1 x * x := by
          simpa [smul_eq_mul, abs_of_pos hscale, mul_assoc, mul_left_comm, mul_comm] using
            (MeasureTheory.Measure.integral_comp_div
              (g := fun y : ℝ => logisticPDFReal 0 1 y * y) scale)
      _ = 0 := by rw [logistic_standard_first_integral]; ring

private lemma logistic_centered_second_integral (mean scale : ℝ) (hscale : 0 < scale) :
    ∫ x, logisticPDFReal mean scale x * (x - mean) ^ 2 = (π ^ 2 / 3) * scale ^ 2 := by
  have hscale_ne : scale ≠ 0 := by linarith
  calc
    ∫ x, logisticPDFReal mean scale x * (x - mean) ^ 2
      = ∫ x, scale * (logisticPDFReal 0 1 ((x - mean) / scale) *
            (((x - mean) / scale) ^ 2)) := by
          congr 1
          ext x
          rw [logisticPDFReal_translate_scale]
          field_simp [hscale_ne]
      _ = scale * ∫ x, logisticPDFReal 0 1 ((x - mean) / scale) *
            (((x - mean) / scale) ^ 2) := by
          rw [MeasureTheory.integral_const_mul]
      _ = scale * ∫ x, logisticPDFReal 0 1 (x / scale) * (x / scale) ^ 2 := by
          congr 1
          simpa using
            (MeasureTheory.integral_sub_right_eq_self (μ := MeasureTheory.volume)
              (fun y : ℝ => logisticPDFReal 0 1 (y / scale) * (y / scale) ^ 2) mean)
      _ = scale * ∫ x, (x / scale) ^ 2 * logisticPDFReal 0 1 (x / scale) := by
          congr 1
          apply MeasureTheory.integral_congr_ae
          filter_upwards with x
          ring
      _ = scale * (scale * ∫ x, x ^ 2 * logisticPDFReal 0 1 x) := by
          congr 1
          simpa [smul_eq_mul, abs_of_pos hscale, mul_assoc, mul_left_comm, mul_comm] using
            (MeasureTheory.Measure.integral_comp_div
              (g := fun y : ℝ => y ^ 2 * logisticPDFReal 0 1 y) scale)
      _ = (π ^ 2 / 3) * scale ^ 2 := by
          rw [show (∫ x, x ^ 2 * logisticPDFReal 0 1 x) =
              ∫ x, logisticPDFReal 0 1 x * x ^ 2 by
                congr 1
                ext x
                ring, logistic_standard_second_integral]
          ring

/-- The expectation of the logistic distribution with location `mean` and scale `scale` is
`mean`. -/
lemma ContDist.logistic_expect (mean scale : ℝ) (hscale : 0 < scale) :
    (ContDist.logistic mean scale hscale).expect id = mean := by
  simp only [ContDist.expect, id, ContDist.logistic_density]
  have hcenter_int := logistic_centered_first_integrable mean scale hscale
  have hconst_int : MeasureTheory.Integrable
      (fun x : ℝ => logisticPDFReal mean scale x * mean) := by
    simpa [mul_comm] using (ContDist.logistic mean scale hscale).integrable.const_mul mean
  have h_eq :
      (fun x : ℝ => logisticPDFReal mean scale x * x) =
        fun x => logisticPDFReal mean scale x * (x - mean) +
          logisticPDFReal mean scale x * mean := by
    funext x
    ring
  have hconst_eq :
      (fun x : ℝ => logisticPDFReal mean scale x * mean) =
        fun x => mean * logisticPDFReal mean scale x := by
    funext x
    ring
  have hpdf_one : ∫ x, logisticPDFReal mean scale x = 1 := by
    simpa [ContDist.logistic_density] using (ContDist.logistic mean scale hscale).integral_one
  calc
    ∫ x, logisticPDFReal mean scale x * x
      = ∫ x, logisticPDFReal mean scale x * (x - mean) +
          logisticPDFReal mean scale x * mean := by
          simp [h_eq]
      _ = mean := by
          rw [MeasureTheory.integral_add hcenter_int hconst_int,
            logistic_centered_first_integral mean scale hscale,
            hconst_eq, MeasureTheory.integral_const_mul, hpdf_one]
          ring

/-- The variance of the logistic distribution with location `mean` and scale `scale` is
`π² / 3 * scale²`. -/
lemma ContDist.logistic_variance (mean scale : ℝ) (hscale : 0 < scale) :
    (ContDist.logistic mean scale hscale).variance id = (π ^ 2 / 3) * scale ^ 2 := by
  simp only [ContDist.variance, ContDist.expect, id, ContDist.logistic_density]
  have hcenter2_int := logistic_centered_second_integrable mean scale hscale
  have hcenter1_int := logistic_centered_first_integrable mean scale hscale
  have hcross_int :
      MeasureTheory.Integrable
          (fun x : ℝ => (2 * mean) * (logisticPDFReal mean scale x * (x - mean))) :=
    hcenter1_int.const_mul (2 * mean)
  have hconst_int : MeasureTheory.Integrable
      (fun x : ℝ => mean ^ 2 * logisticPDFReal mean scale x) := by
    simpa [mul_comm] using
      (ContDist.logistic mean scale hscale).integrable.const_mul (mean ^ 2)
  have h_eq :
      (fun x : ℝ => logisticPDFReal mean scale x * x ^ 2) =
        fun x => logisticPDFReal mean scale x * (x - mean) ^ 2 +
          (2 * mean) * (logisticPDFReal mean scale x * (x - mean)) +
          mean ^ 2 * logisticPDFReal mean scale x := by
    funext x
    ring
  have hcross_zero :
      ∫ x, (2 * mean) * (logisticPDFReal mean scale x * (x - mean)) = 0 := by
    rw [MeasureTheory.integral_const_mul,
      logistic_centered_first_integral mean scale hscale]
    ring
  have hpdf_one : ∫ x, logisticPDFReal mean scale x = 1 := by
    simpa [ContDist.logistic_density] using (ContDist.logistic mean scale hscale).integral_one
  have hconst_value :
      ∫ x, mean ^ 2 * logisticPDFReal mean scale x = mean ^ 2 := by
    rw [MeasureTheory.integral_const_mul, hpdf_one]
    ring
  have hrest :
      ∫ x, (2 * mean) * (logisticPDFReal mean scale x * (x - mean)) +
          mean ^ 2 * logisticPDFReal mean scale x = mean ^ 2 := by
    rw [MeasureTheory.integral_add hcross_int hconst_int, hcross_zero, hconst_value]
    ring
  have hsecond :
      ∫ x, logisticPDFReal mean scale x * x ^ 2 = (π ^ 2 / 3) * scale ^ 2 + mean ^ 2 := by
    calc
      ∫ x, logisticPDFReal mean scale x * x ^ 2
        = ∫ x, logisticPDFReal mean scale x * (x - mean) ^ 2 +
            ((2 * mean) * (logisticPDFReal mean scale x * (x - mean)) +
              mean ^ 2 * logisticPDFReal mean scale x) := by
                simp [h_eq, add_assoc]
        _ = (π ^ 2 / 3) * scale ^ 2 + mean ^ 2 := by
          have hsplit :
              ∫ x, logisticPDFReal mean scale x * (x - mean) ^ 2 +
                ((2 * mean) * (logisticPDFReal mean scale x * (x - mean)) +
                  mean ^ 2 * logisticPDFReal mean scale x) =
                (∫ x, logisticPDFReal mean scale x * (x - mean) ^ 2) +
                  ∫ x, (2 * mean) * (logisticPDFReal mean scale x * (x - mean)) +
                    mean ^ 2 * logisticPDFReal mean scale x := by
            simpa using MeasureTheory.integral_add hcenter2_int (hcross_int.add hconst_int)
          rw [hsplit, logistic_centered_second_integral mean scale hscale, hrest]
  have hmean : ∫ x, logisticPDFReal mean scale x * x = mean := by
    simpa [ContDist.expect, ContDist.logistic_density] using
      ContDist.logistic_expect mean scale hscale
  rw [hsecond, hmean]
  ring

end Econlib.Probability
