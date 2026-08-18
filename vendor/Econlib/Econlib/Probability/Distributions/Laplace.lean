/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.IntegralIdentities
public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.ContDist.CDF

/-!
# Laplace distribution

This file defines the two-sided Laplace density with mean `mean` and scale parameter `scale > 0`,
constructs the corresponding `ContDist`, and proves normalization, CDF, expectation, and variance
formulas.

## Main definitions

* `laplacePDFReal`: Real-valued Laplace density.
* `ContDist.laplace`: Laplace distribution as a `ContDist`.

## Main statements

* `integral_laplacePDFReal_eq_one`: The Laplace density integrates to one.
* `ContDist.laplace_isMode_mean`: The mean is a mode.
* `ContDist.laplace_cdf`: Closed-form CDF of the Laplace distribution.
* `ContDist.laplace_expect`: Expectation of the Laplace distribution equals `mean`.
* `ContDist.laplace_variance`: Variance of the Laplace distribution equals `2 * scale ^ 2`.

## Tags

probability, continuous distributions, laplace
-/

@[expose] public section

open Set MeasureTheory Real Filter

namespace Econlib.Probability

/-- The left branch of the Laplace density, defined on all of `ℝ` as
`exp((x - mean) / scale) / (2 * scale)`. This coincides with the full density on `(-∞, mean]`. -/
noncomputable def laplaceLeftPDFReal (mean scale : ℝ) (x : ℝ) : ℝ :=
  Real.exp ((x - mean) / scale) / (2 * scale)

/-- The right branch of the Laplace density, defined on all of `ℝ` as
`exp(-(x - mean) / scale) / (2 * scale)`. This coincides with the full density on `(mean, ∞)`. -/
noncomputable def laplaceRightPDFReal (mean scale : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(x - mean) / scale) / (2 * scale)

/-- The real-valued Laplace density with location parameter `mean` and scale parameter `scale`,
equal to `exp(-|x - mean| / scale) / (2 * scale)`. -/
noncomputable def laplacePDFReal (mean scale : ℝ) (x : ℝ) : ℝ :=
  (Iic mean).indicator (laplaceLeftPDFReal mean scale) x +
    (Ioi mean).indicator (laplaceRightPDFReal mean scale) x

/-- The left branch `laplaceLeftPDFReal` is nonneg when `scale > 0`. -/
lemma laplaceLeftPDFReal_nonneg (mean scale x : ℝ) (hscale : 0 < scale) :
    0 ≤ laplaceLeftPDFReal mean scale x := by
  unfold laplaceLeftPDFReal
  positivity

/-- The right branch `laplaceRightPDFReal` is nonneg when `scale > 0`. -/
lemma laplaceRightPDFReal_nonneg (mean scale x : ℝ) (hscale : 0 < scale) :
    0 ≤ laplaceRightPDFReal mean scale x := by
  unfold laplaceRightPDFReal
  positivity

/-- The left branch as a constant multiple of `exp ((1/scale) * x)`, so that exponential-integral
lemmas apply. -/
private lemma laplaceLeftPDFReal_eq_const_mul_exp (mean scale : ℝ) (hscale : 0 < scale) :
    (fun x : ℝ => laplaceLeftPDFReal mean scale x) =
      fun x => (Real.exp (-mean / scale) / (2 * scale)) * Real.exp ((1 / scale) * x) := by
  funext x
  unfold laplaceLeftPDFReal
  rw [show (x - mean) / scale = (1 / scale) * x + (-mean / scale) by
    field_simp [show scale ≠ 0 by linarith]
    ring, Real.exp_add]
  ring

/-- The right branch as a constant multiple of `exp ((-1/scale) * x)`, so that exponential-integral
lemmas apply. -/
private lemma laplaceRightPDFReal_eq_const_mul_exp (mean scale : ℝ) (hscale : 0 < scale) :
    (fun x : ℝ => laplaceRightPDFReal mean scale x) =
      fun x => (Real.exp (mean / scale) / (2 * scale)) * Real.exp ((-1 / scale) * x) := by
  funext x
  unfold laplaceRightPDFReal
  rw [show -(x - mean) / scale = (-1 / scale) * x + (mean / scale) by
    field_simp [show scale ≠ 0 by linarith]
    ring, Real.exp_add]
  ring

/-- The branch slope `-1/scale` is negative. -/
private lemma laplace_neg_inv_scale_neg (scale : ℝ) (hscale : 0 < scale) :
    -1 / scale < 0 :=
  div_neg_of_neg_of_pos (by norm_num) hscale

/-- The Laplace density `laplacePDFReal` is nonneg when `scale > 0`. -/
lemma laplacePDFReal_nonneg (mean scale : ℝ) (hscale : 0 < scale) (x : ℝ) :
    0 ≤ laplacePDFReal mean scale x := by
  unfold laplacePDFReal
  by_cases hx : x ≤ mean
  · have hx' : x ∉ Ioi mean := by simpa [Ioi, not_lt] using hx
    simp [hx, hx', laplaceLeftPDFReal_nonneg _ _ _ hscale]
  · have hx' : mean < x := by linarith
    simp [hx, hx', laplaceRightPDFReal_nonneg _ _ _ hscale]

/-- The Laplace density `laplacePDFReal mean scale` is measurable. -/
lemma measurable_laplacePDFReal (mean scale : ℝ) :
    Measurable (laplacePDFReal mean scale) := by
  unfold laplacePDFReal laplaceLeftPDFReal laplaceRightPDFReal
  refine (Measurable.indicator ?_ measurableSet_Iic).add
    (Measurable.indicator ?_ measurableSet_Ioi)
  · fun_prop
  · fun_prop

/-- The Laplace density `laplacePDFReal mean scale` is strongly measurable. -/
lemma stronglyMeasurable_laplacePDFReal (mean scale : ℝ) :
    StronglyMeasurable (laplacePDFReal mean scale) :=
  (measurable_laplacePDFReal mean scale).stronglyMeasurable

private lemma integrable_laplaceLeft_indicator (mean scale : ℝ) (hscale : 0 < scale) :
    Integrable ((Iic mean).indicator (laplaceLeftPDFReal mean scale)) := by
  rw [integrable_indicator_iff measurableSet_Iic]
  have h_exp : IntegrableOn (fun x : ℝ => Real.exp ((1 / scale) * x)) (Iic mean) := by
    simpa [one_div] using integrableOn_exp_mul_Iic (a := 1 / scale) (by positivity) mean
  simpa [laplaceLeftPDFReal_eq_const_mul_exp mean scale hscale] using
    h_exp.const_mul (Real.exp (-mean / scale) / (2 * scale))

private lemma integrable_laplaceRight_indicator (mean scale : ℝ) (hscale : 0 < scale) :
    Integrable ((Ioi mean).indicator (laplaceRightPDFReal mean scale)) := by
  rw [integrable_indicator_iff measurableSet_Ioi]
  have h_exp : IntegrableOn (fun x : ℝ => Real.exp ((-1 / scale) * x)) (Ioi mean) := by
    simpa [one_div] using
      integrableOn_exp_mul_Ioi (a := -1 / scale) (laplace_neg_inv_scale_neg scale hscale) mean
  simpa [laplaceRightPDFReal_eq_const_mul_exp mean scale hscale] using
    h_exp.const_mul (Real.exp (mean / scale) / (2 * scale))

private lemma laplaceLeft_integral_half (mean scale : ℝ) (hscale : 0 < scale) :
    ∫ x in Iic mean, laplaceLeftPDFReal mean scale x = 1 / 2 := by
  rw [laplaceLeftPDFReal_eq_const_mul_exp mean scale hscale, integral_const_mul,
    integral_exp_mul_Iic (a := 1 / scale) (by positivity)]
  have hscale_ne : scale ≠ 0 := by linarith
  calc
    (Real.exp (-mean / scale) / (2 * scale)) * (Real.exp ((1 / scale) * mean) / (1 / scale))
      = (Real.exp (-mean / scale) * Real.exp ((1 / scale) * mean)) / 2 := by
          field_simp [hscale_ne]
    _ = 1 / 2 := by
      rw [← Real.exp_add]
      have : -mean / scale + (1 / scale) * mean = 0 := by
        field_simp [hscale_ne]
        ring
      rw [this, Real.exp_zero]

private lemma laplaceRight_integral_half (mean scale : ℝ) (hscale : 0 < scale) :
    ∫ x in Ioi mean, laplaceRightPDFReal mean scale x = 1 / 2 := by
  rw [laplaceRightPDFReal_eq_const_mul_exp mean scale hscale, integral_const_mul,
    integral_exp_mul_Ioi (a := -1 / scale) (laplace_neg_inv_scale_neg scale hscale)]
  have hscale_ne : scale ≠ 0 := by linarith
  calc
    (Real.exp (mean / scale) / (2 * scale)) *
        (-Real.exp ((-1 / scale) * mean) / (-1 / scale))
      = (Real.exp (mean / scale) * Real.exp ((-1 / scale) * mean)) / 2 := by
          field_simp [hscale_ne]
    _ = 1 / 2 := by
      rw [← Real.exp_add]
      have : mean / scale + (-1 / scale) * mean = 0 := by
        field_simp [hscale_ne]
        ring
      rw [this, Real.exp_zero]

private lemma laplacePDFReal_integrable (mean scale : ℝ) (hscale : 0 < scale) :
    Integrable (laplacePDFReal mean scale) := by
  unfold laplacePDFReal
  exact (integrable_laplaceLeft_indicator mean scale hscale).add
    (integrable_laplaceRight_indicator mean scale hscale)

/-- The Laplace density `laplacePDFReal mean scale` integrates to one when `scale > 0`. -/
theorem integral_laplacePDFReal_eq_one (mean scale : ℝ) (hscale : 0 < scale) :
    ∫ x, laplacePDFReal mean scale x = 1 := by
  unfold laplacePDFReal
  rw [integral_add (integrable_laplaceLeft_indicator mean scale hscale)
    (integrable_laplaceRight_indicator mean scale hscale)]
  rw [integral_indicator measurableSet_Iic, integral_indicator measurableSet_Ioi,
    laplaceLeft_integral_half mean scale hscale, laplaceRight_integral_half mean scale hscale]
  norm_num

/-- The lower Lebesgue integral of `ENNReal.ofReal ∘ laplacePDFReal mean scale` equals one when
`scale > 0`. -/
lemma lintegral_laplacePDFReal_eq_one (mean scale : ℝ) (hscale : 0 < scale) :
    ∫⁻ x, ENNReal.ofReal (laplacePDFReal mean scale x) = 1 := by
  rw [← ENNReal.ofReal_one, ← integral_laplacePDFReal_eq_one mean scale hscale]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (laplacePDFReal_integrable mean scale hscale)
    (ae_of_all _ (laplacePDFReal_nonneg mean scale hscale))).symm

/-- Laplace distribution with mean `mean` and scale `scale`. -/
noncomputable def ContDist.laplace (mean scale : ℝ) (hscale : 0 < scale) : ContDist :=
  ContDist.ofPDFReal (laplacePDFReal mean scale)
    (laplacePDFReal_nonneg mean scale hscale)
    (stronglyMeasurable_laplacePDFReal mean scale)
    (lintegral_laplacePDFReal_eq_one mean scale hscale)

/-- The density of `ContDist.laplace mean scale hscale` is `laplacePDFReal mean scale`. -/
@[simp] lemma ContDist.laplace_density (mean scale : ℝ) (hscale : 0 < scale) (x : ℝ) :
    (ContDist.laplace mean scale hscale).density x = laplacePDFReal mean scale x := rfl

/-- The mean is a mode of the Laplace distribution: Both exponential branches are maximized where
the deviation `|x - mean|` vanishes. -/
lemma ContDist.laplace_isMode_mean (mean scale : ℝ) (hscale : 0 < scale) :
    (ContDist.laplace mean scale hscale).IsMode mean := by
  intro x
  rw [ContDist.laplace_density, ContDist.laplace_density]
  unfold laplacePDFReal
  -- At the mean, the left branch contributes `exp 0 / (2 * scale)` and the right branch is zero.
  rw [Set.indicator_of_mem (Set.self_mem_Iic : mean ∈ Iic mean),
    Set.indicator_of_notMem (show mean ∉ Ioi mean by simp), add_zero]
  have hpeak : laplaceLeftPDFReal mean scale mean = 1 / (2 * scale) := by
    unfold laplaceLeftPDFReal
    rw [sub_self, zero_div, Real.exp_zero]
  rw [hpeak]
  rcases le_or_gt x mean with hx | hx
  · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hx),
      Set.indicator_of_notMem (show x ∉ Ioi mean by simpa using hx), add_zero]
    unfold laplaceLeftPDFReal
    have hexp : Real.exp ((x - mean) / scale) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hscale.le
    exact div_le_div_of_nonneg_right hexp (by positivity)
  · rw [Set.indicator_of_notMem (show x ∉ Iic mean by simpa using hx),
      Set.indicator_of_mem (Set.mem_Ioi.mpr hx), zero_add]
    unfold laplaceRightPDFReal
    have hexp : Real.exp (-(x - mean) / scale) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hscale.le
    exact div_le_div_of_nonneg_right hexp (by positivity)

private lemma laplace_cdf_left (mean scale x : ℝ) (hscale : 0 < scale) (hx : x ≤ mean) :
    ∫ t in Iic x, laplacePDFReal mean scale t = Real.exp ((x - mean) / scale) / 2 := by
  unfold laplacePDFReal
  have hf : IntegrableOn ((Iic mean).indicator (laplaceLeftPDFReal mean scale)) (Iic x) :=
    (integrable_laplaceLeft_indicator mean scale hscale).integrableOn
  have hg : IntegrableOn ((Ioi mean).indicator (laplaceRightPDFReal mean scale)) (Iic x) :=
    (integrable_laplaceRight_indicator mean scale hscale).integrableOn
  rw [integral_add hf hg]
  rw [setIntegral_indicator measurableSet_Iic, setIntegral_indicator measurableSet_Ioi]
  have h_inter_left : Iic x ∩ Iic mean = Iic x := by
    ext t
    constructor
    · intro ht
      exact ht.1
    · intro ht
      exact ⟨ht, le_trans ht hx⟩
  have h_inter_right : Iic x ∩ Ioi mean = ∅ := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
    rintro ⟨htx, htm⟩
    linarith
  rw [h_inter_left, h_inter_right, setIntegral_empty, add_zero]
  rw [laplaceLeftPDFReal_eq_const_mul_exp mean scale hscale, integral_const_mul,
    integral_exp_mul_Iic (a := 1 / scale) (by positivity)]
  have hscale_ne : scale ≠ 0 := by linarith
  calc
    (Real.exp (-mean / scale) / (2 * scale)) * (Real.exp ((1 / scale) * x) / (1 / scale))
      = (Real.exp (-mean / scale) * Real.exp ((1 / scale) * x)) / 2 := by
          field_simp [hscale_ne]
    _ = Real.exp ((x - mean) / scale) / 2 := by
      rw [← Real.exp_add]
      congr 1
      field_simp [hscale_ne]
      ring_nf

private lemma laplace_survival (mean scale x : ℝ) (hscale : 0 < scale) (hx : mean < x) :
    ∫ t in Ioi x, laplacePDFReal mean scale t = Real.exp (-(x - mean) / scale) / 2 := by
  unfold laplacePDFReal
  have hf : IntegrableOn ((Iic mean).indicator (laplaceLeftPDFReal mean scale)) (Ioi x) :=
    (integrable_laplaceLeft_indicator mean scale hscale).integrableOn
  have hg : IntegrableOn ((Ioi mean).indicator (laplaceRightPDFReal mean scale)) (Ioi x) :=
    (integrable_laplaceRight_indicator mean scale hscale).integrableOn
  rw [integral_add hf hg]
  rw [setIntegral_indicator measurableSet_Iic, setIntegral_indicator measurableSet_Ioi]
  have h_inter_left : Ioi x ∩ Iic mean = ∅ := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Iic, mem_empty_iff_false, iff_false]
    rintro ⟨hxt, htm⟩
    linarith
  have h_inter_right : Ioi x ∩ Ioi mean = Ioi x := by
    ext t
    constructor
    · intro ht
      exact ht.1
    · intro ht
      exact ⟨ht, lt_trans hx ht⟩
  rw [h_inter_left, setIntegral_empty, zero_add, h_inter_right,
    laplaceRightPDFReal_eq_const_mul_exp mean scale hscale]
  rw [integral_const_mul,
    integral_exp_mul_Ioi (a := -1 / scale) (laplace_neg_inv_scale_neg scale hscale)]
  have hscale_ne : scale ≠ 0 := by linarith
  calc
    (Real.exp (mean / scale) / (2 * scale)) *
        (-Real.exp ((-1 / scale) * x) / (-1 / scale))
      = (Real.exp (mean / scale) * Real.exp ((-1 / scale) * x)) / 2 := by
          field_simp [hscale_ne]
    _ = Real.exp (-(x - mean) / scale) / 2 := by
      rw [← Real.exp_add]
      congr 1
      field_simp [hscale_ne]
      ring_nf

/-- The CDF of `ContDist.laplace mean scale hscale` satisfies `F(x) = exp((x - mean) / scale) / 2`
for `x ≤ mean` and `F(x) = 1 - exp(-(x - mean) / scale) / 2` for `x > mean`. -/
theorem ContDist.laplace_cdf (mean scale : ℝ) (hscale : 0 < scale) (x : ℝ) :
    (ContDist.laplace mean scale hscale).cdf x =
      if x ≤ mean then Real.exp ((x - mean) / scale) / 2
      else 1 - Real.exp (-(x - mean) / scale) / 2 := by
  by_cases hx : x ≤ mean
  · rw [if_pos hx]
    simpa [ContDist.cdf_eq_integral, ContDist.laplace_density] using
      laplace_cdf_left mean scale x hscale hx
  · have hx' : mean < x := by linarith
    rw [if_neg hx]
    have hsplit := integral_add_compl (s := Iic x) measurableSet_Iic
      (laplacePDFReal_integrable mean scale hscale)
    have hsurv : ∫ t in Ioi x, laplacePDFReal mean scale t =
        Real.exp (-(x - mean) / scale) / 2 :=
      laplace_survival mean scale x hscale hx'
    have hcomp : (Iic x)ᶜ = Ioi x := by ext t; simp
    have hcdf :
        (ContDist.laplace mean scale hscale).cdf x =
          ∫ t in Iic x, laplacePDFReal mean scale t := by
      simp [ContDist.cdf_eq_integral, ContDist.laplace_density]
    have hsplit' := by
      simpa [hcomp] using hsplit
    rw [integral_laplacePDFReal_eq_one mean scale hscale, hsurv] at hsplit'
    rw [hcdf]
    nlinarith [hsplit']

private lemma laplacePDFReal_translate (mean scale x : ℝ) :
    laplacePDFReal mean scale x = laplacePDFReal 0 scale (x - mean) := by
  unfold laplacePDFReal
  by_cases hx : x ≤ mean
  · have hxm : x - mean ≤ 0 := by linarith
    have hxm' : ¬ 0 < x - mean := by linarith
    simp [hx, hxm, hxm', laplaceLeftPDFReal]
  · have hx' : mean < x := by linarith
    have hxm : ¬ x - mean ≤ 0 := by linarith
    have hxm' : 0 < x - mean := by linarith
    simp [hx, hx', hxm, hxm', laplaceRightPDFReal]

private lemma laplace_posMoment1_integrableOn (scale : ℝ) (hscale : 0 < scale) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-(1 / scale) * x)) (Ioi 0) := by
  rw [← integrable_indicator_iff measurableSet_Ioi]
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_indicator measurableSet_Ioi]
  have hval : ∫ x in Ioi (0 : ℝ), x * Real.exp (-(1 / scale) * x) = scale ^ 2 := by
    rw [integral_mul_exp_neg_mul_Ioi (r := 1 / scale) (one_div_pos.mpr hscale)]
    have hscale_ne : scale ≠ 0 := by linarith
    field_simp [hscale_ne]
  rw [hval]
  positivity

private lemma laplace_posMoment2_integrableOn (scale : ℝ) (hscale : 0 < scale) :
    IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-(1 / scale) * x)) (Ioi 0) := by
  rw [← integrable_indicator_iff measurableSet_Ioi]
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_indicator measurableSet_Ioi]
  have hval : ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-(1 / scale) * x) = 2 * scale ^ 3 := by
    rw [integral_sq_mul_exp_neg_mul_Ioi (r := 1 / scale) (one_div_pos.mpr hscale)]
    have hscale_ne : scale ≠ 0 := by linarith
    field_simp [hscale_ne]
  rw [hval]
  positivity

private lemma laplace_posMoment1_integral (scale : ℝ) (hscale : 0 < scale) :
    ∫ x in Ioi (0 : ℝ), x * Real.exp (-(1 / scale) * x) = scale ^ 2 := by
  rw [integral_mul_exp_neg_mul_Ioi (r := 1 / scale) (one_div_pos.mpr hscale)]
  have hscale_ne : scale ≠ 0 := by linarith
  field_simp [hscale_ne]

private lemma laplace_posMoment2_integral (scale : ℝ) (hscale : 0 < scale) :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-(1 / scale) * x) = 2 * scale ^ 3 := by
  rw [integral_sq_mul_exp_neg_mul_Ioi (r := 1 / scale) (one_div_pos.mpr hscale)]
  have hscale_ne : scale ≠ 0 := by linarith
  field_simp [hscale_ne]

private noncomputable def laplaceZeroRightFirst (scale : ℝ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (fun x => laplaceRightPDFReal 0 scale x * x)

private noncomputable def laplaceZeroLeftFirst (scale : ℝ) : ℝ → ℝ :=
  (Iic (0 : ℝ)).indicator (fun x => laplaceLeftPDFReal 0 scale x * x)

private noncomputable def laplaceZeroRightSecond (scale : ℝ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (fun x => laplaceRightPDFReal 0 scale x * x ^ 2)

private noncomputable def laplaceZeroLeftSecond (scale : ℝ) : ℝ → ℝ :=
  (Iic (0 : ℝ)).indicator (fun x => laplaceLeftPDFReal 0 scale x * x ^ 2)

/-- The right branch first-moment integrand as a constant times `x * exp (-(1/scale) * x)`. -/
private lemma laplaceRightFirst_integrand_eq (scale : ℝ) :
    (fun x : ℝ => laplaceRightPDFReal 0 scale x * x) =
      fun x => (1 / (2 * scale)) * (x * Real.exp (-(1 / scale) * x)) := by
  funext x
  simp [laplaceRightPDFReal]
  ring_nf

/-- The right branch second-moment integrand as a constant times `x ^ 2 * exp (-(1/scale) * x)`. -/
private lemma laplaceRightSecond_integrand_eq (scale : ℝ) :
    (fun x : ℝ => laplaceRightPDFReal 0 scale x * x ^ 2) =
      fun x => (1 / (2 * scale)) * (x ^ 2 * Real.exp (-(1 / scale) * x)) := by
  funext x
  simp [laplaceRightPDFReal]
  ring_nf

private lemma laplaceZeroRightFirst_integrable (scale : ℝ) (hscale : 0 < scale) :
    Integrable (laplaceZeroRightFirst scale) := by
  rw [laplaceZeroRightFirst, integrable_indicator_iff measurableSet_Ioi]
  have hbase := laplace_posMoment1_integrableOn scale hscale
  simpa [laplaceRightFirst_integrand_eq scale] using hbase.const_mul (1 / (2 * scale))

private lemma laplaceZeroRightSecond_integrable (scale : ℝ) (hscale : 0 < scale) :
    Integrable (laplaceZeroRightSecond scale) := by
  rw [laplaceZeroRightSecond, integrable_indicator_iff measurableSet_Ioi]
  have hbase := laplace_posMoment2_integrableOn scale hscale
  simpa [laplaceRightSecond_integrand_eq scale] using hbase.const_mul (1 / (2 * scale))

private lemma laplaceZeroLeftFirst_eq_neg_comp (scale : ℝ) :
    laplaceZeroLeftFirst scale = fun x : ℝ => -(laplaceZeroRightFirst scale (-x)) := by
  funext x
  by_cases hx : x ≤ 0
  · rcases (eq_or_lt_of_le (neg_nonneg.mpr hx)).symm with hneg | hneg
    · simp [laplaceZeroLeftFirst, laplaceZeroRightFirst, hx, hneg, laplaceLeftPDFReal,
        laplaceRightPDFReal]
    · have hx0 : x = 0 := by linarith
      simp [laplaceZeroLeftFirst, laplaceZeroRightFirst, hx0]
  · have hneg : ¬ 0 < -x := by linarith
    simp [laplaceZeroLeftFirst, laplaceZeroRightFirst, hx, hneg]

private lemma laplaceZeroLeftSecond_eq_comp (scale : ℝ) :
    laplaceZeroLeftSecond scale = fun x : ℝ => laplaceZeroRightSecond scale (-x) := by
  funext x
  by_cases hx : x ≤ 0
  · rcases (eq_or_lt_of_le (neg_nonneg.mpr hx)).symm with hneg | hneg
    · simp [laplaceZeroLeftSecond, laplaceZeroRightSecond, hx, hneg, laplaceLeftPDFReal,
        laplaceRightPDFReal]
    · have hx0 : x = 0 := by linarith
      simp [laplaceZeroLeftSecond, laplaceZeroRightSecond, hx0]
  · have hneg : ¬ 0 < -x := by linarith
    simp [laplaceZeroLeftSecond, laplaceZeroRightSecond, hx, hneg]

private lemma laplaceZeroLeftFirst_integrable (scale : ℝ) (hscale : 0 < scale) :
    Integrable (laplaceZeroLeftFirst scale) := by
  rw [laplaceZeroLeftFirst_eq_neg_comp scale]
  exact ((laplaceZeroRightFirst_integrable scale hscale).comp_neg).neg

private lemma laplaceZeroLeftSecond_integrable (scale : ℝ) (hscale : 0 < scale) :
    Integrable (laplaceZeroLeftSecond scale) := by
  rw [laplaceZeroLeftSecond_eq_comp scale]
  exact (laplaceZeroRightSecond_integrable scale hscale).comp_neg

private lemma laplaceZeroRightFirst_integral (scale : ℝ) (hscale : 0 < scale) :
    ∫ x, laplaceZeroRightFirst scale x = scale / 2 := by
  rw [laplaceZeroRightFirst, integral_indicator measurableSet_Ioi]
  rw [laplaceRightFirst_integrand_eq scale, integral_const_mul,
    laplace_posMoment1_integral scale hscale]
  have hscale_ne : scale ≠ 0 := by linarith
  field_simp [hscale_ne]

private lemma laplaceZeroRightSecond_integral (scale : ℝ) (hscale : 0 < scale) :
    ∫ x, laplaceZeroRightSecond scale x = scale ^ 2 := by
  rw [laplaceZeroRightSecond, integral_indicator measurableSet_Ioi]
  rw [laplaceRightSecond_integrand_eq scale, integral_const_mul,
    laplace_posMoment2_integral scale hscale]
  have hscale_ne : scale ≠ 0 := by linarith
  field_simp [hscale_ne]

private lemma laplaceZeroLeftFirst_integral (scale : ℝ) (hscale : 0 < scale) :
    ∫ x, laplaceZeroLeftFirst scale x = -(scale / 2) := by
  rw [laplaceZeroLeftFirst_eq_neg_comp scale, integral_neg]
  rw [integral_neg_eq_self (f := laplaceZeroRightFirst scale)]
  rw [laplaceZeroRightFirst_integral scale hscale]

private lemma laplaceZeroLeftSecond_integral (scale : ℝ) (hscale : 0 < scale) :
    ∫ x, laplaceZeroLeftSecond scale x = scale ^ 2 := by
  rw [laplaceZeroLeftSecond_eq_comp scale]
  rw [integral_neg_eq_self (f := laplaceZeroRightSecond scale)]
  exact laplaceZeroRightSecond_integral scale hscale

private lemma laplace_zero_centered_first_eq (scale : ℝ) :
    (fun x : ℝ => laplacePDFReal 0 scale x * x) =
      laplaceZeroLeftFirst scale + laplaceZeroRightFirst scale := by
  funext x
  by_cases hx : x ≤ 0
  · have hx' : x ∉ Ioi (0 : ℝ) := by simpa [Ioi, not_lt] using hx
    simp [laplacePDFReal, laplaceZeroLeftFirst, laplaceZeroRightFirst, hx, hx']
  · have hx' : 0 < x := by linarith
    simp [laplacePDFReal, laplaceZeroLeftFirst, laplaceZeroRightFirst, hx, hx']

private lemma laplace_zero_centered_second_eq (scale : ℝ) :
    (fun x : ℝ => laplacePDFReal 0 scale x * x ^ 2) =
      laplaceZeroLeftSecond scale + laplaceZeroRightSecond scale := by
  funext x
  by_cases hx : x ≤ 0
  · have hx' : x ∉ Ioi (0 : ℝ) := by simpa [Ioi, not_lt] using hx
    simp [laplacePDFReal, laplaceZeroLeftSecond, laplaceZeroRightSecond, hx, hx']
  · have hx' : 0 < x := by linarith
    simp [laplacePDFReal, laplaceZeroLeftSecond, laplaceZeroRightSecond, hx, hx']

private lemma laplace_zero_centered_first_integrable (scale : ℝ) (hscale : 0 < scale) :
    Integrable (fun x : ℝ => laplacePDFReal 0 scale x * x) := by
  rw [laplace_zero_centered_first_eq scale]
  exact (laplaceZeroLeftFirst_integrable scale hscale).add
    (laplaceZeroRightFirst_integrable scale hscale)

private lemma laplace_zero_centered_second_integrable (scale : ℝ) (hscale : 0 < scale) :
    Integrable (fun x : ℝ => laplacePDFReal 0 scale x * x ^ 2) := by
  rw [laplace_zero_centered_second_eq scale]
  exact (laplaceZeroLeftSecond_integrable scale hscale).add
    (laplaceZeroRightSecond_integrable scale hscale)

private lemma laplace_zero_centered_first_integral (scale : ℝ) (hscale : 0 < scale) :
    ∫ x, laplacePDFReal 0 scale x * x = 0 := by
  have hsum : ∫ x, laplaceZeroLeftFirst scale x + laplaceZeroRightFirst scale x = 0 := by
    rw [integral_add (laplaceZeroLeftFirst_integrable scale hscale)
      (laplaceZeroRightFirst_integrable scale hscale)]
    rw [laplaceZeroLeftFirst_integral scale hscale, laplaceZeroRightFirst_integral scale hscale]
    ring
  simpa [laplace_zero_centered_first_eq scale] using hsum

private lemma laplace_zero_centered_second_integral (scale : ℝ) (hscale : 0 < scale) :
    ∫ x, laplacePDFReal 0 scale x * x ^ 2 = 2 * scale ^ 2 := by
  have hsum :
      ∫ x, laplaceZeroLeftSecond scale x + laplaceZeroRightSecond scale x = 2 * scale ^ 2 := by
    rw [integral_add (laplaceZeroLeftSecond_integrable scale hscale)
      (laplaceZeroRightSecond_integrable scale hscale)]
    rw [laplaceZeroLeftSecond_integral scale hscale, laplaceZeroRightSecond_integral scale hscale]
    ring
  simpa [laplace_zero_centered_second_eq scale] using hsum

private lemma laplace_centered_first_integrable (mean scale : ℝ) (hscale : 0 < scale) :
    Integrable (fun x : ℝ => laplacePDFReal mean scale x * (x - mean)) := by
  have hbase := (laplace_zero_centered_first_integrable scale hscale).comp_sub_right mean
  simpa [laplacePDFReal_translate] using hbase

private lemma laplace_centered_second_integrable (mean scale : ℝ) (hscale : 0 < scale) :
    Integrable (fun x : ℝ => laplacePDFReal mean scale x * (x - mean) ^ 2) := by
  have hbase := (laplace_zero_centered_second_integrable scale hscale).comp_sub_right mean
  simpa [laplacePDFReal_translate] using hbase

private lemma laplace_centered_first_integral (mean scale : ℝ) (hscale : 0 < scale) :
    ∫ x, laplacePDFReal mean scale x * (x - mean) = 0 := by
  calc
    ∫ x, laplacePDFReal mean scale x * (x - mean)
      = ∫ x, laplacePDFReal 0 scale (x - mean) * (x - mean) := by
          congr 1
          ext x
          rw [laplacePDFReal_translate]
    _ = ∫ x, laplacePDFReal 0 scale x * x := by
          simpa using
            (integral_sub_right_eq_self (μ := volume)
              (fun y : ℝ => laplacePDFReal 0 scale y * y) mean)
    _ = 0 := laplace_zero_centered_first_integral scale hscale

private lemma laplace_centered_second_integral (mean scale : ℝ) (hscale : 0 < scale) :
    ∫ x, laplacePDFReal mean scale x * (x - mean) ^ 2 = 2 * scale ^ 2 := by
  calc
    ∫ x, laplacePDFReal mean scale x * (x - mean) ^ 2
      = ∫ x, laplacePDFReal 0 scale (x - mean) * (x - mean) ^ 2 := by
          congr 1
          ext x
          rw [laplacePDFReal_translate]
    _ = ∫ x, laplacePDFReal 0 scale x * x ^ 2 := by
          simpa using
            (integral_sub_right_eq_self (μ := volume)
              (fun y : ℝ => laplacePDFReal 0 scale y * y ^ 2) mean)
    _ = 2 * scale ^ 2 := laplace_zero_centered_second_integral scale hscale

/-- The expectation of `ContDist.laplace mean scale hscale` equals `mean`. -/
theorem ContDist.laplace_expect (mean scale : ℝ) (hscale : 0 < scale) :
    (ContDist.laplace mean scale hscale).expect id = mean := by
  simp only [ContDist.expect, id, ContDist.laplace_density]
  have hcenter_int := laplace_centered_first_integrable mean scale hscale
  have hconst_int : Integrable (fun x : ℝ => laplacePDFReal mean scale x * mean) := by
    simpa [mul_comm] using (laplacePDFReal_integrable mean scale hscale).const_mul mean
  have h_eq :
      (fun x : ℝ => laplacePDFReal mean scale x * x) =
        fun x => laplacePDFReal mean scale x * (x - mean) + laplacePDFReal mean scale x * mean := by
    funext x
    ring
  have hconst_eq :
      (fun x : ℝ => laplacePDFReal mean scale x * mean) =
        fun x => mean * laplacePDFReal mean scale x := by
    funext x
    ring
  calc
    ∫ x, laplacePDFReal mean scale x * x
      = ∫ x, laplacePDFReal mean scale x * (x - mean) + laplacePDFReal mean scale x * mean := by
          simp [h_eq]
    _ = mean := by
      rw [integral_add hcenter_int hconst_int, laplace_centered_first_integral mean scale hscale,
        hconst_eq, integral_const_mul, integral_laplacePDFReal_eq_one mean scale hscale]
      ring

/-- The variance of `ContDist.laplace mean scale hscale` equals `2 * scale ^ 2`. -/
theorem ContDist.laplace_variance (mean scale : ℝ) (hscale : 0 < scale) :
    (ContDist.laplace mean scale hscale).variance id = 2 * scale ^ 2 := by
  simp only [ContDist.variance, ContDist.expect, id, ContDist.laplace_density]
  have hcenter2_int := laplace_centered_second_integrable mean scale hscale
  have hcenter1_int := laplace_centered_first_integrable mean scale hscale
  have hcross_int :
      Integrable (fun x : ℝ => (2 * mean) * (laplacePDFReal mean scale x * (x - mean))) :=
    hcenter1_int.const_mul (2 * mean)
  have hconst_int : Integrable (fun x : ℝ => mean ^ 2 * laplacePDFReal mean scale x) := by
    simpa [mul_comm] using (laplacePDFReal_integrable mean scale hscale).const_mul (mean ^ 2)
  have h_eq :
      (fun x : ℝ => laplacePDFReal mean scale x * x ^ 2) =
        fun x => laplacePDFReal mean scale x * (x - mean) ^ 2 +
          (2 * mean) * (laplacePDFReal mean scale x * (x - mean)) +
          mean ^ 2 * laplacePDFReal mean scale x := by
    funext x
    ring
  have hcross_zero :
      ∫ x, (2 * mean) * (laplacePDFReal mean scale x * (x - mean)) = 0 := by
    rw [integral_const_mul, laplace_centered_first_integral mean scale hscale]
    ring
  have hconst_value :
      ∫ x, mean ^ 2 * laplacePDFReal mean scale x = mean ^ 2 := by
    rw [integral_const_mul, integral_laplacePDFReal_eq_one mean scale hscale]
    ring
  have hrest :
      ∫ x, (2 * mean) * (laplacePDFReal mean scale x * (x - mean)) +
          mean ^ 2 * laplacePDFReal mean scale x = mean ^ 2 := by
    rw [integral_add hcross_int hconst_int, hcross_zero, hconst_value]
    ring
  have hsecond :
      ∫ x, laplacePDFReal mean scale x * x ^ 2 = 2 * scale ^ 2 + mean ^ 2 := by
    calc
      ∫ x, laplacePDFReal mean scale x * x ^ 2
        = ∫ x, laplacePDFReal mean scale x * (x - mean) ^ 2 +
            ((2 * mean) * (laplacePDFReal mean scale x * (x - mean)) +
              mean ^ 2 * laplacePDFReal mean scale x) := by
                simp [h_eq, add_assoc]
      _ = 2 * scale ^ 2 + mean ^ 2 := by
        have hsplit :
            ∫ x, laplacePDFReal mean scale x * (x - mean) ^ 2 +
              ((2 * mean) * (laplacePDFReal mean scale x * (x - mean)) +
                mean ^ 2 * laplacePDFReal mean scale x) =
              (∫ x, laplacePDFReal mean scale x * (x - mean) ^ 2) +
                ∫ x, (2 * mean) * (laplacePDFReal mean scale x * (x - mean)) +
                  mean ^ 2 * laplacePDFReal mean scale x := by
          simpa using integral_add hcenter2_int (hcross_int.add hconst_int)
        rw [hsplit, laplace_centered_second_integral mean scale hscale, hrest]
  have hmean : ∫ x, laplacePDFReal mean scale x * x = mean := by
    simpa [ContDist.expect, ContDist.laplace_density] using
      ContDist.laplace_expect mean scale hscale
  rw [hsecond, hmean]
  ring

end Econlib.Probability
