/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.ContDist.CDF
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Truncated exponential distribution

This file defines the real-valued density of a truncated exponential distribution on a closed
interval `[a, b]`, constructs it as a `ContDist`, and records its CDF and expectation.

## Main definitions

* `truncExponentialPDFReal`: The real-valued density of the truncated exponential distribution on
  `[a, b]`.
* `ContDist.truncExponential`: The truncated exponential distribution as a continuous distribution.

## Main statements

* `integral_truncExponentialPDFReal_eq_one`: The density integrates to one.
* `ContDist.truncExponential_cdf`: The closed form of the cumulative distribution function.
* `ContDist.truncExponential_isMode_left`: The left endpoint `a` is a mode.
* `ContDist.truncExponential_expect`: The closed form of the expectation.

## Tags

probability, continuous distributions, truncated exponential
-/

@[expose] public section

open Set MeasureTheory

namespace Econlib.Probability

/-- Real-valued density of the truncated exponential distribution on `[a, b]` with rate `rate > 0`:
`f(x) = rate * exp(-rate * (x - a)) / (1 - exp(-rate * (b - a)))` on `[a, b]`, and `0` elsewhere. -/
noncomputable def truncExponentialPDFReal (a b rate : ℝ) (x : ℝ) : ℝ :=
  if x ∈ Icc a b then
    rate * Real.exp (-rate * (x - a)) / (1 - Real.exp (-rate * (b - a)))
  else 0

/-- The normalizing constant `1 - exp(-rate * (b - a))` is strictly positive when `a < b` and
`rate > 0`. -/
lemma truncExponential_normConst_pos {a b rate : ℝ} (hab : a < b) (hrate : 0 < rate) :
    0 < 1 - Real.exp (-rate * (b - a)) := by
  have hneg : -rate * (b - a) < 0 := by nlinarith
  have hlt : Real.exp (-rate * (b - a)) < 1 := Real.exp_lt_one_iff.mpr hneg
  linarith

/-- The truncated exponential density is nonneg when `a < b` and `rate > 0`. -/
lemma truncExponentialPDFReal_nonneg (a b rate : ℝ) (hab : a < b) (hrate : 0 < rate) (x : ℝ) :
    0 ≤ truncExponentialPDFReal a b rate x := by
  unfold truncExponentialPDFReal
  split_ifs with hx
  · have hc : 0 < 1 - Real.exp (-rate * (b - a)) :=
      truncExponential_normConst_pos hab hrate
    exact div_nonneg
      (mul_nonneg hrate.le (Real.exp_pos _).le) hc.le
  · rfl

/-- The truncated exponential density is measurable. -/
lemma measurable_truncExponentialPDFReal (a b rate : ℝ) :
    Measurable (truncExponentialPDFReal a b rate) := by
  unfold truncExponentialPDFReal
  refine Measurable.ite ?_ ?_ measurable_const
  · exact measurableSet_Icc
  · fun_prop

/-- The truncated exponential density is strongly measurable. -/
lemma stronglyMeasurable_truncExponentialPDFReal (a b rate : ℝ) :
    StronglyMeasurable (truncExponentialPDFReal a b rate) :=
  (measurable_truncExponentialPDFReal a b rate).stronglyMeasurable

/-- The indicator form of the truncated exponential density. -/
private lemma truncExponentialPDFReal_indicator (a b rate : ℝ) :
    truncExponentialPDFReal a b rate =
      (Icc a b).indicator
        (fun x => rate * Real.exp (-rate * (x - a)) /
          (1 - Real.exp (-rate * (b - a)))) := by
  funext x
  unfold truncExponentialPDFReal
  simp [Set.indicator_apply]

/-- Integral of the first moment kernel for the unnormalized truncated exponential density on
`[0, L]`. -/
private lemma intervalIntegral_truncExponential_first_moment_zero (L rate : ℝ)
    (hrate : 0 < rate) :
    ∫ u in (0 : ℝ)..L, rate * u * Real.exp (-rate * u) =
      (1 - Real.exp (-rate * L)) / rate - L * Real.exp (-rate * L) := by
  -- Antiderivative `F(y) = -(y + 1/rate) * exp(-rate * y)` has derivative
  -- `rate * y * exp(-rate * y)`.
  have h_deriv : ∀ u : ℝ,
      HasDerivAt (fun y => -(y + 1 / rate) * Real.exp (-rate * y))
        (rate * u * Real.exp (-rate * u)) u := by
    intro u
    have h1 : HasDerivAt (fun y : ℝ => -(y + 1 / rate)) (-1 : ℝ) u :=
      ((hasDerivAt_id u).add_const (1 / rate)).neg
    have h2 : HasDerivAt (fun y : ℝ => -rate * y) (-rate) u := by
      simpa using (hasDerivAt_id u).const_mul (-rate)
    have h3 : HasDerivAt (fun y : ℝ => Real.exp (-rate * y))
        (Real.exp (-rate * u) * (-rate)) u :=
      (Real.hasDerivAt_exp (-rate * u)).comp u h2
    have h4 := h1.mul h3
    convert h4 using 1
    have hrate_ne : rate ≠ 0 := hrate.ne'
    field_simp
    ring
  have h_cont : Continuous (fun u : ℝ => rate * u * Real.exp (-rate * u)) := by
    fun_prop
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := L)
      (fun u _ => h_deriv u) (h_cont.intervalIntegrable _ _)
  rw [hftc]
  have hrate_ne : rate ≠ 0 := hrate.ne'
  simp [Real.exp_zero]
  field_simp
  ring

/-- The unnormalized truncated exponential density integrates to its normalizing constant. -/
private lemma intervalIntegral_truncExponential_unnormalized (a b rate : ℝ) :
    ∫ x in a..b, rate * Real.exp (-rate * (x - a)) =
      1 - Real.exp (-rate * (b - a)) := by
  -- Antiderivative: `F(x) = -exp(-rate * (x - a))` has derivative
  -- `rate * exp(-rate * (x - a))`.
  have h_deriv : ∀ x : ℝ,
      HasDerivAt (fun y => -Real.exp (-rate * (y - a)))
        (rate * Real.exp (-rate * (x - a))) x := by
    intro x
    have h1 : HasDerivAt (fun y => -rate * (y - a)) (-rate) x := by
      simpa using (((hasDerivAt_id x).sub_const a).const_mul (-rate))
    have h2 := (Real.hasDerivAt_exp (-rate * (x - a))).comp x h1
    convert h2.neg using 1; ring
  have h_cont : Continuous (fun x : ℝ => rate * Real.exp (-rate * (x - a))) := by
    fun_prop
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b)
      (fun x _ => h_deriv x) (h_cont.intervalIntegrable _ _)
  rw [hftc, show a - a = (0 : ℝ) from by ring]
  simp; ring

private lemma integrable_truncExponentialPDFReal (a b rate : ℝ) :
    Integrable (truncExponentialPDFReal a b rate) := by
  rw [truncExponentialPDFReal_indicator]
  rw [integrable_indicator_iff measurableSet_Icc]
  have hcont : Continuous (fun x : ℝ =>
      rate * Real.exp (-rate * (x - a)) / (1 - Real.exp (-rate * (b - a)))) := by
    fun_prop
  exact hcont.integrableOn_Icc

/-- The truncated exponential density integrates to one when `a < b` and `rate > 0`. -/
theorem integral_truncExponentialPDFReal_eq_one (a b rate : ℝ)
    (hab : a < b) (hrate : 0 < rate) :
    ∫ x, truncExponentialPDFReal a b rate x = 1 := by
  rw [truncExponentialPDFReal_indicator, integral_indicator measurableSet_Icc]
  set c := (1 - Real.exp (-rate * (b - a)))
  have hc_pos : 0 < c := truncExponential_normConst_pos hab hrate
  have h_fun_eq :
      (fun x : ℝ => rate * Real.exp (-rate * (x - a)) / c) =
        fun x => (1 / c) * (rate * Real.exp (-rate * (x - a))) := by
    funext x; field_simp
  rw [h_fun_eq]
  rw [show ∫ x in Icc a b, (1 / c) * (rate * Real.exp (-rate * (x - a))) =
        ∫ x in a..b, (1 / c) * (rate * Real.exp (-rate * (x - a))) from by
    rw [intervalIntegral.integral_of_le hab.le]
    exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral_truncExponential_unnormalized a b rate]
  change (1 / c) * c = 1
  field_simp

/-- The `lintegral` (lower Lebesgue integral) of the truncated exponential density equals one. -/
lemma lintegral_truncExponentialPDFReal_eq_one (a b rate : ℝ)
    (hab : a < b) (hrate : 0 < rate) :
    ∫⁻ x, ENNReal.ofReal (truncExponentialPDFReal a b rate x) = 1 := by
  rw [← ENNReal.ofReal_one,
    ← integral_truncExponentialPDFReal_eq_one a b rate hab hrate]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (integrable_truncExponentialPDFReal a b rate)
    (ae_of_all _ (truncExponentialPDFReal_nonneg a b rate hab hrate))).symm

/-- Truncated exponential distribution on `[a, b]` with rate `rate > 0`. -/
noncomputable def ContDist.truncExponential (a b rate : ℝ)
    (hab : a < b) (hrate : 0 < rate) : ContDist :=
  ContDist.ofPDFReal (truncExponentialPDFReal a b rate)
    (truncExponentialPDFReal_nonneg a b rate hab hrate)
    (stronglyMeasurable_truncExponentialPDFReal a b rate)
    (lintegral_truncExponentialPDFReal_eq_one a b rate hab hrate)

/-- The density of `ContDist.truncExponential` equals `truncExponentialPDFReal`. -/
@[simp] lemma ContDist.truncExponential_density (a b rate : ℝ)
    (hab : a < b) (hrate : 0 < rate) (x : ℝ) :
    (ContDist.truncExponential a b rate hab hrate).density x =
      truncExponentialPDFReal a b rate x := rfl

/-- The left endpoint `a` is a mode of the truncated exponential distribution: The density is
decreasing on `[a, b]` and zero outside. -/
lemma ContDist.truncExponential_isMode_left (a b rate : ℝ) (hab : a < b) (hrate : 0 < rate) :
    (ContDist.truncExponential a b rate hab hrate).IsMode a := by
  have hnorm := truncExponential_normConst_pos hab hrate
  intro x
  rw [ContDist.truncExponential_density, ContDist.truncExponential_density]
  unfold truncExponentialPDFReal
  rw [if_pos (left_mem_Icc.mpr hab.le), sub_self, mul_zero, Real.exp_zero, mul_one]
  split_ifs with hx
  · -- `exp(-rate * (x - a)) ≤ 1` since `a ≤ x`
    have hexp : Real.exp (-rate * (x - a)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hx.1]
    have hnum : rate * Real.exp (-rate * (x - a)) ≤ rate := by nlinarith
    exact div_le_div_of_nonneg_right hnum hnorm.le
  · positivity

/-- The truncated exponential density vanishes outside `[a, b]`. -/
lemma ContDist.truncExponential_density_eq_zero_of_not_mem (a b rate : ℝ)
    (hab : a < b) (hrate : 0 < rate) {x : ℝ} (hx : x ∉ Set.Icc a b) :
    (ContDist.truncExponential a b rate hab hrate).density x = 0 := by
  simp [truncExponentialPDFReal, hx]

/-- **CDF of the truncated exponential distribution:** For `x < a` the CDF is `0`, for `x > b` it
is `1`, and for `a ≤ x ≤ b` it equals `(1 - exp(-rate * (x - a))) / (1 - exp(-rate * (b - a)))`. -/
theorem ContDist.truncExponential_cdf (a b rate : ℝ) (hab : a < b) (hrate : 0 < rate)
    (x : ℝ) :
    (ContDist.truncExponential a b rate hab hrate).cdf x =
      if x < a then 0
      else if x ≤ b then
        (1 - Real.exp (-rate * (x - a))) / (1 - Real.exp (-rate * (b - a)))
      else 1 := by
  set d := ContDist.truncExponential a b rate hab hrate
  have h_zero : ∀ t, t ∉ Icc a b → d.density t = 0 :=
    fun t ht => ContDist.truncExponential_density_eq_zero_of_not_mem a b rate hab hrate ht
  by_cases hxa : x < a
  · rw [if_pos hxa]
    exact d.cdf_eq_zero_of_supportsOn_Icc_left h_zero hxa
  by_cases hxb : x ≤ b
  · rw [if_neg hxa, if_pos hxb]
    push Not at hxa
    set c := (1 - Real.exp (-rate * (b - a)))
    have hc_pos : 0 < c := truncExponential_normConst_pos hab hrate
    simp only [ContDist.cdf_eq_integral, d, ContDist.truncExponential_density,
      truncExponentialPDFReal_indicator]
    rw [setIntegral_indicator measurableSet_Icc]
    have h_inter : Iic x ∩ Icc a b = Icc a x := by
      ext t
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨htx, hta, _⟩; exact ⟨hta, htx⟩
      · rintro ⟨hta, htx⟩; exact ⟨htx, hta, le_trans htx hxb⟩
    rw [h_inter]
    rw [show ∫ t in Icc a x, rate * Real.exp (-rate * (t - a)) / c =
        ∫ t in a..x, rate * Real.exp (-rate * (t - a)) / c from by
      rw [intervalIntegral.integral_of_le hxa]
      exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
    have h_fun_eq :
        (fun t : ℝ => rate * Real.exp (-rate * (t - a)) / c) =
          fun t => (1 / c) * (rate * Real.exp (-rate * (t - a))) := by
      funext t; field_simp
    rw [h_fun_eq, intervalIntegral.integral_const_mul,
      intervalIntegral_truncExponential_unnormalized a x rate]
    field_simp
  · rw [if_neg hxa, if_neg hxb]
    push Not at hxb
    exact d.cdf_eq_one_of_supportsOn_Icc_right h_zero hxb.le

/-- **Mean of the truncated exponential distribution:** The expectation of
`X ~ TruncExp(a, b, rate)` is
`E[X] = a + 1 / rate - (b - a) * exp(-rate * (b - a)) / (1 - exp(-rate * (b - a)))`. -/
theorem ContDist.truncExponential_expect (a b rate : ℝ) (hab : a < b) (hrate : 0 < rate) :
    (ContDist.truncExponential a b rate hab hrate).expect id =
      a + 1 / rate -
        (b - a) * Real.exp (-rate * (b - a)) / (1 - Real.exp (-rate * (b - a))) := by
  have hc_pos : 0 < 1 - Real.exp (-rate * (b - a)) :=
    truncExponential_normConst_pos hab hrate
  have hc_ne : (1 - Real.exp (-rate * (b - a))) ≠ 0 := hc_pos.ne'
  have hrate_ne : rate ≠ 0 := hrate.ne'
  generalize hE_def : Real.exp (-rate * (b - a)) = E
  rw [hE_def] at hc_pos hc_ne
  change ∫ x, (ContDist.truncExponential a b rate hab hrate).density x * id x = _
  simp only [id_eq, ContDist.truncExponential_density,
    truncExponentialPDFReal_indicator]
  have h_ind_eq :
      (fun x : ℝ =>
        (Icc a b).indicator
          (fun y => rate * Real.exp (-rate * (y - a)) /
            (1 - Real.exp (-rate * (b - a)))) x * x) =
      (Icc a b).indicator
        (fun x : ℝ =>
          rate * Real.exp (-rate * (x - a)) * x /
            (1 - Real.exp (-rate * (b - a)))) := by
    funext x; simp only [indicator_apply]; split_ifs <;> ring
  rw [h_ind_eq, integral_indicator measurableSet_Icc]
  rw [show ∫ x in Icc a b,
        rate * Real.exp (-rate * (x - a)) * x / (1 - Real.exp (-rate * (b - a))) =
      ∫ x in a..b,
        rate * Real.exp (-rate * (x - a)) * x / (1 - Real.exp (-rate * (b - a))) from by
    rw [intervalIntegral.integral_of_le hab.le]
    exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  -- Split `x = (x - a) + a`, separating into a centered moment and a mass term.
  have h_split :
      (fun x : ℝ =>
        rate * Real.exp (-rate * (x - a)) * x / (1 - Real.exp (-rate * (b - a)))) =
        fun x =>
          (1 / (1 - Real.exp (-rate * (b - a)))) *
              (rate * (x - a) * Real.exp (-rate * (x - a))) +
          (a / (1 - Real.exp (-rate * (b - a)))) *
              (rate * Real.exp (-rate * (x - a))) := by
    funext x; field_simp; ring
  rw [h_split]
  have hcont_centered : Continuous
      (fun x : ℝ => (1 / (1 - Real.exp (-rate * (b - a)))) *
        (rate * (x - a) * Real.exp (-rate * (x - a)))) := by
    fun_prop
  have hcont_mass : Continuous
      (fun x : ℝ => (a / (1 - Real.exp (-rate * (b - a)))) *
        (rate * Real.exp (-rate * (x - a)))) := by
    fun_prop
  rw [intervalIntegral.integral_add
    (hcont_centered.intervalIntegrable _ _) (hcont_mass.intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have h_translate :
      ∫ x in a..b, rate * (x - a) * Real.exp (-rate * (x - a)) =
        ∫ u in (0 : ℝ)..(b - a), rate * u * Real.exp (-rate * u) := by
    have h := intervalIntegral.integral_comp_sub_right (a := a) (b := b)
      (fun u : ℝ => rate * u * Real.exp (-rate * u)) a
    simpa using h
  rw [h_translate,
    intervalIntegral_truncExponential_first_moment_zero (b - a) rate hrate,
    intervalIntegral_truncExponential_unnormalized a b rate, hE_def]
  field_simp
  ring

end Econlib.Probability
