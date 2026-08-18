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
# Triangular distribution

This file defines the triangular density on an interval, constructs it as a continuous and interval
supported distribution, and records normalization and moment formulas.

## Main definitions

* `triangularLeft`: Left linear-ramp branch of the density on `[a, c]`.
* `triangularRight`: Right linear-ramp branch of the density on `(c, b]`.
* `triangularPDFReal`: Real-valued triangular probability density function.
* `ContDist.triangular`: Triangular distribution as a `ContDist`.

## Main statements

* `integral_triangularPDFReal_eq_one`: The density integrates to one.
* `ContDist.triangular_isMode`: The apex parameter `c` is a mode.
* `ContDist.triangular_expect`: Expectation equals `(a + b + c) / 3`.
* `ContDist.triangular_variance`: Variance equals `(a² + b² + c² - ab - ac - bc) / 18`.

## Tags

probability, continuous distributions, triangular
-/

@[expose] public section

open Set MeasureTheory

namespace Econlib.Probability

/-- Left branch of the triangular density: The linear ramp on `[a, c]` for a triangular
distribution with support `[a, b]` and mode `c`. Equals `2(x - a) / ((b - a)(c - a))`. -/
noncomputable def triangularLeft (a b c : ℝ) (x : ℝ) : ℝ :=
  2 * (x - a) / ((b - a) * (c - a))

/-- Right branch of the triangular density: The linear ramp down on `(c, b]` for a triangular
distribution with support `[a, b]` and mode `c`. Equals `2(b - x) / ((b - a)(b - c))`. -/
noncomputable def triangularRight (a b c : ℝ) (x : ℝ) : ℝ :=
  2 * (b - x) / ((b - a) * (b - c))

/-- Real-valued triangular probability density function with support `[a, b]` and mode `c`. Defined
as `triangularLeft` on `[a, c]` and `triangularRight` on `(c, b]`, and zero elsewhere. -/
noncomputable def triangularPDFReal (a b c : ℝ) (x : ℝ) : ℝ :=
  (Icc a c).indicator (triangularLeft a b c) x +
    (Ioc c b).indicator (triangularRight a b c) x

/-- The left branch of the triangular density is nonneg on `[a, c]` when `a < c < b`. -/
lemma triangularLeft_nonneg {a b c x : ℝ} (hac : a < c) (hcb : c < b) (hx : x ∈ Icc a c) :
    0 ≤ triangularLeft a b c x := by
  unfold triangularLeft
  have hxa : 0 ≤ x - a := sub_nonneg.mpr hx.1
  have hba : 0 < b - a := by linarith
  have hca : 0 < c - a := by linarith
  exact div_nonneg (by positivity) (by positivity)

/-- The right branch of the triangular density is nonneg on `(c, b]` when `a < c < b`. -/
lemma triangularRight_nonneg {a b c x : ℝ} (hac : a < c) (hcb : c < b) (hx : x ∈ Ioc c b) :
    0 ≤ triangularRight a b c x := by
  unfold triangularRight
  have hbx : 0 ≤ b - x := sub_nonneg.mpr hx.2
  have hba : 0 < b - a := by linarith
  have hbc : 0 < b - c := by linarith
  exact div_nonneg (by positivity) (by positivity)

/-- The triangular density is nonneg everywhere when `a < c < b`. -/
lemma triangularPDFReal_nonneg (a b c : ℝ) (hac : a < c) (hcb : c < b) (x : ℝ) :
    0 ≤ triangularPDFReal a b c x := by
  unfold triangularPDFReal
  by_cases hx1 : x ∈ Icc a c
  · have hx2 : x ∉ Ioc c b := by
      intro hx
      exact not_lt_of_ge hx1.2 hx.1
    simp [hx1, hx2, triangularLeft_nonneg hac hcb hx1]
  · by_cases hx2 : x ∈ Ioc c b
    · simp [hx1, hx2, triangularRight_nonneg hac hcb hx2]
    · simp [hx1, hx2]

/-- The triangular density is measurable. -/
lemma measurable_triangularPDFReal (a b c : ℝ) :
    Measurable (triangularPDFReal a b c) := by
  unfold triangularPDFReal triangularLeft triangularRight
  refine (Measurable.indicator ?_ measurableSet_Icc).add
    (Measurable.indicator ?_ measurableSet_Ioc)
  · fun_prop
  · fun_prop

/-- The triangular density is strongly measurable. -/
lemma stronglyMeasurable_triangularPDFReal (a b c : ℝ) :
    StronglyMeasurable (triangularPDFReal a b c) :=
  (measurable_triangularPDFReal a b c).stronglyMeasurable

private lemma integrable_triangularLeft_indicator (a b c : ℝ) :
    Integrable ((Icc a c).indicator (triangularLeft a b c)) := by
  rw [integrable_indicator_iff measurableSet_Icc]
  have hcont : Continuous (triangularLeft a b c) := by
    unfold triangularLeft
    fun_prop
  exact hcont.integrableOn_Icc

private lemma integrable_triangularRight_indicator (a b c : ℝ) :
    Integrable ((Ioc c b).indicator (triangularRight a b c)) := by
  rw [integrable_indicator_iff measurableSet_Ioc]
  have hcont : Continuous (triangularRight a b c) := by
    unfold triangularRight
    fun_prop
  have h_intOn_Icc : IntegrableOn (triangularRight a b c) (Icc c b) := hcont.integrableOn_Icc
  exact h_intOn_Icc.mono_set <| by
    intro x hx
    exact ⟨le_of_lt hx.1, hx.2⟩

private lemma triangularPDFReal_integrable (a b c : ℝ) :
    Integrable (triangularPDFReal a b c) := by
  unfold triangularPDFReal
  exact (integrable_triangularLeft_indicator a b c).add
    (integrable_triangularRight_indicator a b c)

private lemma integrable_mul_triangularLeft_indicator (a b c : ℝ) :
    Integrable (fun x => (Icc a c).indicator (triangularLeft a b c) x * x) := by
  rw [funext fun x => (Set.indicator_mul_left (Icc a c) (triangularLeft a b c) (fun x => x)).symm,
    integrable_indicator_iff measurableSet_Icc]
  have hcont : Continuous (fun x => triangularLeft a b c x * x) := by
    unfold triangularLeft
    fun_prop
  exact hcont.integrableOn_Icc

private lemma integrable_mul_triangularRight_indicator (a b c : ℝ) :
    Integrable (fun x => (Ioc c b).indicator (triangularRight a b c) x * x) := by
  rw [funext fun x => (Set.indicator_mul_left (Ioc c b) (triangularRight a b c) (fun x => x)).symm,
    integrable_indicator_iff measurableSet_Ioc]
  have hcont : Continuous (fun x => triangularRight a b c x * x) := by
    unfold triangularRight
    fun_prop
  have h_intOn_Icc : IntegrableOn (fun x => triangularRight a b c x * x) (Icc c b) :=
    hcont.integrableOn_Icc
  exact h_intOn_Icc.mono_set <| by
    intro x hx
    exact ⟨le_of_lt hx.1, hx.2⟩

private lemma integrable_sq_mul_triangularLeft_indicator (a b c : ℝ) :
    Integrable (fun x => (Icc a c).indicator (triangularLeft a b c) x * x ^ 2) := by
  rw [funext fun x =>
      (Set.indicator_mul_left (Icc a c) (triangularLeft a b c) (fun x => x ^ 2)).symm,
    integrable_indicator_iff measurableSet_Icc]
  have hcont : Continuous (fun x => triangularLeft a b c x * x ^ 2) := by
    unfold triangularLeft
    fun_prop
  exact hcont.integrableOn_Icc

private lemma integrable_sq_mul_triangularRight_indicator (a b c : ℝ) :
    Integrable (fun x => (Ioc c b).indicator (triangularRight a b c) x * x ^ 2) := by
  rw [funext fun x =>
      (Set.indicator_mul_left (Ioc c b) (triangularRight a b c) (fun x => x ^ 2)).symm,
    integrable_indicator_iff measurableSet_Ioc]
  have hcont : Continuous (fun x => triangularRight a b c x * x ^ 2) := by
    unfold triangularRight
    fun_prop
  have h_intOn_Icc : IntegrableOn (fun x => triangularRight a b c x * x ^ 2) (Icc c b) :=
    hcont.integrableOn_Icc
  exact h_intOn_Icc.mono_set <| by
    intro x hx
    exact ⟨le_of_lt hx.1, hx.2⟩

private lemma intervalIntegral_triangularLeft (a b c : ℝ) (hac : a < c) :
    ∫ x in a..c, triangularLeft a b c x = (c - a) / (b - a) := by
  have hderiv :
      ∀ x : ℝ,
        HasDerivAt (fun y => (y - a) ^ 2 / ((b - a) * (c - a)))
          (triangularLeft a b c x) x := by
    intro x
    have hsq :
        HasDerivAt (fun y => (y - a) ^ 2) (2 * (x - a)) x := by
      convert ((hasDerivAt_pow 2 (x - a)).comp x ((hasDerivAt_id x).sub_const a)) using 1
      ring
    simpa [triangularLeft, mul_comm, mul_left_comm, mul_assoc] using
      hsq.div_const (((b - a) * (c - a)))
  have hcont : Continuous (triangularLeft a b c) := by
    unfold triangularLeft
    fun_prop
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := c)
      (fun x _ => hderiv x) (hcont.intervalIntegrable a c)
  calc
    ∫ x in a..c, triangularLeft a b c x
        = (c - a) ^ 2 / ((b - a) * (c - a)) - (a - a) ^ 2 / ((b - a) * (c - a)) := by
            simpa using hftc
      _ = (c - a) / (b - a) := by
        have hca : c - a ≠ 0 := by linarith
        field_simp [hca]
        ring

private lemma intervalIntegral_triangularRight (a b c : ℝ) (hcb : c < b) :
    ∫ x in c..b, triangularRight a b c x = (b - c) / (b - a) := by
  have hderiv :
      ∀ x : ℝ,
        HasDerivAt (fun y => -((b - y) ^ 2) / ((b - a) * (b - c)))
          (triangularRight a b c x) x := by
    intro x
    have hsq :
        HasDerivAt (fun y => (b - y) ^ 2) (-2 * (b - x)) x := by
      convert ((hasDerivAt_pow 2 (b - x)).comp x
        ((hasDerivAt_const x b).sub (hasDerivAt_id x))) using 1
      ring
    have hneg : HasDerivAt (fun y => -((b - y) ^ 2)) (2 * (b - x)) x := by
      simpa using hsq.neg
    simpa [triangularRight, mul_comm, mul_left_comm, mul_assoc] using
      hneg.div_const (((b - a) * (b - c)))
  have hcont : Continuous (triangularRight a b c) := by
    unfold triangularRight
    fun_prop
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := c) (b := b)
      (fun x _ => hderiv x) (hcont.intervalIntegrable c b)
  calc
    ∫ x in c..b, triangularRight a b c x
        = -(b - b) ^ 2 / ((b - a) * (b - c)) - -(b - c) ^ 2 / ((b - a) * (b - c)) := by
            simpa using hftc
      _ = (b - c) / (b - a) := by
        have hbc : b - c ≠ 0 := by linarith
        field_simp [hbc]
        ring

private lemma integral_triangularLeft_indicator (a b c : ℝ) (hac : a < c) :
    ∫ x, (Icc a c).indicator (triangularLeft a b c) x = (c - a) / (b - a) := by
  rw [integral_indicator measurableSet_Icc]
  rw [show ∫ x in Icc a c, triangularLeft a b c x = ∫ x in a..c, triangularLeft a b c x from by
    rw [intervalIntegral.integral_of_le (le_of_lt hac)]
    exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  exact intervalIntegral_triangularLeft a b c hac

private lemma integral_triangularRight_indicator (a b c : ℝ) (hcb : c < b) :
    ∫ x, (Ioc c b).indicator (triangularRight a b c) x = (b - c) / (b - a) := by
  rw [integral_indicator measurableSet_Ioc]
  rw [show ∫ x in Ioc c b, triangularRight a b c x = ∫ x in c..b, triangularRight a b c x from by
    rw [intervalIntegral.integral_of_le (le_of_lt hcb)]]
  exact intervalIntegral_triangularRight a b c hcb

private lemma integral_mul_triangularLeft_indicator (a b c : ℝ) (hac : a < c) (hcb : c < b) :
    ∫ x, (Icc a c).indicator (triangularLeft a b c) x * x =
      (2 * c ^ 2 - a * c - a ^ 2) / (3 * (b - a)) := by
  rw [funext fun x => (Set.indicator_mul_left (Icc a c) (triangularLeft a b c) (fun x => x)).symm,
    integral_indicator measurableSet_Icc]
  rw [show ∫ x in Icc a c, triangularLeft a b c x * x =
      ∫ x in a..c, triangularLeft a b c x * x from by
    rw [intervalIntegral.integral_of_le (le_of_lt hac)]
    exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  have hca : c - a ≠ 0 := by linarith
  have hba : b - a ≠ 0 := by linarith
  have hfun :
      (fun x => triangularLeft a b c x * x) =
        fun x => (2 / ((b - a) * (c - a))) * (x ^ 2 - a * x) := by
    funext x
    unfold triangularLeft
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  have h_int_sq : IntervalIntegrable (fun x : ℝ => x ^ 2) volume a c :=
    (continuous_id.pow 2).intervalIntegrable _ _
  have h_int_lin : IntervalIntegrable (fun x : ℝ => a * x) volume a c :=
    ((continuous_const).mul continuous_id).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h_int_sq h_int_lin, integral_sq_Icc,
    intervalIntegral.integral_const_mul, integral_id_Icc]
  field_simp [hca, hba]
  ring

private lemma integral_mul_triangularRight_indicator (a b c : ℝ) (hac : a < c) (hcb : c < b) :
    ∫ x, (Ioc c b).indicator (triangularRight a b c) x * x =
      (b ^ 2 + b * c - 2 * c ^ 2) / (3 * (b - a)) := by
  rw [funext fun x => (Set.indicator_mul_left (Ioc c b) (triangularRight a b c) (fun x => x)).symm,
    integral_indicator measurableSet_Ioc]
  rw [show ∫ x in Ioc c b, triangularRight a b c x * x =
      ∫ x in c..b, triangularRight a b c x * x from by
    rw [intervalIntegral.integral_of_le (le_of_lt hcb)]]
  have hbc : b - c ≠ 0 := by linarith
  have hba : b - a ≠ 0 := by linarith
  have hfun :
      (fun x => triangularRight a b c x * x) =
        fun x => (2 / ((b - a) * (b - c))) * (b * x - x ^ 2) := by
    funext x
    unfold triangularRight
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  have h_int_lin : IntervalIntegrable (fun x : ℝ => b * x) volume c b :=
    ((continuous_const).mul continuous_id).intervalIntegrable _ _
  have h_int_sq : IntervalIntegrable (fun x : ℝ => x ^ 2) volume c b :=
    (continuous_id.pow 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h_int_lin h_int_sq, intervalIntegral.integral_const_mul,
    integral_id_Icc, integral_sq_Icc]
  field_simp [hbc, hba]
  ring

private lemma integral_sq_mul_triangularLeft_indicator (a b c : ℝ) (hac : a < c) (hcb : c < b) :
    ∫ x, (Icc a c).indicator (triangularLeft a b c) x * x ^ 2 =
      (3 * c ^ 3 - a * c ^ 2 - a ^ 2 * c - a ^ 3) / (6 * (b - a)) := by
  rw [funext fun x =>
      (Set.indicator_mul_left (Icc a c) (triangularLeft a b c) (fun x => x ^ 2)).symm,
    integral_indicator measurableSet_Icc]
  rw [show ∫ x in Icc a c, triangularLeft a b c x * x ^ 2 =
      ∫ x in a..c, triangularLeft a b c x * x ^ 2 from by
    rw [intervalIntegral.integral_of_le (le_of_lt hac)]
    exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
  have hca : c - a ≠ 0 := by linarith
  have hba : b - a ≠ 0 := by linarith
  have hfun :
      (fun x => triangularLeft a b c x * x ^ 2) =
        fun x => (2 / ((b - a) * (c - a))) * (x ^ 3 - a * x ^ 2) := by
    funext x
    unfold triangularLeft
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  have h_int_cube : IntervalIntegrable (fun x : ℝ => x ^ 3) volume a c :=
    (continuous_id.pow 3).intervalIntegrable _ _
  have h_int_sq : IntervalIntegrable (fun x : ℝ => a * x ^ 2) volume a c :=
    ((continuous_const).mul (continuous_id.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h_int_cube h_int_sq, integral_cube_Icc,
    intervalIntegral.integral_const_mul, integral_sq_Icc]
  field_simp [hca, hba]
  ring

private lemma integral_sq_mul_triangularRight_indicator (a b c : ℝ) (hac : a < c) (hcb : c < b) :
    ∫ x, (Ioc c b).indicator (triangularRight a b c) x * x ^ 2 =
      (b ^ 3 + b ^ 2 * c + b * c ^ 2 - 3 * c ^ 3) / (6 * (b - a)) := by
  rw [funext fun x =>
      (Set.indicator_mul_left (Ioc c b) (triangularRight a b c) (fun x => x ^ 2)).symm,
    integral_indicator measurableSet_Ioc]
  rw [show ∫ x in Ioc c b, triangularRight a b c x * x ^ 2 =
      ∫ x in c..b, triangularRight a b c x * x ^ 2 from by
    rw [intervalIntegral.integral_of_le (le_of_lt hcb)]]
  have hbc : b - c ≠ 0 := by linarith
  have hba : b - a ≠ 0 := by linarith
  have hfun :
      (fun x => triangularRight a b c x * x ^ 2) =
        fun x => (2 / ((b - a) * (b - c))) * (b * x ^ 2 - x ^ 3) := by
    funext x
    unfold triangularRight
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  have h_int_sq : IntervalIntegrable (fun x : ℝ => b * x ^ 2) volume c b :=
    ((continuous_const).mul (continuous_id.pow 2)).intervalIntegrable _ _
  have h_int_cube : IntervalIntegrable (fun x : ℝ => x ^ 3) volume c b :=
    (continuous_id.pow 3).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h_int_sq h_int_cube, intervalIntegral.integral_const_mul,
    integral_sq_Icc, integral_cube_Icc]
  field_simp [hbc, hba]
  ring

/-- The triangular density integrates to one: `∫ x, triangularPDFReal a b c x = 1`. -/
theorem integral_triangularPDFReal_eq_one (a b c : ℝ) (hac : a < c) (hcb : c < b) :
    ∫ x, triangularPDFReal a b c x = 1 := by
  unfold triangularPDFReal
  rw [integral_add (integrable_triangularLeft_indicator a b c)
    (integrable_triangularRight_indicator a b c)]
  rw [integral_triangularLeft_indicator a b c hac, integral_triangularRight_indicator a b c hcb]
  have hba : b - a ≠ 0 := by linarith
  field_simp [hba]
  ring

/-- The lower Lebesgue integral of `ENNReal.ofReal ∘ triangularPDFReal a b c` equals one. -/
lemma lintegral_triangularPDFReal_eq_one (a b c : ℝ) (hac : a < c) (hcb : c < b) :
    ∫⁻ x, ENNReal.ofReal (triangularPDFReal a b c x) = 1 := by
  rw [← ENNReal.ofReal_one, ← integral_triangularPDFReal_eq_one a b c hac hcb]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (triangularPDFReal_integrable a b c)
    (ae_of_all _ (triangularPDFReal_nonneg a b c hac hcb))).symm

/-- The triangular continuous distribution on `[a, b]` with mode `c`, constructed from
`triangularPDFReal` via `ContDist.ofPDFReal`. Requires `a < c < b`. -/
noncomputable def ContDist.triangular (a b c : ℝ) (hac : a < c) (hcb : c < b) : ContDist :=
  ContDist.ofPDFReal (triangularPDFReal a b c)
    (triangularPDFReal_nonneg a b c hac hcb)
    (stronglyMeasurable_triangularPDFReal a b c)
    (lintegral_triangularPDFReal_eq_one a b c hac hcb)

/-- The density of the triangular distribution is zero outside its support `[a, b]`. -/
lemma ContDist.triangular_density_eq_zero_of_not_mem (a b c : ℝ) (hac : a < c) (hcb : c < b)
    {x : ℝ} (hx : x ∉ Set.Icc a b) : (ContDist.triangular a b c hac hcb).density x = 0 := by
  unfold ContDist.triangular ContDist.ofPDFReal triangularPDFReal
  by_cases hx1 : x ∈ Icc a c
  · exfalso
    exact hx ⟨hx1.1, hx1.2.trans (le_of_lt hcb)⟩
  · by_cases hx2 : x ∈ Ioc c b
    · exfalso
      exact hx ⟨le_of_lt (lt_trans hac hx2.1), hx2.2⟩
    · simp [hx1, hx2]

/-- The density of `ContDist.triangular a b c hac hcb` equals `triangularPDFReal a b c`. -/
@[simp] lemma ContDist.triangular_density (a b c : ℝ) (hac : a < c) (hcb : c < b) (x : ℝ) :
    (ContDist.triangular a b c hac hcb).density x = triangularPDFReal a b c x := rfl

/-- The CDF of the triangular distribution equals the integral of the density over `(-∞, x]`. -/
lemma ContDist.triangular_cdf (a b c : ℝ) (hac : a < c) (hcb : c < b) (x : ℝ) :
    (ContDist.triangular a b c hac hcb).cdf x = ∫ t in Set.Iic x, triangularPDFReal a b c t := by
  simp [ContDist.cdf_eq_integral]

/-- The apex parameter `c` is a mode of the triangular distribution: Both linear ramps are
dominated by the peak value `2 / (b - a)` attained at `c`. -/
lemma ContDist.triangular_isMode (a b c : ℝ) (hac : a < c) (hcb : c < b) :
    (ContDist.triangular a b c hac hcb).IsMode c := by
  have hba : (0 : ℝ) < b - a := by linarith
  have hca : (0 : ℝ) < c - a := by linarith
  have hbc : (0 : ℝ) < b - c := by linarith
  -- The density at the apex equals the peak value `2 / (b - a)`.
  have hpeak : (ContDist.triangular a b c hac hcb).density c = 2 / (b - a) := by
    rw [ContDist.triangular_density]
    unfold triangularPDFReal
    rw [Set.indicator_of_mem (by constructor <;> linarith : c ∈ Icc a c),
      Set.indicator_of_notMem (by simp), add_zero]
    unfold triangularLeft
    rw [mul_comm (b - a) (c - a), ← div_div]
    rw [mul_div_assoc, div_self hca.ne']
    ring
  intro x
  rw [hpeak, ContDist.triangular_density]
  unfold triangularPDFReal
  by_cases hx1 : x ∈ Icc a c
  · rw [Set.indicator_of_mem hx1,
      Set.indicator_of_notMem (fun hx2 => absurd hx1.2 (not_le.mpr hx2.1)), add_zero]
    unfold triangularLeft
    -- `2(x - a) ≤ 2(c - a)` since `x ≤ c`, then divide by `(b - a)(c - a) > 0`
    rw [div_le_div_iff₀ (by positivity) hba]
    nlinarith [hx1.2]
  · by_cases hx2 : x ∈ Ioc c b
    · rw [Set.indicator_of_notMem hx1, Set.indicator_of_mem hx2, zero_add]
      unfold triangularRight
      -- `2(b - x) ≤ 2(b - c)` since `c < x`, then divide by `(b - a)(b - c) > 0`
      rw [div_le_div_iff₀ (by positivity) hba]
      nlinarith [hx2.1]
    · rw [Set.indicator_of_notMem hx1, Set.indicator_of_notMem hx2, add_zero]
      positivity

/-- **Expectation of the triangular distribution:** `E[X] = (a + b + c) / 3`. -/
theorem ContDist.triangular_expect (a b c : ℝ) (hac : a < c) (hcb : c < b) :
    (ContDist.triangular a b c hac hcb).expect id = (a + b + c) / 3 := by
  simp only [ContDist.expect, ContDist.triangular_density, id]
  unfold triangularPDFReal
  have h_eq :
      (fun x : ℝ => ((Icc a c).indicator (triangularLeft a b c) x +
        (Ioc c b).indicator (triangularRight a b c) x) * x) =
      (fun x : ℝ => (Icc a c).indicator (triangularLeft a b c) x * x +
        (Ioc c b).indicator (triangularRight a b c) x * x) := by
    funext x
    ring
  rw [h_eq]
  rw [integral_add (integrable_mul_triangularLeft_indicator a b c)
    (integrable_mul_triangularRight_indicator a b c)]
  rw [integral_mul_triangularLeft_indicator a b c hac hcb,
    integral_mul_triangularRight_indicator a b c hac hcb]
  have hba : b - a ≠ 0 := by linarith
  field_simp [hba]
  ring

/-- **Variance of the triangular distribution:** `Var[X] = (a² + b² + c² - ab - ac - bc) / 18`. -/
theorem ContDist.triangular_variance (a b c : ℝ) (hac : a < c) (hcb : c < b) :
    (ContDist.triangular a b c hac hcb).variance id =
      (a ^ 2 + b ^ 2 + c ^ 2 - a * b - a * c - b * c) / 18 := by
  simp only [ContDist.variance, ContDist.expect, ContDist.triangular_density, id]
  unfold triangularPDFReal
  have h_mean_eq :
      (fun x : ℝ => ((Icc a c).indicator (triangularLeft a b c) x +
        (Ioc c b).indicator (triangularRight a b c) x) * x) =
      (fun x : ℝ => (Icc a c).indicator (triangularLeft a b c) x * x +
        (Ioc c b).indicator (triangularRight a b c) x * x) := by
    funext x
    ring
  have h_mean :
      ∫ x, ((Icc a c).indicator (triangularLeft a b c) x +
        (Ioc c b).indicator (triangularRight a b c) x) * x = (a + b + c) / 3 := by
    simpa [ContDist.expect, ContDist.triangular_density, id, triangularPDFReal, h_mean_eq] using
      ContDist.triangular_expect a b c hac hcb
  have h_eq :
      (fun x : ℝ => ((Icc a c).indicator (triangularLeft a b c) x +
        (Ioc c b).indicator (triangularRight a b c) x) * x ^ 2) =
      (fun x : ℝ => (Icc a c).indicator (triangularLeft a b c) x * x ^ 2 +
        (Ioc c b).indicator (triangularRight a b c) x * x ^ 2) := by
    funext x
    ring
  rw [h_eq]
  rw [integral_add (integrable_sq_mul_triangularLeft_indicator a b c)
    (integrable_sq_mul_triangularRight_indicator a b c)]
  rw [integral_sq_mul_triangularLeft_indicator a b c hac hcb,
    integral_sq_mul_triangularRight_indicator a b c hac hcb, h_mean]
  have hba : b - a ≠ 0 := by linarith
  field_simp [hba]
  ring

/-- The symmetric triangular distribution (mode at the midpoint `(a + b) / 2`) has expectation
equal to the midpoint `(a + b) / 2`. -/
lemma ContDist.triangular_expect_symmetric (a b : ℝ) (hab : a < b) :
    (ContDist.triangular a b ((a + b) / 2)
      (by linarith) (by linarith)).expect id = (a + b) / 2 := by
  rw [ContDist.triangular_expect a b ((a + b) / 2) (by linarith) (by linarith)]
  ring

end Econlib.Probability
