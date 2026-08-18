/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.IntegralReal
public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.ContDist.CDF
public import Econlib.Probability.ContDist.CDFStieltjes
public import Mathlib.Probability.Distributions.Beta

/-!
# Beta distribution

This file constructs beta distributions as continuous distributions and records density,
expectation, variance, and CDF formulas. It also introduces the mean-and-concentration
parametrization `betaWithMean pi κ = Beta(κπ, κ(1−π))`, the strict concavity of its log-weight, the
U-shape of the density ratio under concentration change, and the boundary / integrated-CDF
identities for that family.

## Main definitions

* `ContDist.beta`: Beta distribution as a continuous distribution.
* `betaWithMean`: The mean-π, concentration-κ parametrization.

## Main statements

* `integral_betaPDFReal_eq_one`: Normalization of the beta density.
* `ContDist.beta_expect`, `ContDist.beta_variance`, `ContDist.beta_cdf`: Moment / CDF formulas.
* `betaWithMean_expect`, `betaWithMean_variance`: Moments of `betaWithMean`.
* `betaWithMean_integrable_mul_continuous`: The density times a continuous function is integrable.
* `beta_logWeight_strictConcave`, `beta_density_ratio_Ushaped`: Log-weight concavity and the
  U-shaped density ratio.
* `betaWithMean_cdf_zero`, `betaWithMean_cdf_one`, `betaWithMean_integrated_cdf`: Boundary and
  integrated-CDF identities.

## Tags

probability, continuous distributions, beta
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace Econlib.Probability

/-! ## Bridge lemmas: `betaPDFReal` and `ContDist` -/

/-- `betaPDFReal α β` is nonneg for positive shape parameters. -/
lemma betaPDFReal_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    0 ≤ betaPDFReal α β x := by
  by_cases h : 0 < x ∧ x < 1
  · exact le_of_lt (betaPDFReal_pos h.1 h.2 hα hβ)
  · simp [betaPDFReal, h]

/-- `betaPDFReal α β x = 0` whenever `x ∉ (0, 1)`. -/
lemma betaPDFReal_eq_zero_of_not_mem (α β : ℝ) {x : ℝ} (hx : ¬(0 < x ∧ x < 1)) :
    betaPDFReal α β x = 0 := by
  simp [betaPDFReal, hx]

/-- `ENNReal.ofReal ∘ betaPDFReal α β` equals the `ℝ≥0∞`-valued `betaPDF α β`. -/
lemma ofReal_betaPDFReal_eq_betaPDF (α β : ℝ) :
    (fun x => ENNReal.ofReal (betaPDFReal α β x)) = betaPDF α β := by
  ext x; simp [betaPDF, betaPDFReal]

/-- The beta density integrates to 1: `∫ x, betaPDFReal α β x = 1` for positive shape parameters. -/
lemma integral_betaPDFReal_eq_one (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, betaPDFReal α β x = 1 :=
  integral_eq_one_of_lintegral_ofReal_eq_one
    (betaPDFReal_nonneg hα hβ)
    (stronglyMeasurable_betaPDFReal α β)
    (by rw [ofReal_betaPDFReal_eq_betaPDF, lintegral_betaPDF_eq_one hα hβ])

/-! ## Beta distribution as a `ContDist` -/

/-- Beta distribution with shape parameters `α` and `β`. -/
noncomputable def ContDist.beta (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : ContDist where
  density := betaPDFReal α β
  nonneg := betaPDFReal_nonneg hα hβ
  integrable := integrable_of_lintegral_ofReal_eq_one
    (betaPDFReal_nonneg hα hβ)
    (stronglyMeasurable_betaPDFReal α β)
    (by rw [ofReal_betaPDFReal_eq_betaPDF, lintegral_betaPDF_eq_one hα hβ])
  integral_one := integral_betaPDFReal_eq_one α β hα hβ

/-- The beta density vanishes outside `[0, 1]`. -/
lemma ContDist.beta_density_eq_zero_of_not_mem (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) : (ContDist.beta α β hα hβ).density x = 0 := by
  simp only [ContDist.beta]
  refine betaPDFReal_eq_zero_of_not_mem α β ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rintro ⟨hx0, hx1⟩
  rcases hx with hx | hx <;> linarith

@[simp] lemma ContDist.beta_density (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    (ContDist.beta α β hα hβ).density x = betaPDFReal α β x := rfl

/-- Explicit formula for the beta density at interior points `x ∈ (0, 1)`. -/
lemma ContDist.beta_density_eq (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (x : ℝ)
    (hx0 : 0 < x) (hx1 : x < 1) :
    (ContDist.beta α β hα hβ).density x =
      (1 / ProbabilityTheory.beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1) := by
  simp [betaPDFReal, hx0, hx1]

/-- The ratio `B(α+1,β) / B(α,β) = α / (α+β)` via Gamma recurrence. -/
private lemma beta_ratio (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ProbabilityTheory.beta (α + 1) β / ProbabilityTheory.beta α β = α / (α + β) := by
  simp only [ProbabilityTheory.beta]
  rw [Real.Gamma_add_one (ne_of_gt hα),
      show α + 1 + β = (α + β) + 1 from by ring,
      Real.Gamma_add_one (ne_of_gt (add_pos hα hβ))]
  field_simp

/-- Pointwise: `betaPDFReal α β x * x = (B(α+1,β)/B(α,β)) * betaPDFReal (α+1) β x`. -/
private lemma betaPDFReal_mul_id (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    betaPDFReal α β x * x =
      (ProbabilityTheory.beta (α + 1) β / ProbabilityTheory.beta α β) *
        betaPDFReal (α + 1) β x := by
  simp only [betaPDFReal]
  split_ifs with h1
  · have hx_ne : x ≠ 0 := ne_of_gt h1.1
    have hB : (beta α β) ≠ 0 := (beta_pos hα hβ).ne'
    have hB1 : (beta (α + 1) β) ≠ 0 := (beta_pos (by linarith : 0 < α + 1) hβ).ne'
    have key : x ^ (α - 1) * x = x ^ α := by
      rw [← Real.rpow_add_one hx_ne, sub_add_cancel]
    rw [show (α + 1 - 1 : ℝ) = α from by ring,
        show (1 : ℝ) / beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1) * x =
            1 / beta α β * (x ^ (α - 1) * x) * (1 - x) ^ (β - 1) from by ring,
        key]
    field_simp
  · ring

/-- The mean of a Beta(α, β) distribution is `α / (α + β)`. -/
lemma ContDist.beta_expect (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (ContDist.beta α β hα hβ).expect id = α / (α + β) := by
  simp only [ContDist.expect, ContDist.beta, id]
  have hα1 : (0 : ℝ) < α + 1 := by linarith
  have : (fun x => betaPDFReal α β x * x) = fun x =>
      (ProbabilityTheory.beta (α + 1) β / ProbabilityTheory.beta α β) *
        betaPDFReal (α + 1) β x :=
    funext (fun x => betaPDFReal_mul_id α β x hα hβ)
  rw [this, integral_const_mul, integral_betaPDFReal_eq_one (α + 1) β hα1 hβ, mul_one,
      beta_ratio α β hα hβ]

/-- The ratio `B(α+2,β) / B(α,β) = α(α+1) / ((α+β)(α+β+1))`. -/
private lemma beta_ratio_sq (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    ProbabilityTheory.beta (α + 2) β / ProbabilityTheory.beta α β =
      α * (α + 1) / ((α + β) * (α + β + 1)) := by
  simp only [ProbabilityTheory.beta]
  rw [show α + 2 = (α + 1) + 1 from by ring,
      Real.Gamma_add_one (ne_of_gt (by linarith : 0 < α + 1)),
      Real.Gamma_add_one (ne_of_gt hα),
      show (α + 1 + 1 + β : ℝ) = ((α + β) + 1) + 1 from by ring,
      Real.Gamma_add_one (ne_of_gt (by linarith : 0 < (α + β) + 1)),
      Real.Gamma_add_one (ne_of_gt (add_pos hα hβ))]
  field_simp

/-- Pointwise: `betaPDFReal α β x * x^2 = (B(α+2,β)/B(α,β)) * betaPDFReal (α+2) β x`. -/
private lemma betaPDFReal_mul_sq (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    betaPDFReal α β x * x ^ 2 =
      (ProbabilityTheory.beta (α + 2) β / ProbabilityTheory.beta α β) *
        betaPDFReal (α + 2) β x := by
  simp only [betaPDFReal]
  split_ifs with h1
  · have hx_ne : x ≠ 0 := ne_of_gt h1.1
    have hB : (beta α β) ≠ 0 := (beta_pos hα hβ).ne'
    have hB2 : (beta (α + 2) β) ≠ 0 := (beta_pos (by linarith : 0 < α + 2) hβ).ne'
    have key : x ^ (α - 1) * x ^ 2 = x ^ (α + 1) := by
      rw [← Real.rpow_natCast x 2, ← Real.rpow_add h1.1]
      congr 1; ring
    rw [show (α + 2 - 1 : ℝ) = α + 1 from by ring,
        show (1 : ℝ) / beta α β * x ^ (α - 1) * (1 - x) ^ (β - 1) * x ^ 2 =
            1 / beta α β * (x ^ (α - 1) * x ^ 2) * (1 - x) ^ (β - 1) from by ring,
        key]
    field_simp
  · ring

/-- The variance of a Beta(α, β) distribution is `αβ / ((α+β)² (α+β+1))`. -/
lemma ContDist.beta_variance (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    (ContDist.beta α β hα hβ).variance id =
      α * β / ((α + β) ^ 2 * (α + β + 1)) := by
  simp only [ContDist.variance, ContDist.expect, ContDist.beta, id]
  have hα2 : (0 : ℝ) < α + 2 := by linarith
  have h_sq : (fun x => betaPDFReal α β x * (x ^ 2)) = fun x =>
      (ProbabilityTheory.beta (α + 2) β / ProbabilityTheory.beta α β) *
        betaPDFReal (α + 2) β x :=
    funext (fun x => betaPDFReal_mul_sq α β x hα hβ)
  rw [h_sq, integral_const_mul, integral_betaPDFReal_eq_one (α + 2) β hα2 hβ, mul_one,
      beta_ratio_sq α β hα hβ]
  have hα1 : (0 : ℝ) < α + 1 := by linarith
  have h_id : (fun x => betaPDFReal α β x * x) = fun x =>
      (ProbabilityTheory.beta (α + 1) β / ProbabilityTheory.beta α β) *
        betaPDFReal (α + 1) β x :=
    funext (fun x => betaPDFReal_mul_id α β x hα hβ)
  rw [h_id, integral_const_mul, integral_betaPDFReal_eq_one (α + 1) β hα1 hβ, mul_one,
      beta_ratio α β hα hβ]
  have hab_pos : (0 : ℝ) < α + β := add_pos hα hβ
  have hab1_pos : (0 : ℝ) < α + β + 1 := by linarith
  field_simp; ring

/-- The CDF of `ContDist.beta α β` equals the integral of `betaPDFReal α β` over `(-∞, x]`. -/
lemma ContDist.beta_cdf (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    (ContDist.beta α β hα hβ).cdf x = ∫ t in Set.Iic x, betaPDFReal α β t := by
  simp [ContDist.cdf_eq_integral, ContDist.beta_density]

/-! ## Beta-with-mean parametrization and density-ratio U-shape -/

section BetaWithMean

/-- Beta distribution with mean π and concentration κ: Beta(κπ, κ(1−π)). Lower κ means more
dispersed (higher variance). -/
noncomputable def betaWithMean (pi kappa : ℝ)
    (hpi_pos : 0 < pi) (hpi_lt : pi < 1) (hkappa : 0 < kappa) : ContDist :=
  ContDist.beta (kappa * pi) (kappa * (1 - pi))
    (mul_pos hkappa hpi_pos) (mul_pos hkappa (by linarith))

variable {pi kappa : ℝ} (hpi_pos : 0 < pi) (hpi_lt : pi < 1) (hkappa : 0 < kappa)

/-- The mean of `betaWithMean pi kappa` equals `pi`, independent of the concentration `kappa`. -/
lemma betaWithMean_expect :
    (betaWithMean pi kappa hpi_pos hpi_lt hkappa).expect id = pi := by
  unfold betaWithMean
  rw [ContDist.beta_expect]
  have hk_ne : kappa ≠ 0 := ne_of_gt hkappa
  have : kappa * pi + kappa * (1 - pi) = kappa := by ring
  rw [this, mul_div_cancel_left₀ _ hk_ne]

/-- The variance of `betaWithMean pi kappa` equals `pi * (1 - pi) / (kappa + 1)`. -/
lemma betaWithMean_variance :
    (betaWithMean pi kappa hpi_pos hpi_lt hkappa).variance id =
      pi * (1 - pi) / (kappa + 1) := by
  unfold betaWithMean
  rw [ContDist.beta_variance]
  have hk_ne : kappa ≠ 0 := ne_of_gt hkappa
  have hk1_ne : kappa + 1 ≠ 0 := ne_of_gt (by linarith)
  have hsum : kappa * pi + kappa * (1 - pi) = kappa := by ring
  rw [hsum]
  field_simp

/-- The variance of `betaWithMean pi` is strictly decreasing in the concentration parameter:
`κ₁ < κ₂` implies `pi * (1 - pi) / (κ₂ + 1) < pi * (1 - pi) / (κ₁ + 1)`. -/
lemma betaWithMean_variance_lt
    (hpi_pos : 0 < pi) (hpi_lt : pi < 1)
    {κ₁ κ₂ : ℝ} (hk1 : 0 < κ₁) (hlt : κ₁ < κ₂) :
    pi * (1 - pi) / (κ₂ + 1) < pi * (1 - pi) / (κ₁ + 1) := by
  exact div_lt_div_of_pos_left (mul_pos hpi_pos (by linarith)) (by linarith) (by linarith)

/-- The pointwise product of a `betaWithMean` density with a continuous function is integrable.
Since the Beta density vanishes outside `(0, 1)` and a continuous function is bounded on the
compact interval `[0, 1]`, the product is dominated by a scalar multiple of the density, which is
integrable. -/
lemma betaWithMean_integrable_mul_continuous (f : ℝ → ℝ) (hf : Continuous f) :
    MeasureTheory.Integrable
      (fun x => (betaWithMean pi kappa hpi_pos hpi_lt hkappa).density x * f x) := by
  set d := betaWithMean pi kappa hpi_pos hpi_lt hkappa
  have hf_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, ‖f x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hf.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun x hx => (hC x hx).trans (le_max_left _ _)⟩
  obtain ⟨C, hC_pos, hC_bound⟩ := hf_bdd
  have hdom : ∀ x, ‖d.density x * f x‖ ≤ C * d.density x := by
    intro x
    rw [norm_mul]
    by_cases hx : 0 < x ∧ x < 1
    · calc ‖d.density x‖ * ‖f x‖
          ≤ ‖d.density x‖ * C := by
            apply mul_le_mul_of_nonneg_left
            · exact hC_bound x ⟨le_of_lt hx.1, le_of_lt hx.2⟩
            · exact norm_nonneg _
        _ = C * d.density x := by
            rw [mul_comm, Real.norm_of_nonneg (d.nonneg x)]
    · -- The Beta density vanishes outside (0, 1).
      have hdx : d.density x = 0 := by
        change ProbabilityTheory.betaPDFReal _ _ x = 0
        unfold ProbabilityTheory.betaPDFReal
        simp [hx]
      simp [hdx]
  have hint_bound : MeasureTheory.Integrable (fun x => C * d.density x) :=
    d.integrable.const_mul C
  exact hint_bound.mono'
    (d.integrable.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall hdom)

/-- The weight function `g(x) = π log x + (1-π) log(1-x)` is strictly concave on `(0,1)` with
maximum at `x = π`. This drives the U-shape of the Beta density ratio under concentration change. -/
lemma beta_logWeight_strictConcave
    (hpi_pos : 0 < pi) (hpi_lt : pi < 1) :
    StrictConcaveOn ℝ (Ioo 0 1)
      (fun x : ℝ => pi * Real.log x + (1 - pi) * Real.log (1 - x)) := by
  have hA : StrictConcaveOn ℝ (Ioo 0 1) Real.log := by
    have : StrictConcaveOn ℝ (Ioi 0) Real.log := strictConcaveOn_log_Ioi
    exact this.subset (fun x hx => hx.1) (convex_Ioo 0 1)
  -- x ↦ log (1 - x) strictly concave on (0,1), via precomposition with affine 1 - x
  have hB : StrictConcaveOn ℝ (Ioo 0 1) (fun x : ℝ => Real.log (1 - x)) := by
    refine ⟨convex_Ioo 0 1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hx' : (1 - x) ∈ Ioi 0 := by simp; linarith [hx.2]
    have hy' : (1 - y) ∈ Ioi 0 := by simp; linarith [hy.2]
    have hxy' : 1 - x ≠ 1 - y := fun h => hxy (by linarith)
    have key := strictConcaveOn_log_Ioi.2 hx' hy' hxy' ha hb hab
    simp only [smul_eq_mul, gt_iff_lt]
    have : a * (1 - x) + b * (1 - y) = 1 - (a * x + b * y) := by linarith
    rw [← this]
    simpa [smul_eq_mul] using key
  refine ⟨convex_Ioo 0 1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have kA := hA.2 hx hy hxy ha hb hab
  have kB := hB.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at kA kB ⊢
  nlinarith [kA, kB, hpi_pos, mul_pos ha hb]

/-- The Beta density ratio `f_{κ₁}/f_{κ₂}` on `(0,1)` equals `C · exp((κ₁-κ₂)·g(x))` where
`g(x) = π log x + (1-π) log(1-x)`. Since `κ₁ < κ₂` and `g` is strictly concave with maximum at `π`,
the ratio is U-shaped: Decreasing on `(0,π)` and increasing on `(π,1)`. -/
lemma beta_density_ratio_Ushaped {κ₁ κ₂ : ℝ}
    (hk1 : 0 < κ₁) (hk2 : 0 < κ₂) (hlt : κ₁ < κ₂) :
    let d₁ := betaWithMean pi κ₁ hpi_pos hpi_lt hk1
    let d₂ := betaWithMean pi κ₂ hpi_pos hpi_lt hk2
    (∀ x₁ x₂, x₁ ∈ Ioo 0 pi → x₂ ∈ Ioo 0 pi → x₁ < x₂ →
      d₁.density x₂ * d₂.density x₁ ≤ d₁.density x₁ * d₂.density x₂) ∧
    (∀ x₁ x₂, x₁ ∈ Ioo pi 1 → x₂ ∈ Ioo pi 1 → x₁ < x₂ →
      d₁.density x₁ * d₂.density x₂ ≤ d₁.density x₂ * d₂.density x₁) := by
  intro d₁ d₂
  have h1mpi : 0 < 1 - pi := by linarith
  set g := fun x : ℝ => pi * Real.log x + (1 - pi) * Real.log (1 - x) with hg_def
  have g_deriv : ∀ x : ℝ, 0 < x → x < 1 →
    HasDerivAt g (pi / x - (1 - pi) / (1 - x)) x := by
    intro x hx_pos hx_lt
    have hd_log : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (ne_of_gt hx_pos)
    have hd_log1x : HasDerivAt (fun t => Real.log (1 - t)) (-(1 - x)⁻¹) x :=
      HasDerivAt.comp_const_sub 1 x (Real.hasDerivAt_log (by linarith))
    have := (hd_log.const_mul pi).add (hd_log1x.const_mul (1 - pi))
    convert this using 1
    ring
  have g_cont : ContinuousOn g (Ioo 0 1) := fun x hx =>
    ((g_deriv x hx.1 hx.2).continuousAt).continuousWithinAt
  -- g is strictly increasing on (0,π) and strictly decreasing on (π,1)
  have g_incr : StrictMonoOn g (Ioc 0 pi) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioc 0 pi)
      (g_cont.mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hpi_lt⟩))
      (fun x hx => by
        rw [interior_Ioc] at hx
        exact (g_deriv x hx.1 (lt_trans hx.2 hpi_lt)).hasDerivWithinAt)
    intro x hx
    rw [interior_Ioc] at hx
    have h1x : 0 < 1 - x := by linarith [lt_trans hx.2 hpi_lt]
    rw [sub_pos, div_lt_div_iff₀ h1x hx.1]
    nlinarith [hx.1, hx.2, hpi_pos]
  have g_decr : StrictAntiOn g (Ico pi 1) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ico pi 1)
      (g_cont.mono (fun x hx => ⟨lt_of_lt_of_le hpi_pos hx.1, hx.2⟩))
      (fun x hx => by
        rw [interior_Ico] at hx
        exact (g_deriv x (lt_trans hpi_pos hx.1) hx.2).hasDerivWithinAt)
    intro x hx
    rw [interior_Ico] at hx
    have hx0 : 0 < x := lt_trans hpi_pos hx.1
    have h1x : 0 < 1 - x := by linarith [hx.2]
    rw [sub_neg, div_lt_div_iff₀ hx0 h1x]
    nlinarith [hx.1, hx.2, h1mpi]
  have log_dens : ∀ {κ} (hκ : 0 < κ) {x}, x ∈ Ioo 0 1 →
      Real.log ((betaWithMean pi κ hpi_pos hpi_lt hκ).density x) =
        Real.log (1 / ProbabilityTheory.beta (κ * pi) (κ * (1 - pi)))
        + (κ * pi - 1) * Real.log x + (κ * (1 - pi) - 1) * Real.log (1 - x) := by
    intro κ hκ x ⟨hx0, hx1⟩
    have hB : 0 < ProbabilityTheory.beta (κ * pi) (κ * (1 - pi)) :=
      ProbabilityTheory.beta_pos (mul_pos hκ hpi_pos) (mul_pos hκ h1mpi)
    have hxp : 0 < x ^ (κ * pi - 1) := Real.rpow_pos_of_pos hx0 _
    have h1xp : 0 < (1 - x) ^ (κ * (1 - pi) - 1) := Real.rpow_pos_of_pos (by linarith) _
    have hBinv : 0 < 1 / ProbabilityTheory.beta (κ * pi) (κ * (1 - pi)) :=
      div_pos one_pos hB
    change Real.log (ProbabilityTheory.betaPDFReal (κ * pi) (κ * (1 - pi)) x) = _
    rw [show ProbabilityTheory.betaPDFReal (κ * pi) (κ * (1 - pi)) x
          = (1 / ProbabilityTheory.beta (κ * pi) (κ * (1 - pi)))
            * x ^ (κ * pi - 1) * (1 - x) ^ (κ * (1 - pi) - 1) from by
        simp [ProbabilityTheory.betaPDFReal, hx0, hx1]]
    rw [Real.log_mul (by positivity) (ne_of_gt h1xp),
        Real.log_mul (ne_of_gt hBinv) (ne_of_gt hxp),
        Real.log_rpow hx0, Real.log_rpow (by linarith)]
  have dens_pos : ∀ {κ} (hκ : 0 < κ) {x}, x ∈ Ioo 0 1 →
      0 < (betaWithMean pi κ hpi_pos hpi_lt hκ).density x := fun hκ _ hx =>
    ProbabilityTheory.betaPDFReal_pos hx.1 hx.2
      (mul_pos hκ hpi_pos) (mul_pos hκ h1mpi)
  have key : ∀ x₁ x₂, x₁ ∈ Ioo 0 1 → x₂ ∈ Ioo 0 1 → g x₁ ≤ g x₂ →
      d₁.density x₂ * d₂.density x₁ ≤ d₁.density x₁ * d₂.density x₂ := by
    intro x₁ x₂ hx₁ hx₂ hg_le
    have h11 : 0 < d₁.density x₁ := dens_pos hk1 hx₁
    have h12 : 0 < d₁.density x₂ := dens_pos hk1 hx₂
    have h21 : 0 < d₂.density x₁ := dens_pos hk2 hx₁
    have h22 : 0 < d₂.density x₂ := dens_pos hk2 hx₂
    rw [← Real.log_le_log_iff, Real.log_mul, Real.log_mul,
        log_dens hk1 hx₂, log_dens hk2 hx₁, log_dens hk1 hx₁, log_dens hk2 hx₂] <;> nlinarith
  refine ⟨fun x₁ x₂ hx₁ hx₂ h12 => key x₁ x₂
    ⟨hx₁.1, lt_trans hx₁.2 hpi_lt⟩ ⟨hx₂.1, lt_trans hx₂.2 hpi_lt⟩
    (g_incr ⟨hx₁.1, le_of_lt hx₁.2⟩ ⟨hx₂.1, le_of_lt hx₂.2⟩ h12).le,
    fun x₁ x₂ hx₁ hx₂ h12 => ?_⟩
  have hx₁_01 : x₁ ∈ Ioo 0 1 := ⟨lt_trans hpi_pos hx₁.1, hx₁.2⟩
  have hx₂_01 : x₂ ∈ Ioo 0 1 := ⟨lt_trans hpi_pos hx₂.1, hx₂.2⟩
  exact key x₂ x₁ hx₂_01 hx₁_01
    (g_decr ⟨le_of_lt hx₁.1, hx₁.2⟩ ⟨le_of_lt hx₂.1, hx₂.2⟩ h12).le

end BetaWithMean

/-! ## CDF of `betaWithMean` -/

section BetaWithMeanCDF

variable {pi : ℝ} (hpi_pos : 0 < pi) (hpi_lt : pi < 1)

/-- The CDF of `betaWithMean` vanishes at `x ≤ 0`. -/
lemma betaWithMean_cdf_zero {κ : ℝ} (hk : 0 < κ) (x : ℝ) (hx : x ≤ 0) :
    (betaWithMean pi κ hpi_pos hpi_lt hk).cdf x = 0 := by
  simp only [ContDist.cdf_eq_integral]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro t ht
  have ht0 : t ≤ 0 := le_trans (mem_Iic.mp ht) hx
  -- betaWithMean density = betaPDFReal, which vanishes outside (0,1)
  exact betaPDFReal_eq_zero_of_not_mem _ _ fun h => not_lt.mpr ht0 h.1

/-- The CDF of `betaWithMean` equals `1` at `x ≥ 1`. -/
lemma betaWithMean_cdf_one {κ : ℝ} (hk : 0 < κ) (x : ℝ) (hx : 1 ≤ x) :
    (betaWithMean pi κ hpi_pos hpi_lt hk).cdf x = 1 := by
  set d := betaWithMean pi κ hpi_pos hpi_lt hk
  simp only [ContDist.cdf_eq_integral]
  have h_tail : ∫ t in Ioi x, d.density t = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    have ht1 : 1 ≤ t := le_trans hx (le_of_lt (mem_Ioi.mp ht))
    exact betaPDFReal_eq_zero_of_not_mem _ _ fun h => not_lt.mpr ht1 h.2
  have h_split := integral_add_compl (s := Iic x) measurableSet_Iic d.integrable
  rw [compl_Iic] at h_split
  linarith [d.integral_one]

/-- `betaPDFReal α β` is continuous at every interior point of `(0,1)`. -/
lemma betaPDFReal_continuousAt {α β x : ℝ} (_hα : 0 < α) (_hβ : 0 < β)
    (hx0 : 0 < x) (hx1 : x < 1) :
    ContinuousAt (ProbabilityTheory.betaPDFReal α β) x := by
  have hx_ne : x ≠ 0 := ne_of_gt hx0
  have h1x_ne : (1 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
  set g := fun t : ℝ => 1 / ProbabilityTheory.beta α β * t ^ (α - 1) * (1 - t) ^ (β - 1)
  have hg_cont : ContinuousAt g x :=
    (continuousAt_const.mul (ContinuousAt.rpow_const continuousAt_id (Or.inl hx_ne))).mul
      ((continuousAt_const.sub continuousAt_id).rpow_const (Or.inl h1x_ne))
  exact hg_cont.congr_of_eventuallyEq <| by
    filter_upwards [Ioo_mem_nhds hx0 hx1] with t ht
    simp only [ProbabilityTheory.betaPDFReal, g, ht.1, ht.2, and_self, ite_true]

/-- The integrated CDF of a `betaWithMean` distribution satisfies
`∫ t in [0,1], F(t) dt = 1 - π`. -/
lemma betaWithMean_integrated_cdf {κ : ℝ} (hk : 0 < κ) :
    ∫ t in Icc 0 1, (betaWithMean pi κ hpi_pos hpi_lt hk).cdf t = 1 - pi := by
  set d := betaWithMean pi κ hpi_pos hpi_lt hk
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hF0 : d.cdf 0 = 0 := betaWithMean_cdf_zero hpi_pos hpi_lt hk 0 (le_refl 0)
  have hF1 : d.cdf 1 = 1 := betaWithMean_cdf_one hpi_pos hpi_lt hk 1 (le_refl 1)
  have hF_cont : Continuous d.cdf := contdist_cdf_continuous d
  have hα_pos : 0 < κ * pi := mul_pos hk hpi_pos
  have hβ_pos : 0 < κ * (1 - pi) := mul_pos hk (by linarith)
  have hF_deriv : ∀ x ∈ Ioo (min 0 1) (max 0 1), HasDerivAt d.cdf (d.density x) x := by
    simp only [min_eq_left (by norm_num : (0:ℝ) ≤ 1), max_eq_right (by norm_num : (0:ℝ) ≤ 1)]
    intro x hx
    exact d.deriv_cdf_eq_density x (betaPDFReal_continuousAt hα_pos hβ_pos hx.1 hx.2)
  have hid_deriv : ∀ x ∈ Ioo (min 0 1) (max 0 1), HasDerivAt id (1 : ℝ) x :=
    fun x _ => hasDerivAt_id x
  have hdens_int : IntervalIntegrable d.density volume 0 1 :=
    d.integrable.intervalIntegrable
  have h1_int : IntervalIntegrable (fun _ => (1 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  -- Integration by parts: ∫₀¹ t · f(t) dt = [t · F(t)]₀¹ - ∫₀¹ F(t) dt = 1 - ∫₀¹ F(t) dt
  have h_ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    continuousOn_id hF_cont.continuousOn hid_deriv hF_deriv h1_int hdens_int
  simp only [id, one_mul] at h_ibp
  rw [hF0, hF1] at h_ibp
  have h_expect : d.expect id = pi := betaWithMean_expect hpi_pos hpi_lt hk
  -- Density vanishes outside (0,1), so the full integral of density * t localizes to [0,1]
  have h_vanish : ∀ t, t ∉ Ioo 0 1 → d.density t = 0 := by
    intro t ht
    simp only [mem_Ioo, not_and_or, not_lt] at ht
    refine betaPDFReal_eq_zero_of_not_mem _ _ ?_
    rcases ht with ht | ht
    · exact fun h => not_lt.mpr ht h.1
    · exact fun h => not_le.mpr h.2 ht
  have h_dens_id_int : Integrable (fun t => d.density t * t) := by
    apply d.integrable.mono
      ((ProbabilityTheory.stronglyMeasurable_betaPDFReal _ _).aestronglyMeasurable.mul
        measurable_id.aestronglyMeasurable)
    apply ae_of_all; intro t
    simp only [Pi.mul_apply, id]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases ht : t ∈ Ioo 0 1
    · have h01 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], le_of_lt ht.2⟩
      calc |d.density t| * |t| ≤ |d.density t| * 1 := by
            apply mul_le_mul_of_nonneg_left h01 (abs_nonneg _)
        _ = |d.density t| := mul_one _
    · have hd0 : betaPDFReal (κ * pi) (κ * (1 - pi)) t = 0 := h_vanish t ht
      simp [hd0]
  have h_full_eq_interval : ∫ t, d.density t * t = ∫ t in (0:ℝ)..1, d.density t * t := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    rw [← integral_add_compl measurableSet_Ioc h_dens_id_int]
    · have h_compl_zero : ∫ t in (Ioc 0 1)ᶜ, d.density t * t = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro t ht
        simp only [mem_compl_iff, mem_Ioc, not_and_or, not_lt, not_le] at ht
        have h_not_Ioo : t ∉ Ioo 0 1 := by
          simp only [mem_Ioo, not_and_or, not_lt]
          rcases ht with ht | ht
          · left; exact ht
          · right; exact le_of_lt ht
        simp [h_vanish t h_not_Ioo]
      linarith
  have h_mul_comm : ∫ t in (0:ℝ)..1, t * d.density t = ∫ t in (0:ℝ)..1, d.density t * t := by
    congr 1; ext t; ring
  have h_expect_eq : d.expect id = ∫ t, d.density t * t := rfl
  have h_interval_eq_pi : ∫ t in (0:ℝ)..1, t * d.density t = pi := by
    rw [h_mul_comm, ← h_full_eq_interval, h_expect_eq.symm, h_expect]
  linarith

end BetaWithMeanCDF

end Econlib.Probability
