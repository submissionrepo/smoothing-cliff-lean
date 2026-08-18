/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Distributions.Beta.Basic
public import Econlib.Probability.Order.SOSD.Basic
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Order.BourbakiWitt

/-!
# Single crossing of `betaWithMean` CDFs and the resulting SOSD

The CDF difference `D(x) = F_{κ₁}(x) - F_{κ₂}(x)` between two `betaWithMean` distributions of
differing concentration crosses zero exactly once on `(0, 1)`. Combined with the equal-mean
condition `∫₀¹ F = 1 - π`, this yields the second-order stochastic dominance ordering.

## Main statements

* `beta_cdf_single_crossing` — single-crossing structure of the CDF difference.
* `CDF.SOSD.of_singleCrossing_of_equal_mean` — generic SOSD-from-single-crossing lemma.
* `betaWithMean_sosd` — `Beta(κ₂π, κ₂(1-π))` SOSD `Beta(κ₁π, κ₁(1-π))` for `κ₁ < κ₂`.

## Tags

beta distribution, single crossing, second-order stochastic dominance, SOSD, stochastic dominance
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace Econlib.Probability

variable {pi : ℝ} (hpi_pos : 0 < pi) (hpi_lt : pi < 1)

/-- If two CDFs are both zero at `0`, their difference vanishes to the left of `0`. -/
lemma cdf_sub_eq_zero_of_nonpos (d₁ d₂ : ContDist)
    (hF₁_zero : d₁.cdf 0 = 0) (hF₂_zero : d₂.cdf 0 = 0) :
    ∀ x, x ≤ 0 → d₁.cdf x - d₂.cdf x = 0 := by
  intro x hx
  have h1 : d₁.cdf x ≤ d₁.cdf 0 := d₁.cdf.mono hx
  have h2 : 0 ≤ d₁.cdf x := d₁.cdf_nonneg x
  have h1' : d₂.cdf x ≤ d₂.cdf 0 := d₂.cdf.mono hx
  have h2' : 0 ≤ d₂.cdf x := d₂.cdf_nonneg x
  have hF₁x : d₁.cdf x = 0 := le_antisymm (by linarith [hF₁_zero]) h2
  have hF₂x : d₂.cdf x = 0 := le_antisymm (by linarith [hF₂_zero]) h2'
  rw [hF₁x, hF₂x, sub_zero]

/-- If two CDFs are both one at `1`, their difference vanishes to the right of `1`. -/
lemma cdf_sub_eq_zero_of_one_le (d₁ d₂ : ContDist)
    (hF₁_one : d₁.cdf 1 = 1) (hF₂_one : d₂.cdf 1 = 1) :
    ∀ x, 1 ≤ x → d₁.cdf x - d₂.cdf x = 0 := by
  intro x hx
  have h1 : d₁.cdf 1 ≤ d₁.cdf x := d₁.cdf.mono hx
  have h2 : d₁.cdf x ≤ 1 := d₁.cdf_le_one x
  have h1' : d₂.cdf 1 ≤ d₂.cdf x := d₂.cdf.mono hx
  have h2' : d₂.cdf x ≤ 1 := d₂.cdf_le_one x
  have hF₁x : d₁.cdf x = 1 := le_antisymm h2 (by linarith [hF₁_one])
  have hF₂x : d₂.cdf x = 1 := le_antisymm h2' (by linarith [hF₂_one])
  rw [hF₁x, hF₂x, sub_self]

/-- A continuous nonnegative function on `[0, 1]` with zero integral is identically zero on
`[0, 1]`. -/
lemma eqOn_zero_of_nonneg_of_integral_eq_zero {D : ℝ → ℝ}
    (hD_cont : Continuous D) (hD_integral_Icc : ∫ t in Icc 0 1, D t = 0)
    (hD_ge : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ D t) :
    Set.EqOn D (fun _ => (0 : ℝ)) (Icc 0 1) := by
  have hD_ae : D =ᵐ[volume.restrict (Icc 0 1)] 0 := by
    have h_nonneg : ∀ᵐ t ∂(volume.restrict (Icc 0 1)), 0 ≤ D t := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hD_ge t ht
    exact (setIntegral_eq_zero_iff_of_nonneg_ae h_nonneg
      hD_cont.integrableOn_Icc).mp hD_integral_Icc
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hD_ae
    hD_cont.continuousOn continuousOn_const

/-- A continuous nonpositive function on `[0, 1]` with zero integral is identically zero on
`[0, 1]`. -/
lemma eqOn_zero_of_nonpos_of_integral_eq_zero {D : ℝ → ℝ}
    (hD_cont : Continuous D) (hD_integral_Icc : ∫ t in Icc 0 1, D t = 0)
    (hD_le : ∀ t ∈ Icc (0 : ℝ) 1, D t ≤ 0) :
    Set.EqOn D (fun _ => (0 : ℝ)) (Icc 0 1) := by
  have hD_ae : D =ᵐ[volume.restrict (Icc 0 1)] 0 := by
    have h_neg_nonneg : ∀ᵐ t ∂(volume.restrict (Icc 0 1)), 0 ≤ (-D) t := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [Pi.neg_apply]
      linarith [hD_le t ht]
    have h_neg_int : IntegrableOn (fun t => -D t) (Icc 0 1) :=
      hD_cont.neg.integrableOn_Icc
    have h_neg_eq : ∫ t in Icc 0 1, (-D) t = 0 := by
      simp only [Pi.neg_apply, integral_neg]
      linarith [hD_integral_Icc]
    filter_upwards [(setIntegral_eq_zero_iff_of_nonneg_ae h_neg_nonneg h_neg_int).mp h_neg_eq]
      with t ht
    simp only [Pi.neg_apply, Pi.zero_apply] at ht ⊢
    linarith
  exact Measure.eqOn_Icc_of_ae_eq volume (by norm_num : (0 : ℝ) ≠ 1) hD_ae
    hD_cont.continuousOn continuousOn_const

/-- Given a continuous `D` on `[0, 1]` with zero endpoints, zero total integral, and not
identically zero, the supremum of the prefix-nonnegative set is an interior point where `D` returns
to zero and `D` is nonnegative on the left half. -/
lemma exists_prefix_nonneg_boundary {D : ℝ → ℝ}
    (hD_cont : Continuous D) (hD0 : D 0 = 0) (hD1 : D 1 = 0)
    (hD_vanish_left : ∀ x, x ≤ 0 → D x = 0)
    (hD_integral_Icc : ∫ t in Icc 0 1, D t = 0)
    (hD_not_zero : ¬ Set.EqOn D (fun _ => (0 : ℝ)) (Icc 0 1)) :
    ∃ x₀ : ℝ, 0 ≤ x₀ ∧ x₀ < 1 ∧ D x₀ = 0 ∧
      (∀ x, x < x₀ → 0 ≤ D x) ∧
      (∀ y ∈ Icc (0 : ℝ) 1, (∀ t ∈ Icc (0 : ℝ) y, 0 ≤ D t) → y ≤ x₀) ∧
      (∃ a ∈ Ioo 0 1, 0 < D a) := by
  have hD_pos : ∃ a ∈ Ioo 0 1, 0 < D a := by
    by_contra h_not_pos
    push Not at h_not_pos
    apply hD_not_zero
    have hD_le : ∀ t ∈ Icc (0 : ℝ) 1, D t ≤ 0 := fun t ht => by
      rcases eq_or_lt_of_le ht.1 with h0 | h0
      · rw [← h0, hD0]
      rcases eq_or_lt_of_le ht.2 with h1 | h1
      · rw [h1, hD1]
      · exact h_not_pos t ⟨h0, h1⟩
    exact eqOn_zero_of_nonpos_of_integral_eq_zero hD_cont hD_integral_Icc hD_le
  set S := {x ∈ Icc (0 : ℝ) 1 | ∀ t ∈ Icc (0 : ℝ) x, 0 ≤ D t} with hS_def
  have h0S : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_refl _, zero_le_one⟩, fun t ht => ?_⟩
    have : t = 0 := le_antisymm ht.2 ht.1
    rw [this, hD0]
  have hS_bdd : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
  have hS_ne : S.Nonempty := ⟨0, h0S⟩
  set x₀ := sSup S with hx₀_def
  have hD_nonneg_prefix : ∀ x, x < x₀ → 0 ≤ D x := by
    intro x hx_lt
    by_cases hx_neg : x ≤ 0
    · rw [hD_vanish_left x hx_neg]
    · push Not at hx_neg
      obtain ⟨y, hyS, hxy⟩ := exists_lt_of_lt_csSup hS_ne hx_lt
      exact hyS.2 x ⟨le_of_lt hx_neg, le_of_lt hxy⟩
  have hx₀_le1 : x₀ ≤ 1 := csSup_le hS_ne (fun x hx => hx.1.2)
  have hx₀_ge0 : 0 ≤ x₀ := le_csSup hS_bdd h0S
  have hDx₀_nonneg : 0 ≤ D x₀ := by
    by_contra h_neg
    push Not at h_neg
    obtain ⟨ε, hε_pos, hε_nhd⟩ :=
      Metric.continuousAt_iff.mp hD_cont.continuousAt (-D x₀) (by linarith)
    have hε2 : x₀ - ε / 2 < x₀ := by linarith
    have hD_ge : 0 ≤ D (x₀ - ε / 2) := hD_nonneg_prefix _ hε2
    have h_in_ball : dist (x₀ - ε / 2) x₀ < ε := by
      rw [Real.dist_eq]
      simp only [sub_sub_cancel_left, abs_neg]
      rw [abs_of_pos (by linarith : ε / 2 > 0)]
      linarith
    have h_close := hε_nhd h_in_ball
    rw [Real.dist_eq] at h_close
    have : |D (x₀ - ε / 2) - D x₀| < -D x₀ := h_close
    rw [abs_lt] at this
    linarith
  have hx₀_lt1 : x₀ < 1 := by
    by_contra h_ge
    push Not at h_ge
    have hx₀_eq : x₀ = 1 := le_antisymm hx₀_le1 h_ge
    have hD_ge_01 : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ D t := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with h1 | h1
      · rw [h1]
        exact le_of_eq hD1.symm
      · exact hD_nonneg_prefix t (by rw [hx₀_eq]; exact h1)
    exact hD_not_zero (eqOn_zero_of_nonneg_of_integral_eq_zero hD_cont hD_integral_Icc hD_ge_01)
  have hDx₀_eq : D x₀ = 0 := by
    refine le_antisymm ?_ hDx₀_nonneg
    by_contra h_pos
    push Not at h_pos
    obtain ⟨ε, hε_pos, hε_nhd⟩ := Metric.continuousAt_iff.mp hD_cont.continuousAt
      (D x₀) (lt_of_le_of_lt (le_refl _) h_pos)
    set y := min (x₀ + ε / 2) ((1 + x₀) / 2) with hy_def
    have hy_gt : x₀ < y := by
      simp only [hy_def, lt_min_iff]
      constructor <;> linarith
    have hy_le1 : y ≤ 1 := by
      simp only [hy_def]
      exact min_le_of_right_le (by linarith)
    have hy_in_S : y ∈ S := by
      refine ⟨⟨by linarith [hx₀_ge0], hy_le1⟩, fun t ht => ?_⟩
      rcases lt_or_ge t x₀ with h | h
      · exact hD_nonneg_prefix t h
      · have h_dist : dist t x₀ < ε := by
          rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr h)]
          calc t - x₀ ≤ y - x₀ := by linarith [ht.2]
            _ ≤ (x₀ + ε / 2) - x₀ := by
                linarith [min_le_left (x₀ + ε / 2) ((1 + x₀) / 2)]
            _ = ε / 2 := by ring
            _ < ε := by linarith
        have := hε_nhd h_dist
        rw [Real.dist_eq] at this
        linarith [abs_lt.mp this]
    exact not_lt.mpr (le_csSup hS_bdd hy_in_S) hy_gt
  have hprefix_max :
      ∀ y ∈ Icc (0 : ℝ) 1, (∀ t ∈ Icc (0 : ℝ) y, 0 ≤ D t) → y ≤ x₀ := by
    intro y hy hprefix
    exact le_csSup hS_bdd ⟨hy, hprefix⟩
  exact ⟨x₀, hx₀_ge0, hx₀_lt1, hDx₀_eq, hD_nonneg_prefix, hprefix_max, hD_pos⟩

/-- The CDF difference of two beta-with-mean distributions has derivative equal to the density
difference on `(0,1)`. -/
lemma betaWithMean_cdfDiff_hasDerivAt {κ₁ κ₂ x : ℝ}
    (hk1 : 0 < κ₁) (hk2 : 0 < κ₂) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y =>
        (betaWithMean pi κ₁ hpi_pos hpi_lt hk1).cdf y -
        (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).cdf y)
      ((betaWithMean pi κ₁ hpi_pos hpi_lt hk1).density x -
        (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).density x) x := by
  have hα₁ : 0 < κ₁ * pi := mul_pos hk1 hpi_pos
  have hβ₁ : 0 < κ₁ * (1 - pi) := mul_pos hk1 (by linarith)
  have hα₂ : 0 < κ₂ * pi := mul_pos hk2 hpi_pos
  have hβ₂ : 0 < κ₂ * (1 - pi) := mul_pos hk2 (by linarith)
  exact ((betaWithMean pi κ₁ hpi_pos hpi_lt hk1).deriv_cdf_eq_density x
      (betaPDFReal_continuousAt hα₁ hβ₁ hx.1 hx.2)).sub
    ((betaWithMean pi κ₂ hpi_pos hpi_lt hk2).deriv_cdf_eq_density x
      (betaPDFReal_continuousAt hα₂ hβ₂ hx.1 hx.2))

/-- On the right of the beta mean `π`, if `f₂(a) ≤ f₁(a)` at some `a ∈ (π, 1)`, then
`f₂(b) ≤ f₁(b)` for all `b ∈ (π, 1)` with `a < b`. This follows from the U-shaped density ratio of
`betaWithMean` distributions with different concentration parameters. -/
lemma betaWithMean_density_le_of_density_le_right {κ₁ κ₂ a b : ℝ}
    (hk1 : 0 < κ₁) (hk2 : 0 < κ₂) (hlt : κ₁ < κ₂)
    (ha : a ∈ Ioo pi 1) (hb : b ∈ Ioo pi 1) (hab : a < b)
    (hge : (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).density a ≤
      (betaWithMean pi κ₁ hpi_pos hpi_lt hk1).density a) :
    (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).density b ≤
      (betaWithMean pi κ₁ hpi_pos hpi_lt hk1).density b := by
  set d₁ := betaWithMean pi κ₁ hpi_pos hpi_lt hk1
  set d₂ := betaWithMean pi κ₂ hpi_pos hpi_lt hk2
  have hα₂ : 0 < κ₂ * pi := mul_pos hk2 hpi_pos
  have hβ₂ : 0 < κ₂ * (1 - pi) := mul_pos hk2 (by linarith)
  have hf₂a : 0 < d₂.density a :=
    ProbabilityTheory.betaPDFReal_pos (lt_trans hpi_pos ha.1) ha.2 hα₂ hβ₂
  have hf₂b : 0 < d₂.density b :=
    ProbabilityTheory.betaPDFReal_pos (lt_trans hpi_pos hb.1) hb.2 hα₂ hβ₂
  have hcross : d₁.density a * d₂.density b ≤ d₁.density b * d₂.density a :=
    (beta_density_ratio_Ushaped hpi_pos hpi_lt hk1 hk2 hlt).2 a b ha hb hab
  nlinarith [mul_le_mul_of_nonneg_right hge (le_of_lt hf₂b)]

/-- On the left of the beta mean `π`, if `f₂(b) ≤ f₁(b)` at some `b ∈ (0, π)`, then `f₂(a) ≤ f₁(a)`
for all `a ∈ (0, π)` with `a < b`. This follows from the U-shaped density ratio of `betaWithMean`
distributions with different concentration parameters. -/
lemma betaWithMean_density_le_of_density_le_left {κ₁ κ₂ a b : ℝ}
    (hk1 : 0 < κ₁) (hk2 : 0 < κ₂) (hlt : κ₁ < κ₂)
    (ha : a ∈ Ioo 0 pi) (hb : b ∈ Ioo 0 pi) (hab : a < b)
    (hge : (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).density b ≤
      (betaWithMean pi κ₁ hpi_pos hpi_lt hk1).density b) :
    (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).density a ≤
      (betaWithMean pi κ₁ hpi_pos hpi_lt hk1).density a := by
  set d₁ := betaWithMean pi κ₁ hpi_pos hpi_lt hk1
  set d₂ := betaWithMean pi κ₂ hpi_pos hpi_lt hk2
  have hα₂ : 0 < κ₂ * pi := mul_pos hk2 hpi_pos
  have hβ₂ : 0 < κ₂ * (1 - pi) := mul_pos hk2 (by linarith)
  have hf₂a : 0 < d₂.density a :=
    ProbabilityTheory.betaPDFReal_pos ha.1 (lt_trans ha.2 hpi_lt) hα₂ hβ₂
  have hf₂b : 0 < d₂.density b :=
    ProbabilityTheory.betaPDFReal_pos hb.1 (lt_trans hb.2 hpi_lt) hα₂ hβ₂
  have hcross : d₁.density b * d₂.density a ≤ d₁.density a * d₂.density b :=
    (beta_density_ratio_Ushaped hpi_pos hpi_lt hk1 hk2 hlt).1 a b ha hb hab
  nlinarith [mul_le_mul_of_nonneg_right hge (le_of_lt hf₂a)]

/-- Two `betaWithMean` distributions with distinct concentration parameters `κ₁ ≠ κ₂` have
different CDFs on `[0, 1]`; their CDF difference is not identically zero. -/
lemma betaWithMean_cdf_sub_not_eqOn_zero {κ₁ κ₂ : ℝ}
    (hk1 : 0 < κ₁) (hk2 : 0 < κ₂) (hlt : κ₁ < κ₂) :
    ¬ Set.EqOn
      (fun x =>
        (betaWithMean pi κ₁ hpi_pos hpi_lt hk1).cdf x -
        (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).cdf x)
      (fun _ => (0 : ℝ)) (Icc 0 1) := by
  set d₁ := betaWithMean pi κ₁ hpi_pos hpi_lt hk1
  set d₂ := betaWithMean pi κ₂ hpi_pos hpi_lt hk2
  set F₁ := d₁.cdf
  set F₂ := d₂.cdf
  intro heq
  have hF_eq : ∀ x ∈ Icc (0 : ℝ) 1, F₁ x = F₂ x := by intro x hx; linarith [heq hx]
  have hα₁ : 0 < κ₁ * pi := mul_pos hk1 hpi_pos
  have hβ₁ : 0 < κ₁ * (1 - pi) := mul_pos hk1 (by linarith)
  have hα₂ : 0 < κ₂ * pi := mul_pos hk2 hpi_pos
  have hβ₂ : 0 < κ₂ * (1 - pi) := mul_pos hk2 (by linarith)
  have hdens_eq_at : ∀ x ∈ Ioo (0 : ℝ) 1, d₁.density x = d₂.density x := by
    intro x hx
    have hd1 := d₁.deriv_cdf_eq_density x (betaPDFReal_continuousAt hα₁ hβ₁ hx.1 hx.2)
    have hd2 := d₂.deriv_cdf_eq_density x (betaPDFReal_continuousAt hα₂ hβ₂ hx.1 hx.2)
    have hF_eq_nhds : F₁ =ᶠ[nhds x] F₂ := by
      exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioo 0 1, Ioo_mem_nhds hx.1 hx.2,
        fun y hy => hF_eq y ⟨le_of_lt hy.1, le_of_lt hy.2⟩⟩
    exact hd1.unique (hd2.congr_of_eventuallyEq hF_eq_nhds)
  have hpi2 : pi / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hpi34 : 3 * pi / 4 ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have heq2 := hdens_eq_at (pi / 2) hpi2
  have heq34 := hdens_eq_at (3 * pi / 4) hpi34
  have hd1_pos2 : 0 < d₁.density (pi / 2) :=
    ProbabilityTheory.betaPDFReal_pos hpi2.1 hpi2.2 hα₁ hβ₁
  have hd1_pos34 : 0 < d₁.density (3 * pi / 4) :=
    ProbabilityTheory.betaPDFReal_pos hpi34.1 hpi34.2 hα₁ hβ₁
  have hd2_pos2 : 0 < d₂.density (pi / 2) := heq2 ▸ hd1_pos2
  have hd2_pos34 : 0 < d₂.density (3 * pi / 4) := heq34 ▸ hd1_pos34
  have hδ : 0 < κ₂ - κ₁ := sub_pos.mpr hlt
  set x₁ := pi / 2
  set x₂ := 3 * pi / 4
  set g := fun x : ℝ => pi * Real.log x + (1 - pi) * Real.log (1 - x) with hg_def
  have hg_strict : g x₁ < g x₂ := by
    have hx1_pi : x₁ ∈ Ioo 0 pi :=
      ⟨show (0 : ℝ) < pi / 2 by linarith, show pi / 2 < pi by linarith⟩
    have hx2_pi : x₂ ∈ Ioo 0 pi :=
      ⟨show (0 : ℝ) < 3 * pi / 4 by linarith, show 3 * pi / 4 < pi by linarith⟩
    apply strictMonoOn_of_deriv_pos (convex_Ioo 0 pi) ?_ ?_ hx1_pi hx2_pi
      (show pi / 2 < 3 * pi / 4 by linarith)
    · apply ContinuousOn.add
      · exact continuousOn_const.mul (Real.continuousOn_log.mono
          (fun x hx => ne_of_gt (mem_Ioo.mp hx).1))
      · exact continuousOn_const.mul (Real.continuousOn_log.comp
          (continuousOn_const.sub continuousOn_id)
          (fun x hx => ne_of_gt (by have := (mem_Ioo.mp hx).2; linarith)))
    · intro x hx
      rw [interior_Ioo] at hx
      have hx_pos : (0 : ℝ) < x := hx.1
      have hx_lt : x < pi := hx.2
      have hx_ne : x ≠ 0 := ne_of_gt hx_pos
      have h1x_ne : (1 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
      have hd : HasDerivAt g (pi * x⁻¹ + (1 - pi) * (-(1 - x)⁻¹)) x := by
        have hd_log : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx_ne
        have hd_log1x : HasDerivAt (fun t => Real.log (1 - t)) (-(1 - x)⁻¹) x :=
          HasDerivAt.comp_const_sub 1 x (Real.hasDerivAt_log (by linarith))
        exact (hd_log.const_mul pi).add (hd_log1x.const_mul (1 - pi))
      rw [hd.deriv, show pi * x⁻¹ + (1 - pi) * (-(1 - x)⁻¹) =
        pi / x - (1 - pi) / (1 - x) by rw [div_eq_mul_inv, div_eq_mul_inv]; ring]
      rw [sub_pos, div_lt_div_iff₀ (by linarith : (0 : ℝ) < 1 - x) hx_pos]
      nlinarith
  have h_strict : d₁.density x₂ * d₂.density x₁ < d₁.density x₁ * d₂.density x₂ := by
    rw [← Real.log_lt_log_iff (mul_pos hd1_pos34 hd2_pos2) (mul_pos hd1_pos2 hd2_pos34)]
    have log_dens' : ∀ (κ : ℝ) (hκ : 0 < κ) (y : ℝ), y ∈ Ioo 0 1 →
        Real.log ((betaWithMean pi κ hpi_pos hpi_lt hκ).density y) =
          Real.log (1 / ProbabilityTheory.beta (κ * pi) (κ * (1 - pi))) +
          (κ * pi - 1) * Real.log y + (κ * (1 - pi) - 1) * Real.log (1 - y) := by
      intro κ hκ y hy
      have hy0 : (0 : ℝ) < y := hy.1
      have hy1 : y < 1 := hy.2
      have h1y : (0 : ℝ) < 1 - y := by linarith
      change Real.log (ProbabilityTheory.betaPDFReal (κ * pi) (κ * (1 - pi)) y) = _
      rw [show ProbabilityTheory.betaPDFReal (κ * pi) (κ * (1 - pi)) y =
          (1 / ProbabilityTheory.beta (κ * pi) (κ * (1 - pi))) *
            y ^ (κ * pi - 1) * (1 - y) ^ (κ * (1 - pi) - 1) by
        simp [ProbabilityTheory.betaPDFReal, hy0, hy1]]
      have hC : 0 < 1 / ProbabilityTheory.beta (κ * pi) (κ * (1 - pi)) :=
        div_pos one_pos (ProbabilityTheory.beta_pos (mul_pos hκ hpi_pos) (mul_pos hκ (by linarith)))
      rw [Real.log_mul (ne_of_gt (mul_pos hC (Real.rpow_pos_of_pos hy0 _)))
            (ne_of_gt (Real.rpow_pos_of_pos h1y _)),
          Real.log_mul (ne_of_gt hC) (ne_of_gt (Real.rpow_pos_of_pos hy0 _)),
          Real.log_rpow hy0, Real.log_rpow h1y]
    have hl1x1 := log_dens' κ₁ hk1 x₁ hpi2
    have hl1x2 := log_dens' κ₁ hk1 x₂ hpi34
    have hl2x1 := log_dens' κ₂ hk2 x₁ hpi2
    have hl2x2 := log_dens' κ₂ hk2 x₂ hpi34
    rw [Real.log_mul (ne_of_gt hd1_pos34) (ne_of_gt hd2_pos2),
        Real.log_mul (ne_of_gt hd1_pos2) (ne_of_gt hd2_pos34)]
    rw [hl1x2, hl2x1, hl1x1, hl2x2]
    set lx₁ := Real.log x₁
    set lx₂ := Real.log x₂
    set l1x₁ := Real.log (1 - x₁)
    set l1x₂ := Real.log (1 - x₂)
    have hg_strict' : pi * lx₁ + (1 - pi) * l1x₁ < pi * lx₂ + (1 - pi) * l1x₂ :=
      hg_strict
    nlinarith [mul_pos hδ (sub_pos.mpr hg_strict')]
  rw [heq2, heq34] at h_strict
  linarith [mul_comm (d₂.density x₂) (d₂.density x₁)]

/-- **Single crossing of beta CDFs:** For `κ₁ < κ₂`, the CDF difference
`D(x) = F_{κ₁}(x) - F_{κ₂}(x)` crosses zero exactly once on `(0, 1)`. Specifically, there exists
`x₀ ∈ (0, 1)` such that `F_{κ₁}(x) ≥ F_{κ₂}(x)` for `x < x₀` and `F_{κ₁}(x) ≤ F_{κ₂}(x)` for
`x > x₀`. -/
public theorem beta_cdf_single_crossing {κ₁ κ₂ : ℝ}
    (hk1 : 0 < κ₁) (hk2 : 0 < κ₂) (hlt : κ₁ < κ₂) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ < 1 ∧
      (∀ x, x < x₀ →
        (betaWithMean pi κ₁ hpi_pos hpi_lt hk1).cdf x ≥
        (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).cdf x) ∧
      (∀ x, x₀ < x →
        (betaWithMean pi κ₁ hpi_pos hpi_lt hk1).cdf x ≤
        (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).cdf x) := by
  set d₁ := betaWithMean pi κ₁ hpi_pos hpi_lt hk1
  set d₂ := betaWithMean pi κ₂ hpi_pos hpi_lt hk2
  set F₁ := d₁.cdf
  set F₂ := d₂.cdf
  set D := fun x => F₁ x - F₂ x
  have hF₁_cont : Continuous F₁ := contdist_cdf_continuous d₁
  have hF₂_cont : Continuous F₂ := contdist_cdf_continuous d₂
  have hD_cont : Continuous D := hF₁_cont.sub hF₂_cont
  have hF₁_zero : F₁ 0 = 0 := betaWithMean_cdf_zero hpi_pos hpi_lt hk1 0 (le_refl 0)
  have hF₂_zero : F₂ 0 = 0 := betaWithMean_cdf_zero hpi_pos hpi_lt hk2 0 (le_refl 0)
  have hF₁_one : F₁ 1 = 1 := betaWithMean_cdf_one hpi_pos hpi_lt hk1 1 (le_refl 1)
  have hF₂_one : F₂ 1 = 1 := betaWithMean_cdf_one hpi_pos hpi_lt hk2 1 (le_refl 1)
  have hD0 : D 0 = 0 := by simp only [D, hF₁_zero, hF₂_zero, sub_zero]
  have hD1 : D 1 = 0 := by simp only [D, hF₁_one, hF₂_one, sub_self]
  have hD_vanish_left : ∀ x, x ≤ 0 → D x = 0 := by
    simpa [D, F₁, F₂] using cdf_sub_eq_zero_of_nonpos d₁ d₂ hF₁_zero hF₂_zero
  have hD_vanish_right : ∀ x, 1 ≤ x → D x = 0 := by
    simpa [D, F₁, F₂] using cdf_sub_eq_zero_of_one_le d₁ d₂ hF₁_one hF₂_one
  -- Both CDFs integrate to 1 - π over [0, 1], so their difference integrates to zero.
  have hD_integral_Icc : ∫ t in Icc 0 1, D t = 0 := by
    have h1 := betaWithMean_integrated_cdf hpi_pos hpi_lt hk1
    have h2 := betaWithMean_integrated_cdf hpi_pos hpi_lt hk2
    have hF₁_int : IntegrableOn F₁ (Icc 0 1) := hF₁_cont.integrableOn_Icc
    have hF₂_int : IntegrableOn F₂ (Icc 0 1) := hF₂_cont.integrableOn_Icc
    unfold D
    rw [integral_sub hF₁_int hF₂_int, h1, h2, sub_self]
  have hD_not_zero : ¬ Set.EqOn D (fun _ => (0:ℝ)) (Icc 0 1) := by
    simpa [D, F₁, F₂, d₁, d₂] using
      betaWithMean_cdf_sub_not_eqOn_zero hpi_pos hpi_lt hk1 hk2 hlt
  obtain ⟨x₀, hx₀_ge0, hx₀_lt1, hDx₀_eq, hD_nonneg_prefix, hprefix_max, hD_pos⟩ :=
    exists_prefix_nonneg_boundary hD_cont hD0 hD1 hD_vanish_left
      hD_integral_Icc hD_not_zero
  -- D' = f₁ - f₂ follows sign pattern (+, -, +) due to the U-shaped density ratio;
  -- D is antitone on [x₀, c₂] where f₂ dominates, then monotone on [c₂, 1] back to 0.
  have hα₁ : 0 < κ₁ * pi := mul_pos hk1 hpi_pos
  have hβ₁ : 0 < κ₁ * (1 - pi) := mul_pos hk1 (by linarith)
  have hα₂ : 0 < κ₂ * pi := mul_pos hk2 hpi_pos
  have hβ₂ : 0 < κ₂ * (1 - pi) := mul_pos hk2 (by linarith)
  have hD_deriv : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt D (d₁.density x - d₂.density x) x := by
    intro x hx
    simpa [D, F₁, F₂, d₁, d₂] using
      betaWithMean_cdfDiff_hasDerivAt hpi_pos hpi_lt hk1 hk2 hx
  have hf₂_pos : ∀ x ∈ Ioo (0:ℝ) 1, 0 < d₂.density x :=
    fun x hx => ProbabilityTheory.betaPDFReal_pos hx.1 hx.2 hα₂ hβ₂
  have hU := beta_density_ratio_Ushaped hpi_pos hpi_lt hk1 hk2 hlt
  -- c₂ is the last point in (x₀, 1) where d₁ ≤ d₂; beyond c₂, d₂ ≤ d₁.
  have hf₁_cont : ContinuousOn d₁.density (Ioo 0 1) :=
    fun x hx => (betaPDFReal_continuousAt hα₁ hβ₁ hx.1 hx.2).continuousWithinAt
  have hf₂_cont : ContinuousOn d₂.density (Ioo 0 1) :=
    fun x hx => (betaPDFReal_continuousAt hα₂ hβ₂ hx.1 hx.2).continuousWithinAt
  have hDiff_cont : ContinuousOn (fun x => d₁.density x - d₂.density x) (Ioo 0 1) :=
    hf₁_cont.sub hf₂_cont
  have ratio_mono_right : ∀ a b, a ∈ Ioo pi 1 → b ∈ Ioo pi 1 → a < b →
      d₂.density a ≤ d₁.density a → d₂.density b ≤ d₁.density b := by
    intro a b ha hb hab hge
    simpa [d₁, d₂] using
      betaWithMean_density_le_of_density_le_right hpi_pos hpi_lt hk1 hk2 hlt ha hb hab hge
  have ratio_mono_left : ∀ a b, a ∈ Ioo 0 pi → b ∈ Ioo 0 pi → a < b →
      d₂.density b ≤ d₁.density b → d₂.density a ≤ d₁.density a := by
    intro a b ha hb hab hge
    simpa [d₁, d₂] using
      betaWithMean_density_le_of_density_le_left hpi_pos hpi_lt hk1 hk2 hlt ha hb hab hge
  have hcrossing : ∃ c₂ ∈ Icc x₀ 1,
      (∀ x ∈ Ioo x₀ c₂, d₁.density x ≤ d₂.density x) ∧
      (∀ x ∈ Ioo c₂ 1, d₂.density x ≤ d₁.density x) := by
    -- Degenerate cases
    by_cases h_all_le : ∀ x ∈ Ioo x₀ 1, d₁.density x ≤ d₂.density x
    · refine ⟨1, ⟨hx₀_lt1.le, le_refl _⟩, h_all_le, fun x hx => ?_⟩
      exact absurd hx.1 (not_lt.mpr hx.2.le)
    push Not at h_all_le; obtain ⟨a₀, ha₀, hfa₀⟩ := h_all_le
    by_cases h_all_ge : ∀ x ∈ Ioo x₀ 1, d₂.density x ≤ d₁.density x
    · refine ⟨x₀, ⟨le_refl _, hx₀_lt1.le⟩, fun x hx => ?_, h_all_ge⟩
      exact absurd hx.1 (not_lt.mpr hx.2.le)
    push Not at h_all_ge; obtain ⟨b₀, hb₀, hfb₀⟩ := h_all_ge
    -- At x₀ the derivative D'(x₀) ≤ 0: if D'(x₀) > 0, then D > 0 just to the right of x₀,
    -- contradicting x₀ being the last point of the prefix-nonnegative region.
    have hdens_x₀ : 0 < x₀ → d₁.density x₀ ≤ d₂.density x₀ := by
      intro hx₀_pos
      by_contra h_gt; push Not at h_gt
      have hderiv_pos : 0 < d₁.density x₀ - d₂.density x₀ := by linarith
      have hx₀_in : x₀ ∈ Ioo (0:ℝ) 1 := ⟨hx₀_pos, hx₀_lt1⟩
      have hHD := hD_deriv x₀ hx₀_in
      rw [hasDerivAt_iff_isLittleO_nhds_zero] at hHD
      have hlit := hHD.def (by linarith : 0 < (d₁.density x₀ - d₂.density x₀) / 2)
      rw [Metric.eventually_nhds_iff] at hlit
      obtain ⟨δ, hδ_pos, hδ_ball⟩ := hlit
      set h := min (δ / 2) ((1 - x₀) / 2) with hh_def
      have hh_pos : 0 < h := lt_min (by linarith) (by linarith)
      have hh_lt_δ : h < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have hh_x₀ : x₀ + h < 1 := by linarith [min_le_right (δ / 2) ((1 - x₀) / 2)]
      have hD_pos_interval : ∀ t ∈ Ioo x₀ (x₀ + h), 0 < D t := by
        intro t ht
        set h' := t - x₀
        have hh'_pos : 0 < h' := by linarith [ht.1]
        have hh'_lt_h : h' < h := by linarith [ht.2]
        have hh'_lt_δ : h' < δ := lt_trans hh'_lt_h hh_lt_δ
        have hh'_dist : dist h' 0 < δ := by
          rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos hh'_pos]; exact hh'_lt_δ
        have hε' := hδ_ball hh'_dist
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hh'_pos] at hε'
        simp only [hDx₀_eq, sub_zero, smul_eq_mul] at hε'
        have ht_eq : x₀ + h' = t := by ring
        rw [ht_eq] at hε'
        rw [abs_le] at hε'
        nlinarith
      have hy_prefix : ∀ t ∈ Icc (0 : ℝ) (x₀ + h / 2), 0 ≤ D t := by
        intro t ht
        rcases lt_or_ge t x₀ with h_lt | h_ge
        · exact hD_nonneg_prefix t h_lt
        · rcases eq_or_lt_of_le h_ge with rfl | h_gt
          · exact le_of_eq hDx₀_eq.symm
          · exact le_of_lt (hD_pos_interval t ⟨h_gt, by linarith [ht.2]⟩)
      have hy_le : x₀ + h / 2 ≤ x₀ :=
        hprefix_max (x₀ + h / 2) ⟨by linarith, by linarith⟩ hy_prefix
      exact not_lt.mpr hy_le (by linarith : x₀ < x₀ + h / 2)
    -- There exists a₁ ∈ (π, 1) with d₁(a₁) > d₂(a₁); otherwise D would be globally
    -- nonneg with zero integral, forcing D ≡ 0 and contradicting distinctness.
    have h_ratio_large : ∃ a₁ ∈ Ioo pi 1, d₂.density a₁ < d₁.density a₁ := by
      by_contra h_neg; push Not at h_neg
      apply hD_not_zero
      have hD_anti_pi : AntitoneOn D (Icc pi 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Icc pi 1)
        · exact hD_cont.continuousOn
        · intro x hx
          rw [interior_Icc] at hx
          exact (hD_deriv x ⟨lt_trans hpi_pos hx.1, hx.2⟩).differentiableAt.differentiableWithinAt
        · intro x hx
          rw [interior_Icc] at hx
          rw [(hD_deriv x ⟨lt_trans hpi_pos hx.1, hx.2⟩).deriv]
          linarith [h_neg x ⟨hx.1, hx.2⟩]
      have hDpi_nonneg : 0 ≤ D pi := by
        linarith [hD_anti_pi ⟨le_refl _, hpi_lt.le⟩ ⟨hpi_lt.le, le_refl _⟩ hpi_lt.le, hD1]
      have hD_nonneg_pi1 : ∀ x ∈ Icc pi 1, 0 ≤ D x := by
        intro x hx
        linarith [hD_anti_pi hx ⟨hpi_lt.le, le_refl _⟩ hx.2, hD1]
      by_cases hx₀_pi : pi ≤ x₀
      · have hD_nonneg_01 : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ D t := by
          intro t ht
          rcases le_or_gt t x₀ with h | h
          · rcases eq_or_lt_of_le h with rfl | hlt
            · exact le_of_eq hDx₀_eq.symm
            · exact hD_nonneg_prefix t hlt
          · exact hD_nonneg_pi1 t ⟨le_trans hx₀_pi (le_of_lt h), ht.2⟩
        exact eqOn_zero_of_nonneg_of_integral_eq_zero hD_cont hD_integral_Icc hD_nonneg_01
      · -- x₀ < π: show D ≥ 0 also on [x₀, π] by contradiction via ratio_mono_left.
        push Not at hx₀_pi
        by_cases hD_nonneg_mid : ∀ t ∈ Icc x₀ pi, 0 ≤ D t
        · have hD_nonneg_01 : ∀ t ∈ Icc (0:ℝ) 1, 0 ≤ D t := by
            intro t ht
            rcases le_or_gt t x₀ with h | h
            · rcases eq_or_lt_of_le h with rfl | hlt
              · exact le_of_eq hDx₀_eq.symm
              · exact hD_nonneg_prefix t hlt
            · rcases le_or_gt t pi with hp | hp
              · exact hD_nonneg_mid t ⟨le_of_lt h, hp⟩
              · exact hD_nonneg_pi1 t ⟨le_of_lt hp, ht.2⟩
          exact eqOn_zero_of_nonneg_of_integral_eq_zero hD_cont hD_integral_Icc hD_nonneg_01
        · push Not at hD_nonneg_mid
          obtain ⟨b, hb, hDb⟩ := hD_nonneg_mid
          have hb_lt_pi : b < pi := by
            rcases eq_or_lt_of_le hb.2 with rfl | hlt
            · linarith
            · exact hlt
          -- MVT on [b, π] yields c ∈ (b, π) with D'(c) > 0, so d₁(c) > d₂(c).
          have hD_incr : 0 < D pi - D b := by linarith
          have hb_gt_x₀ : x₀ < b := by
            rcases eq_or_lt_of_le hb.1 with rfl | hlt
            · linarith [hDx₀_eq]
            · exact hlt
          have hb_pos : 0 < b := lt_of_le_of_lt hx₀_ge0 hb_gt_x₀
          obtain ⟨c, hcb, hc_deriv⟩ := exists_hasDerivAt_eq_slope D
            (fun x => d₁.density x - d₂.density x) hb_lt_pi
            (hD_cont.continuousOn.mono (Set.subset_univ _))
            (fun x hx => hD_deriv x ⟨lt_trans hb_pos hx.1, lt_trans hx.2 hpi_lt⟩)
          have hc_pos : 0 < (D pi - D b) / (pi - b) := div_pos hD_incr (by linarith)
          have hd1_gt : d₂.density c < d₁.density c := by linarith [hc_deriv]
          have hc_in_0pi : c ∈ Ioo 0 pi := ⟨by linarith [hcb.1], hcb.2⟩
          -- ratio_mono_left propagates d₁ ≥ d₂ leftward from c to all of (0, b).
          have hd1_ge_on_0b : ∀ x ∈ Ioo 0 b, d₂.density x ≤ d₁.density x := by
            intro x hx
            have hx_in : x ∈ Ioo 0 pi := ⟨hx.1, lt_trans hx.2 hb_lt_pi⟩
            exact ratio_mono_left x c hx_in hc_in_0pi (lt_trans hx.2 hcb.1) (le_of_lt hd1_gt)
          -- D' ≥ 0 on (0, b) implies D is monotone on [0, b], so D(b) ≥ D(0) = 0.
          have hD_mono_0b : MonotoneOn D (Icc 0 b) := by
            apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b)
            · exact hD_cont.continuousOn
            · intro x hx; rw [interior_Icc] at hx
              have hx01 : x ∈ Ioo (0:ℝ) 1 := ⟨hx.1, lt_trans (lt_trans hx.2 hb_lt_pi) hpi_lt⟩
              exact (hD_deriv x hx01).differentiableAt.differentiableWithinAt
            · intro x hx; rw [interior_Icc] at hx
              have hx01 : x ∈ Ioo (0:ℝ) 1 := ⟨hx.1, lt_trans (lt_trans hx.2 hb_lt_pi) hpi_lt⟩
              rw [(hD_deriv x hx01).deriv]
              linarith [hd1_ge_on_0b x ⟨hx.1, hx.2⟩]
          have hD_b_nonneg : 0 ≤ D b := by
            have := hD_mono_0b ⟨le_refl _, by linarith [hb_pos]⟩
              ⟨by linarith [hb_pos], le_refl _⟩ (by linarith [hb_pos])
            linarith [hD0]
          linarith
    obtain ⟨a₁, ha₁, hfa₁⟩ := h_ratio_large
    -- c₂ = sSup of the set where d₁ ≤ d₂ holds on the prefix (x₀, y); bounded above by a₁.
    set T := {y ∈ Icc x₀ 1 | ∀ t ∈ Ioo x₀ y, d₁.density t ≤ d₂.density t}
    have hx₀T : x₀ ∈ T := ⟨⟨le_refl _, hx₀_lt1.le⟩,
      fun t ht => absurd (lt_trans ht.1 ht.2) (lt_irrefl _)⟩
    have hT_bdd : BddAbove T := ⟨1, fun y hy => hy.1.2⟩
    have hT_ne : T.Nonempty := ⟨x₀, hx₀T⟩
    have ha₁_x₀ : x₀ < a₁ := by
      by_contra h_ge; push Not at h_ge
      rcases eq_or_lt_of_le h_ge with rfl | hlt
      · have := hdens_x₀ (lt_trans hpi_pos ha₁.1)
        linarith
      · have hx₀_pi : pi < x₀ := lt_trans ha₁.1 hlt
        have hx₀_pos' : 0 < x₀ := lt_trans (lt_trans hpi_pos ha₁.1) hlt
        have h_le := hdens_x₀ hx₀_pos'
        have hcross : d₁.density a₁ * d₂.density x₀ ≤ d₁.density x₀ * d₂.density a₁ :=
          hU.2 a₁ x₀ ha₁ ⟨hx₀_pi, hx₀_lt1⟩ hlt
        have hc_pos : 0 < d₂.density x₀ := hf₂_pos x₀ ⟨hx₀_pos', hx₀_lt1⟩
        have ha1p : 0 < d₂.density a₁ := hf₂_pos a₁ ⟨lt_trans hpi_pos ha₁.1, ha₁.2⟩
        have h_chain : d₁.density a₁ * d₂.density x₀ ≤ d₂.density x₀ * d₂.density a₁ := by
          calc d₁.density a₁ * d₂.density x₀
              ≤ d₁.density x₀ * d₂.density a₁ := hcross
            _ ≤ d₂.density x₀ * d₂.density a₁ :=
                mul_le_mul_of_nonneg_right h_le (le_of_lt ha1p)
        have : d₁.density a₁ ≤ d₂.density a₁ := by
          rw [mul_comm] at h_chain; exact le_of_mul_le_mul_left h_chain hc_pos
        linarith
    have hT_le_a₁ : ∀ y ∈ T, y ≤ a₁ := by
      intro y hy; by_contra h_gt; push Not at h_gt
      exact absurd (hy.2 a₁ ⟨ha₁_x₀, h_gt⟩) (not_le.mpr hfa₁)
    set c₂ := sSup T
    have hc₂_le_a₁ : c₂ ≤ a₁ := csSup_le hT_ne hT_le_a₁
    have hc₂_ge_x₀ : x₀ ≤ c₂ := le_csSup hT_bdd hx₀T
    have hc₂_le1 : c₂ ≤ 1 := le_trans hc₂_le_a₁ (le_of_lt ha₁.2)
    have hdens_left : ∀ x ∈ Ioo x₀ c₂, d₁.density x ≤ d₂.density x := by
      intro x hx
      obtain ⟨y, hyT, hxy⟩ := exists_lt_of_lt_csSup hT_ne hx.2
      exact hyT.2 x ⟨hx.1, hxy⟩
    -- Second condition: for x ∈ (c₂, 1), d₂(x) ≤ d₁(x)
    have hdens_right : ∀ x ∈ Ioo c₂ 1, d₂.density x ≤ d₁.density x := by
      intro x hx
      have hx_not_T : x ∉ T := fun hxT => not_lt.mpr (le_csSup hT_bdd hxT) hx.1
      have hx_in : x ∈ Icc x₀ 1 := ⟨le_trans hc₂_ge_x₀ (le_of_lt hx.1), le_of_lt hx.2⟩
      have h_not_all : ¬ (∀ t ∈ Ioo x₀ x, d₁.density t ≤ d₂.density t) := by
        intro h; exact hx_not_T ⟨hx_in, h⟩
      push Not at h_not_all
      obtain ⟨t, ht, hft⟩ := h_not_all
      by_cases ht_pi : pi < t
      · have hx_pi : pi < x := lt_trans ht_pi ht.2
        exact ratio_mono_right t x ⟨ht_pi, lt_trans ht.2 hx.2⟩ ⟨hx_pi, hx.2⟩
          ht.2 (le_of_lt hft)
      · push Not at ht_pi
        by_cases hx_ge_a₁ : a₁ ≤ x
        · rcases eq_or_lt_of_le hx_ge_a₁ with rfl | hlt_a₁x
          · exact le_of_lt hfa₁
          · exact ratio_mono_right a₁ x ha₁ ⟨lt_of_lt_of_le ha₁.1 hx_ge_a₁, hx.2⟩
              hlt_a₁x (le_of_lt hfa₁)
        · -- t ≤ π and x < a₁: find t' ∈ (x₀, π) with d₁(t') > d₂(t') to derive contradiction.
          push Not at hx_ge_a₁
          exfalso
          have hx₀_lt_pi : x₀ < pi := lt_of_lt_of_le ht.1 ht_pi
          obtain ⟨t', ht'_mem, hft'⟩ : ∃ t' ∈ Ioo x₀ pi, d₂.density t' < d₁.density t' := by
            rcases lt_or_eq_of_le ht_pi with ht_lt_pi | ht_eq_pi
            · exact ⟨t, ⟨ht.1, ht_lt_pi⟩, hft⟩
            · -- t = π: d₁(π) > d₂(π), use continuity to find a nearby t' < π.
              have h_diff_pos : 0 < d₁.density t - d₂.density t := by linarith
              have ht_in01 : t ∈ Ioo (0:ℝ) 1 := ⟨by linarith [ht.1],
                lt_trans ht.2 hx.2⟩
              have h_cont : ContinuousAt (fun x => d₁.density x - d₂.density x) t :=
                (hDiff_cont t ht_in01).continuousAt (Ioo_mem_nhds ht_in01.1 ht_in01.2)
              obtain ⟨ε, hε_pos, hε_nhd⟩ := Metric.continuousAt_iff.mp h_cont
                ((d₁.density t - d₂.density t) / 2) (by linarith)
              have hmin_pos : 0 < min (ε / 2) ((t - x₀) / 2) :=
                lt_min (by linarith) (by linarith [ht.1])
              have hδ := min_le_left (ε / 2) ((t - x₀) / 2)
              have hδ' := min_le_right (ε / 2) ((t - x₀) / 2)
              have hmin_pos' : 0 < min (ε / 2) ((pi - x₀) / 2) := by
                rw [← ht_eq_pi]; exact hmin_pos
              refine ⟨t - min (ε / 2) ((t - x₀) / 2),
                ⟨by linarith, by rw [ht_eq_pi]; linarith [hmin_pos']⟩, ?_⟩
              have ht'_dist : dist (t - min (ε / 2) ((t - x₀) / 2)) t < ε := by
                rw [Real.dist_eq,
                  show t - min (ε / 2) ((t - x₀) / 2) - t =
                      -(min (ε / 2) ((t - x₀) / 2)) by
                    ring]
                rw [abs_neg, abs_of_pos hmin_pos]; linarith
              have h_close := hε_nhd ht'_dist
              rw [Real.dist_eq] at h_close
              have := abs_lt.mp h_close
              linarith
          -- Now t' ∈ (x₀, π) with d₁(t') > d₂(t').
          -- x₀ > 0 or x₀ = 0?
          by_cases hx₀_pos' : 0 < x₀
          · -- x₀ > 0: cross-product gives d₁ ≤ d₂ on (x₀, π), contradiction.
            have hle := hdens_x₀ hx₀_pos'
            have hx₀_in : x₀ ∈ Ioo 0 pi := ⟨hx₀_pos', hx₀_lt_pi⟩
            have ht'_in : t' ∈ Ioo 0 pi := ⟨lt_trans hx₀_pos' ht'_mem.1, ht'_mem.2⟩
            have hcross := hU.1 x₀ t' hx₀_in ht'_in ht'_mem.1
            have hd₂x₀ := hf₂_pos x₀ ⟨hx₀_pos', hx₀_lt1⟩
            have hd₂t' := hf₂_pos t' ⟨ht'_in.1, lt_trans ht'_in.2 hpi_lt⟩
            -- d₁(t') * d₂(x₀) ≤ d₁(x₀) * d₂(t') ≤ d₂(x₀) * d₂(t')
            have h1 : d₁.density t' * d₂.density x₀ ≤ d₂.density t' * d₂.density x₀ :=
              calc d₁.density t' * d₂.density x₀
                  ≤ d₁.density x₀ * d₂.density t' := hcross
                _ ≤ d₂.density x₀ * d₂.density t' :=
                    mul_le_mul_of_nonneg_right hle (le_of_lt hd₂t')
                _ = d₂.density t' * d₂.density x₀ := mul_comm _ _
            exact absurd (le_of_mul_le_mul_right h1 hd₂x₀) (not_le.mpr hft')
          · push Not at hx₀_pos'
            have hx₀_eq0 : x₀ = 0 := le_antisymm hx₀_pos' hx₀_ge0
            have ht'_pos : 0 < t' := by linarith [ht'_mem.1]
            have ht'_lt1 : t' < 1 := lt_trans ht'_mem.2 hpi_lt
            have ht'_in_0pi : t' ∈ Ioo 0 pi := ⟨ht'_pos, ht'_mem.2⟩
            have hd1_ge : ∀ s ∈ Ioo 0 t', d₂.density s ≤ d₁.density s := by
              intro s hs
              exact ratio_mono_left s t' ⟨hs.1, lt_trans hs.2 ht'_mem.2⟩
                ht'_in_0pi hs.2 (le_of_lt hft')
            have hD_mono_0t : MonotoneOn D (Icc 0 t') := by
              apply monotoneOn_of_deriv_nonneg (convex_Icc 0 t')
              · exact hD_cont.continuousOn
              · intro s hs; rw [interior_Icc] at hs
                have hdiff :=
                  (hD_deriv s ⟨hs.1, lt_trans hs.2 ht'_lt1⟩).differentiableAt
                exact hdiff.differentiableWithinAt
              · intro s hs; rw [interior_Icc] at hs
                rw [(hD_deriv s ⟨hs.1, lt_trans hs.2 ht'_lt1⟩).deriv]
                linarith [hd1_ge s ⟨hs.1, hs.2⟩]
            have ht'_prefix : ∀ s ∈ Icc (0 : ℝ) t', 0 ≤ D s := by
              intro s hs
              rcases eq_or_lt_of_le hs.1 with rfl | hs_pos
              · exact le_of_eq hD0.symm
              · have := hD_mono_0t ⟨le_refl _, le_of_lt ht'_pos⟩
                  ⟨le_of_lt hs_pos, hs.2⟩ (le_of_lt hs_pos)
                linarith [hD0]
            have : x₀ < t' := by linarith [ht'_pos]
            have ht'_le : t' ≤ x₀ :=
              hprefix_max t' ⟨le_of_lt ht'_pos, le_of_lt ht'_lt1⟩ ht'_prefix
            exact not_lt.mpr ht'_le this
    exact ⟨c₂, ⟨hc₂_ge_x₀, hc₂_le1⟩, hdens_left, hdens_right⟩
  obtain ⟨c₂, ⟨hc₂_ge, hc₂_le⟩, hdens_left, hdens_right⟩ := hcrossing
  have hD_anti : AntitoneOn D (Icc x₀ c₂) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc x₀ c₂)
    · exact hD_cont.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : (0 : ℝ) < x := by linarith [hx.1]
      have hx1 : x < (1 : ℝ) := by linarith [hx.2]
      exact (hD_deriv x ⟨hx0, hx1⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : (0 : ℝ) < x := by linarith [hx.1]
      have hx1 : x < (1 : ℝ) := by linarith [hx.2]
      rw [(hD_deriv x ⟨hx0, hx1⟩).deriv]
      linarith [hdens_left x ⟨hx.1, hx.2⟩]
  have hD_mono : MonotoneOn D (Icc c₂ 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc c₂ 1)
    · exact hD_cont.continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : (0 : ℝ) < x := by linarith [hx.1]
      exact (hD_deriv x ⟨hx0, hx.2⟩).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : (0 : ℝ) < x := by linarith [hx.1]
      rw [(hD_deriv x ⟨hx0, hx.2⟩).deriv]
      linarith [hdens_right x ⟨hx.1, hx.2⟩]
  have hD_nonpos_after : ∀ x, x₀ < x → D x ≤ 0 := by
    intro x hx
    by_cases hx1 : 1 ≤ x
    · exact le_of_eq (hD_vanish_right x hx1)
    push Not at hx1
    by_cases hxc : x ≤ c₂
    · have h1 : x₀ ∈ Icc x₀ c₂ := ⟨le_refl _, hc₂_ge⟩
      have h2 : x ∈ Icc x₀ c₂ := ⟨le_of_lt hx, hxc⟩
      linarith [hD_anti h1 h2 (le_of_lt hx), hDx₀_eq]
    · push Not at hxc
      have h1 : x ∈ Icc c₂ 1 := ⟨le_of_lt hxc, le_of_lt hx1⟩
      have h2 : (1 : ℝ) ∈ Icc c₂ 1 := ⟨hc₂_le, le_refl _⟩
      linarith [hD_mono h1 h2 (le_of_lt hx1), hD1]
  have hx₀_pos : 0 < x₀ := by
    by_contra h_le; push Not at h_le
    have hx₀_eq : x₀ = 0 := le_antisymm h_le hx₀_ge0
    obtain ⟨a, ha, hDa⟩ := hD_pos
    have : D a ≤ 0 := hD_nonpos_after a (by rw [hx₀_eq]; exact ha.1)
    linarith
  exact ⟨x₀, hx₀_pos, hx₀_lt1,
    fun x hx => by linarith [hD_nonneg_prefix x hx],
    fun x hx => by linarith [hD_nonpos_after x hx]⟩

/-- If two CDFs `F` and `G` supported on `[0, 1]` have equal means and `F` single-crosses `G` from
above (i.e., there exists `x₀ ∈ (0, 1)` with `F(x) ≥ G(x)` for `x < x₀` and `F(x) ≤ G(x)` for
`x > x₀`), then `G` second-order stochastically dominates `F`. -/
public theorem CDF.SOSD.of_singleCrossing_of_equal_mean (F G : CDF)
    (hF_cont : Continuous ⇑F) (hG_cont : Continuous ⇑G)
    -- CDFs agree outside [0,1] (both supported on [0,1])
    (hF_zero : ∀ x, x ≤ 0 → ⇑F x = 0)
    (hG_zero : ∀ x, x ≤ 0 → ⇑G x = 0)
    (hF_one : ∀ x, 1 ≤ x → ⇑F x = 1)
    (hG_one : ∀ x, 1 ≤ x → ⇑G x = 1)
    -- Equal means: ∫₀¹ F(t) dt = ∫₀¹ G(t) dt
    (h_equal_area : ∫ t in Icc 0 1, ⇑F t = ∫ t in Icc 0 1, ⇑G t)
    -- Single crossing: F - G is first ≥ 0 then ≤ 0
    (h_cross : ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ < 1 ∧
      (∀ x, x < x₀ → ⇑F x ≥ ⇑G x) ∧
      (∀ x, x₀ < x → ⇑F x ≤ ⇑G x)) :
    CDF.SOSD G F := by
  refine CDF.SOSD.mk' (CDF.integrableTails_of_continuous_of_zero hG_cont hG_zero)
    (CDF.integrableTails_of_continuous_of_zero hF_cont hF_zero) ?_
  obtain ⟨x₀, hx₀_pos, hx₀_lt1, hFG_before, hFG_after⟩ := h_cross
  have hF_Icc : ∀ (a b : ℝ), IntegrableOn ⇑F (Icc a b) := fun _ _ =>
    hF_cont.integrableOn_Icc
  have hG_Icc : ∀ (a b : ℝ), IntegrableOn ⇑G (Icc a b) := fun _ _ =>
    hG_cont.integrableOn_Icc
  -- For f vanishing on (-∞, 0]: ∫ Iic z = ∫ Icc 0 z.
  have Iic_to_Icc :
      ∀ (f : ℝ → ℝ), Continuous f → (∀ y, y ≤ 0 → f y = 0) → ∀ (z : ℝ), 0 < z →
        ∫ t in Iic z, f t = ∫ t in Icc 0 z, f t := by
    intro f hfc hfz z hz
    have hsplit : Iic z = Iic 0 ∪ Ioc 0 z := (Iic_union_Ioc_eq_Iic (le_of_lt hz)).symm
    have hdisj : Disjoint (Iic 0) (Ioc 0 z) :=
      Set.disjoint_left.mpr fun _ ha hb => not_lt.mpr (mem_Iic.mp ha) (mem_Ioc.mp hb).1
    rw [hsplit, setIntegral_union hdisj measurableSet_Ioc
      (integrableOn_zero.congr_fun (fun t ht => (hfz t (mem_Iic.mp ht)).symm)
        measurableSet_Iic)
      (hfc.integrableOn_Icc (a := 0) (b := z) |>.mono_set Ioc_subset_Icc_self),
      setIntegral_eq_zero_of_forall_eq_zero (fun t ht => hfz t (mem_Iic.mp ht)),
      zero_add, setIntegral_congr_set Ioc_ae_eq_Icc]
  have Icc_split : ∀ (a b : ℝ), 0 ≤ a → a ≤ b →
      Icc (0 : ℝ) b = Icc 0 a ∪ Ioc a b ∧ Disjoint (Icc (0 : ℝ) a) (Ioc a b) := by
    intro a b ha0 hab
    refine ⟨?_, Set.disjoint_left.mpr fun t ht1 ht2 =>
      not_lt.mpr (mem_Icc.mp ht1).2 (mem_Ioc.mp ht2).1⟩
    ext t; simp only [mem_union, mem_Icc, mem_Ioc]; constructor
    · intro ⟨h0, hb'⟩
      by_cases hta : t ≤ a
      · left; exact ⟨h0, hta⟩
      · right; push Not at hta; exact ⟨hta, hb'⟩
    · rintro (⟨h0, ha'⟩ | ⟨ha', hb'⟩)
      · exact ⟨h0, le_trans ha' hab⟩
      · exact ⟨by linarith, hb'⟩
  intro x
  by_cases hx0 : x ≤ 0
  · have hFx : ∫ t in Iic x, ⇑F t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht =>
        hF_zero t (le_trans (mem_Iic.mp ht) hx0)
    have hGx : ∫ t in Iic x, ⇑G t = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun t ht =>
        hG_zero t (le_trans (mem_Iic.mp ht) hx0)
    simp_all only [ge_iff_le, Icc_union_Ioc_eq_Icc, true_and, implies_true,
      integratedCDF_succ, integratedCDF_zero, Std.le_refl]
  push Not at hx0
  simp only [integratedCDF]
  rw [Iic_to_Icc ⇑F hF_cont hF_zero x hx0, Iic_to_Icc ⇑G hG_cont hG_zero x hx0]
  by_cases hx1 : 1 ≤ x
  · obtain ⟨h_eq, h_disj⟩ := Icc_split 1 x (by linarith) hx1
    rw [h_eq,
      setIntegral_union h_disj measurableSet_Ioc (hG_Icc 0 1)
        (hG_Icc 1 x |>.mono_set Ioc_subset_Icc_self),
      setIntegral_union h_disj measurableSet_Ioc (hF_Icc 0 1)
        (hF_Icc 1 x |>.mono_set Ioc_subset_Icc_self)]
    have hFG_tail : ∫ t in Ioc 1 x, ⇑F t = ∫ t in Ioc 1 x, ⇑G t :=
      setIntegral_congr_fun measurableSet_Ioc fun t ht => by
        rw [hF_one t (le_of_lt (mem_Ioc.mp ht).1), hG_one t (le_of_lt (mem_Ioc.mp ht).1)]
    linarith [h_equal_area]
  push Not at hx1
  by_cases hxx0 : x < x₀
  · apply setIntegral_mono_on (hG_Icc 0 x) (hF_Icc 0 x) measurableSet_Icc
    intro t ⟨ht0, htx⟩
    by_cases ht_zero : t ≤ 0
    · rw [hG_zero t ht_zero, hF_zero t ht_zero]
    · push Not at ht_zero
      exact hFG_before t (lt_of_le_of_lt htx hxx0)
  push Not at hxx0
  obtain ⟨h_split_01, h_disj⟩ := Icc_split x 1 (le_of_lt hx0) (le_of_lt hx1)
  have hIoc_sub : Ioc x 1 ⊆ Icc 0 1 := fun t ⟨htx, ht1⟩ => ⟨by linarith, ht1⟩
  have hFs := setIntegral_union h_disj measurableSet_Ioc
    (hF_Icc 0 x) (hF_Icc 0 1 |>.mono_set hIoc_sub)
  have hGs := setIntegral_union h_disj measurableSet_Ioc
    (hG_Icc 0 x) (hG_Icc 0 1 |>.mono_set hIoc_sub)
  rw [h_split_01] at h_equal_area; rw [hFs, hGs] at h_equal_area
  have h_tail_le : ∫ t in Ioc x 1, ⇑F t ≤ ∫ t in Ioc x 1, ⇑G t :=
    setIntegral_mono_on (hF_Icc 0 1 |>.mono_set hIoc_sub)
      (hG_Icc 0 1 |>.mono_set hIoc_sub) measurableSet_Ioc
      fun t ⟨htx, _⟩ => hFG_after t (lt_of_le_of_lt hxx0 htx)
  linarith

/-- A higher-concentration beta distribution second-order stochastically dominates a
lower-concentration one with the same mean: For `κ₁ < κ₂`, `Beta(κ₂π, κ₂(1-π))` SOSD
`Beta(κ₁π, κ₁(1-π))`. -/
public theorem betaWithMean_sosd {κ₁ κ₂ : ℝ}
    (hk1 : 0 < κ₁) (hk2 : 0 < κ₂) (hlt : κ₁ < κ₂) :
    CDF.SOSD (betaWithMean pi κ₂ hpi_pos hpi_lt hk2).cdf
         (betaWithMean pi κ₁ hpi_pos hpi_lt hk1).cdf := by
  set d₁ := betaWithMean pi κ₁ hpi_pos hpi_lt hk1
  set d₂ := betaWithMean pi κ₂ hpi_pos hpi_lt hk2
  apply CDF.SOSD.of_singleCrossing_of_equal_mean d₁.cdf d₂.cdf
    (contdist_cdf_continuous d₁) (contdist_cdf_continuous d₂)
    (betaWithMean_cdf_zero hpi_pos hpi_lt hk1)
    (betaWithMean_cdf_zero hpi_pos hpi_lt hk2)
    (betaWithMean_cdf_one hpi_pos hpi_lt hk1)
    (betaWithMean_cdf_one hpi_pos hpi_lt hk2)
  · rw [betaWithMean_integrated_cdf hpi_pos hpi_lt hk1,
        betaWithMean_integrated_cdf hpi_pos hpi_lt hk2]
  · exact beta_cdf_single_crossing hpi_pos hpi_lt hk1 hk2 hlt

end Econlib.Probability

end -- noncomputable section
