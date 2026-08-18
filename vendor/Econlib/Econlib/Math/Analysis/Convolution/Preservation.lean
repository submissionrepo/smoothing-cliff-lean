/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convolution

/-!
# Preservation lemmas for mollifier convolution

Generic real-analysis facts about the convolution `φ ⋆ u` on `ℝ` with a nonnegative compact-support
kernel `φ`: Integrability of the convolution integrand, preservation of monotonicity and concavity,
and a uniform linear-growth bound. None of these depend on a probability carrier or stochastic
order; the statements are purely analytic facts about compactly supported convolution kernels.

## Main statements

* `integrable_conv_integrand` — integrability of `t ↦ φ(t)·u(x-t)` for continuous `u`.
* `convolution_monotone` — `φ ⋆ u` is monotone when `φ ≥ 0` and `u` is monotone.
* `convolution_concaveOn` — `φ ⋆ u` is concave when `φ ≥ 0` and `u` is concave.
* `mollify_uniform_bound` — linear-growth bound for mollified linear-growth `u`.

## Tags

convolution, mollifier, monotone, concave, real analysis
-/

@[expose] public section

open MeasureTheory Set Filter Function
open scoped Topology ENNReal Real Convolution

/-- The convolution integrand `t ↦ φ(t) · u(x - t)` is integrable when `φ` has compact support and
both `φ` and `u` are continuous. -/
lemma integrable_conv_integrand {φ : ℝ → ℝ} {u : ℝ → ℝ} (x : ℝ)
    (hφ_supp : HasCompactSupport φ) (hφ_cont : Continuous φ)
    (hu_cont : Continuous u) :
    Integrable (fun t => φ t * u (x - t)) := by
  -- φ t * u(x-t) = φ t • u(x-t); use LocallyIntegrable.integrable_smul_left_of_hasCompactSupport
  have hu_loc : LocallyIntegrable (fun t => u (x - t)) :=
    (hu_cont.comp (continuous_const.sub continuous_id')).locallyIntegrable
  simpa only [smul_eq_mul] using
    hu_loc.integrable_smul_left_of_hasCompactSupport hφ_cont hφ_supp

/-- Convolution with a nonneg compact-support kernel preserves monotonicity. -/
lemma convolution_monotone {φ : ℝ → ℝ} {u : ℝ → ℝ}
    (hφ_nn : ∀ x, 0 ≤ φ x) (hu : Monotone u)
    (hφ_supp : HasCompactSupport φ) (hφ_cont : Continuous φ)
    (hu_cont : Continuous u) :
    Monotone (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) := by
  intro x₁ x₂ hx
  simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]
  apply integral_mono
  · exact integrable_conv_integrand x₁ hφ_supp hφ_cont hu_cont
  · exact integrable_conv_integrand x₂ hφ_supp hφ_cont hu_cont
  · intro t
    exact mul_le_mul_of_nonneg_left (hu (sub_le_sub_right hx t)) (hφ_nn t)

/-- Convolution with a nonneg compact-support kernel preserves concavity. -/
lemma convolution_concaveOn {φ : ℝ → ℝ} {u : ℝ → ℝ}
    (hφ_nn : ∀ x, 0 ≤ φ x) (hu : ConcaveOn ℝ univ u)
    (hφ_supp : HasCompactSupport φ) (hφ_cont : Continuous φ)
    (hu_cont : Continuous u) :
    ConcaveOn ℝ univ (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    -- Merge the left side into a single integral via linearity, then bound the integrand
    -- pointwise using concavity and `a*x + b*y - t = a*(x-t) + b*(y-t)`.
    rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add
          ((integrable_conv_integrand x hφ_supp hφ_cont hu_cont).const_mul a)
          ((integrable_conv_integrand y hφ_supp hφ_cont hu_cont).const_mul b)]
    apply integral_mono
    · exact ((integrable_conv_integrand x hφ_supp hφ_cont hu_cont).const_mul a).add
              ((integrable_conv_integrand y hφ_supp hφ_cont hu_cont).const_mul b)
    · exact integrable_conv_integrand (a * x + b * y) hφ_supp hφ_cont hu_cont
    · intro t
      dsimp only
      have h_conc := hu.2 (mem_univ (x - t)) (mem_univ (y - t)) ha hb hab
      simp only [smul_eq_mul] at h_conc
      have h_key : a * (x - t) + b * (y - t) = a * x + b * y - t := by
        linear_combination -t * hab
      calc a * (φ t * u (x - t)) + b * (φ t * u (y - t))
          = φ t * (a * u (x - t) + b * u (y - t)) := by ring
        _ ≤ φ t * u (a * (x - t) + b * (y - t)) :=
            mul_le_mul_of_nonneg_left h_conc (hφ_nn t)
        _ = φ t * u (a * x + b * y - t) := by rw [h_key]

/-- Mollified functions are uniformly dominated when u has linear growth: |u_ε(x)| ≤ C(1+|x|+ε) ≤
2C(1+|x|) for ε ≤ 1. -/
lemma mollify_uniform_bound (u : ℝ → ℝ) (C : ℝ) (hC : 0 < C)
    (h_bound : ∀ x, |u x| ≤ C * (1 + |x|)) :
    ∀ (φ : ℝ → ℝ), (∀ x, 0 ≤ φ x) → (∫ x, φ x = 1) →
      (support φ ⊆ Metric.closedBall 0 1) →
      ∀ x, |(φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x| ≤ 2 * C * (1 + |x|) := by
  intro φ hφ_nn hφ_one hφ_supp x
  simp only [MeasureTheory.convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  -- φ is integrable (since ∫ φ = 1 ≠ 0, Bochner integral of non-integrable = 0)
  have hφ_int : Integrable φ := by
    by_contra h; simp [integral_undef h] at hφ_one
  -- Pointwise bound: φ(t) * |u(x-t)| ≤ φ(t) * C(2+|x|)
  have h_pw : ∀ t, φ t * |u (x - t)| ≤ φ t * (C * (2 + |x|)) := by
    intro t
    by_cases ht : φ t = 0
    · simp [ht]
    · apply mul_le_mul_of_nonneg_left _ (hφ_nn t)
      have h_in_ball : t ∈ Metric.closedBall (0 : ℝ) 1 :=
        hφ_supp (Function.mem_support.mpr ht)
      rw [Metric.mem_closedBall, dist_zero_right] at h_in_ball
      have h_abs_t : |t| ≤ 1 := by rwa [Real.norm_eq_abs] at h_in_ball
      calc |u (x - t)| ≤ C * (1 + |x - t|) := h_bound _
        _ ≤ C * (2 + |x|) := by
            apply mul_le_mul_of_nonneg_left _ hC.le
            linarith [abs_sub x t]
  -- Main chain
  calc |∫ t, φ t * u (x - t)|
      ≤ ∫ t, |φ t * u (x - t)| := abs_integral_le_integral_abs
    _ = ∫ t, φ t * |u (x - t)| := by
        congr 1; ext t; rw [abs_mul, abs_of_nonneg (hφ_nn t)]
    _ ≤ ∫ t, φ t * (C * (2 + |x|)) := by
        apply integral_mono_of_nonneg
        · exact ae_of_all _ (fun t => mul_nonneg (hφ_nn t) (abs_nonneg _))
        · exact hφ_int.mul_const _
        · exact ae_of_all _ h_pw
    _ = (∫ t, φ t) * (C * (2 + |x|)) := integral_mul_const _ _
    _ = C * (2 + |x|) := by rw [hφ_one, one_mul]
    _ ≤ 2 * C * (1 + |x|) := by nlinarith [abs_nonneg x]
