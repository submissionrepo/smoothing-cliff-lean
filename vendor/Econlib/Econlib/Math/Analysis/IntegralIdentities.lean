/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Closed-form integral identities

This file proves elementary closed-form integral identities: Polynomial integrals on a finite
interval `[a, b]` (from `integral_pow` via FTC) and exponential integrals on `[0, ∞)` (from the
Gamma function, `∫ x in Ioi 0, xⁿ · exp(-r·x) = n! / r^(n+1)`).

## Main statements

* `integral_id_Icc`, `integral_sq_Icc`, `integral_cube_Icc` — polynomial integrals on `[a, b]`.
* `integral_exp_neg_mul_Ioi`, `integral_mul_exp_neg_mul_Ioi`, `integral_sq_mul_exp_neg_mul_Ioi` —
  exponential integrals on `[0, ∞)`.

## Tags

integral, polynomial, exponential, gamma function
-/

@[expose] public section

open Set Real

/-! ### Polynomial integrals on finite intervals -/

/-- `∫ x in a..b, x = (b² - a²) / 2`. -/
lemma integral_id_Icc (a b : ℝ) :
    ∫ x in a..b, x = (b ^ 2 - a ^ 2) / 2 := by
  have := integral_pow (n := 1) (a := a) (b := b)
  simp only [pow_one] at this
  linarith

/-- `∫ x in a..b, x² = (b³ - a³) / 3`. -/
lemma integral_sq_Icc (a b : ℝ) :
    ∫ x in a..b, x ^ 2 = (b ^ 3 - a ^ 3) / 3 := by
  have := integral_pow (n := 2) (a := a) (b := b)
  linarith

/-- `∫ x in a..b, x³ = (b⁴ - a⁴) / 4`. -/
lemma integral_cube_Icc (a b : ℝ) :
    ∫ x in a..b, x ^ 3 = (b ^ 4 - a ^ 4) / 4 := by
  have := integral_pow (n := 3) (a := a) (b := b)
  linarith

/-! ### Exponential integrals on `[0, ∞)` -/

/-- `∫ x in Ioi 0, exp(-r*x) = 1/r` for `r > 0`. -/
lemma integral_exp_neg_mul_Ioi (r : ℝ) (hr : 0 < r) :
    ∫ x in Ioi (0 : ℝ), exp (-r * x) = 1 / r := by
  -- Use Gamma integral identity with a = 1: ∫ t^0 * exp(-(r*t)) = (1/r)^1 * Γ(1)
  simp_rw [neg_mul]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (one_pos : 0 < (1 : ℝ)) hr
  simpa only [show (1 : ℝ) - 1 = 0 from by norm_num, rpow_zero, one_mul, rpow_one,
    Gamma_one, mul_one] using h

/-- `∫ x in Ioi 0, x * exp(-r*x) = 1/r²` for `r > 0`. -/
lemma integral_mul_exp_neg_mul_Ioi (r : ℝ) (hr : 0 < r) :
    ∫ x in Ioi (0 : ℝ), x * exp (-r * x) = 1 / r ^ 2 := by
  -- Use Gamma integral identity with a = 2: ∫ t^1 * exp(-(r*t)) = (1/r)^2 * Γ(2)
  simp_rw [neg_mul]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (two_pos : 0 < (2 : ℝ)) hr
  simp only [show (2 : ℝ) - 1 = 1 from by norm_num] at h
  have hG : Gamma 2 = 1 := by norm_num [Gamma_nat_eq_factorial]
  rw [hG, mul_one] at h
  -- h : ∫ t in Ioi 0, t ^ (1:ℝ) * exp(-(r * t)) = (1/r)^2
  simp only [rpow_one] at h
  -- h : ∫ t in Ioi 0, t * exp(-(r * t)) = (1/r)^2
  -- Goal: ∫ x in Ioi 0, x * exp(-(r * x)) = 1/r^2
  rw [h]; norm_num

/-- `∫ x in Ioi 0, x² * exp(-r*x) = 2/r³` for `r > 0`. -/
lemma integral_sq_mul_exp_neg_mul_Ioi (r : ℝ) (hr : 0 < r) :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * exp (-r * x) = 2 / r ^ 3 := by
  simp_rw [neg_mul]
  have h := integral_rpow_mul_exp_neg_mul_Ioi (three_pos : 0 < (3 : ℝ)) hr
  ring_nf
  have hG : Gamma 3 = 2 := by norm_num [Gamma_nat_eq_factorial]
  have : ∀ t : ℝ, r * t = t * r := fun t => mul_comm r t
  simp only [show (3 : ℝ) - 1 = 2 from by norm_num, this] at h
  rw [one_div, hG] at h
  norm_cast at h
