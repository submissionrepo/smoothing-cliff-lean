/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Cauchy–Schwarz inequality for Bochner integrals

The **Cauchy–Schwarz inequality** in the form of an inequality between integrals of real-valued
functions: The square of the integral of a product is bounded by the product of the integrals of
the squares, under explicit integrability hypotheses.

## Main statements

* `MeasureTheory.integral_inner_mul_le_norm_sq_mul_norm_sq` — `(∫ g · h)² ≤ (∫ g²) · (∫ h²)`.

## Tags

cauchy-schwarz, integral, inequality
-/

open MeasureTheory

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The **Cauchy–Schwarz inequality for integrals**: The square of the integral of a product is
bounded by the product of the integrals of the squares. That is,
`(∫ x, g x * h x ∂μ)² ≤ (∫ x, (g x)² ∂μ) * (∫ x, (h x)² ∂μ)`. -/
public theorem integral_inner_mul_le_norm_sq_mul_norm_sq
    (g h : α → ℝ)
    (hg2 : Integrable (fun x => g x ^ 2) μ)
    (hh2 : Integrable (fun x => h x ^ 2) μ)
    (hgh : Integrable (fun x => g x * h x) μ) :
    (∫ x, g x * h x ∂μ) ^ 2 ≤ (∫ x, g x ^ 2 ∂μ) * (∫ x, h x ^ 2 ∂μ) := by
  suffices key : ∀ t : ℝ, 0 ≤ (∫ x, g x ^ 2 ∂μ) * (t * t) +
      (2 * ∫ x, g x * h x ∂μ) * t + (∫ x, h x ^ 2 ∂μ) by
    have disc := discrim_le_zero key
    unfold discrim at disc
    nlinarith [disc]
  intro t
  -- The quadratic `0 ≤ ∫ (t·g + h)²` expands to the discriminant form by linearity of `∫`.
  have step1 : 0 ≤ ∫ x, (t * g x + h x) ^ 2 ∂μ := by
    apply integral_nonneg; intro x; positivity
  have hexpand : ∫ x, (t * g x + h x) ^ 2 ∂μ =
      t * t * (∫ x, g x ^ 2 ∂μ) + 2 * t * (∫ x, g x * h x ∂μ) + ∫ x, h x ^ 2 ∂μ :=
    calc ∫ x, (t * g x + h x) ^ 2 ∂μ
        = ∫ x, (t * t * (g x ^ 2) + 2 * t * (g x * h x) + h x ^ 2) ∂μ := by
          congr 1; ext x; ring
      _ = ∫ x, (t * t * (g x ^ 2) + 2 * t * (g x * h x)) ∂μ + ∫ x, h x ^ 2 ∂μ :=
          integral_add ((hg2.const_mul _).add (hgh.const_mul _)) hh2
      _ = t * t * (∫ x, g x ^ 2 ∂μ) + 2 * t * (∫ x, g x * h x ∂μ) + ∫ x, h x ^ 2 ∂μ := by
          rw [integral_add (hg2.const_mul _) (hgh.const_mul _), integral_const_mul,
            integral_const_mul]
  linarith [step1, hexpand]

end MeasureTheory
