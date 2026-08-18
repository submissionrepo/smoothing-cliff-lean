/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Distributions.Gaussian
public import Econlib.Probability.Order.MLRP.FOSD

/-!
# The Gaussian location family has the (strict) MLRP

Fixing the variance `v`, the Gaussian *location* family `θ ↦ N(θ, v)` is the textbook example of a
density family with the **monotone likelihood ratio property** (MLRP) — and in fact the *strict*
MLRP. This file packages that fact as `ContDist.gaussianLocation_hasMLRP` /
`ContDist.gaussianLocation_hasStrictMLRP`, feeding the abstract MLRP ⇒ FOSD ⇒ comparative-statics
engine of `Econlib.Probability.Order.MLRP.FOSD`.

## The mathematics

Write the density as `f(x ∣ θ) = C · exp(-(x-θ)² / (2v))`, where the normalizing constant
`C = (√(2πv))⁻¹` does not depend on `θ`. The MLRP cross-product inequality
`f(x₁∣θ₂)·f(x₂∣θ₁) ≤ f(x₂∣θ₂)·f(x₁∣θ₁)` (for `θ₁ < θ₂`, `x₁ ≤ x₂`) reduces, after cancelling `C²`
and taking logs, to comparing exponents. The difference of exponents is exactly
`2(θ₂-θ₁)(x₂-x₁) / (2v) ≥ 0`, which is strictly positive when both orderings are strict, giving the
strict MLRP. The exponent algebra is shared by both directions and factored into the private helper
`gaussianExponentDiff_le` / `gaussianExponentDiff_lt`.

## Main statements

* `ContDist.gaussianLocation_hasMLRP` — the Gaussian location family has the MLRP.
* `ContDist.gaussianLocation_hasStrictMLRP` — the Gaussian location family has the strict MLRP.

## Tags

monotone likelihood ratio, mlrp, gaussian, normal, location family
-/

@[expose] public section

open MeasureTheory Set Real ProbabilityTheory

namespace Econlib.Probability

/-- The exponent difference at the heart of the Gaussian MLRP cross-product inequality. With
`V > 0`, `θ₁ ≤ θ₂` and `x₁ ≤ x₂` the "off-diagonal" exponent sum is dominated by the "diagonal"
one, because the gap is `2(θ₂-θ₁)(x₂-x₁) / (2V) ≥ 0`. -/
private lemma gaussianExponentDiff_le {V : ℝ} (hV : 0 < V) {θ₁ θ₂ x₁ x₂ : ℝ}
    (hθ : θ₁ ≤ θ₂) (hx : x₁ ≤ x₂) :
    -(x₁ - θ₂) ^ 2 / (2 * V) + -(x₂ - θ₁) ^ 2 / (2 * V)
      ≤ -(x₂ - θ₂) ^ 2 / (2 * V) + -(x₁ - θ₁) ^ 2 / (2 * V) := by
  have h2V : (0 : ℝ) < 2 * V := by linarith
  rw [← add_div, ← add_div, div_le_div_iff_of_pos_right h2V]
  nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hθ)]

/-- The strict form of `gaussianExponentDiff_le`: When both orderings are strict, the exponent gap
`2(θ₂-θ₁)(x₂-x₁) / (2V) > 0` is strictly positive. -/
private lemma gaussianExponentDiff_lt {V : ℝ} (hV : 0 < V) {θ₁ θ₂ x₁ x₂ : ℝ}
    (hθ : θ₁ < θ₂) (hx : x₁ < x₂) :
    -(x₁ - θ₂) ^ 2 / (2 * V) + -(x₂ - θ₁) ^ 2 / (2 * V)
      < -(x₂ - θ₂) ^ 2 / (2 * V) + -(x₁ - θ₁) ^ 2 / (2 * V) := by
  have h2V : (0 : ℝ) < 2 * V := by linarith
  rw [← add_div, ← add_div, div_lt_div_iff_of_pos_right h2V]
  nlinarith [mul_pos (sub_pos.2 hx) (sub_pos.2 hθ)]

/-- **The Gaussian location family is MLRP.** Fixing the variance `v`, the density family
`f(x, θ) = (gaussian θ v).density x` satisfies the monotone likelihood ratio property. After
unfolding the density, the common normalizing constant `C` factors out as `C² ≥ 0`, the
exponentials combine, and monotonicity of `exp` reduces the claim to the quadratic inequality
`2(θ₂-θ₁)(x₂-x₁) ≥ 0` (the exponent gap of `gaussianExponentDiff_le`). -/
theorem ContDist.gaussianLocation_hasMLRP (v : ℝ) (hv : 0 < v) :
    HasMLRP (fun θ => ContDist.gaussian θ v hv) := by
  intro θ₁ θ₂ x₁ x₂ hθ hx
  simp only [ContDist.gaussian_density, gaussianPDFReal]
  set V : ℝ := (gaussianVarianceNNReal v hv : ℝ) with hV
  have hVpos : 0 < V := by rw [hV, gaussianVarianceNNReal_coe]; exact hv
  set C : ℝ := (√(2 * π * V))⁻¹ with hC
  -- The products of exponentials are ordered by the (nonnegative) exponent gap.
  have hprod : rexp (-(x₁ - θ₂) ^ 2 / (2 * V)) * rexp (-(x₂ - θ₁) ^ 2 / (2 * V))
             ≤ rexp (-(x₂ - θ₂) ^ 2 / (2 * V)) * rexp (-(x₁ - θ₁) ^ 2 / (2 * V)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (gaussianExponentDiff_le hVpos hθ.le hx)
  -- Multiply through by the common constant `C² ≥ 0`.
  calc C * rexp (-(x₁ - θ₂) ^ 2 / (2 * V)) * (C * rexp (-(x₂ - θ₁) ^ 2 / (2 * V)))
      = C ^ 2 * (rexp (-(x₁ - θ₂) ^ 2 / (2 * V)) * rexp (-(x₂ - θ₁) ^ 2 / (2 * V))) := by ring
    _ ≤ C ^ 2 * (rexp (-(x₂ - θ₂) ^ 2 / (2 * V)) * rexp (-(x₁ - θ₁) ^ 2 / (2 * V))) :=
        mul_le_mul_of_nonneg_left hprod (sq_nonneg C)
    _ = C * rexp (-(x₂ - θ₂) ^ 2 / (2 * V)) * (C * rexp (-(x₁ - θ₁) ^ 2 / (2 * V))) := by ring

/-- **The Gaussian location family is strictly MLRP.** When both the types and the signals are
strictly ordered, the cross-product inequality is strict: The exponent gap `2(θ₂-θ₁)(x₂-x₁) > 0`
(from `gaussianExponentDiff_lt`) is strictly positive, `exp` is strictly monotone, and the common
constant `C² > 0` preserves the strict inequality. -/
theorem ContDist.gaussianLocation_hasStrictMLRP (v : ℝ) (hv : 0 < v) :
    HasStrictMLRP (fun θ => ContDist.gaussian θ v hv) := by
  intro θ₁ θ₂ x₁ x₂ hθ hx
  simp only [ContDist.gaussian_density, gaussianPDFReal]
  set V : ℝ := (gaussianVarianceNNReal v hv : ℝ) with hV
  have hVpos : 0 < V := by rw [hV, gaussianVarianceNNReal_coe]; exact hv
  set C : ℝ := (√(2 * π * V))⁻¹ with hC
  -- The products of exponentials are strictly ordered by the (positive) exponent gap.
  have hprod : rexp (-(x₁ - θ₂) ^ 2 / (2 * V)) * rexp (-(x₂ - θ₁) ^ 2 / (2 * V))
             < rexp (-(x₂ - θ₂) ^ 2 / (2 * V)) * rexp (-(x₁ - θ₁) ^ 2 / (2 * V)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_lt_exp.mpr (gaussianExponentDiff_lt hVpos hθ hx)
  -- Multiply through by the common constant `C² > 0`.
  calc C * rexp (-(x₁ - θ₂) ^ 2 / (2 * V)) * (C * rexp (-(x₂ - θ₁) ^ 2 / (2 * V)))
      = C ^ 2 * (rexp (-(x₁ - θ₂) ^ 2 / (2 * V)) * rexp (-(x₂ - θ₁) ^ 2 / (2 * V))) := by ring
    _ < C ^ 2 * (rexp (-(x₂ - θ₂) ^ 2 / (2 * V)) * rexp (-(x₁ - θ₁) ^ 2 / (2 * V))) :=
        mul_lt_mul_of_pos_left hprod (by positivity)
    _ = C * rexp (-(x₂ - θ₂) ^ 2 / (2 * V)) * (C * rexp (-(x₁ - θ₁) ^ 2 / (2 * V))) := by ring

end Econlib.Probability
