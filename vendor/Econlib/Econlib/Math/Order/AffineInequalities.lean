/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Sign constraints on affine functions nonpositive on the positive ray

If an affine function `t ↦ A·t + B` is nonpositive for every `t > 0`, then both its constant term
and its slope are nonpositive.

## Main results

* `affine_const_nonpos_of_forall_pos` — `(∀ δ > 0, A·δ + B ≤ 0) → B ≤ 0`.
* `affine_slope_nonpos_of_forall_pos` — `(∀ t > 0, A·t + B ≤ 0) → A ≤ 0`.
-/

@[expose] public section

/-- If an affine function `δ ↦ A·δ + B` is nonpositive for every `δ > 0`, then `B ≤ 0`. -/
lemma affine_const_nonpos_of_forall_pos {A B : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → A * δ + B ≤ 0) : B ≤ 0 := by
  by_contra hB
  push Not at hB
  set δ := B / (2 * (|A| + 1)) with hδ
  have hden : 0 < 2 * (|A| + 1) := by positivity
  have hδ_pos : 0 < δ := by rw [hδ]; positivity
  have hδB : δ * (2 * (|A| + 1)) = B := by rw [hδ]; field_simp
  have hbound : |A| * δ ≤ B / 2 :=
    le_of_mul_le_mul_right (by nlinarith [abs_nonneg A, hδB]) hden
  have := h δ hδ_pos
  nlinarith [neg_abs_le A, hδ_pos.le]

/-- If an affine function `t ↦ A·t + B` is nonpositive for every `t > 0`, then `A ≤ 0`. -/
lemma affine_slope_nonpos_of_forall_pos {A B : ℝ}
    (h : ∀ t : ℝ, 0 < t → A * t + B ≤ 0) : A ≤ 0 := by
  by_contra hA
  push Not at hA
  set t : ℝ := (|B| + 1) / A with ht
  have ht_pos : 0 < t := by rw [ht]; positivity
  have hAt : A * t = |B| + 1 := by rw [ht]; field_simp
  have := h t ht_pos
  have hBabs : -|B| ≤ B := neg_abs_le B
  nlinarith
