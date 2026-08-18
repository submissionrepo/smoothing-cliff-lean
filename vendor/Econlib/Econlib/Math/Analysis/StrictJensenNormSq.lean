/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Strict Jensen inequality for the squared norm

For a non-degenerate convex combination `∑ λⁱ yⁱ = y₀` in an inner-product space, with some
`yⁱ ≠ y₀`, the squared norm satisfies `‖y₀‖² < ∑ λⁱ ‖yⁱ‖²`. The strictness comes from the strict
convexity of `‖·‖²`, quantified through the variance identity
`∑ λⁱ ‖yⁱ - y₀‖² = (∑ λⁱ ‖yⁱ‖²) - ‖y₀‖²`.

## Main statements

* `strict_Jensen_norm_sq` — the strict Jensen inequality `‖y₀‖² < ∑ λⁱ ‖yⁱ‖²` for a non-degenerate
  convex combination.

## Tags

Jensen inequality, squared norm, strict convexity, inner product space
-/

@[expose] public section

open scoped InnerProductSpace

/-- Strict Jensen inequality for the squared norm in an inner-product space.  For a non-degenerate
convex combination `∑ λⁱ yⁱ = y₀` with some `yⁱ ≠ y₀`, `‖y₀‖² < ∑ λⁱ ‖yⁱ‖²`. -/
lemma strict_Jensen_norm_sq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] {y₀ : E} {yi : ι → E} {lam : ι → ℝ}
    (hlam_pos : ∀ i, 0 < lam i)
    (hlam_sum : ∑ i, lam i = 1)
    (h_combo : ∑ i, lam i • yi i = y₀)
    (h_nontriv : ∃ i, yi i ≠ y₀) :
    ‖y₀‖ ^ 2 < ∑ i, lam i * ‖yi i‖ ^ 2 := by
  have h_inner_sum : ∑ i, lam i * inner ℝ (yi i) y₀ = ‖y₀‖ ^ 2 := by
    have h_smul : ∀ i, lam i * inner ℝ (yi i) y₀ = inner ℝ (lam i • yi i) y₀ :=
      fun i => (real_inner_smul_left (yi i) y₀ (lam i)).symm
    rw [Finset.sum_congr rfl (fun i _ => h_smul i), ← sum_inner, h_combo,
        real_inner_self_eq_norm_sq]
  have h_const_sum : ∑ i, lam i * ‖y₀‖ ^ 2 = ‖y₀‖ ^ 2 := by
    rw [← Finset.sum_mul, hlam_sum, one_mul]
  have h_id : ∑ i, lam i * ‖yi i - y₀‖ ^ 2
              = (∑ i, lam i * ‖yi i‖ ^ 2) - ‖y₀‖ ^ 2 := by
    have expand : ∀ i,
        lam i * ‖yi i - y₀‖ ^ 2
          = lam i * ‖yi i‖ ^ 2 - 2 * (lam i * inner ℝ (yi i) y₀)
            + lam i * ‖y₀‖ ^ 2 := by
      intro i; rw [norm_sub_sq_real]; ring
    calc ∑ i, lam i * ‖yi i - y₀‖ ^ 2
        = ∑ i, (lam i * ‖yi i‖ ^ 2 - 2 * (lam i * inner ℝ (yi i) y₀)
                + lam i * ‖y₀‖ ^ 2) :=
          Finset.sum_congr rfl (fun i _ => expand i)
      -- Split the sum termwise, factor `2` out of the inner-product sum, then evaluate the
      -- inner-product and constant sums via `h_inner_sum`/`h_const_sum`.
      _ = (∑ i, lam i * ‖yi i‖ ^ 2) - 2 * ‖y₀‖ ^ 2 + ‖y₀‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
                h_inner_sum, h_const_sum]
      _ = (∑ i, lam i * ‖yi i‖ ^ 2) - ‖y₀‖ ^ 2 := by ring
  have h_pos : 0 < ∑ i, lam i * ‖yi i - y₀‖ ^ 2 := by
    obtain ⟨i₀, h_ne⟩ := h_nontriv
    have h_term_pos : 0 < lam i₀ * ‖yi i₀ - y₀‖ ^ 2 :=
      mul_pos (hlam_pos i₀)
        (pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr h_ne)) 2)
    have h_nn : ∀ i ∈ (Finset.univ : Finset ι),
                  0 ≤ lam i * ‖yi i - y₀‖ ^ 2 :=
      fun i _ => mul_nonneg (hlam_pos i).le (sq_nonneg _)
    exact lt_of_lt_of_le h_term_pos
      (Finset.single_le_sum h_nn (Finset.mem_univ i₀))
  linarith
