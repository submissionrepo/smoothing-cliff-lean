/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Real.Archimedean
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# A weighted-supremum bound

A nonnegatively-weighted combination of the suprema of two bounded-above sets of reals is bounded
by any uniform bound on the corresponding weighted combinations of their elements.

## Main results

* `mul_csSup_add_mul_csSup_le` — `α * sSup S₁ + β * sSup S₂ ≤ B` from a pointwise bound.
-/

@[expose] public section

/-- If `∀ r₁ ∈ S₁, ∀ r₂ ∈ S₂, α * r₁ + β * r₂ ≤ B` and `α, β ≥ 0`, then
`α * sSup S₁ + β * sSup S₂ ≤ B`. -/
lemma mul_csSup_add_mul_csSup_le {S₁ S₂ : Set ℝ} {α β B : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hne₁ : S₁.Nonempty) (hne₂ : S₂.Nonempty)
    -- kept for API symmetry with the natural boundedness hypotheses; `csSup_le` needs no bound
    (_hbdd₁ : BddAbove S₁) (_hbdd₂ : BddAbove S₂)
    (h : ∀ r₁ ∈ S₁, ∀ r₂ ∈ S₂, α * r₁ + β * r₂ ≤ B) :
    α * sSup S₁ + β * sSup S₂ ≤ B := by
  have step1 : ∀ r₁ ∈ S₁, α * r₁ + β * sSup S₂ ≤ B := by
    intro r₁ hr₁
    by_cases hβ0 : β = 0
    · subst hβ0; simp
      obtain ⟨r₂, hr₂⟩ := hne₂
      have := h r₁ hr₁ r₂ hr₂; simp at this; linarith
    · have hβpos : 0 < β := lt_of_le_of_ne hβ (Ne.symm hβ0)
      suffices β * sSup S₂ ≤ B - α * r₁ by linarith
      have hsup : sSup S₂ ≤ (B - α * r₁) / β :=
        csSup_le hne₂ (fun r₂ hr₂ => by
          rw [le_div_iff₀ hβpos]; linarith [h r₁ hr₁ r₂ hr₂])
      calc β * sSup S₂ ≤ β * ((B - α * r₁) / β) :=
              mul_le_mul_of_nonneg_left hsup (le_of_lt hβpos)
        _ = B - α * r₁ := by field_simp
  by_cases hα0 : α = 0
  · subst hα0; simp
    obtain ⟨r₁, hr₁⟩ := hne₁
    have := step1 r₁ hr₁; simp at this; linarith
  · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    suffices α * sSup S₁ ≤ B - β * sSup S₂ by linarith
    have hsup : sSup S₁ ≤ (B - β * sSup S₂) / α :=
      csSup_le hne₁ (fun r₁ hr₁ => by
        rw [le_div_iff₀ hαpos]; linarith [step1 r₁ hr₁])
    calc α * sSup S₁ ≤ α * ((B - β * sSup S₂) / α) :=
            mul_le_mul_of_nonneg_left hsup (le_of_lt hαpos)
      _ = B - β * sSup S₂ := by field_simp
