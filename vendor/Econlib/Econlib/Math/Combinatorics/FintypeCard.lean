/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card

/-!
# Existence of fresh elements from cardinality bounds

Given a finite type whose cardinality exceeds a small bound, one can always find an element
distinct from a fixed list of elements. These are the `Fintype.card`-phrased pigeonhole facts used
by the Arrow's-theorem development (picking a "third" and "fourth" alternative).

Mathlib provides the `Cardinal.mk`-phrased `Cardinal.exists_ne_ne_of_three_le`; the lemmas here
keep the `Fintype.card` interface expected by finite consumers and additionally cover the
four-element case, for which Mathlib has no analog.

## Main results

* `Fintype.exists_ne_of_three_le_card` — with `3 ≤ Fintype.card α`, any two elements admit a third
  distinct from both.
* `Fintype.exists_ne_of_four_le_card` — with `4 ≤ Fintype.card α`, any three elements admit a
  fourth distinct from all.

## Tags

Fintype, cardinality, pigeonhole, distinct elements
-/

@[expose] public section

/-- Pick a third element not in `{u, v}`. Requires `3 ≤ Fintype.card α`. -/
theorem Fintype.exists_ne_of_three_le_card {α : Type*} [Fintype α]
    (h3 : 3 ≤ Fintype.card α) (u v : α) : ∃ w : α, w ≠ u ∧ w ≠ v := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset α) ⊆ ({u, v} : Finset α) := by
    intro z _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hzu : z = u
    · exact Or.inl hzu
    · exact Or.inr (h z hzu)
  have hcard_le : Fintype.card α ≤ ({u, v} : Finset α).card := by
    have := Finset.card_le_card hsub
    simpa using this
  have hcard_le2 : ({u, v} : Finset α).card ≤ 2 := by
    calc ({u, v} : Finset α).card
        ≤ ({v} : Finset α).card + 1 := Finset.card_insert_le _ _
      _ = 1 + 1 := by rw [Finset.card_singleton]
      _ = 2 := rfl
  omega

/-- Pick a fourth element not in `{u, v, w}`. Requires `4 ≤ Fintype.card α`. -/
theorem Fintype.exists_ne_of_four_le_card {α : Type*} [Fintype α]
    (hCard : 4 ≤ Fintype.card α) (u v w : α) : ∃ t : α, t ≠ u ∧ t ≠ v ∧ t ≠ w := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset α) ⊆ ({u, v, w} : Finset α) := by
    intro z _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hzu : z = u
    · exact Or.inl hzu
    · by_cases hzv : z = v
      · exact Or.inr (Or.inl hzv)
      · exact Or.inr (Or.inr (h z hzu hzv))
  have hcard_le : Fintype.card α ≤ ({u, v, w} : Finset α).card := by
    have := Finset.card_le_card hsub
    simpa using this
  have hcard_le3 : ({u, v, w} : Finset α).card ≤ 3 := by
    calc ({u, v, w} : Finset α).card
        ≤ ({v, w} : Finset α).card + 1 := Finset.card_insert_le _ _
      _ ≤ ({w} : Finset α).card + 1 + 1 := by
          apply Nat.add_le_add_right
          exact Finset.card_insert_le _ _
      _ = 1 + 1 + 1 := by rw [Finset.card_singleton]
      _ = 3 := rfl
  omega
