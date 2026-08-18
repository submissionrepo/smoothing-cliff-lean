/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Real.Archimedean
public import Mathlib.Order.Interval.Set.Basic

/-!
# Order facts about real intervals

Small set-theoretic identities for intervals on `ℝ` not covered directly by Mathlib.

## Main results

* `iInter_Iic_neg_nat_eq_empty` — the left tails `Iic (-n)` shrink to the empty set as `n → ∞`.
-/

@[expose] public section

open Set

/-- The left tails `Iic (-n)` shrink to the empty set as `n → ∞`. -/
lemma iInter_Iic_neg_nat_eq_empty : ⋂ n : ℕ, Iic (-(n : ℝ)) = ∅ := by
  ext x; simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall]
  exact ⟨⌈-x⌉₊ + 1, by push_cast; linarith [Nat.le_ceil (-x)]⟩
