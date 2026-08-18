/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Tactic.FinCases

/-!
# Suprema over `Fin 2`

In a conditionally complete linear order, the supremum over `Fin 2` is the binary `max`. This is
the conditionally complete analog of Mathlib's complete-lattice `iSup`-evaluation lemmas, used to
evaluate best-case payoffs over two alternatives in finite games over `ℝ`.

## Main statements

* `iSup_fin_two` — `⨆ i : Fin 2, f i = max (f 0) (f 1)`.

## Tags

supremum, fin two, conditionally complete
-/

@[expose] public section

/-- In a conditionally complete linear order, the supremum over `Fin 2` is the binary `max`. -/
lemma iSup_fin_two {α : Type*} [ConditionallyCompleteLinearOrder α] (f : Fin 2 → α) :
    ⨆ i, f i = max (f 0) (f 1) := by
  apply le_antisymm
  · apply ciSup_le
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  · apply max_le
    · exact le_ciSup (Set.Finite.bddAbove (Set.finite_range f)) 0
    · exact le_ciSup (Set.Finite.bddAbove (Set.finite_range f)) 1

end
