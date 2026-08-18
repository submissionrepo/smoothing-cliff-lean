/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Upper semicontinuity of partial suprema over a compact factor

If `F : α × β → ℝ` is upper semicontinuous and `β` is a nonempty compact space, then the partial
supremum `x ↦ sSup {F (x, b) : b ∈ β}` is upper semicontinuous on `α`.

This is the standard fact that taking a supremum over a compact parameter preserves upper
semicontinuity.

## Main statements

* `upperSemicontinuous_sSup_compact` — the partial supremum of an upper semicontinuous function
  over a nonempty compact factor is upper semicontinuous.

## Notes

Because the supremum is attained on the compact factor, no boundedness or attainment hypothesis is
needed beyond compactness of `β`.

## Tags

upper semicontinuous, supremum, compact, partial supremum
-/

@[expose] public section

open Set

/-- If `F : α × β → ℝ` is upper semicontinuous and `β` is a nonempty compact space, then the
partial supremum `x ↦ sSup {F (x, b) | b : β}` is upper semicontinuous. -/
lemma upperSemicontinuous_sSup_compact
    {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] [CompactSpace β]
    [Nonempty β] {F : α × β → ℝ} (hF : UpperSemicontinuous F) :
    UpperSemicontinuous
      (fun x : α => sSup {y : ℝ | ∃ b : β, y = F (x, b)}) := by
  rw [upperSemicontinuous_iff_isClosed_preimage]
  intro c
  let S : Set (α × β) := {q | c ≤ F q}
  have hS_closed : IsClosed S := hF.isClosed_preimage c
  have hproj_closed : IsClosed (Prod.fst '' S) :=
    isClosedMap_fst_of_compactSpace S hS_closed
  convert hproj_closed using 1
  -- Each section `b ↦ F (x, b)` attains its max on the compact `β`.
  have hmax : ∀ x : α, ∃ bmax : β, ∀ b : β, F (x, b) ≤ F (x, bmax) := by
    intro x
    obtain ⟨bmax, -, hbmax⟩ :=
      ((hF.comp (Continuous.prodMk_right x)).upperSemicontinuousOn Set.univ).exists_isMaxOn
        Set.univ_nonempty isCompact_univ
    exact ⟨bmax, fun b => hbmax trivial⟩
  ext x
  constructor
  · intro hx
    obtain ⟨bmax, hbmax⟩ := hmax x
    have hsup_eq :
        sSup {y : ℝ | ∃ b : β, y = F (x, b)} = F (x, bmax) :=
      le_antisymm
        (csSup_le ⟨F (x, bmax), bmax, rfl⟩ (by rintro y ⟨b, rfl⟩; exact hbmax b))
        (le_csSup ⟨F (x, bmax), by rintro y ⟨b, rfl⟩; exact hbmax b⟩ ⟨bmax, rfl⟩)
    refine ⟨(x, bmax), ?_, rfl⟩
    simpa [hsup_eq] using hx
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨bmax, hbmax⟩ := hmax q.1
    have hbd : BddAbove {y : ℝ | ∃ b : β, y = F (q.1, b)} :=
      ⟨F (q.1, bmax), by rintro y ⟨b, rfl⟩; exact hbmax b⟩
    exact hq.trans (le_csSup hbd ⟨q.2, rfl⟩)
