/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Set.Image

/-!
# Range of a composition with the range factorization

A small `Set.range` identity: Precomposing `g : Set.range v → Z` with the canonical surjection
`x ↦ ⟨v x, _⟩ : X → Set.range v` does not change the range.

## Main results

* `Set.range_comp_rangeFactorization` — `range (g ∘ rangeFactorization v) = range g`.
-/

@[expose] public section

namespace Set

/-- The range of `g` composed with the canonical map into `Set.range v` equals the range of `g`. -/
lemma range_comp_rangeFactorization {X Y Z : Type*} (v : X → Y) (g : Set.range v → Z) :
    Set.range (g ∘ fun x => (⟨v x, Set.mem_range_self x⟩ : Set.range v)) = Set.range g := by
  ext t; simp only [Set.mem_range, Function.comp]
  exact ⟨fun ⟨x, h⟩ => ⟨⟨v x, Set.mem_range_self x⟩, h⟩,
         fun ⟨⟨s, hs⟩, h⟩ => by obtain ⟨x, rfl⟩ := hs; exact ⟨x, h⟩⟩

end Set
