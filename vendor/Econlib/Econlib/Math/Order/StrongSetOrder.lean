/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Order.Lattice

/-!
# Strong set order

The **strong set order** `A ≤ₛ B` on a lattice holds when `a ⊓ b ∈ A` and `a ⊔ b ∈ B` for every
`a ∈ A` and `b ∈ B`. It is the set-valued ordering underlying Topkis-style monotone comparative
statics, expressing that `B` sits "above" `A`.

## Main definitions

* `StrongSetOrder` — the strong set order on subsets of a lattice.

## Main statements

* `strongSetOrder_of_forall_le` — on a linear order, `A ≤ₛ B` whenever every element of `A` is
  below every element of `B`.

## Tags

strong set order, lattice, comparative statics, veinott
-/

@[expose] public section

/-- The strong set order (Veinott): `A ≤ₛ B` iff for all `a ∈ A` and `b ∈ B`, `a ⊓ b ∈ A` and
`a ⊔ b ∈ B`. On a lattice this captures the idea that `B` is "higher" than `A` in a set-valued
sense. -/
def StrongSetOrder {α : Type*} [Lattice α] (A B : Set α) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, a ⊓ b ∈ A ∧ a ⊔ b ∈ B

/-- On a linear order, if every element of `A` is `≤` every element of `B`, then `A ≤ₛ B` in the
strong set order. -/
lemma strongSetOrder_of_forall_le {α : Type*} [LinearOrder α] {A B : Set α}
    (h : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) : StrongSetOrder A B := by
  intro a ha b hb
  have hab := h a ha b hb
  exact ⟨by rwa [inf_eq_left.mpr hab], by rwa [sup_eq_right.mpr hab]⟩
