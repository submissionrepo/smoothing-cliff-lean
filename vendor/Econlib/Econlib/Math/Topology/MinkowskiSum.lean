/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Openness of finite Minkowski sums

The Minkowski sum (`Pointwise` addition of sets) over a nonempty finset of open sets is open, in
any topological additive group. Nonemptiness is required: The empty sum is the singleton `{0}`,
which is not open in general.

## Main results

* `isOpen_finset_sum_of_nonempty` — `∑ i ∈ s, f i` is open when `s` is nonempty and each `f i` is
  open.
-/

@[expose] public section

open Pointwise

/-- The Minkowski sum of open sets over a nonempty finset is open. -/
lemma isOpen_finset_sum_of_nonempty {ι : Type*} {L : ℕ}
    {s : Finset ι} (hs : s.Nonempty) {f : ι → Set (Fin L → ℝ)}
    (hf : ∀ i ∈ s, IsOpen (f i)) :
    IsOpen (∑ i ∈ s, f i) := by
  induction s using Finset.cons_induction with
  | empty => exact absurd hs Finset.not_nonempty_empty
  | cons a s has _ih =>
    rw [Finset.sum_cons]
    by_cases hs' : s.Nonempty
    · exact (hf a (Finset.mem_cons_self a s)).add_right
    · rw [Finset.not_nonempty_iff_eq_empty] at hs'
      subst hs'
      simpa using hf a (Finset.mem_cons_self a _)

end
