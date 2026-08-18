/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic

/-!
# Finite preference representations

This file contains representation theorems for rational preferences on finite outcome spaces.
Finiteness is enough to build an ordinal utility by counting lower contour sets,
`u x = |{z | x ≽ z}|`, which preserves the preference order.

## Main statements

* `exists_nat_utility_representation_of_finite` — every preference relation on a finite type admits
  an ordinal utility representation valued in `ℕ`.
* `exists_utility_representation_of_finite` — the real-valued specialization.
* `PreferenceRel.exists_greatest_on` — every nonempty subset of a finite type has a `≽`-greatest
  element.

## Tags

preference relation, utility, ordinal representation, finite
-/

@[expose] public section

namespace Econlib.Preferences

/-- Any preference relation on a finite type admits an ordinal utility representation into `ℕ`.

The utility is the cardinality of the lower contour set. This representation is ordinal: It only
preserves preference order, and the numerical gaps between utility values carry no economic
meaning. -/
theorem exists_nat_utility_representation_of_finite {X : Type*} [Finite X]
    (R : PreferenceRel X) :
    ∃ u : X → ℕ, RepresentsPreferenceIn R u := by
  classical
  letI : Fintype X := Fintype.ofFinite X
  let u : X → ℕ := fun x => (Finset.univ.filter (fun z => R.le x z)).card
  use u
  intro x y
  simp only [u]
  constructor
  · intro hxy
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact R.le_trans x y z hxy hz
  · intro huxy
    by_contra hnxy
    have hyx : R.le y x := by
      rcases R.le_total x y with h | h
      · exact absurd h hnxy
      · exact h
    have hsub : Finset.univ.filter (fun z => R.le x z)
      ⊆ Finset.univ.filter (fun z => R.le y z) := by
        intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact R.le_trans y x z hyx hz
    have hy_in : y ∈ Finset.univ.filter (fun z => R.le y z) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact R.le_refl y
    have hy_not : y ∉ Finset.univ.filter (fun z => R.le x z) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hnxy
    have hss : Finset.univ.filter (fun z => R.le x z) ⊂
        Finset.univ.filter (fun z => R.le y z) :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hy_not (h ▸ hy_in)⟩
    exact (not_lt_of_ge huxy) (Finset.card_lt_card hss)

/-- Any rational preference relation on a finite type admits a real-valued utility
representation.

This is the real-valued specialization of the lower-contour-cardinality construction. Prefer
`exists_nat_utility_representation_of_finite` when a theorem only needs an ordinal
representation. -/
theorem exists_utility_representation_of_finite {X : Type*} [Finite X]
    (R : PreferenceRel X) :
    ∃ u : X → ℝ, RepresentsRealPreference R u := by
  obtain ⟨u, hu⟩ := exists_nat_utility_representation_of_finite R
  exact ⟨fun x => (u x : ℝ), fun x y => (hu x y).trans Nat.cast_le.symm⟩

/-- Any preference relation (total preorder) has a `≽`-greatest element on every nonempty subset.
This is the existence fact behind `Optimization.argmaxRel` nonemptiness on finite alternative
spaces (e.g. voting rules); on infinite spaces use compactness (Berge) instead. -/
theorem PreferenceRel.exists_greatest_on {X : Type*} [Finite X] (R : PreferenceRel X)
    {S : Set X} (hne : S.Nonempty) : ∃ x ∈ S, ∀ y ∈ S, x ≽[R] y := by
  obtain ⟨u, hu⟩ := exists_nat_utility_representation_of_finite R
  obtain ⟨x, hxS, hxmax⟩ := Set.exists_max_image S u S.toFinite hne
  exact ⟨x, hxS, fun y hy => (hu x y).mpr (hxmax y hy)⟩

end Econlib.Preferences
