/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Core preference relations and utility representations

This file defines the outcome-generic core of the preference API. A `PreferenceRel X` is a total
preorder on an arbitrary outcome type `X`; no real line, vector space, topology, or arithmetic is
required. The notation `x ≽[R] y` reads as "`x` is weakly preferred to `y`", with derived strict
preference `≻[R]` and indifference `~[R]`.

## Main definitions

* `PreferenceRel` — a rational weak preference relation: A reflexive, transitive, complete relation
  on an outcome type.
* `PreferenceRel.lt`, `PreferenceRel.indiff` — strict preference and indifference.
* `PreferenceRel.upperContour`, `lowerContour`, `strictUpperContour`, `strictLowerContour` — weak
  and strict contour sets.
* `RepresentsPreferenceIn` — ordinal representation of a preference by a utility valued in an
  arbitrary preorder.
* `RepresentsRealPreference` — the real-valued specialization of `RepresentsPreferenceIn`.
* `preferenceOfUtilityIn` — the preference relation induced by a utility valued in a linear order;
  `preferenceOfRealUtility` is its real-valued specialization.

## Main statements

* `PreferenceRel.trichotomy` — exactly one of `x ≻ y`, `y ≻ x`, `x ~ y` holds.
* `preferenceOfUtilityIn_represents` — `preferenceOfUtilityIn u` is represented by `u`.

## Notes

The utility layer is split deliberately. `RepresentsPreferenceIn R u` is the ordinal interface: Its
codomain can be any preorder, so finite preferences are represented in `ℕ`, ordinal APIs choose
their own ordered scales, and theorems do not inherit unnecessary real-valued assumptions.
`RepresentsRealPreference R u` is the real-valued specialization, for theorems needing cardinal
operations, convexity, integration, topology, differentiability, or expected utility.

## Tags

preference relation, utility, ordinal representation, contour set, indifference
-/

@[expose] public section

namespace Econlib.Preferences

/-- A rational weak preference relation on outcomes of type `X`. The field `le x y` means `x` is at
least as good as `y`. The relation is a total preorder: Reflexive, transitive, and complete. -/
structure PreferenceRel (X : Type*) where
  /-- Weak preference: `le x y` means `x` is weakly preferred to `y`. -/
  le : X → X → Prop
  /-- Reflexivity of weak preference. -/
  le_refl : ∀ x, le x x
  /-- Transitivity of weak preference. -/
  le_trans : ∀ x y z, le x y → le y z → le x z
  /-- Completeness of weak preference. -/
  le_total : ∀ x y, le x y ∨ le y x

scoped notation x " ≽[" R "] " y => PreferenceRel.le R x y

namespace PreferenceRel

variable {X : Type*} (R : PreferenceRel X)

/-- Strict preference: `x ≻[R] y` iff `x ≽[R] y` and not `y ≽[R] x`. -/
def lt (x y : X) : Prop := (x ≽[R] y) ∧ ¬(y ≽[R] x)

/-- Indifference: `x ~[R] y` iff both weak comparisons hold. -/
def indiff (x y : X) : Prop := (x ≽[R] y) ∧ (y ≽[R] x)

end PreferenceRel

scoped notation x " ≻[" R "] " y => PreferenceRel.lt R x y
scoped notation x " ~[" R "] " y => PreferenceRel.indiff R x y

namespace PreferenceRel

variable {X : Type*} (R : PreferenceRel X)

/-! ### Extensionality -/

/-- Two preference relations are equal when their `le` relations agree; the remaining fields are
proof-irrelevant. -/
lemma ext_le {R S : PreferenceRel X} (h : R.le = S.le) : R = S := by
  cases R; cases S; congr

/-! ### Strict preference properties -/

/-- Irreflexivity of strict preference: `x ≻ x` is impossible. -/
@[simp] lemma lt_irrefl (x : X) : ¬ (x ≻[R] x) := fun h => h.2 (R.le_refl x)

/-- Transitivity of strict preference: If `x ≻ y` and `y ≻ z`, then `x ≻ z`. -/
lemma lt_trans {x y z : X} (h1 : x ≻[R] y) (h2 : y ≻[R] z) : x ≻[R] z :=
  ⟨R.le_trans x y z h1.1 h2.1, fun h3 => h1.2 (R.le_trans y z x h2.1 h3)⟩

/-- If `x ≻ y` and `y ≽ z`, then `x ≻ z`. -/
lemma lt_of_lt_of_le {x y z : X} (h1 : x ≻[R] y) (h2 : y ≽[R] z) : x ≻[R] z :=
  ⟨R.le_trans x y z h1.1 h2, fun h3 => h1.2 (R.le_trans y z x h2 h3)⟩

/-- If `x ≽ y` and `y ≻ z`, then `x ≻ z`. -/
lemma lt_of_le_of_lt {x y z : X} (h1 : x ≽[R] y) (h2 : y ≻[R] z) : x ≻[R] z :=
  ⟨R.le_trans x y z h1 h2.1, fun h3 => h2.2 (R.le_trans z x y h3 h1)⟩

/-! ### Indifference properties -/

/-- Reflexivity of indifference: `x ~ x`. -/
@[simp] lemma indiff_refl (x : X) : x ~[R] x := ⟨R.le_refl x, R.le_refl x⟩

/-- Symmetry of indifference: If `x ~ y` then `y ~ x`. -/
lemma indiff_symm {x y : X} (h : x ~[R] y) : y ~[R] x := ⟨h.2, h.1⟩

/-- Transitivity of indifference: If `x ~ y` and `y ~ z`, then `x ~ z`. -/
lemma indiff_trans {x y z : X} (h1 : x ~[R] y) (h2 : y ~[R] z) : x ~[R] z :=
  ⟨R.le_trans x y z h1.1 h2.1, R.le_trans z y x h2.2 h1.2⟩

/-- The indifference relation as an equivalence relation on `X`. -/
def indiffSetoid : Setoid X where
  r x y := indiff R x y
  iseqv := ⟨indiff_refl R, (fun {_ } => indiff_symm R), (fun { _ _} => indiff_trans R)⟩

/-! ### Trichotomy -/

/-- If `x ~ y`, then not `x ≻ y`. -/
lemma not_lt_of_indiff {x y : X} (h : x ~[R] y) : ¬ (x ≻[R] y) :=
  fun h' => h'.2 h.2

/-- If `x ≻ y`, then not `x ~ y`. -/
lemma not_indiff_of_lt {x y : X} (h : x ≻[R] y) : ¬ (x ~[R] y) :=
  fun h' => h.2 h'.2

/-- If `x ≻ y`, then not `y ≻ x`. -/
lemma not_lt_both {x y : X} (h : x ≻[R] y) : ¬ (y ≻[R] x) :=
  fun h' => h.2 h'.1

/-- Trichotomy: At least one of `x ≻ y`, `y ≻ x`, or `x ~ y` holds. This is an inclusive
disjunction; the three cases are mutually exclusive by `not_lt_both`, `not_indiff_of_lt`, and
`not_lt_of_indiff`. -/
theorem trichotomy (x y : X) : (x ≻[R] y) ∨ (y ≻[R] x) ∨ (x ~[R] y) := by
  by_cases hxy : x ≽[R] y <;> by_cases hyx : y ≽[R] x
  · exact Or.inr (Or.inr ⟨hxy, hyx⟩)
  · exact Or.inl ⟨hxy, hyx⟩
  · exact Or.inr (Or.inl ⟨hyx, hxy⟩)
  · exact (R.le_total x y).elim (absurd · hxy) (absurd · hyx)

/-! ### Weak preference properties -/

/-- From strict preference to weak preference. -/
lemma le_of_lt {x y : X} (h : x ≻[R] y) : x ≽[R] y := h.1

/-- From indifference to weak preference. -/
lemma le_of_indiff {x y : X} (h : x ~[R] y) : x ≽[R] y := h.1

/-! ### Contour sets

Contour sets are defined for arbitrary outcome types. Topological properties such as closedness
and openness are added in `ContinuousPreferenceRel`; convex or lattice properties are added by
geometry predicates in `Preferences.Geometry`. -/

/-- Weak upper contour set: Alternatives weakly preferred to `x`. -/
def upperContour (x : X) : Set X := {y | y ≽[R] x}

/-- Weak lower contour set: Alternatives weakly worse than `x`. -/
def lowerContour (x : X) : Set X := {y | x ≽[R] y}

/-- Strict upper contour set: Alternatives strictly preferred to `x`. -/
def strictUpperContour (x : X) : Set X := {y | y ≻[R] x}

/-- Strict lower contour set: Alternatives strictly worse than `x`. -/
def strictLowerContour (x : X) : Set X := {y | x ≻[R] y}

/-! ### Contour set complement identities -/

/-- The strict lower contour set is the complement of the upper contour set. -/
lemma strictLowerContour_eq_compl_upperContour (x : X) :
    R.strictLowerContour x = (R.upperContour x)ᶜ := by
  ext y
  simp only [strictLowerContour, upperContour, Set.mem_compl_iff, Set.mem_setOf_eq, lt]
  exact ⟨And.right, fun hny => ⟨(R.le_total x y).elim id (absurd · hny), hny⟩⟩

/-- The strict upper contour set is the complement of the lower contour set. -/
lemma strictUpperContour_eq_compl_lowerContour (x : X) :
    R.strictUpperContour x = (R.lowerContour x)ᶜ := by
  ext y
  simp only [strictUpperContour, lowerContour, Set.mem_compl_iff, Set.mem_setOf_eq, lt]
  exact ⟨And.right, fun hny => ⟨(R.le_total y x).elim id (absurd · hny), hny⟩⟩

/-! ### Contour set monotonicity -/

/-- Strict preference lifts to containment of strict lower contour sets: If `x ≻ y`, then every
alternative strictly worse than `y` is also strictly worse than `x`. -/
lemma strictLowerContour_subset_of_lt {x y : X} (h : x ≻[R] y) :
    R.strictLowerContour y ⊆ R.strictLowerContour x :=
  fun _ hz => R.lt_of_le_of_lt h.1 hz

/-- Indifferent alternatives have identical strict lower contour sets. -/
lemma strictLowerContour_eq_of_indiff {x y : X} (h : x ~[R] y) :
    R.strictLowerContour x = R.strictLowerContour y := by
  ext z
  exact ⟨fun hz => R.lt_of_le_of_lt h.2 hz, fun hz => R.lt_of_le_of_lt h.1 hz⟩

/-- If `x ≻ y`, then `y` belongs to the strict lower contour set of `x`. -/
lemma mem_strictLowerContour_of_lt {x y : X} (h : x ≻[R] y) :
    y ∈ R.strictLowerContour x := h

end PreferenceRel

/-- A utility representation of a preference relation into an arbitrary ordered scale. The order
convention follows the weak-preference notation: `x ≽[R] y` iff the utility of `x` is weakly above
the utility of `y`. The codomain need not carry addition or topology; ordinal representation only
needs an order. -/
def RepresentsPreferenceIn {X U : Type*} [Preorder U] (R : PreferenceRel X) (u : X → U) : Prop :=
  ∀ x y, (x ≽[R] y) ↔ u y ≤ u x

/-- Real-valued preference representation. Use this for cardinal, convex, expected, or smooth
utility statements; use `RepresentsPreferenceIn` for purely ordinal APIs. -/
abbrev RepresentsRealPreference {X : Type*} (R : PreferenceRel X) (u : X → ℝ) : Prop :=
  RepresentsPreferenceIn R u

/-- Construct the ordinal preference relation represented by a utility function. The codomain only
needs a linear order. -/
def preferenceOfUtilityIn {X U : Type*} [LinearOrder U] (u : X → U) : PreferenceRel X where
  le x y := u y ≤ u x
  le_refl x := le_refl (u x)
  le_trans _ _ _ hxy hyz := le_trans hyz hxy
  le_total _ _ := (le_total (u _) (u _)).symm

/-- Real-valued specialization of `preferenceOfUtilityIn`. -/
noncomputable abbrev preferenceOfRealUtility {X : Type*} (u : X → ℝ) : PreferenceRel X :=
  preferenceOfUtilityIn u

/-- Weak preference under a utility representation reads as a weak utility comparison: `x ≽ y` iff
`u y ≤ u x`. -/
@[simp] lemma preferenceOfUtilityIn_le_iff {X U : Type*} [LinearOrder U]
    (u : X → U) (x y : X) :
    PreferenceRel.le (preferenceOfUtilityIn u) x y ↔ u y ≤ u x := Iff.rfl

/-- Strict preference under a utility representation reads as a strict utility comparison: `x ≻ y`
iff `y` has strictly lower utility than `x`. The companion of `preferenceOfUtilityIn_le_iff` for
`≻`. -/
@[simp] lemma preferenceOfUtilityIn_lt_iff {X U : Type*} [LinearOrder U]
    (u : X → U) (x y : X) :
    (preferenceOfUtilityIn u).lt x y ↔ u y < u x := by
  simp only [PreferenceRel.lt, preferenceOfUtilityIn_le_iff, not_le]
  exact and_iff_right_of_imp le_of_lt

/-- Indifference under a utility representation reads as utility equality: `x ~ y` iff `x` and `y`
carry the same utility. Companion of `preferenceOfUtilityIn_le_iff` for `~`. -/
@[simp] lemma preferenceOfUtilityIn_indiff_iff {X U : Type*} [LinearOrder U]
    (u : X → U) (x y : X) :
    (preferenceOfUtilityIn u).indiff x y ↔ u x = u y := by
  simp only [PreferenceRel.indiff, preferenceOfUtilityIn_le_iff]
  rw [and_comm]
  exact le_antisymm_iff.symm

/-- `preferenceOfUtilityIn u` is represented by `u`. -/
@[simp] theorem preferenceOfUtilityIn_represents {X U : Type*} [LinearOrder U]
    (u : X → U) : RepresentsPreferenceIn (preferenceOfUtilityIn u) u :=
  fun _ _ => Iff.rfl

end Econlib.Preferences
