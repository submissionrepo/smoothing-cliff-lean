/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.SocialChoice.Profile.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Preference-construction operations

Reusable operations for building specific preference relations: Pushing an alternative to the top
or bottom (`moveToTop`, `moveToBottom`) and swapping two alternatives (`swapPref`). Each operation
preserves strictness when the input is strict and preserves the relative ordering of every pair not
involving the named alternatives. The predicates `AtTop`, `AtBottom`, and `AtExtreme` record where
a fixed alternative sits in a ranking.

## Main definitions

* `AtTop`, `AtBottom`, `AtExtreme` — an alternative ranks strictly above all others, strictly below
  all others, or at one of the two extremes.
* `moveToTop`, `moveToBottom` — relocate one alternative to the top or bottom, holding all other
  pairs fixed.
* `swapPref` — exchange the labels of two alternatives in a preference relation.

## Main statements

* `atTop_moveToTop`, `atBottom_moveToBottom` — the relocated alternative ends up at the named
  extreme.
* `moveToTop_le_of_ne`, `moveToBottom_le_of_ne`, `swapPref_le_of_ne` — relocation and swapping
  preserve pairs not involving the named alternatives.
* `StrictPref.moveToTop`, `StrictPref.moveToBottom`, `StrictPref.swapPref` — each operation
  preserves strictness.

## Notes

These operations supply the profile transformations used to formulate pivotal-voter and decisive
coalition arguments, including Arrow-style impossibility results.

## Tags

social choice, preference relation, move to top, move to bottom, swap, strict preference
-/

@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

variable {Alt : Type*}

/-! ### Extremal positions of an alternative -/

/-- `R` ranks `b` strictly above every other alternative. -/
def AtTop (R : PreferenceRel Alt) (b : Alt) : Prop :=
  ∀ a : Alt, a ≠ b → (b ≻[R] a)

/-- `R` ranks `b` strictly below every other alternative. -/
def AtBottom (R : PreferenceRel Alt) (b : Alt) : Prop :=
  ∀ a : Alt, a ≠ b → (a ≻[R] b)

/-- `R` ranks `b` at one of the two extremes. -/
def AtExtreme (R : PreferenceRel Alt) (b : Alt) : Prop :=
  AtTop R b ∨ AtBottom R b

/-- If `b` is at the top, it is at an extreme. -/
lemma AtTop.atExtreme {R : PreferenceRel Alt} {b : Alt} (h : AtTop R b) :
    AtExtreme R b := Or.inl h

/-- If `b` is at the bottom, it is at an extreme. -/
lemma AtBottom.atExtreme {R : PreferenceRel Alt} {b : Alt} (h : AtBottom R b) :
    AtExtreme R b := Or.inr h

/-- `b` cannot be both at the top and at the bottom (assuming there is something else around). -/
lemma not_atTop_and_atBottom {R : PreferenceRel Alt} {b : Alt}
    (hT : AtTop R b) (hB : AtBottom R b) {a : Alt} (ha : a ≠ b) : False :=
  -- `b ≻ a` from the top and `a ≻ b` from the bottom directly contradict.
  (hT a ha).2 (hB a ha).1

/-! ### Moving an alternative to the top or bottom -/

/-- `moveToTop R b`: A preference that places `b` at the top while preserving the relative order of
every other pair under `R`. -/
def moveToTop (R : PreferenceRel Alt) (b : Alt) : PreferenceRel Alt where
  le x y := x = b ∨ (y ≠ b ∧ R.le x y)
  le_refl x := by
    by_cases hx : x = b
    · exact Or.inl hx
    · exact Or.inr ⟨hx, R.le_refl x⟩
  le_trans x y z hxy hyz := by
    rcases hxy with hxb | ⟨hyb, hxy⟩
    · exact Or.inl hxb
    · rcases hyz with hyb' | ⟨hzb, hyz⟩
      · exact absurd hyb' hyb
      · exact Or.inr ⟨hzb, R.le_trans x y z hxy hyz⟩
  le_total x y := by
    by_cases hx : x = b
    · exact Or.inl (Or.inl hx)
    · by_cases hy : y = b
      · exact Or.inr (Or.inl hy)
      · rcases R.le_total x y with hxy | hyx
        · exact Or.inl (Or.inr ⟨hy, hxy⟩)
        · exact Or.inr (Or.inr ⟨hx, hyx⟩)

/-- `moveToBottom R b`: A preference that places `b` at the bottom while preserving the relative
order of every other pair under `R`. -/
def moveToBottom (R : PreferenceRel Alt) (b : Alt) : PreferenceRel Alt where
  le x y := y = b ∨ (x ≠ b ∧ R.le x y)
  le_refl x := by
    by_cases hx : x = b
    · exact Or.inl hx
    · exact Or.inr ⟨hx, R.le_refl x⟩
  le_trans x y z hxy hyz := by
    rcases hyz with hzb | ⟨hyb, hyz⟩
    · exact Or.inl hzb
    · rcases hxy with hyb' | ⟨hxb, hxy⟩
      · exact absurd hyb' hyb
      · exact Or.inr ⟨hxb, R.le_trans x y z hxy hyz⟩
  le_total x y := by
    by_cases hx : x = b
    · exact Or.inr (Or.inl hx)
    · by_cases hy : y = b
      · exact Or.inl (Or.inl hy)
      · rcases R.le_total x y with hxy | hyx
        · exact Or.inl (Or.inr ⟨hx, hxy⟩)
        · exact Or.inr (Or.inr ⟨hy, hyx⟩)

@[simp] lemma moveToTop_le_iff (R : PreferenceRel Alt) (b x y : Alt) :
    (moveToTop R b).le x y ↔ x = b ∨ (y ≠ b ∧ R.le x y) := Iff.rfl

@[simp] lemma moveToBottom_le_iff (R : PreferenceRel Alt) (b x y : Alt) :
    (moveToBottom R b).le x y ↔ y = b ∨ (x ≠ b ∧ R.le x y) := Iff.rfl

/-- After `moveToTop`, `b` is at the top. -/
lemma atTop_moveToTop (R : PreferenceRel Alt) (b : Alt) :
    AtTop (moveToTop R b) b := by
  intro a ha
  refine ⟨Or.inl rfl, ?_⟩
  rintro (hab | ⟨hbb, _⟩)
  · exact ha hab
  · exact hbb rfl

/-- After `moveToBottom`, `b` is at the bottom. -/
lemma atBottom_moveToBottom (R : PreferenceRel Alt) (b : Alt) :
    AtBottom (moveToBottom R b) b := by
  intro a ha
  refine ⟨Or.inl rfl, ?_⟩
  rintro (hab | ⟨hbb, _⟩)
  · exact ha hab
  · exact hbb rfl

/-- `moveToTop` preserves the relative order of every pair not involving `b`. -/
lemma moveToTop_le_of_ne {R : PreferenceRel Alt} {b x y : Alt}
    (hx : x ≠ b) (hy : y ≠ b) :
    (moveToTop R b).le x y ↔ R.le x y := by
  unfold moveToTop
  simp only [hx, hy, ne_eq, not_false_eq_true, true_and, false_or]

/-- `moveToBottom` preserves the relative order of every pair not involving `b`. -/
lemma moveToBottom_le_of_ne {R : PreferenceRel Alt} {b x y : Alt}
    (hx : x ≠ b) (hy : y ≠ b) :
    (moveToBottom R b).le x y ↔ R.le x y := by
  unfold moveToBottom
  simp only [hx, hy, ne_eq, not_false_eq_true, true_and, false_or]

/-- `moveToTop` preserves strictness. -/
lemma StrictPref.moveToTop {R : PreferenceRel Alt} (h : StrictPref R) (b : Alt) :
    StrictPref (moveToTop R b) := by
  intro x y ⟨hxy, hyx⟩
  -- `b` is on top, so indifference can only hold strictly below `b`, where it is `R`-indifference.
  rcases hxy with hxb | ⟨hyb_ne, hxyR⟩ <;> rcases hyx with hyb | ⟨hxb', hyxR⟩
  · rw [hxb, hyb]
  · exact absurd hxb hxb'
  · exact absurd hyb hyb_ne
  · exact h x y ⟨hxyR, hyxR⟩

/-- `moveToBottom` preserves strictness. -/
lemma StrictPref.moveToBottom {R : PreferenceRel Alt} (h : StrictPref R) (b : Alt) :
    StrictPref (moveToBottom R b) := by
  intro x y ⟨hxy, hyx⟩
  -- `b` is at the bottom, so indifference can only hold strictly above `b`, where it is
  -- `R`-indifference.
  rcases hxy with hyb | ⟨hxb_ne, hxyR⟩ <;> rcases hyx with hxb | ⟨hyb', hyxR⟩
  · rw [hxb, hyb]
  · exact absurd hyb hyb'
  · exact absurd hxb hxb_ne
  · exact h x y ⟨hxyR, hyxR⟩

/-! ### Swap of two alternatives in a preference relation

`swapPref R a c` swaps the labels of `a` and `c` in `R`, leaving everything else fixed. -/

variable [DecidableEq Alt]

/-- Swap two alternatives in a preference relation.

`swapPref R a c` is the preference whose `le` on `(x, y)` equals `R`'s `le` on
`(swap a c x, swap a c y)`. When `a = c` this is `R` unchanged. -/
def swapPref (R : PreferenceRel Alt) (a c : Alt) : PreferenceRel Alt where
  le x y := R.le ((Equiv.swap a c) x) ((Equiv.swap a c) y)
  le_refl _ := R.le_refl _
  le_trans _ _ _ hxy hyz := R.le_trans _ _ _ hxy hyz
  le_total _ _ := R.le_total _ _

@[simp] lemma swapPref_le_iff (R : PreferenceRel Alt) (a c x y : Alt) :
    (swapPref R a c).le x y ↔ R.le ((Equiv.swap a c) x) ((Equiv.swap a c) y) :=
  Iff.rfl

/-- The strict part of `swapPref` pulls back along the swap: `x ≻ y` under `swapPref R a c` iff the
swapped images are strictly ordered under `R`. -/
@[simp] lemma swapPref_lt_iff (R : PreferenceRel Alt) (a c x y : Alt) :
    (swapPref R a c).lt x y ↔ R.lt ((Equiv.swap a c) x) ((Equiv.swap a c) y) := Iff.rfl

/-- `swapPref` preserves strictness. -/
lemma StrictPref.swapPref {R : PreferenceRel Alt} (h : StrictPref R) (a c : Alt) :
    StrictPref (swapPref R a c) := by
  intro x y hxy
  have hRind : ((Equiv.swap a c) x) ~[R] ((Equiv.swap a c) y) := hxy
  have hxy' := h _ _ hRind
  exact (Equiv.swap a c).injective hxy'

/-- `swapPref` preserves any pair `(x, y)` not involving `a` or `c`. -/
lemma swapPref_le_of_ne {R : PreferenceRel Alt} {a c x y : Alt}
    (hxa : x ≠ a) (hxc : x ≠ c) (hya : y ≠ a) (hyc : y ≠ c) :
    (swapPref R a c).le x y ↔ R.le x y := by
  simp only [swapPref_le_iff]
  rw [Equiv.swap_apply_of_ne_of_ne hxa hxc, Equiv.swap_apply_of_ne_of_ne hya hyc]

/-- `swapPref` flips the `(a, c)` pair. -/
lemma swapPref_le_swap (R : PreferenceRel Alt) (a c : Alt) :
    (swapPref R a c).le a c ↔ R.le c a := by
  simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- `swapPref` flips the `(c, a)` pair. -/
lemma swapPref_le_swap' (R : PreferenceRel Alt) (a c : Alt) :
    (swapPref R a c).le c a ↔ R.le a c := by
  simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- `swapPref` flips the strict `(a, c)` pair. -/
lemma swapPref_lt_iff_swap (R : PreferenceRel Alt) (a c : Alt) :
    (swapPref R a c).lt a c ↔ R.lt c a := by
  unfold PreferenceRel.lt
  simp

/-- The `(a, b)` pair under `swapPref R a c` equals the `(c, b)` pair under `R` for `b ∉ {a, c}`. -/
lemma swapPref_le_left_a {R : PreferenceRel Alt} {a c b : Alt}
    (hba : b ≠ a) (hbc : b ≠ c) :
    (swapPref R a c).le a b ↔ R.le c b := by
  simp only [swapPref_le_iff, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hba hbc]

/-- The `(b, a)` pair under `swapPref R a c` equals the `(b, c)` pair under `R` for `b ∉ {a, c}`. -/
lemma swapPref_le_right_a {R : PreferenceRel Alt} {a c b : Alt}
    (hba : b ≠ a) (hbc : b ≠ c) :
    (swapPref R a c).le b a ↔ R.le b c := by
  simp only [swapPref_le_iff, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hba hbc]

/-- The `(c, b)` pair under `swapPref R a c` equals the `(a, b)` pair under `R` for `b ∉ {a, c}`. -/
lemma swapPref_le_left_c {R : PreferenceRel Alt} {a c b : Alt}
    (hba : b ≠ a) (hbc : b ≠ c) :
    (swapPref R a c).le c b ↔ R.le a b := by
  simp only [swapPref_le_iff, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hba hbc]

/-- The `(b, c)` pair under `swapPref R a c` equals the `(b, a)` pair under `R` for `b ∉ {a, c}`. -/
lemma swapPref_le_right_c {R : PreferenceRel Alt} {a c b : Alt}
    (hba : b ≠ a) (hbc : b ≠ c) :
    (swapPref R a c).le b c ↔ R.le b a := by
  simp only [swapPref_le_iff, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hba hbc]

end Econlib.SocialChoice
