/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Finite Preferences Always Have a Utility Representation

A foundational fact of choice theory: Any *rational* preference relation — one that is reflexive,
transitive, and complete — over a finite set of alternatives can be represented by a utility
function. The utility function is just a numerical scorecard whose order agrees with the
preference: `x` is weakly preferred to `y` exactly when `x` scores at least as high as `y`. This
file exhibits the construction on a concrete four-alternative ranking with an indifference class,
displays a concrete representing utility, and harvests both a natural-number-valued and a
real-valued representation from the library's existence theorems.

## The model

The outcome space is four alternatives, `X := Fin 4` (think of four policies, candidates, or
bundles). The decision maker ranks them `0 ≻ 1 ~ 2 ≻ 3`: Alternative `0` is strictly best,
alternatives `1` and `2` are interchangeable, and `3` is strictly worst. The indifference class
`{1, 2}` is the point of the example: A utility representation must assign equal scores to
indifferent alternatives, so the interesting case of the representation biconditional — the
`u y = u x` case, not just the strict comparisons — is exercised.

For definiteness we seed this ranking from a scoring function `![2, 1, 1, 0]` via
`preferenceOfRealUtility`, so that `0` scores `2`, both `1` and `2` score `1`, and `3` scores `0`.
This is purely a convenient way to write down a specific complete, transitive ranking. The
existence theorems below do **not** see this seed: They treat `R` as an abstract order relation and
would produce a utility for any finite preference, however it was specified. The seed then
returns as a concrete witness: `seed_represents` checks it against the
representation interface, closing the loop between the displayed ranking and an explicit
representing utility.

## The mathematics

The representation interface is `RepresentsPreferenceIn R u`, which asserts `x ≽[R] y ↔ u y ≤ u x`
for all `x, y` (real-valued specialization: `RepresentsRealPreference R u`). The library proves two
existence theorems for finite outcome spaces:

* `exists_nat_utility_representation_of_finite` builds an *ordinal* utility into `ℕ` by counting
  lower contour sets, `u x = |{z | x ≽ z}|`;
* `exists_utility_representation_of_finite` is its real-valued convenience specialization.

`Fin 4` is a `Fintype`, hence `Finite`, so both apply with no extra work. We also read off the
concrete ranking — strict preferences and the indifference — directly from the seeding scores, by
unfolding `≻`/`~` to weak comparisons via `preferenceOfUtilityIn_le_iff`.

## Main definitions and theorems

* `R` — the concrete preference on `Fin 4`, seeded so that `0 ≻ 1 ~ 2 ≻ 3`.
* `zero_pref_one`, `two_pref_three` — strict ranking facts, stated with `≻[R]`.
* `one_indiff_two` — the indifference `1 ~[R] 2`: Equal scores, interchangeable alternatives.
* `zero_pref_three` — strict preference composes across the indifference class: `0 ≻ 1 ≽ 2 ≻ 3`.
* `seed_represents` — the seed `![2, 1, 1, 0]` itself represents `R`: A concrete utility for the
  concrete ranking, assigning equal scores exactly on the indifference class.
* `has_nat_representation` — `R` is represented by some `u : Fin 4 → ℕ`.
* `has_real_representation` — `R` is represented by some `u : Fin 4 → ℝ`.
-/

noncomputable section

namespace EconlibExamples.Preferences.FiniteRepresentation

open Econlib.Preferences

/-! ## A concrete ranking over four alternatives, with an indifference class -/

/-- The concrete preference on four alternatives, seeded from the scoring function
`![2, 1, 1, 0]`.

The seed assigns scores `0 ↦ 2`, `1 ↦ 1`, `2 ↦ 1`, `3 ↦ 0`, which determines the ranking
`0 ≻ 1 ~ 2 ≻ 3` — two strict steps around an indifference class. The seed is only a way to write a
specific complete, transitive relation; the existence theorems below ignore it and apply to any
finite preference. -/
def R : PreferenceRel (Fin 4) := preferenceOfRealUtility ![2, 1, 1, 0]

/-! ## The ranking, read off from the seed

Recall `R.lt x y` (notation `x ≻[R] y`) unfolds to `(x ≽[R] y) ∧ ¬(y ≽[R] x)`: The first
argument is the strictly preferred alternative; `x ~[R] y` is mutual weak preference. Because
`preferenceOfRealUtility` is a reducible abbreviation of `preferenceOfUtilityIn`, the `@[simp]`
read-off lemmas `preferenceOfUtilityIn_lt_iff` / `preferenceOfUtilityIn_indiff_iff` fire directly
through the `R` seed, collapsing each comparison to a numeric (in)equality on the seeding scores
that `norm_num` settles (the scores live in `ℝ`, so `decide` does not apply). The only manual step
is selecting the `Matrix.cons_val_*` lemmas that index into the literal `![…]`. -/

/-- Alternative `0` is strictly preferred to alternative `1`. -/
theorem zero_pref_one : (0 : Fin 4) ≻[R] 1 := by
  simp only [R, preferenceOfUtilityIn_lt_iff, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Alternatives `1` and `2` are indifferent: They carry the same score, so the decision maker is
happy to swap one for the other. This is the case a representation theorem must get right beyond
the strict comparisons. -/
theorem one_indiff_two : (1 : Fin 4) ~[R] 2 := by
  simp only [R, preferenceOfUtilityIn_indiff_iff, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- Alternative `2` is strictly preferred to alternative `3`. -/
theorem two_pref_three : (2 : Fin 4) ≻[R] 3 := by
  simp only [R, preferenceOfUtilityIn_lt_iff, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Matrix.cons_val_three]
  norm_num

/-- Strict preference composes across the indifference class: `0 ≻ 1 ≽ 2 ≻ 3` collapses to `0 ≻ 3`.
Mixing strict and weak steps exercises `lt_of_lt_of_le` and `lt_trans` of the preference-relation
API. -/
theorem zero_pref_three : (0 : Fin 4) ≻[R] 3 :=
  R.lt_trans (R.lt_of_lt_of_le zero_pref_one one_indiff_two.1) two_pref_three

/-! ## A concrete representing utility

The seed itself is a representation: `RepresentsPreferenceIn` is checked, not assumed. In
particular the indifferent pair `1 ~ 2` receives the same score `1` — equality of utilities on
indifference classes is exactly what distinguishes a representation from a mere strict-order
embedding. -/

/-- **The seed represents the ranking.** The scoring function `![2, 1, 1, 0]` satisfies the
representation interface for `R`: `x ≽[R] y ↔ u y ≤ u x` for all pairs, including the equal-score
indifference class `{1, 2}`. -/
theorem seed_represents : RepresentsRealPreference R ![2, 1, 1, 0] :=
  preferenceOfUtilityIn_represents _

/-! ## Utility representations exist, abstractly

Both conclusions are immediate instances of the finite-representation existence theorems:
`Fin 4` is finite, and the theorems treat `R` as an abstract order relation, never looking at the
seed. -/

/-- `R` admits a natural-number-valued (ordinal) utility representation. -/
theorem has_nat_representation : ∃ u : Fin 4 → ℕ, RepresentsPreferenceIn R u :=
  exists_nat_utility_representation_of_finite R

/-- `R` admits a real-valued utility representation. -/
theorem has_real_representation : ∃ u : Fin 4 → ℝ, RepresentsRealPreference R u :=
  exists_utility_representation_of_finite R

end EconlibExamples.Preferences.FiniteRepresentation
