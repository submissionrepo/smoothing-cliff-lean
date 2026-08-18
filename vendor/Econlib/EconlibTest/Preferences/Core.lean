/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Preferences
import Mathlib

/-!
# Preferences Core Non-Vacuity Checks

Compile-time semantic witnesses for `Econlib.Preferences.Basic` (order/indifference algebra,
contour-set API, utility-representation bridge) and `Econlib.Preferences.Pareto` (Pareto
irreflexivity).

The whole test is anchored on one concrete `PreferenceRel (Fin 3)` induced by the utility vector

```
u = ![0, 1, 1]  (i.e. u 0 = 0, u 1 = 1, u 2 = 1)
```

The induced preference convention is: `R.le x y ↔ u y ≤ u x` (x weakly preferred to y).

Hand-computed ranking:

* `1 ≻ 0` — strictly: U 1 = 1 > 0 = u 0.
* `2 ≻ 0` — strictly: U 2 = 1 > 0 = u 0.
* `1 ~ 2` — indifferent: U 1 = u 2 = 1.
* `¬ (0 ≻ 1)` — checked in the negative: U 1 = 1 ≮ 0 = u 0.
* `¬ (0 ≽ 1)` — checked in the negative: U 1 = 1 ≰ 0 = u 0.

These witnesses catch:

* A direction reversal in the `_lt_iff`/`_le_iff` bridge (if ↔ were flipped the negative checks
  would fire as false).
* Missing algebra lemmas (irreflexivity, transitivity, trichotomy, mixed le/lt chains) that only
  manifest when actually applied to concrete points.
* Contour-set complement identities and membership claims resolved by numeric computation.
* Pareto irreflexivity on a two-agent profile where at least one agent's utility is non-constant.
-/

noncomputable section

namespace EconlibTest.Preferences.Core

open Econlib.Preferences

/-- The concrete utility vector: U 0 = 0, u 1 = 1, u 2 = 1. -/
private abbrev u : Fin 3 → ℕ := ![0, 1, 1]

/-- The preference relation induced by `u`. `R.le x y` iff `u y ≤ u x` (x weakly preferred to y). -/
private abbrev R : PreferenceRel (Fin 3) := preferenceOfUtilityIn u

/-! ## Section 1. Representation round-trip

We plug concrete alternatives into `preferenceOfUtilityIn_lt_iff`, `_le_iff`, `_indiff_iff`,
and `_represents`, checking both positive and negative directions against the numbers. -/

section representation

/-- **Strict preference, positive direction.** Alternative 1 is strictly preferred to 0 because
`u 0 = 0 < 1 = u 1`. Exercises the `_lt_iff` bridge in the correct direction. -/
theorem lt_one_zero : R.lt 1 0 := by
  rw [preferenceOfUtilityIn_lt_iff]
  decide

/-- **Strict preference, another positive.** Alternative 2 is strictly preferred to 0. -/
theorem lt_two_zero : R.lt 2 0 := by
  rw [preferenceOfUtilityIn_lt_iff]
  decide

/-- **Negative strict direction.** Alternative 0 is NOT strictly preferred to 1;
`u 1 = 1 ≮ 0 =
u 0`. This catches a direction reversal in the `_lt_iff` bridge: If the iff were
flipped, this would be `False`. -/
theorem not_lt_zero_one : ¬ R.lt 0 1 := by
  rw [preferenceOfUtilityIn_lt_iff]
  decide

/-- **Indifference, positive.** Alternatives 1 and 2 are indifferent because `u 1 = u 2 = 1`. -/
theorem indiff_one_two : R.indiff 1 2 := by
  rw [preferenceOfUtilityIn_indiff_iff]
  decide

/-- **Weak preference, positive.** Alternative 1 is weakly preferred to 0 because `u 0 ≤ u 1`. -/
theorem le_one_zero : R.le 1 0 := by
  rw [preferenceOfUtilityIn_le_iff]
  decide

/-- **Negative weak direction.** Alternative 0 is NOT weakly preferred to 1; `u 1 = 1 ≰ 0 = u 0`. -/
theorem not_le_zero_one : ¬ R.le 0 1 := by
  rw [preferenceOfUtilityIn_le_iff]
  decide

/-- **Representation round-trip.** `preferenceOfUtilityIn_represents` says `R.le x y ↔ u y ≤ u x` —
applying it at `(1, 0)` recovers the numeric inequality directly. -/
theorem represents_at_one_zero : (R.le 1 0) ↔ u 0 ≤ u 1 :=
  preferenceOfUtilityIn_represents u 1 0

end representation

/-! ## Section 2. Order/indifference algebra on `R`

Every structural lemma is exercised on concrete triples derived from the `u = ![0,1,1]`
witness, so the algebra cannot be discharged by vacuously-true closures. -/

section algebra

/-- **Irreflexivity.** Alternative 1 does not strictly prefer itself. -/
theorem lt_one_irrefl : ¬ R.lt 1 1 := R.lt_irrefl 1

-- Under `u = ![0,1,1]` there is no strict three-step chain (alternatives 1 and 2 are
-- indifferent). To exercise `lt_trans`, we introduce a second utility `v = ![0,1,2]` with a
-- genuine strict chain 2 ≻ 1 ≻ 0 under `S = preferenceOfUtilityIn v`.

/-- Helper utility with strictly separated values for a genuine `lt_trans` chain. -/
private abbrev v : Fin 3 → ℕ := ![0, 1, 2]
private abbrev S : PreferenceRel (Fin 3) := preferenceOfUtilityIn v

/-- `S.lt 1 0`: 1 strictly preferred to 0 under `v`. -/
private theorem S_lt_one_zero : S.lt 1 0 := by
  rw [preferenceOfUtilityIn_lt_iff]; decide

/-- `S.lt 2 1`: 2 strictly preferred to 1 under `v`. -/
private theorem S_lt_two_one : S.lt 2 1 := by
  rw [preferenceOfUtilityIn_lt_iff]; decide

/-- `lt_trans` witness on `S`: 2 strictly preferred to 1 and 1 strictly preferred to 0 implies 2
strictly preferred to 0 by transitivity. -/
theorem lt_trans_two_one_zero : S.lt 2 0 :=
  S.lt_trans S_lt_two_one S_lt_one_zero

/-- `S.le 2 1`: 2 weakly preferred to 1 under `v` (genuinely weak, *not* indifference, since
`v 1 = 1 ≠ 2 = v 2`). Used to give `lt_of_le_of_lt` a discriminating weak leg. -/
private theorem S_le_two_one : S.le 2 1 := by
  rw [preferenceOfUtilityIn_le_iff]; decide

/-- `S.le 1 0`: 1 weakly preferred to 0 under `v` (genuinely weak, since `v 0 = 0 ≠ 1 = v 1`). -/
private theorem S_le_one_zero : S.le 1 0 := by
  rw [preferenceOfUtilityIn_le_iff]; decide

/-- **`lt_of_le_of_lt` witness.** A genuine *strict* weak leg: `S.le 2 1` (`v 1 = 1 < 2 = v 2`, so
weak preference that is not indifference) and `S.lt 1 0` (`v 0 = 0 < 1 = v 1`) chain to `S.lt 2 0`.
Swapping the weak-leg direction (`S.le 1 2`, which is false) would break this. -/
theorem lt_of_le_of_lt_witness : S.lt 2 0 :=
  S.lt_of_le_of_lt S_le_two_one S_lt_one_zero

/-- **`lt_of_lt_of_le` witness.** A genuine *strict* weak leg: `S.lt 2 1` (`v 1 = 1 < 2 = v 2`) and
`S.le 1 0` (`v 0 = 0 < 1 = v 1`, weak but not reflexive nor indifference) chain to `S.lt 2 0`. The
weak leg compares the distinct endpoints `1` and `0`, so a reflexive/indifferent witness would not
substitute for it. -/
theorem lt_of_lt_of_le_witness : S.lt 2 0 :=
  S.lt_of_lt_of_le S_lt_two_one S_le_one_zero

/-- **`le_of_lt`.** Strict preference implies weak preference: `R.lt 1 0 → R.le 1 0`. -/
theorem le_of_lt_witness : R.le 1 0 :=
  R.le_of_lt lt_one_zero

/-- **`trichotomy` exhaustiveness.** For alternatives 1 and 0, the library disjunction holds:
exactly one of `1 ≻ 0`, `0 ≻ 1`, `1 ~ 0`. (Exhaustiveness only; exclusivity is below.) -/
theorem trichotomy_one_zero : (R.lt 1 0) ∨ (R.lt 0 1) ∨ (R.indiff 1 0) :=
  R.trichotomy 1 0

/-- **`trichotomy` resolves to the unique branch.** This genuinely *consumes* `R.trichotomy 1 0`:
it case-splits the library disjunction and, using the exclusion lemmas (`not_lt_both`,
`not_indiff_of_lt`) and the fact that the other two branches are refuted by the numbers
(`0 ≻ 1` and `1 ~ 0` are both false), shows the first branch `1 ≻ 0` is the one that fires and the
other two are excluded — the "exactly one" reading of trichotomy. Deleting `R.trichotomy` would
leave no disjunction to case on. -/
theorem trichotomy_one_zero_resolved : R.lt 1 0 ∧ ¬ R.lt 0 1 ∧ ¬ R.indiff 1 0 := by
  rcases R.trichotomy 1 0 with h | h | h
  · -- The first branch fires; exclude the other two from it.
    exact ⟨h, R.not_lt_both h, R.not_indiff_of_lt h⟩
  · -- `0 ≻ 1` contradicts the numbers (`u 1 = 1 ≮ 0 = u 0`).
    exact absurd h not_lt_zero_one
  · -- `1 ~ 0` contradicts the numbers (`u 1 = 1 ≠ 0 = u 0`).
    exact absurd h (R.not_indiff_of_lt lt_one_zero)

/-- **`not_lt_both`.** Since 1 ≻ 0, we cannot have 0 ≻ 1. -/
theorem not_lt_both_witness : ¬ R.lt 0 1 :=
  R.not_lt_both lt_one_zero

/-- A second preference relation on `Fin 3` whose `le` field is *not* definitionally the `le` of
`R = preferenceOfUtilityIn u`: it is written as `¬ (u x < u y)` rather than `u y ≤ u x`. The two
relations agree only after the propositional rewrite `not_lt`, so proving `R = Rnot` genuinely
*consumes* `PreferenceRel.ext_le` rather than collapsing to `rfl`. -/
private def Rnot : PreferenceRel (Fin 3) where
  le x y := ¬ (u x < u y)
  le_refl x := lt_irrefl (u x)
  le_trans x y z hxy hyz := by
    rw [not_lt] at hxy hyz ⊢; exact le_trans hyz hxy
  le_total x y := by
    rw [not_lt, not_lt]; exact (le_total (u x) (u y)).symm

/-- **`ext_le`.** `R` and `Rnot` carry definitionally distinct `le` fields (`u y ≤ u x` vs
`¬ (u x < u y)`); after the `not_lt` rewrite the two functions agree, and `PreferenceRel.ext_le`
upgrades that pointwise agreement to equality of the whole structures. This would fail to compile if
`ext_le` were deleted or stated for a different field. -/
theorem ext_le_witness : R = Rnot :=
  PreferenceRel.ext_le (by funext x y; simp only [Rnot, R, preferenceOfUtilityIn_le_iff, not_lt])

/-- **`indiff_refl`.** Every alternative is indifferent to itself. -/
theorem indiff_refl_witness : R.indiff 0 0 := R.indiff_refl 0

/-- **`indiff_symm`.** Symmetry of indifference: `1 ~ 2` implies `2 ~ 1`. -/
theorem indiff_symm_witness : R.indiff 2 1 := R.indiff_symm indiff_one_two

-- For a *non-degenerate* indifference-transitivity chain we need three mutually indifferent and
-- distinct endpoints, which `u = ![0,1,1]` cannot supply (alternative 0 is strictly worse). Use a
-- constant utility `w = ![5,5,5]` so that all of `Fin 3` is indifferent, then chain `0 ~ 1` and
-- `1 ~ 2` to the *distinct-endpoint* conclusion `0 ~ 2`.
private abbrev w : Fin 3 → ℕ := ![5, 5, 5]
private abbrev T : PreferenceRel (Fin 3) := preferenceOfUtilityIn w

private theorem T_indiff_zero_one : T.indiff 0 1 := by
  rw [preferenceOfUtilityIn_indiff_iff]; decide

private theorem T_indiff_one_two : T.indiff 1 2 := by
  rw [preferenceOfUtilityIn_indiff_iff]; decide

/-- **`indiff_trans`.** A non-degenerate transitivity chain across *distinct* endpoints: under the
constant utility `w = ![5,5,5]`, `0 ~ 1` and `1 ~ 2` chain to `0 ~ 2` (endpoints `0 ≠ 2`). This
exercises transitivity through an intermediate point rather than collapsing to reflexivity. -/
theorem indiff_trans_witness : T.indiff 0 2 :=
  T.indiff_trans T_indiff_zero_one T_indiff_one_two

/-- **`indiffSetoid` carrier.** The indifference setoid on `Fin 3` identifies 1 and 2. -/
theorem indiffSetoid_identifies_one_two : R.indiffSetoid.r 1 2 := indiff_one_two

/-- **`le_of_indiff`.** Indifference gives weak preference in both directions. -/
theorem le_of_indiff_witness : R.le 1 2 :=
  R.le_of_indiff indiff_one_two

/-- **`not_lt_of_indiff`.** Indifference excludes strict preference: `1 ~ 2` implies `¬ (1 ≻ 2)`. -/
theorem not_lt_of_indiff_witness : ¬ R.lt 1 2 :=
  R.not_lt_of_indiff indiff_one_two

/-- **`not_indiff_of_lt`.** Strict preference excludes indifference: `1 ≻ 0` implies `¬ (1 ~ 0)`. -/
theorem not_indiff_of_lt_witness : ¬ R.indiff 1 0 :=
  R.not_indiff_of_lt lt_one_zero

end algebra

/-! ## Section 3. Contour-set API on explicit elements

Complement identities and membership facts are checked at alternative 1 (which has a
non-trivial strict lower contour: Only alternative 0 lies strictly below it) and at the indifferent
pair 1/2. -/

section contours

/-- **`strictLowerContour_eq_compl_upperContour` at 1.**
`strictLowerContour R 1 = (upperContour R 1)ᶜ`.
`upperContour R 1 = {y | y ≽[R] 1} = {y | u 1 ≤ u y} = {y | 1 ≤ u y} = {1, 2}`. -/
theorem strictLowerContour_eq_compl_upperContour_at_one :
    R.strictLowerContour 1 = (R.upperContour 1)ᶜ :=
  R.strictLowerContour_eq_compl_upperContour 1

/-- **`strictUpperContour_eq_compl_lowerContour` at 0.**
`strictUpperContour R 0 = (lowerContour R 0)ᶜ`.
`lowerContour R 0 = {y | 0 ≽[R] y} = {y | u y ≤ u 0} = {y | u y ≤ 0} = {0}`. -/
theorem strictUpperContour_eq_compl_lowerContour_at_zero :
    R.strictUpperContour 0 = (R.lowerContour 0)ᶜ :=
  R.strictUpperContour_eq_compl_lowerContour 0

/-- **Concrete contour computation.** `R.strictLowerContour 1 = {0}`: the only alternative strictly
worse than `1` is `0` (`u 0 = 0 < 1 = u 1`, while `u 2 = 1` ties). The numeric content the
complement-identity docstring promised. -/
theorem strictLowerContour_one_eq : R.strictLowerContour 1 = {0} := by
  ext y
  simp only [PreferenceRel.strictLowerContour, Set.mem_setOf_eq, preferenceOfUtilityIn_lt_iff,
    Set.mem_singleton_iff]
  fin_cases y <;> simp [u]

/-- **Concrete contour computation.** `R.upperContour 1 = {1, 2}`: the alternatives weakly preferred
to `1` are `1` and `2` (both have utility `1`); `0` is excluded. -/
theorem upperContour_one_eq : R.upperContour 1 = {1, 2} := by
  ext y
  simp only [PreferenceRel.upperContour, Set.mem_setOf_eq, preferenceOfUtilityIn_le_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases y <;> simp [u]

/-- **Concrete contour computation.** `R.lowerContour 0 = {0}`: the only alternative weakly worse
than `0` is `0` itself (`u 0 = 0` is the strict minimum). -/
theorem lowerContour_zero_eq : R.lowerContour 0 = {0} := by
  ext y
  simp only [PreferenceRel.lowerContour, Set.mem_setOf_eq, preferenceOfUtilityIn_le_iff,
    Set.mem_singleton_iff]
  fin_cases y <;> simp [u]

/-- **Concrete contour computation.** `R.strictUpperContour 0 = {1, 2}`: the alternatives strictly
preferred to `0` are exactly `1` and `2` (utility `1 > 0`). -/
theorem strictUpperContour_zero_eq : R.strictUpperContour 0 = {1, 2} := by
  ext y
  simp only [PreferenceRel.strictUpperContour, Set.mem_setOf_eq, preferenceOfUtilityIn_lt_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  fin_cases y <;> simp [u]

/-- **`mem_strictLowerContour_of_lt`.** Since `1 ≻ 0`, alternative 0 lies in
`strictLowerContour R 1`. -/
theorem mem_strictLowerContour_of_lt_witness : (0 : Fin 3) ∈ R.strictLowerContour 1 :=
  R.mem_strictLowerContour_of_lt lt_one_zero

/-- **`strictLowerContour_subset_of_lt`, non-vacuous source.** Under `v = ![0,1,2]` we have
`S.lt 2 1` (`v 1 = 1 < 2 = v 2`), so the *nonempty* contour `S.strictLowerContour 1 = {y | v y < 1}
= {0}` is contained in `S.strictLowerContour 2 = {y | v y < 2} = {0, 1}`. The original `R`-version
had an empty source (`R.strictLowerContour 0 = ∅`); here `0` is an explicit member of the source,
pushed through the subset to land in the target. -/
theorem strictLowerContour_subset_of_lt_witness :
    S.strictLowerContour 1 ⊆ S.strictLowerContour 2 :=
  S.strictLowerContour_subset_of_lt S_lt_two_one

/-- The source contour is genuinely nonempty: `0 ∈ S.strictLowerContour 1`, and the subset carries
it into `S.strictLowerContour 2`. -/
theorem strictLowerContour_subset_nonvacuous :
    (0 : Fin 3) ∈ S.strictLowerContour 1 ∧ (0 : Fin 3) ∈ S.strictLowerContour 2 := by
  have h0 : (0 : Fin 3) ∈ S.strictLowerContour 1 :=
    S.mem_strictLowerContour_of_lt S_lt_one_zero
  exact ⟨h0, strictLowerContour_subset_of_lt_witness h0⟩

/-- **`strictLowerContour_eq_of_indiff`.** Since `1 ~ 2`, their strict lower contours coincide:
Both equal `{y | u y < 1} = {0}`. -/
theorem strictLowerContour_eq_of_indiff_witness :
    R.strictLowerContour 1 = R.strictLowerContour 2 :=
  R.strictLowerContour_eq_of_indiff indiff_one_two

end contours

/-! ## Section 4. Pareto dominance: orientation and irreflexivity

A two-agent profile where agent 0 uses preference `R` (utility `u = ![0,1,1]`) and agent 1 uses
preference `S` (utility `v = ![0,1,2]`). We check three things: (1) the *oriented* dominance
`(1,1) ▷ (0,0)` holds (both agents weakly prefer alternative `1` to `0`, agent 0 strictly), (2) the
*reverse* `(0,0) ▷ (1,1)` is refuted (agent 0 does not weakly prefer `0` to `1`), and (3) no profile
dominates itself. Checks (1)+(2) catch an orientation bug in `ParetoDominates` that self-dominance
is blind to. -/

section pareto

/-- The two-agent preference profile: Agent `0` uses `R`, agent `1` uses `S`. -/
private abbrev twoAgentR : Fin 2 → PreferenceRel (Fin 3) := ![R, S]

/-- The "good" outcome profile: Both agents receive alternative 1. -/
private abbrev goodProfile : Fin 2 → Fin 3 := fun _ => 1

/-- The "bad" outcome profile: Both agents receive alternative 0. -/
private abbrev badProfile : Fin 2 → Fin 3 := fun _ => 0

/-- **`ParetoDominates`, oriented positive witness.** The all-`1` profile Pareto-dominates the
all-`0` profile: agent 0 (`R`) has `1 ≻ 0` (`u 0 = 0 < 1 = u 1`) and agent 1 (`S`) has `1 ≽ 0`
(`v 0 = 0 ≤ 1 = v 1`), so every agent weakly prefers `1` to `0` and agent 0 strictly does. -/
theorem pareto_dominates_good_bad : ParetoDominates twoAgentR goodProfile badProfile := by
  refine ⟨fun i => ?_, 0, ?_⟩
  · -- Weak preference for both agents.
    fin_cases i
    · change (1 : Fin 3) ≽[R] 0
      rw [preferenceOfUtilityIn_le_iff]; decide
    · change (1 : Fin 3) ≽[S] 0
      rw [preferenceOfUtilityIn_le_iff]; decide
  · -- Agent 0 strictly prefers `1` to `0`.
    change (1 : Fin 3) ≻[R] 0
    rw [preferenceOfUtilityIn_lt_iff]; decide

/-- **`ParetoDominates`, oriented negative witness.** The reverse dominance fails: the all-`0`
profile does *not* Pareto-dominate the all-`1` profile, because agent 0 does not even weakly prefer
`0` to `1` (`u 1 = 1 ≰ 0 = u 0`). This is exactly the orientation an argument-swap bug would
violate. -/
theorem not_pareto_dominates_bad_good : ¬ ParetoDominates twoAgentR badProfile goodProfile := by
  rintro ⟨hweak, -⟩
  -- Agent 0's weak-preference condition `0 ≽[R] 1` is false.
  exact not_le_zero_one (hweak 0)

/-- **`not_paretoDominates_self`.** No profile can Pareto-dominate itself. At any putative strict
gainer `i`, we would need `twoAgentR i .lt 1 1`, which is irreflexive. -/
theorem pareto_irrefl_witness : ¬ ParetoDominates twoAgentR goodProfile goodProfile :=
  not_paretoDominates_self twoAgentR goodProfile

end pareto

end EconlibTest.Preferences.Core

end
