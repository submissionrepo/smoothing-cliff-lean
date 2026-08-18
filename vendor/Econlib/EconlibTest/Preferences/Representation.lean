/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Preferences
import Mathlib

/-!
# Preferences Representation Non-Vacuity Checks

Compile-time semantic witnesses for `Econlib.Preferences.Representation.Debreu` — the Debreu
continuous-utility representation machinery (`ContinuousPreferenceRel`, the raw-utility
construction, and the continuity bridges). The theorem's failure mode is **circular
instantiation**: Running a representation theorem on an order that *already came from* a utility
proves nothing. So the primary witness is built ORDER-FIRST.

## The order-first witness (`closerPref` on `[0,1]`)

On `X := Set.Icc (0:ℝ) 1`, the preference `closerPref` is defined *directly by its `le` relation*:
`x ≽ y` iff `x` is at least as close to the bliss point `1/2` as `y`, i.e. `|x - 1/2| ≤ |y - 1/2|`.
No utility enters the construction. Hand-computed ranking on four concrete policies:

* `pHalf = 1/2` (distance `0`), `pQuarter = 1/4` (distance `1/4`), `pZero = 0` (distance `1/2`),
  `pOne = 1` (distance `1/2`).
* Strict chain `pHalf ≻ pQuarter ≻ pZero` and the gap `pHalf ≻ pZero`.
* Indifference `pZero ~ pOne`.

`produced_utility_recovers_ranking` invokes `exists_rawUtility` to *produce* a representing utility
`v` from the topology of `[0,1]` alone, then checks that `v` reflects exactly this ordering:
`v pZero < v pQuarter < v pHalf`, `v pZero < v pHalf`, and `v pZero = v pOne`. A construction
returning a junk or constant utility fails every conjunct.

## Continuity round-trip (`uLin = id` on `ℝ`)

From the concrete continuous utility `uLin x = x` ("more is better"), `continuousPref_…` induces a
preference whose contour sets are pinned to concrete intervals: Strict upper/lower contours are
`Ioi x` / `Iio x` (open), weak contours are `Ici x` / `Iic x` (closed). Membership of explicit
points is checked. The bundled `ContinuousPreferenceRel` mirrors and constructor value lemmas
(`ofContinuousUtility_val` / `ofContinuousPref_val`) are exercised on the same data.

## Bounds and scaffolding

`rawUtility_nonneg` / `rawUtility_le_two` / `rawUtility_summable` are checked at `pHalf` (guarding
against a negative / unbounded / divergent construction). The index-monotonicity, separating-index,
preimage-identity, openness, and gap-arithmetic scaffolding (`basisLowerContourIndices_*`,
`exists_separating_index`, `upper/lower_preimage_eq_*`, `isOpen_upper/lower_preimage`, `ge_gap` /
`le_gap`, `range_comp_eq`, `exists_countable_basis_indexed`) is exercised on concrete data — the
gap lemmas with `t` strictly past the gap so the derived inequality is non-trivial.

These witnesses catch:

* A circular representation theorem (the order-first witness has no pre-existing utility).
* A direction reversal in the represents bridge (a flipped `↔` would invert every `<` recovered).
* A junk-valued raw utility (the bounds and summability would fail).
* Broken contour/preimage identities (the explicit interval pins would fail).
-/

noncomputable section

namespace EconlibTest.Preferences.Representation

open Econlib.Preferences

/-! ## The order-first witness: "closer to 1/2 is better" on `[0,1]` -/

/-- The state space: The closed unit interval, a nonempty second-countable space. -/
private abbrev X : Type := Set.Icc (0 : ℝ) 1

/-- The distance-to-bliss map, with bliss point `1/2`. -/
private abbrev dist12 (x : X) : ℝ := |(x : ℝ) - 1 / 2|

private theorem dist12_continuous : Continuous dist12 :=
  (continuous_subtype_val.sub continuous_const).abs

/-- The "closer to `1/2` is better" preference, defined ORDER-FIRST by its `le` relation: `x ≽ y`
exactly when `x` is at least as close to `1/2` as `y`. No utility function enters the construction
— Debreu's machinery must *produce* one. -/
private def closerPref : PreferenceRel X where
  le x y := dist12 x ≤ dist12 y
  le_refl _ := le_refl _
  le_trans _ _ _ hxy hyz := hxy.trans hyz
  le_total _ _ := le_total _ _

@[simp] private lemma closerPref_le_iff (x y : X) :
    (x ≽[closerPref] y) ↔ dist12 x ≤ dist12 y := Iff.rfl

/-- Continuity of the order-first preference, proved from the topology alone: The weak contour sets
are sub/superlevel sets of the continuous distance map. -/
private theorem closerPref_continuous : ContinuousPref closerPref := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · have : closerPref.upperContour x = {y | dist12 y ≤ dist12 x} := rfl
    rw [this]; exact isClosed_le dist12_continuous continuous_const
  · have : closerPref.lowerContour x = {y | dist12 x ≤ dist12 y} := rfl
    rw [this]; exact isClosed_le continuous_const dist12_continuous

/-- The bundled continuous preference, built by the order-first constructor `ofContinuousPref`. -/
private def R : ContinuousPreferenceRel X :=
  ContinuousPreferenceRel.ofContinuousPref closerPref closerPref_continuous

private lemma R_val : R.val = closerPref :=
  ContinuousPreferenceRel.ofContinuousPref_val closerPref closerPref_continuous

/-- **`continuousPref_iff_exists`.** The `Prop`-valued continuity of `closerPref` is equivalent to
its being the underlying relation of some bundled `ContinuousPreferenceRel`. -/
theorem continuousPref_iff_exists_witness :
    ContinuousPref closerPref ↔ ∃ C : ContinuousPreferenceRel X, C.val = closerPref :=
  continuousPref_iff_exists closerPref

/-- **Forward direction (`.mp`), applied to `closerPref_continuous`.** Feeding the concretely-proved
continuity through the iff *produces* a bundled `ContinuousPreferenceRel` whose `val` is
`closerPref` — not merely a restatement of the equivalence. -/
theorem continuousPref_iff_exists_forward :
    ∃ C : ContinuousPreferenceRel X, C.val = closerPref :=
  (continuousPref_iff_exists closerPref).mp closerPref_continuous

/-- **Converse direction (`.mpr`), applied to the bundle `R`.** From the bundled `R` (with
`R.val = closerPref`) the iff recovers the `Prop`-valued continuity of `closerPref`. -/
theorem continuousPref_iff_exists_converse : ContinuousPref closerPref :=
  (continuousPref_iff_exists closerPref).mpr ⟨R, R_val⟩

/-! ### Concrete alternatives and their hand-computed ranking

Four policies on `[0,1]`, with distances to the bliss point `1/2`:

* `pHalf = 1/2` — distance `0` (the bliss point, strictly best).
* `pQuarter = 1/4` — distance `1/4`.
* `pZero = 0` — distance `1/2`.
* `pOne = 1` — distance `1/2`.

Hand-computed order (closer is better):

* `pHalf ≻ pQuarter ≻ pZero` — a genuine strict three-step chain (`0 < 1/4 < 1/2`).
* `pHalf ≻ pZero` — strict.
* `pZero ~ pOne` — indifferent (both at distance `1/2`). -/

private def pHalf : X := ⟨1 / 2, by norm_num⟩
private def pQuarter : X := ⟨1 / 4, by norm_num⟩
private def pZero : X := ⟨0, by norm_num⟩
private def pOne : X := ⟨1, by norm_num⟩

private lemma dist12_pHalf : dist12 pHalf = 0 := by
  rw [dist12, show (pHalf : ℝ) = 1 / 2 from rfl]; norm_num
private lemma dist12_pQuarter : dist12 pQuarter = 1 / 4 := by
  rw [dist12, show (pQuarter : ℝ) = 1 / 4 from rfl, abs_of_nonpos] <;> norm_num
private lemma dist12_pZero : dist12 pZero = 1 / 2 := by
  rw [dist12, show (pZero : ℝ) = 0 from rfl, abs_of_nonpos] <;> norm_num
private lemma dist12_pOne : dist12 pOne = 1 / 2 := by
  rw [dist12, show (pOne : ℝ) = 1 from rfl, abs_of_nonneg] <;> norm_num

/-- Strict preference under `closerPref` reads as a strict distance comparison: Closer is strictly
better. The order-first analog of `preferenceOfUtilityIn_lt_iff`. -/
private lemma closerPref_lt_iff (x y : X) : R.val.lt x y ↔ dist12 x < dist12 y := by
  rw [R_val, PreferenceRel.lt]
  simp only [closerPref_le_iff, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

/-- Indifference under `closerPref` is equality of distances. -/
private lemma closerPref_indiff_iff (x y : X) : R.val.indiff x y ↔ dist12 x = dist12 y := by
  rw [R_val, PreferenceRel.indiff]
  simp only [closerPref_le_iff]
  exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩

/-- `pHalf ≻ pQuarter`: The bliss point is strictly preferred to `1/4` (`0 < 1/4`). -/
private theorem lt_half_quarter : R.val.lt pHalf pQuarter := by
  rw [closerPref_lt_iff, dist12_pHalf, dist12_pQuarter]; norm_num

/-- `pQuarter ≻ pZero`: `1/4` is strictly preferred to `0` (`1/4 < 1/2`). -/
private theorem lt_quarter_zero : R.val.lt pQuarter pZero := by
  rw [closerPref_lt_iff, dist12_pQuarter, dist12_pZero]; norm_num

/-- `pHalf ≻ pZero`: The bliss point is strictly preferred to `0` (`0 < 1/2`). -/
private theorem lt_half_zero : R.val.lt pHalf pZero := by
  rw [closerPref_lt_iff, dist12_pHalf, dist12_pZero]; norm_num

/-- `pZero ~ pOne`: The endpoints are indifferent — both lie at distance `1/2` from `1/2`. -/
private theorem indiff_zero_one : R.val.indiff pZero pOne := by
  rw [closerPref_indiff_iff, dist12_pZero, dist12_pOne]

/-! ### The payload: A PRODUCED utility recovers the order-first ranking

This is the heart of the non-vacuity test. `exists_rawUtility` is fed nothing but the
order-first `closerPref` (bundled in `R`); it *produces* a representing utility `v` from the
topology of `[0,1]` via the Debreu separable-order construction. We then check that this produced
`v` reflects exactly the ranking we computed by hand — strict where we said strict, equal where we
said indifferent. A construction that returned a junk or constant utility would fail every one of
these. -/

/-- From a real representation, strict preference forces a strict utility gap. -/
private lemma lt_of_represents {v : X → ℝ} (hv : RepresentsRealPreference R.val v)
    {x y : X} (h : R.val.lt x y) : v y < v x :=
  lt_of_le_of_ne ((hv x y).mp h.1) (fun he => h.2 ((hv y x).mpr he.ge))

/-- From a real representation, indifference forces equal utilities. -/
private lemma eq_of_represents {v : X → ℝ} (hv : RepresentsRealPreference R.val v)
    {x y : X} (h : R.val.indiff x y) : v x = v y :=
  le_antisymm ((hv y x).mp h.2) ((hv x y).mp h.1)

/-- **The produced utility recovers the order-first ranking.** Debreu's `exists_rawUtility`,
applied to the order-first `R`, yields a utility `v` for which the hand-computed strict chain
`pHalf ≻ pQuarter ≻ pZero` shows up as a strict chain of utility values
`v pZero < v pQuarter < v pHalf`, the strict gap `pHalf ≻ pZero` as `v pZero < v pHalf`, and the
indifference `pZero ~ pOne` as the equality `v pZero = v pOne`. Nothing supplied the utility; the
construction had to build it from the order and topology, and it lands on the right ordering. -/
theorem produced_utility_recovers_ranking :
    ∃ v : X → ℝ,
      RepresentsRealPreference R.val v ∧
      v pQuarter < v pHalf ∧
      v pZero < v pQuarter ∧
      v pZero < v pHalf ∧
      v pZero = v pOne := by
  obtain ⟨v, hv⟩ := R.exists_rawUtility
  exact ⟨v, hv,
    lt_of_represents hv lt_half_quarter,
    lt_of_represents hv lt_quarter_zero,
    lt_of_represents hv lt_half_zero,
    eq_of_represents hv indiff_zero_one⟩

/-- **The *final* Debreu theorem recovers the ranking — with continuity.** Where
`produced_utility_recovers_ranking` stops at the raw stage (`exists_rawUtility`), this consumes the
headline `ContinuousPreferenceRel.exists_continuous_utility_representation`: it produces a utility
`v` that is both a representation *and* `Continuous`, and the hand-computed strict chain
`pHalf ≻ pQuarter ≻ pZero`, the gap `pHalf ≻ pZero`, and the indifference `pZero ~ pOne` all show up
in `v`. This guards the gap-collapsing / composition / order-topology-continuity machinery the raw
witness skips. -/
theorem produced_continuous_utility_recovers_ranking :
    ∃ v : X → ℝ,
      RepresentsRealPreference R.val v ∧
      Continuous v ∧
      v pQuarter < v pHalf ∧
      v pZero < v pQuarter ∧
      v pZero < v pHalf ∧
      v pZero = v pOne := by
  obtain ⟨v, hv, hcont⟩ := R.exists_continuous_utility_representation
  exact ⟨v, hv, hcont,
    lt_of_represents hv lt_half_quarter,
    lt_of_represents hv lt_quarter_zero,
    lt_of_represents hv lt_half_zero,
    eq_of_represents hv indiff_zero_one⟩

/-! ## Continuity round-trip: From a concrete continuous utility back to its contour topology

Now we run the bridge in the *other* direction: Start from an explicit continuous numeric
utility `uLin x = x` (the "more is better" / monotone preference on `ℝ`), induce the preference via
`continuousPref_preferenceOfRealUtility`, and confirm its contour topology is exactly the order
topology of `ℝ`. For this utility the contour sets are concrete intervals:

* `strictUpperContour x = Ioi x` (the policies strictly above `x`),
* `strictLowerContour x = Iio x`,
* `upperContour x = Ici x` (closed),
* `lowerContour x = Iic x` (closed).

We pin each identity and check membership of an explicit point. -/

/-- The concrete continuous utility on `ℝ`: The identity, i.e. "more is better". -/
private abbrev uLin : ℝ → ℝ := id

/-- The induced "more is better" preference: `x ≽ y ↔ y ≤ x`. -/
private abbrev L : PreferenceRel ℝ := preferenceOfRealUtility uLin

/-- **`continuousPref_preferenceOfRealUtility`.** A continuous numeric utility induces a continuous
preference; here the input continuity is just `continuous_id`. -/
private theorem L_continuous : ContinuousPref L :=
  continuousPref_preferenceOfRealUtility (u := uLin) continuous_id

/-- For `uLin`, the strict upper contour of `x` is the open ray `Ioi x`. -/
private lemma strictUpperContour_L_eq (x : ℝ) : L.strictUpperContour x = Set.Ioi x := by
  ext y
  simp only [PreferenceRel.strictUpperContour, Set.mem_setOf_eq, Set.mem_Ioi,
    preferenceOfUtilityIn_lt_iff, uLin, id]

/-- For `uLin`, the strict lower contour of `x` is the open ray `Iio x`. -/
private lemma strictLowerContour_L_eq (x : ℝ) : L.strictLowerContour x = Set.Iio x := by
  ext y
  simp only [PreferenceRel.strictLowerContour, Set.mem_setOf_eq, Set.mem_Iio,
    preferenceOfUtilityIn_lt_iff, uLin, id]

/-- For `uLin`, the weak upper contour of `x` is the closed ray `Ici x`. -/
private lemma upperContour_L_eq (x : ℝ) : L.upperContour x = Set.Ici x := by
  ext y
  simp only [PreferenceRel.upperContour, Set.mem_setOf_eq, Set.mem_Ici,
    preferenceOfUtilityIn_le_iff, uLin, id]

/-- For `uLin`, the weak lower contour of `x` is the closed ray `Iic x`. -/
private lemma lowerContour_L_eq (x : ℝ) : L.lowerContour x = Set.Iic x := by
  ext y
  simp only [PreferenceRel.lowerContour, Set.mem_setOf_eq, Set.mem_Iic,
    preferenceOfUtilityIn_le_iff, uLin, id]

/-- **`ContinuousPref.isOpen_strictUpperContour`, concretely.** The strict upper contour of `0` is
the open ray `Ioi 0`, and is open; the explicit point `1` lies in it (`0 < 1`). -/
theorem isOpen_strictUpperContour_L : IsOpen (L.strictUpperContour 0) ∧
    (1 : ℝ) ∈ L.strictUpperContour 0 := by
  refine ⟨L_continuous.isOpen_strictUpperContour 0, ?_⟩
  rw [strictUpperContour_L_eq]; norm_num

/-- **`ContinuousPref.isOpen_strictLowerContour`, concretely.** The strict lower contour of `0` is
the open ray `Iio 0`, and is open; the explicit point `-1` lies in it (`-1 < 0`). -/
theorem isOpen_strictLowerContour_L : IsOpen (L.strictLowerContour 0) ∧
    (-1 : ℝ) ∈ L.strictLowerContour 0 := by
  refine ⟨L_continuous.isOpen_strictLowerContour 0, ?_⟩
  rw [strictLowerContour_L_eq]; norm_num

/-- **`ContinuousPref.closed_upper`, concretely.** The weak upper contour of `0` is the closed ray
`Ici 0`, and is closed; the explicit point `0` lies in it. -/
theorem closed_upper_L : IsClosed (L.upperContour 0) ∧ (0 : ℝ) ∈ L.upperContour 0 := by
  refine ⟨L_continuous.closed_upper 0, ?_⟩
  rw [upperContour_L_eq]; exact Set.self_mem_Ici

/-- **`ContinuousPref.closed_lower`, concretely.** The weak lower contour of `0` is the closed ray
`Iic 0`, and is closed; the explicit point `-2` lies in it. -/
theorem closed_lower_L : IsClosed (L.lowerContour 0) ∧ (-2 : ℝ) ∈ L.lowerContour 0 := by
  refine ⟨L_continuous.closed_lower 0, ?_⟩
  rw [lowerContour_L_eq]; norm_num

/-! ### The bundled `ContinuousPreferenceRel` mirrors and constructor value lemmas

`ofContinuousUtility` packages a continuous utility into the data-carrying bundle; its `val` is
the induced preference by `ofContinuousUtility_val`. The bundled `isOpen_strictUpperContour` /
`isOpen_strictLowerContour` mirror the `Prop`-valued lemmas above. We also exercise
`ofContinuousPref` / `ofContinuousPref_val`, the order-first constructor used to build `R`. -/

/-- The bundled continuous preference built from the continuous utility `uLin`. -/
private def Lbundle : ContinuousPreferenceRel ℝ :=
  ContinuousPreferenceRel.ofContinuousUtility uLin continuous_id

/-- **`ofContinuousUtility_val`.** The bundled relation is the utility-induced preference. -/
theorem ofContinuousUtility_val_witness : Lbundle.val = preferenceOfRealUtility uLin :=
  ContinuousPreferenceRel.ofContinuousUtility_val uLin continuous_id

/-- **Bundled `ContinuousPreferenceRel.isOpen_strictUpperContour`.** The strict upper contour of
`0` under the bundled preference is the open ray `Ioi 0` (via `ofContinuousUtility_val`), and is
open. -/
theorem bundled_isOpen_strictUpperContour : IsOpen (Lbundle.val.strictUpperContour 0) ∧
    Lbundle.val.strictUpperContour 0 = Set.Ioi 0 := by
  refine ⟨Lbundle.isOpen_strictUpperContour 0, ?_⟩
  rw [ofContinuousUtility_val_witness]; exact strictUpperContour_L_eq 0

/-- **Bundled `ContinuousPreferenceRel.isOpen_strictLowerContour`.** The strict lower contour of
`0` under the bundled preference is the open ray `Iio 0`, and is open. -/
theorem bundled_isOpen_strictLowerContour : IsOpen (Lbundle.val.strictLowerContour 0) ∧
    Lbundle.val.strictLowerContour 0 = Set.Iio 0 := by
  refine ⟨Lbundle.isOpen_strictLowerContour 0, ?_⟩
  rw [ofContinuousUtility_val_witness]; exact strictLowerContour_L_eq 0

/-- **`ofContinuousPref_val`.** The order-first bundle `R` carries `closerPref` as its `val`
(already used in `R_val`); restated here directly through the constructor lemma. -/
theorem ofContinuousPref_val_witness :
    (ContinuousPreferenceRel.ofContinuousPref closerPref closerPref_continuous).val = closerPref :=
  ContinuousPreferenceRel.ofContinuousPref_val closerPref closerPref_continuous

/-! ## Bounds / normalization sanity and the raw-utility scaffolding

The Debreu raw utility `v(x) = ∑_{n ∈ basisLowerContourIndices B x} 2⁻ⁿ` is normalized into
`[0,2]`. We obtain a concrete basis `B` from second-countability (exercising
`exists_countable_basis_indexed` on `[0,1]`) and check the bounds and summability at the concrete
point `pHalf`, guarding against a junk-valued construction. We then exercise the index-monotonicity
/ separating-index scaffolding on our hand-computed strict and indifferent pairs. -/

/-- A concrete basis on `[0,1]` from second-countability, and its defining property. Obtaining it
exercises `exists_countable_basis_indexed` non-vacuously on the concrete space `X`. -/
private lemma exists_basis_X :
    ∃ B : ℕ → Set X, (∀ n, IsOpen (B n)) ∧
      ∀ (x : X) (U : Set X), IsOpen U → x ∈ U → ∃ n, x ∈ B n ∧ B n ⊆ U :=
  ContinuousPreferenceRel.exists_countable_basis_indexed (X := X)

/-- **Bounds on the produced raw utility.** For any basis `B` and at the concrete point `pHalf`,
the raw utility is nonnegative and bounded by `2` — the normalization range `[0,2]`. These guard
against a junk-valued (e.g. negative or unbounded) construction. -/
theorem rawUtility_bounds_at_pHalf (B : ℕ → Set X) :
    0 ≤ R.rawUtility B pHalf ∧ R.rawUtility B pHalf ≤ 2 :=
  ⟨R.rawUtility_nonneg B pHalf, R.rawUtility_le_two B pHalf⟩

/-- **Bounds *plus* a strict separating gap on a concrete basis.** With the *concrete* basis from
`exists_basis_X` (not an arbitrary `B`), the raw utility at `pHalf` and `pZero` both lie in `[0,2]`
*and* are strictly separated: `rawUtility B pZero < rawUtility B pHalf`. The strict gap rules out
the trivial junk utilities (constant zero, or any constant) that the range bounds alone admit — a
genuine non-vacuity guard for the construction, not merely a "no negative / no overflow" check. -/
theorem rawUtility_bounds_and_gap :
    ∃ B : ℕ → Set X,
      (0 ≤ R.rawUtility B pZero ∧ R.rawUtility B pZero ≤ 2) ∧
      (0 ≤ R.rawUtility B pHalf ∧ R.rawUtility B pHalf ≤ 2) ∧
      R.rawUtility B pZero < R.rawUtility B pHalf := by
  obtain ⟨B, _, hB_basis⟩ := exists_basis_X
  exact ⟨B,
    ⟨R.rawUtility_nonneg B pZero, R.rawUtility_le_two B pZero⟩,
    ⟨R.rawUtility_nonneg B pHalf, R.rawUtility_le_two B pHalf⟩,
    R.rawUtility_lt_of_lt B hB_basis lt_half_zero⟩

open Classical in
/-- **`rawUtility_summable`.** The geometric summand sequence defining `rawUtility` at `pHalf` is
summable (dominated by `∑ 2⁻ⁿ = 2`), so the `tsum` is well-defined rather than junk. -/
theorem rawUtility_summable_at_pHalf (B : ℕ → Set X) :
    Summable (fun n => if n ∈ R.basisLowerContourIndices B pHalf then (2⁻¹ : ℝ) ^ n else 0) :=
  R.rawUtility_summable B pHalf

/-- **`basisLowerContourIndices_subset_of_lt`.** Since `pHalf ≻ pQuarter`, the lower-contour index
set of `pQuarter` is contained in that of `pHalf`: Strict preference enlarges the index set. -/
theorem basisLowerContourIndices_subset_witness (B : ℕ → Set X) :
    R.basisLowerContourIndices B pQuarter ⊆ R.basisLowerContourIndices B pHalf :=
  R.basisLowerContourIndices_subset_of_lt B lt_half_quarter

/-- **`basisLowerContourIndices_eq_of_indiff`.** Since `pZero ~ pOne`, their lower-contour index
sets coincide. -/
theorem basisLowerContourIndices_eq_witness (B : ℕ → Set X) :
    R.basisLowerContourIndices B pZero = R.basisLowerContourIndices B pOne :=
  R.basisLowerContourIndices_eq_of_indiff B indiff_zero_one

/-- **`rawUtility_eq_of_indiff`, concretely.** The indifferent pair `pZero ~ pOne` produces equal
raw utilities for any basis. -/
theorem rawUtility_eq_of_indiff_witness (B : ℕ → Set X) :
    R.rawUtility B pZero = R.rawUtility B pOne :=
  R.rawUtility_eq_of_indiff B indiff_zero_one

/-- **`exists_separating_index` and `rawUtility_lt_of_lt`.** With the concrete basis from
`exists_basis_X` and the strict pair `pHalf ≻ pQuarter`, there is a basis index separating the two
lower-contour index sets, and the raw utility is strictly larger at `pHalf`. -/
theorem exists_separating_index_witness :
    ∃ B : ℕ → Set X,
      (∃ m ∈ R.basisLowerContourIndices B pHalf, m ∉ R.basisLowerContourIndices B pQuarter) ∧
      R.rawUtility B pQuarter < R.rawUtility B pHalf := by
  obtain ⟨B, _, hB_basis⟩ := exists_basis_X
  exact ⟨B, R.exists_separating_index B hB_basis lt_half_quarter,
    R.rawUtility_lt_of_lt B hB_basis lt_half_quarter⟩

/-- **`rawUtility_represents`.** With the concrete basis from `exists_basis_X`, the raw utility
represents the order-first preference: It recovers the strict ranking `pQuarter < pHalf` in utility
values. (`exists_rawUtility` already assembles this internally; here we name the representation
explicitly and check it produces the expected strict gap.) -/
theorem rawUtility_represents_witness :
    ∃ B : ℕ → Set X, RepresentsRealPreference R.val (R.rawUtility B) ∧
      R.rawUtility B pQuarter < R.rawUtility B pHalf := by
  obtain ⟨B, _, hB_basis⟩ := exists_basis_X
  exact ⟨B, R.rawUtility_represents B hB_basis,
    R.rawUtility_lt_of_lt B hB_basis lt_half_quarter⟩

/-! ### Preimage identities, gap arithmetic, and openness of preimages

The preimage identities `upper_preimage_eq_strictUpperContour` /
`lower_preimage_eq_strictLowerContour` need a representing utility; we feed the concrete linear
utility `uLin` on `ℝ` (range `univ`, which trivially has all open gaps), via the bundle `Lbundle`.
The gap lemmas `ge_gap` / `le_gap` are pure real-analysis facts exercised on the concrete set
`{0, 1}` with the gap `Ioo 0 1`. -/

/-- `uLin` represents the bundled preference `Lbundle.val`. -/
private lemma Lbundle_represents : RepresentsRealPreference Lbundle.val uLin := by
  rw [ofContinuousUtility_val_witness]; exact preferenceOfUtilityIn_represents uLin

/-- The range of the linear utility is all of `ℝ`, which vacuously has all open gaps (no bounded
nonempty interval can be disjoint from `univ`). -/
private lemma hasAllOpenGaps_range_uLin : HasAllOpenGaps (Set.range uLin) := by
  rw [show Set.range uLin = Set.univ from Set.range_id]
  intro r₁ r₂ hlt hdisj _ _
  exact absurd hdisj (by
    rw [Set.inter_univ]; exact Set.nonempty_iff_ne_empty.mp (Set.nonempty_Icc.mpr hlt.le))

/-- **`upper_preimage_eq_strictUpperContour`, concretely.** For `uLin`, the superlevel preimage
`{x | uLin x > uLin 0}` is the strict upper contour of `0`, namely `Ioi 0`. -/
theorem upper_preimage_eq_witness :
    {x : ℝ | uLin x > uLin 0} = Lbundle.val.strictUpperContour 0 :=
  Lbundle.upper_preimage_eq_strictUpperContour uLin Lbundle_represents 0

/-- **`lower_preimage_eq_strictLowerContour`, concretely.** For `uLin`, the sublevel preimage
`{x | uLin x < uLin 0}` is the strict lower contour of `0`, namely `Iio 0`. -/
theorem lower_preimage_eq_witness :
    {x : ℝ | uLin x < uLin 0} = Lbundle.val.strictLowerContour 0 :=
  Lbundle.lower_preimage_eq_strictLowerContour uLin Lbundle_represents 0

/-- **`isOpen_upper_preimage`, concretely.** The superlevel preimage `{x | uLin x > 0}` is open,
and equals the ray `Ioi 0`. -/
theorem isOpen_upper_preimage_witness :
    IsOpen {x : ℝ | uLin x > 0} ∧ {x : ℝ | uLin x > 0} = Set.Ioi 0 := by
  refine ⟨Lbundle.isOpen_upper_preimage uLin Lbundle_represents hasAllOpenGaps_range_uLin 0, ?_⟩
  ext x; simp [uLin, Set.mem_Ioi]

/-- **`isOpen_lower_preimage`, concretely.** The sublevel preimage `{x | uLin x < 0}` is open, and
equals the ray `Iio 0`. -/
theorem isOpen_lower_preimage_witness :
    IsOpen {x : ℝ | uLin x < 0} ∧ {x : ℝ | uLin x < 0} = Set.Iio 0 := by
  refine ⟨Lbundle.isOpen_lower_preimage uLin Lbundle_represents hasAllOpenGaps_range_uLin 0, ?_⟩
  ext x; simp [uLin, Set.mem_Iio]

/-! ### Discrete two-level utility: the *gap branch* of `isOpen_…_preimage`

The `uLin` witnesses above have `range uLin = univ`, where `HasAllOpenGaps` is *vacuous* and the
threshold `0` lies *in* the range, so the genuine gap-case algebra (`ge_gap` / `le_gap` /
`sInf`/`sSup` boundary handling) is never exercised. Here we use a discrete two-level utility
`uTwo : Bool → ℝ`, `uTwo false = 0`, `uTwo true = 2`, whose range is `{0, 2}` — a *nontrivial* open
gap `(0, 2)` — and a threshold `1` that lies *strictly inside the gap* (not in the range). This is
exactly the case the gap branch was written for. -/

/-- The discrete two-level utility on `Bool`: value `2` at `true`, `0` at `false`. -/
private abbrev uTwo : Bool → ℝ := fun b => if b then 2 else 0

/-- The bundled continuous preference from `uTwo` (`Bool` is discrete, so `uTwo` is continuous). -/
private def LtwoBundle : ContinuousPreferenceRel Bool :=
  ContinuousPreferenceRel.ofContinuousUtility uTwo continuous_of_discreteTopology

private lemma LtwoBundle_represents : RepresentsRealPreference LtwoBundle.val uTwo := by
  change RepresentsRealPreference (ContinuousPreferenceRel.ofContinuousUtility uTwo _).val uTwo
  rw [ContinuousPreferenceRel.ofContinuousUtility_val]; exact preferenceOfUtilityIn_represents uTwo

/-- The range of `uTwo` is the two-point set `{0, 2}`. -/
private lemma uTwo_range : Set.range uTwo = {0, 2} := by
  ext y; simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨b, rfl⟩; cases b <;> simp [uTwo]
  · rintro (rfl | rfl)
    · exact ⟨false, by simp [uTwo]⟩
    · exact ⟨true, by simp [uTwo]⟩

private lemma gap02_empty : Set.Ioo (0 : ℝ) 2 ∩ ({0, 2} : Set ℝ) = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨h0, h2⟩ (rfl | rfl) <;> linarith

/-- **`HasAllOpenGaps` on a *nontrivial* gap.** `{0, 2}` has the single open gap `(0, 2)`: any
closed interval `[r₁, r₂]` disjoint from `{0, 2}` but bounded below and above by members forces
`0 < r₁` and `r₂ < 2` (the only member below is `0`, the only one above is `2`), so
`[r₁, r₂] ⊆ (0, 2)`. Unlike
`hasAllOpenGaps_range_uLin`, this is *not* vacuous. -/
private lemma uTwo_gaps : HasAllOpenGaps (Set.range uTwo) := by
  rw [uTwo_range]
  intro r₁ r₂ hlt _ ⟨x, hx_mem, hx_lt⟩ ⟨y, hy_mem, hy_lt⟩
  refine ⟨0, 2, ⟨by simp, by simp, by norm_num, gap02_empty⟩, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx_mem hy_mem
  have hr2 : r₂ < 2 := by
    rcases hy_mem with rfl | rfl
    · rcases hx_mem with rfl | rfl <;> linarith
    · exact hy_lt
  have hr1 : 0 < r₁ := by
    rcases hx_mem with rfl | rfl
    · exact hx_lt
    · linarith
  intro w hw; simp only [Set.mem_Icc] at hw
  exact ⟨by linarith [hw.1], by linarith [hw.2]⟩

/-- **`isOpen_upper_preimage`, *gap branch*.** The superlevel preimage `{x | uTwo x > 1}` at the
threshold `1` — which sits *strictly inside the gap* `(0, 2)`, not in the range — is open and equals
`{true}`. This exercises the `sInf`/`ge_gap` algebra a sign error would corrupt; the `uLin`
witness, with its in-range threshold, cannot. -/
theorem isOpen_upper_preimage_gap :
    IsOpen {x : Bool | uTwo x > 1} ∧ {x : Bool | uTwo x > 1} = {true} := by
  refine ⟨LtwoBundle.isOpen_upper_preimage uTwo LtwoBundle_represents uTwo_gaps 1, ?_⟩
  ext b; cases b <;> simp [uTwo]

/-- **`isOpen_lower_preimage`, *gap branch*.** The sublevel preimage `{x | uTwo x < 1}` at the
in-gap threshold `1` is open and equals `{false}`, exercising the `sSup`/`le_gap` algebra. -/
theorem isOpen_lower_preimage_gap :
    IsOpen {x : Bool | uTwo x < 1} ∧ {x : Bool | uTwo x < 1} = {false} := by
  refine ⟨LtwoBundle.isOpen_lower_preimage uTwo LtwoBundle_represents uTwo_gaps 1, ?_⟩
  ext b; cases b <;> simp [uTwo]

/-- The gap `Ioo 0 1` is empty in the three-point set `{0, 1, 5}` — no real strictly between `0`
and `1` lies in `{0, 1, 5}`. (The point `5` lies past the gap, making `ge_gap` / `le_gap`
non-trivial.) -/
private lemma gap_zero_one_empty : Set.Ioo (0 : ℝ) 1 ∩ ({0, 1, 5} : Set ℝ) = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨hz0, hz1⟩ (rfl | rfl | rfl) <;> linarith

/-- **`ge_of_mem_of_gap`, as the universally-quantified gap consequence.** With `T = {0, 1, 5}` and
the empty gap `Ioo 0 1`, *every* member of `T` strictly above the gap's left endpoint `0` is at or
beyond the right endpoint `1`: `∀ t ∈ T, 0 < t → 1 ≤ t`. Unlike the bare arithmetic `1 ≤ 5`, this
statement is *not* `norm_num`-dischargeable — it genuinely records the gap content (its only
nontrivial instance is `t = 5`, giving `1 ≤ 5`). -/
theorem ge_gap_witness : ∀ t ∈ ({0, 1, 5} : Set ℝ), (0 : ℝ) < t → (1 : ℝ) ≤ t :=
  fun _ ht hlt => ge_of_mem_of_gap ht gap_zero_one_empty hlt

/-- The gap `Ioo (-4) 0` is empty in `{-10, -4, 0, 1, 5}` — no real strictly between `-4` and `0`
lies in the set. (The point `-10` lies before the gap, making `le_of_mem_of_gap` non-trivial.) -/
private lemma gap_neg_four_zero_empty :
    Set.Ioo (-4 : ℝ) 0 ∩ ({-10, -4, 0, 1, 5} : Set ℝ) = ∅ := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_and]
  rintro ⟨hz0, hz1⟩ (rfl | rfl | rfl | rfl | rfl) <;> linarith

/-- **`le_of_mem_of_gap`, as the universally-quantified gap consequence.** With
`T = {-10, -4, 0, 1, 5}` and the empty gap `Ioo (-4) 0`, *every* member of `T` strictly below the
gap's right endpoint `0` is at or below the left endpoint `-4`: `∀ t ∈ T, t < 0 → t ≤ -4`. Not
`norm_num`-dischargeable; its only nontrivial instance is `t = -10`, giving `-10 ≤ -4`. -/
theorem le_gap_witness : ∀ t ∈ ({-10, -4, 0, 1, 5} : Set ℝ), t < (0 : ℝ) → t ≤ -4 :=
  fun _ ht hlt => le_of_mem_of_gap ht gap_neg_four_zero_empty hlt

/-- **`range_comp_rangeFactorization`, on a *concrete* projection.** Specializing it at `uLin` to
the explicit `g = fun s => (s : ℝ) + 1` (the "shift the value by one" projection out of
`range uLin`), the range of the lifted composite equals the range of `g`. Instantiating `g`
(rather than leaving it arbitrary) gives the identity checkable content — see `range_comp_eq_mem`
below. -/
theorem range_comp_eq_witness :
    Set.range ((fun s => (s : ℝ) + 1) ∘
        fun x => (⟨uLin x, Set.mem_range_self x⟩ : Set.range uLin)) =
      Set.range (fun s : Set.range uLin => (s : ℝ) + 1) :=
  Set.range_comp_rangeFactorization uLin (fun s => (s : ℝ) + 1)

/-- Concrete content of the range identity: the value `1` (the shift of `uLin 0 = 0`) lies in the
range of the lifted composite. -/
theorem range_comp_eq_mem :
    (1 : ℝ) ∈ Set.range ((fun s => (s : ℝ) + 1) ∘
        fun x => (⟨uLin x, Set.mem_range_self x⟩ : Set.range uLin)) := by
  rw [range_comp_eq_witness]
  exact ⟨⟨uLin 0, Set.mem_range_self 0⟩, by simp [uLin]⟩

end EconlibTest.Preferences.Representation

end
