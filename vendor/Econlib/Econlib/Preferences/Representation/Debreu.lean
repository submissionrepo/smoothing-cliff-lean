/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Data.Set.Range
public import Econlib.Math.Order.GapFilling
public import Econlib.Preferences.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Debreu's Continuous Utility Representation Theorem

This file proves Debreu's theorem: Every continuous preference relation on a second-countable
topological space admits a continuous real-valued utility representation.

This is intentionally a real-valued representation theorem. Continuity is a topological property of
the utility scale, and `ℝ` provides the ordered topological scale for the representation. For
purely ordinal finite representations, see `Preferences.Finite`; for the outcome-generic preference
relation itself, see `Preferences.Basic`.

## Main definitions

* `ContinuousPreferenceRel` — a rational preference bundled with continuity (closed contour sets).
* `ContinuousPreferenceRel.basisLowerContourIndices` — the set of basis indices whose open set lies
  entirely in the strict lower contour of a point.
* `ContinuousPreferenceRel.rawUtility` — the utility
  `v(x) = ∑_{n ∈ basisLowerContourIndices B x} 2⁻ⁿ`.

## Main statements

* `ContinuousPreferenceRel.rawUtility_represents` — the raw utility represents the preference.
* `ContinuousPreferenceRel.exists_continuous_utility_representation` — Debreu's theorem: Existence
  of a continuous utility representation.

## References

* Debreu, Gerard. 1954. “Representation of a Preference Ordering by a Numerical Function.” In
  *Decision Processes*, edited by R. M. Thrall, C. H. Coombs, and R. L. Davis. Wiley.

## Tags

preference relation, utility, continuous representation, debreu, second-countable
-/

@[expose] public section

open Set
open scoped BigOperators

namespace Econlib.Preferences

/-- A continuous rational preference relation.

Continuity is stated by closed weak upper and lower contour sets. The bundled
`val : PreferenceRel X` remains the ordinal object; the closed-contour fields add the topological
assumptions needed for Debreu's real-valued representation theorem. -/
structure ContinuousPreferenceRel (X : Type) [TopologicalSpace X] [Nonempty X] where
  /-- The underlying rational preference relation. -/
  val : PreferenceRel X
  /-- Weak upper contour sets are closed. -/
  closed_upper : ∀ x, IsClosed (val.upperContour x)
  /-- Weak lower contour sets are closed. -/
  closed_lower : ∀ x, IsClosed (val.lowerContour x)

/-- **Continuity of a preference relation** (`Prop`-valued): Weak upper and lower contour sets are
closed. This is the proof-irrelevant analog of the data-carrying `ContinuousPreferenceRel`,
suitable as a hypothesis in `Prop` regularity bundles where carrying `val : PreferenceRel X` and a
coherence equation would be a tax. -/
structure ContinuousPref {X : Type*} [TopologicalSpace X] (R : PreferenceRel X) : Prop where
  /-- Weak upper contour sets are closed. -/
  closed_upper : ∀ x, IsClosed (R.upperContour x)
  /-- Weak lower contour sets are closed. -/
  closed_lower : ∀ x, IsClosed (R.lowerContour x)

/-- Bridge: `ContinuousPref R` holds iff `R` is the underlying relation of some
`ContinuousPreferenceRel`. Lets consumers move between the proof-irrelevant predicate and the
bundled form Debreu's theorem consumes. -/
lemma continuousPref_iff_exists {X : Type} [TopologicalSpace X] [Nonempty X]
    (R : PreferenceRel X) :
    ContinuousPref R ↔ ∃ C : ContinuousPreferenceRel X, C.val = R := by
  constructor
  · rintro ⟨hu, hl⟩; exact ⟨⟨R, hu, hl⟩, rfl⟩
  · rintro ⟨C, rfl⟩; exact ⟨C.closed_upper, C.closed_lower⟩

namespace ContinuousPref

variable {X : Type*} [TopologicalSpace X] {R : PreferenceRel X}

/-- Strict upper contour sets are open (complement of the closed weak lower contour). The
`Prop`-valued analog of `ContinuousPreferenceRel.isOpen_strictUpperContour`. -/
lemma isOpen_strictUpperContour (h : ContinuousPref R) (x : X) :
    IsOpen (R.strictUpperContour x) := by
  rw [R.strictUpperContour_eq_compl_lowerContour]
  exact (h.closed_lower x).isOpen_compl

/-- Strict lower contour sets are open (complement of the closed weak upper contour). -/
lemma isOpen_strictLowerContour (h : ContinuousPref R) (x : X) :
    IsOpen (R.strictLowerContour x) := by
  rw [R.strictLowerContour_eq_compl_upperContour]
  exact (h.closed_upper x).isOpen_compl

end ContinuousPref

/-- A continuous real utility induces a continuous preference (`Prop`-valued). The direct builder
for `RegularEconomy.contPref` in utility-based constructors (linear, Cobb–Douglas, …); unlike
`ContinuousPreferenceRel.ofContinuousUtility` it needs no `[Nonempty X]`. -/
lemma continuousPref_preferenceOfRealUtility {X : Type*} [TopologicalSpace X] {u : X → ℝ}
    (hu : Continuous u) : ContinuousPref (preferenceOfRealUtility u) :=
  ⟨fun x => by
      simpa [PreferenceRel.upperContour, preferenceOfRealUtility, preferenceOfUtilityIn]
        using isClosed_le continuous_const hu,
   fun x => by
      simpa [PreferenceRel.lowerContour, preferenceOfRealUtility, preferenceOfUtilityIn]
        using isClosed_le hu continuous_const⟩

namespace ContinuousPreferenceRel

variable {X : Type} [TopologicalSpace X] [Nonempty X] (R : ContinuousPreferenceRel X)

/-- Coerce a `ContinuousPreferenceRel` to its underlying `PreferenceRel`. -/
instance : Coe (ContinuousPreferenceRel X) (PreferenceRel X) := ⟨fun R => R.val⟩

/-- **Continuity bridge from a utility function.** A continuous real utility `u` induces a
continuous preference relation: The weak contour sets of `preferenceOfRealUtility u` are the closed
sublevel/superlevel sets `{y | u x ≤ u y}` and `{y | u y ≤ u x}`. This is the constructor that
builds `RegularEconomy.contPref` for utility-based consumers (linear, Cobb–Douglas, …). -/
noncomputable def ofContinuousUtility {X : Type} [TopologicalSpace X] [Nonempty X]
    (u : X → ℝ) (hu : Continuous u) : ContinuousPreferenceRel X where
  val := preferenceOfRealUtility u
  closed_upper x := by
    simpa [PreferenceRel.upperContour, preferenceOfRealUtility, preferenceOfUtilityIn]
      using isClosed_le continuous_const hu
  closed_lower x := by
    simpa [PreferenceRel.lowerContour, preferenceOfRealUtility, preferenceOfUtilityIn]
      using isClosed_le hu continuous_const

/-- The underlying preference relation of `ofContinuousUtility u hu` is
`preferenceOfRealUtility u`, definitionally. -/
@[simp] lemma ofContinuousUtility_val {X : Type} [TopologicalSpace X] [Nonempty X]
    (u : X → ℝ) (hu : Continuous u) :
    (ofContinuousUtility u hu).val = preferenceOfRealUtility u := rfl

/-- **Continuity bridge from closed contour sets.** Bundle a preference relation that is
topologically continuous (`ContinuousPref`: Closed weak upper and lower contour sets) into a
`ContinuousPreferenceRel`, with no generating utility in sight. This is the constructor for
preferences built order-theoretically; Debreu's theorem then produces the continuous utility. For
preferences already induced by a continuous utility, use `ofContinuousUtility` instead. -/
def ofContinuousPref {X : Type} [TopologicalSpace X] [Nonempty X]
    (R : PreferenceRel X) (h : ContinuousPref R) : ContinuousPreferenceRel X :=
  ⟨R, h.closed_upper, h.closed_lower⟩

/-- The underlying preference relation of `ofContinuousPref R h` is `R`, definitionally. -/
@[simp] lemma ofContinuousPref_val {X : Type} [TopologicalSpace X] [Nonempty X]
    (R : PreferenceRel X) (h : ContinuousPref R) :
    (ofContinuousPref R h).val = R := rfl

/-! ### Openness of strict contour sets

Continuity of `≽` is stated as closedness of weak contour sets. By complementation, the strict
contour sets are open. This is the key topological input: It provides basis elements separating
strictly-ranked alternatives and makes preimages of open rays open when the threshold is in the
range of the utility function. -/

/-- Strict upper contour sets are open (complement of the closed weak lower contour). -/
lemma isOpen_strictUpperContour (x : X) : IsOpen (R.val.strictUpperContour x) := by
  rw [R.val.strictUpperContour_eq_compl_lowerContour]
  exact (R.closed_lower x).isOpen_compl

/-- Strict lower contour sets are open (complement of the closed weak upper contour). -/
lemma isOpen_strictLowerContour (x : X) : IsOpen (R.val.strictLowerContour x) := by
  rw [R.val.strictLowerContour_eq_compl_upperContour]
  exact (R.closed_upper x).isOpen_compl

/-! ### Raw utility construction

Given a countable basis `{Bₙ}` (from second-countability), `basisLowerContourIndices B x` is
the set of indices `n` such that `Bₙ` lies entirely in the strict lower contour of `x`, and
`v(x) = ∑_{n ∈ basisLowerContourIndices B x} 2⁻ⁿ`. The index set is monotone in the preference and
the geometric series is summable with values in `[0, 2]`, so strict preference yields a strictly
larger index set and hence a strictly larger sum. -/

/-- The basis indices whose open set is entirely in the strict lower contour of `x`. -/
def basisLowerContourIndices (B : ℕ → Set X) (x : X) : Set ℕ :=
  {n | B n ⊆ R.val.strictLowerContour x}

open Classical in
/-- Raw ordinal utility: `v(x) = ∑_{n ∈ basisLowerContourIndices B x} 2⁻ⁿ`. -/
noncomputable def rawUtility (B : ℕ → Set X) (x : X) : ℝ :=
  ∑' n, if n ∈ R.basisLowerContourIndices B x then (2⁻¹ : ℝ) ^ n else 0

/-- An ℕ-indexed topological basis from second-countability. -/
lemma exists_countable_basis_indexed [SecondCountableTopology X] :
    ∃ B : ℕ → Set X, (∀ n, IsOpen (B n)) ∧
      ∀ (x : X) (U : Set X), IsOpen U → x ∈ U → ∃ n, x ∈ B n ∧ B n ⊆ U := by
  obtain ⟨b, hb_count, _, hb_basis⟩ := TopologicalSpace.exists_countable_basis X
  have hb_nonempty : b.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨v, hv_mem, _, _⟩ := hb_basis.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨v, hv_mem⟩
  obtain ⟨f, hf_surj⟩ := hb_count.exists_surjective hb_nonempty
  refine ⟨fun n => (f n).val, fun n => hb_basis.isOpen (f n).property, ?_⟩
  intro x U hU hxU
  obtain ⟨v, hv_mem, hxv, hvU⟩ := hb_basis.exists_subset_of_mem_open hxU hU
  obtain ⟨n, hn⟩ := hf_surj ⟨v, hv_mem⟩
  exact ⟨n, by simp [show (f n).val = v from congrArg Subtype.val hn, hxv],
    by simp [show (f n).val = v from congrArg Subtype.val hn, hvU]⟩

/-! ### Summability and boundedness

The terms of `rawUtility` are dominated by the geometric series `∑ 2⁻ⁿ = 2`, so the sum
converges and takes values in `[0, 2]`. -/

open Classical in
/-- The terms of `rawUtility` are summable, dominated by the geometric series `∑ (1/2)^n`. -/
lemma rawUtility_summable (B : ℕ → Set X) (x : X) :
    Summable (fun n => if n ∈ R.basisLowerContourIndices B x then (2⁻¹ : ℝ) ^ n else 0) := by
  apply Summable.of_nonneg_of_le
  · intro n; split_ifs <;> positivity
  · intro n; split_ifs with h
    · exact le_refl _
    · positivity
  · exact summable_geometric_of_lt_one (by positivity) (by norm_num)

/-- The raw utility is nonneg, as a tsum of nonneg terms. -/
lemma rawUtility_nonneg (B : ℕ → Set X) (x : X) : 0 ≤ R.rawUtility B x := by
  apply tsum_nonneg
  intro n; split_ifs <;> positivity

open Classical in
/-- The raw utility is at most `2`, the sum of the full geometric series `∑ (1/2)^n`. -/
lemma rawUtility_le_two (B : ℕ → Set X) (x : X) : R.rawUtility B x ≤ 2 := by
  calc ∑' n, (if n ∈ R.basisLowerContourIndices B x then (2⁻¹ : ℝ) ^ n else 0)
      ≤ ∑' n, (2⁻¹ : ℝ) ^ n := by
        apply Summable.tsum_le_tsum
        · intro n; split_ifs with h
          · exact le_refl _
          · positivity
        · exact R.rawUtility_summable B x
        · exact summable_geometric_of_lt_one (by positivity) (by norm_num)
    _ = 2 := tsum_geometric_inv_two

/-! ### Basis lower-contour index monotonicity

`basisLowerContourIndices` respects the preference: Strict preference gives strict inclusion,
and indifference gives equality. -/

/-- Strict preference `x ≻ y` implies
`basisLowerContourIndices B y ⊆ basisLowerContourIndices B x`. -/
lemma basisLowerContourIndices_subset_of_lt (B : ℕ → Set X) {x y : X} (h : x ≻[R.val] y) :
    R.basisLowerContourIndices B y ⊆ R.basisLowerContourIndices B x := by
  intro n hn
  exact Set.Subset.trans hn (R.val.strictLowerContour_subset_of_lt h)

/-- Indifference `x ~ y` implies `basisLowerContourIndices B x = basisLowerContourIndices B y`. -/
lemma basisLowerContourIndices_eq_of_indiff (B : ℕ → Set X) {x y : X} (h : x ~[R.val] y) :
    R.basisLowerContourIndices B x = R.basisLowerContourIndices B y := by
  ext n
  simp only [basisLowerContourIndices, Set.mem_setOf_eq, R.val.strictLowerContour_eq_of_indiff h]

/-! ### Representation proof

`rawUtility` represents the preference: Indifference gives equal index sets hence equal sums,
and strict preference gives a strictly larger index set hence a strictly larger sum. -/

/-- Indifferent alternatives have equal raw utility. -/
lemma rawUtility_eq_of_indiff (B : ℕ → Set X) {x y : X} (h : x ~[R.val] y) :
    R.rawUtility B x = R.rawUtility B y := by
  unfold rawUtility
  congr 1; ext n; rw [R.basisLowerContourIndices_eq_of_indiff B h]

/-- If `x ≻ y`, there is a basis element containing `y` that witnesses a strict inclusion of
lower-contour index sets. -/
lemma exists_separating_index
    (B : ℕ → Set X) (hB_basis : ∀ (x : X) (U : Set X), IsOpen U → x ∈ U → ∃ n, x ∈ B n ∧ B n ⊆ U)
    {x y : X} (h : x ≻[R.val] y) :
    ∃ m, m ∈ R.basisLowerContourIndices B x ∧ m ∉ R.basisLowerContourIndices B y := by
  have hy_in : y ∈ R.val.strictLowerContour x := h
  have hopen : IsOpen (R.val.strictLowerContour x) := R.isOpen_strictLowerContour x
  obtain ⟨m, hym, hmSL⟩ := hB_basis y _ hopen hy_in
  refine ⟨m, hmSL, ?_⟩
  intro hm
  have : y ∈ R.val.strictLowerContour y := hm hym
  exact (R.val.lt_irrefl y) this

/-- Strict preference implies strictly higher utility: `x ≻ y → v(x) > v(y)`. -/
lemma rawUtility_lt_of_lt
    (B : ℕ → Set X) (hB_basis : ∀ (x : X) (U : Set X), IsOpen U → x ∈ U → ∃ n, x ∈ B n ∧ B n ⊆ U)
    {x y : X} (h : R.val.lt x y) :
    R.rawUtility B y < R.rawUtility B x := by
  have hy_in : y ∈ R.val.strictLowerContour x := h
  obtain ⟨m, hym, hmSL⟩ := hB_basis y _ (R.isOpen_strictLowerContour x) hy_in
  have hm_in : m ∈ R.basisLowerContourIndices B x := hmSL
  have hm_notin : m ∉ R.basisLowerContourIndices B y := fun hm => (R.val.lt_irrefl y) (hm hym)
  apply Summable.tsum_lt_tsum_of_nonneg
  · intro n; split_ifs <;> positivity
  · intro n
    split_ifs with h1 h2 h2
    · exact le_refl _
    · exact absurd (R.basisLowerContourIndices_subset_of_lt B h h1) h2
    · positivity
    · exact le_refl _
  · rw [if_neg hm_notin, if_pos hm_in]; positivity
  · exact R.rawUtility_summable B x

/-- The raw utility function represents the continuous preference, given a topological basis `B`:
`x ≽ y ↔ v(x) ≥ v(y)`. -/
theorem rawUtility_represents
    (B : ℕ → Set X)
    (hB_basis : ∀ (x : X) (U : Set X), IsOpen U → x ∈ U → ∃ n, x ∈ B n ∧ B n ⊆ U) :
    RepresentsRealPreference R.val (R.rawUtility B) := by
  intro x y
  constructor
  · intro hxy
    by_cases hyx : y ≽[R.val] x
    · exact le_of_eq (R.rawUtility_eq_of_indiff B ⟨hxy, hyx⟩).symm
    · exact le_of_lt (R.rawUtility_lt_of_lt B hB_basis ⟨hxy, hyx⟩)
  · intro huv
    by_contra h
    have hyx : y ≻[R.val] x := ⟨(R.val.le_total x y).elim (absurd · h) id, h⟩
    have := R.rawUtility_lt_of_lt B hB_basis hyx
    linarith

/-- Existence of a (not necessarily continuous) utility representation on a second-countable
space. -/
lemma exists_rawUtility [SecondCountableTopology X] :
    (∃ v : X → ℝ, RepresentsRealPreference R.val v) := by
  obtain ⟨B, hB_open, hB_basis⟩ := exists_countable_basis_indexed (X := X)
  exact ⟨R.rawUtility B, R.rawUtility_represents B hB_basis⟩

/-! ### Preimage openness

Continuity of `u` follows from openness of the preimages of open rays `{x | u(x) > r}` and
`{x | u(x) < r}` for every `r ∈ ℝ`. When `r` is in the range of `u`, these preimages coincide with
the strict contour sets, which are open by continuity of `≽`. When `r` is not in the range, the
all-open-gaps property of the range provides a gap `(a, b)` containing `r`, and the preimage equals
the one at the gap endpoint, a contour set. -/

/-- If `u` represents `≽`, then `{x | u x > u y}` equals the strict upper contour of `y`. -/
lemma upper_preimage_eq_strictUpperContour
    (u : X → ℝ) (hu_rep : RepresentsRealPreference R.val u) (y : X) :
    {x | u x > u y} = R.val.strictUpperContour y := by
  ext x; simp only [Set.mem_setOf_eq, PreferenceRel.strictUpperContour, PreferenceRel.lt]
  exact ⟨fun hux => ⟨(hu_rep x y).mpr hux.le, fun hle => not_lt.mpr ((hu_rep y x).mp hle) hux⟩,
         fun ⟨_, hnyx⟩ => by by_contra h; push Not at h; exact hnyx ((hu_rep y x).mpr h)⟩

/-- If `u` represents `≽`, then `{x | u x < u y}` equals the strict lower contour of `y`. -/
lemma lower_preimage_eq_strictLowerContour
    (u : X → ℝ) (hu_rep : RepresentsRealPreference R.val u) (y : X) :
    {x | u x < u y} = R.val.strictLowerContour y := by
  ext x; simp only [Set.mem_setOf_eq, PreferenceRel.strictLowerContour, PreferenceRel.lt]
  exact ⟨fun hux => ⟨(hu_rep y x).mpr hux.le, fun hle => not_lt.mpr ((hu_rep x y).mp hle) hux⟩,
         fun ⟨_, hnxy⟩ => by by_contra h; push Not at h; exact hnxy ((hu_rep x y).mpr h)⟩

/-- The preimage `{x | u(x) > r}` is open for any `r`, given that `u` represents `≽` and `range(u)`
has all open gaps. This is one half of the order-topology subbasis argument. -/
lemma isOpen_upper_preimage (u : X → ℝ) (hu : RepresentsRealPreference R.val u)
    (hgaps : HasAllOpenGaps (Set.range u)) (r : ℝ) : IsOpen {x | u x > r} := by
  by_cases hr : r ∈ Set.range u
  · obtain ⟨y, rfl⟩ := hr
    rw [R.upper_preimage_eq_strictUpperContour u hu y]; exact R.isOpen_strictUpperContour y
  · by_cases h_above : ∃ t ∈ Set.range u, r < t
    swap
    · push Not at h_above
      have : {x | u x > r} = ∅ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact h_above (u x) (Set.mem_range_self x)
      rw [this]; exact isOpen_empty
    by_cases h_below : ∃ t ∈ Set.range u, t < r
    swap
    · push Not at h_below
      have : {x | u x > r} = Set.univ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact lt_of_le_of_ne (h_below (u x) (Set.mem_range_self x))
          (fun h => hr (h ▸ Set.mem_range_self x))
      rw [this]; exact isOpen_univ
    -- r ∉ range u with values on both sides; use the infimum of the upper part
    have hne : {t ∈ Set.range u | r < t}.Nonempty := h_above
    have hbdd : BddBelow {t ∈ Set.range u | r < t} := ⟨r, fun t ⟨_, ht⟩ => ht.le⟩
    by_cases h_acc : sInf {t ∈ Set.range u | r < t} = r
    · -- r is an accumulation point from above: write the preimage as a union over range values
      suffices heq : {x | u x > r} =
          ⋃ (p : {t ∈ Set.range u | r < t}), {x | u x > (p : ℝ)} by
        rw [heq]; apply isOpen_iUnion; intro ⟨t, htT, _⟩
        obtain ⟨y, rfl⟩ := htT
        rw [R.upper_preimage_eq_strictUpperContour u hu y]; exact R.isOpen_strictUpperContour y
      ext x; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hxr
        have : ∃ t ∈ {t ∈ Set.range u | r < t}, t < u x := by
          by_contra h; push Not at h
          have : u x ≤ sInf {t ∈ Set.range u | r < t} := le_csInf hne h
          linarith [h_acc]
        obtain ⟨t, ht, htx⟩ := this; exact ⟨⟨t, ht⟩, htx⟩
      · intro ⟨⟨_, _, htr⟩, hxt⟩; exact lt_trans htr hxt
    · -- r is separated from the range above by an open gap; reduce to the gap endpoint
      have h_inf_gt : r < sInf {t ∈ Set.range u | r < t} :=
        lt_of_le_of_ne (le_csInf hne (fun t ⟨_, ht⟩ => ht.le)) (Ne.symm h_acc)
      have hr₂ : r < (r + sInf {t ∈ Set.range u | r < t}) / 2 := by linarith
      have hr₂_inf : (r + sInf {t ∈ Set.range u | r < t}) / 2 <
          sInf {t ∈ Set.range u | r < t} := by linarith
      have h_disj : Set.Icc r ((r + sInf {t ∈ Set.range u | r < t}) / 2) ∩
          Set.range u = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro t ⟨⟨hrt, htr₂⟩, htT⟩
        rcases eq_or_lt_of_le hrt with rfl | hrt'
        · exact hr htT
        · linarith [csInf_le hbdd (show t ∈ {t ∈ Set.range u | r < t} from ⟨htT, hrt'⟩)]
      have h_above' : ∃ y ∈ Set.range u,
          (r + sInf {t ∈ Set.range u | r < t}) / 2 < y := by
        obtain ⟨t, htT, hrt⟩ := h_above
        exact ⟨t, htT, lt_of_lt_of_le hr₂_inf (csInf_le hbdd ⟨htT, hrt⟩)⟩
      obtain ⟨a, b, ⟨ha_mem, _, _, hgap⟩, hcontain⟩ := hgaps r _ hr₂ h_disj h_below h_above'
      have hr_in := hcontain (Set.left_mem_Icc.mpr hr₂.le)
      suffices heq : {x | u x > r} = {x | u x > a} by
        obtain ⟨y, rfl⟩ := ha_mem
        rw [heq, R.upper_preimage_eq_strictUpperContour u hu y]; exact R.isOpen_strictUpperContour y
      ext x; simp only [Set.mem_setOf_eq]
      exact ⟨fun hxr => lt_of_lt_of_le (Set.mem_Ioo.mp hr_in).1 hxr.le,
             fun hxa => lt_of_lt_of_le (Set.mem_Ioo.mp hr_in).2
               (ge_of_mem_of_gap (Set.mem_range_self x) hgap hxa)⟩

/-- The preimage `{x | u(x) < r}` is open for any `r`, given that `u` represents `≽` and `range(u)`
has all open gaps. This is the other half of the order-topology subbasis argument. -/
lemma isOpen_lower_preimage (u : X → ℝ) (hu : RepresentsRealPreference R.val u)
    (hgaps : HasAllOpenGaps (Set.range u)) (r : ℝ) : IsOpen {x | u x < r} := by
  by_cases hr : r ∈ Set.range u
  · obtain ⟨y, rfl⟩ := hr
    rw [R.lower_preimage_eq_strictLowerContour u hu y]; exact R.isOpen_strictLowerContour y
  · by_cases h_below : ∃ t ∈ Set.range u, t < r
    swap
    · push Not at h_below
      have : {x | u x < r} = ∅ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact h_below (u x) (Set.mem_range_self x)
      rw [this]; exact isOpen_empty
    by_cases h_above : ∃ t ∈ Set.range u, r < t
    swap
    · push Not at h_above
      have : {x | u x < r} = Set.univ := by
        ext x; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact lt_of_le_of_ne (h_above (u x) (Set.mem_range_self x))
          (fun h => hr (h.symm ▸ Set.mem_range_self x))
      rw [this]; exact isOpen_univ
    -- r ∉ range u with values on both sides; use the supremum of the lower part
    have hne : {t ∈ Set.range u | t < r}.Nonempty := h_below
    have hbdd : BddAbove {t ∈ Set.range u | t < r} := ⟨r, fun t ⟨_, ht⟩ => ht.le⟩
    by_cases h_acc : sSup {t ∈ Set.range u | t < r} = r
    · -- r is an accumulation point from below: write the preimage as a union over range values
      suffices heq : {x | u x < r} =
          ⋃ (p : {t ∈ Set.range u | t < r}), {x | u x < (p : ℝ)} by
        rw [heq]; apply isOpen_iUnion; intro ⟨t, htT, _⟩
        obtain ⟨y, rfl⟩ := htT
        rw [R.lower_preimage_eq_strictLowerContour u hu y]; exact R.isOpen_strictLowerContour y
      ext x; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      constructor
      · intro hxr
        have : ∃ t ∈ {t ∈ Set.range u | t < r}, u x < t := by
          by_contra h; push Not at h
          have : sSup {t ∈ Set.range u | t < r} ≤ u x := csSup_le hne h
          linarith [h_acc]
        obtain ⟨t, ht, htx⟩ := this; exact ⟨⟨t, ht⟩, htx⟩
      · intro ⟨⟨_, _, htr⟩, hxt⟩; exact lt_trans hxt htr
    · -- r is separated from the range below by an open gap; reduce to the gap endpoint
      have h_sup_lt : sSup {t ∈ Set.range u | t < r} < r :=
        lt_of_le_of_ne (csSup_le hne (fun t ⟨_, ht⟩ => ht.le)) h_acc
      have hr₁ : (sSup {t ∈ Set.range u | t < r} + r) / 2 < r := by linarith
      have hr₁_sup : sSup {t ∈ Set.range u | t < r} <
          (sSup {t ∈ Set.range u | t < r} + r) / 2 := by linarith
      have h_disj : Set.Icc ((sSup {t ∈ Set.range u | t < r} + r) / 2) r ∩
          Set.range u = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro t ⟨⟨htr₁, htr⟩, htT⟩
        rcases eq_or_lt_of_le htr with rfl | htr'
        · exact hr htT
        · linarith [le_csSup hbdd (show t ∈ {t ∈ Set.range u | t < r} from ⟨htT, htr'⟩)]
      have h_below' : ∃ y ∈ Set.range u,
          y < (sSup {t ∈ Set.range u | t < r} + r) / 2 := by
        obtain ⟨t, htT, hrt⟩ := h_below
        exact ⟨t, htT, lt_of_le_of_lt (le_csSup hbdd ⟨htT, hrt⟩) hr₁_sup⟩
      obtain ⟨a, b, ⟨_, hb_mem, _, hgap⟩, hcontain⟩ := hgaps _ r hr₁ h_disj h_below' h_above
      have hr_in := hcontain (Set.right_mem_Icc.mpr hr₁.le)
      suffices heq : {x | u x < r} = {x | u x < b} by
        obtain ⟨y, rfl⟩ := hb_mem
        rw [heq, R.lower_preimage_eq_strictLowerContour u hu y]; exact R.isOpen_strictLowerContour y
      ext x; simp only [Set.mem_setOf_eq]
      exact ⟨fun hxr => lt_of_le_of_lt hxr.le (Set.mem_Ioo.mp hr_in).2,
             fun hxb => lt_of_le_of_lt
               (le_of_mem_of_gap (Set.mem_range_self x) hgap hxb)
               (Set.mem_Ioo.mp hr_in).1⟩

/-! ### Debreu's theorem

`exists_continuous_utility_representation` assembles the construction: The raw representation
`exists_rawUtility`, composed with a gap-collapsing map, gives a representation whose range has all
open gaps, and continuity then follows from the preimage-openness lemmas. -/

/-- **Debreu's Representation Theorem** (Debreu 1954): A continuous preference relation on a
second-countable topological space admits a continuous utility representation. -/
theorem exists_continuous_utility_representation [SecondCountableTopology X] [Nonempty X] :
    ∃ u : X → ℝ, RepresentsRealPreference R.val u ∧ Continuous u := by
  obtain ⟨v, hv_rep⟩ := R.exists_rawUtility
  -- Compose with a gap-collapsing strictly monotone map so that the range has all open gaps.
  obtain ⟨g, hg_mono, hg_gaps⟩ :=
    exists_strictMono_hasAllOpenGaps_range (Set.range v)
  let u : X → ℝ := g ∘ fun x => (⟨v x, Set.mem_range_self x⟩ : Set.range v)
  have hu_rep : RepresentsRealPreference R.val u := by
    intro x y; simp only [u, Function.comp]
    constructor
    · intro hxy; exact hg_mono.monotone ((hv_rep x y).mp hxy)
    · intro huxy
      apply (hv_rep x y).mpr
      by_contra h
      push Not at h
      exact absurd huxy (not_le.mpr (hg_mono h))
  have hT_gaps : HasAllOpenGaps (Set.range u) := by
    rw [Set.range_comp_rangeFactorization]; exact hg_gaps
  refine ⟨u, hu_rep, ?_⟩
  rw [OrderTopology.continuous_iff]
  intro r
  constructor
  · show IsOpen (u ⁻¹' Set.Ioi r)
    rw [show u ⁻¹' Set.Ioi r = {x | u x > r} from by ext; simp [Set.mem_Ioi]]
    exact R.isOpen_upper_preimage u hu_rep hT_gaps r
  · show IsOpen (u ⁻¹' Set.Iio r)
    rw [show u ⁻¹' Set.Iio r = {x | u x < r} from by ext; simp [Set.mem_Iio]]
    exact R.isOpen_lower_preimage u hu_rep hT_gaps r

end ContinuousPreferenceRel

end Econlib.Preferences
