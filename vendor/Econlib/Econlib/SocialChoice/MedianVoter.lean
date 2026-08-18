/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Geometry.SinglePeaked
public import Econlib.SocialChoice.Rule.Majority
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Tactic.Linarith

/-!
# Black's Median Voter Theorem

If every voter has a **single-peaked** preference on a linearly ordered alternative space (Black
1948), then any alternative `m` such that strictly more than half the voters' peaks are `≥ m` and
strictly more than half are `≤ m` is a **Condorcet winner** under majority rule. For an odd
electorate the median peak always satisfies both conditions, establishing existence of a Condorcet
winner.

## Main definitions

* `prefSet`: The set of voters who strictly prefer one alternative to another.

## Main statements

* `condorcetWinner_of_majority_pivot`: If a strict majority of voters have peak `≥ m` and a strict
  majority have peak `≤ m`, then `m` is a Condorcet winner.
* `exists_condorcetWinner_of_singlePeaked`: Black's existence theorem, that every odd-cardinality
  electorate of single-peaked voters admits a Condorcet winner.

## Notes

The single-peaked structure rules out indifference between distinct alternatives on the same side
of the peak, so no separate strict-preference hypothesis is needed.

## References

* Black, Duncan. 1948. “On the Rationale of Group Decision-Making.” *Journal of Political Economy*
  56 (1): 23–34. [https://doi.org/10.1086/256633](https://doi.org/10.1086/256633).

## Tags

social choice, median voter, condorcet winner, single-peaked preferences, black's theorem
-/

@[expose] public section

namespace Econlib.SocialChoice

open Econlib.Preferences

variable {Voter : Type*} [Fintype Voter]
variable {Alt : Type*}

/-- The set of voters who strictly prefer `x` to `y`.

Noncomputable by design: The filter predicate `(P i).lt x y` is `Prop`-valued over the abstract
`PreferenceRel.le` and is decided classically rather than via a threaded `Decidable` bracket field
(see `majorityCount` in `Rule/Majority.lean` for the full rationale). -/
private noncomputable def prefSet (P : Profile Voter Alt) (x y : Alt) :
    Finset Voter :=
  letI : DecidablePred (fun i : Voter => (P i).lt x y) := Classical.decPred _
  Finset.univ.filter (fun i : Voter => (P i).lt x y)

private lemma majorityCount_eq_prefSet_card
    (P : Profile Voter Alt) (x y : Alt) :
    majorityCount P x y = (prefSet P x y).card := by
  unfold majorityCount prefSet
  congr 1

private lemma prefSet_disjoint (P : Profile Voter Alt) (x y : Alt) :
    Disjoint (prefSet P x y) (prefSet P y x) := by
  rw [Finset.disjoint_left]
  intro i hi hj
  unfold prefSet at hi hj
  classical
  have hxy : (P i).lt x y := (Finset.mem_filter.mp hi).2
  have hyx : (P i).lt y x := (Finset.mem_filter.mp hj).2
  exact hxy.2 hyx.1

private lemma prefSet_card_add_le
    (P : Profile Voter Alt) (x y : Alt) :
    (prefSet P x y).card + (prefSet P y x).card ≤ Fintype.card Voter := by
  classical
  calc (prefSet P x y).card + (prefSet P y x).card
      = (prefSet P x y ∪ prefSet P y x).card :=
        (Finset.card_union_of_disjoint (prefSet_disjoint P x y)).symm
    _ ≤ Fintype.card Voter := by
        rw [← Finset.card_univ]; exact Finset.card_le_card (Finset.subset_univ _)

variable [LinearOrder Alt]

/-- Voters whose peak is at least `m` strictly prefer `m` to any `x < m`. -/
private lemma high_peak_subset_prefSet_left
    {P : Profile Voter Alt} (sp : ∀ i, SinglePeakedRel (P i))
    {x m : Alt} (hxm : x < m) :
    (Finset.univ.filter (fun i : Voter => m ≤ (sp i).peak)) ⊆ prefSet P m x := by
  classical
  intro i hi
  have hpi : m ≤ (sp i).peak := (Finset.mem_filter.mp hi).2
  have hpref : (P i).lt m x := (sp i).left_of_peak x m hxm hpi
  unfold prefSet
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpref⟩

/-- Voters whose peak is at most `m` strictly prefer `m` to any `x > m`. -/
private lemma low_peak_subset_prefSet_right
    {P : Profile Voter Alt} (sp : ∀ i, SinglePeakedRel (P i))
    {m x : Alt} (hmx : m < x) :
    (Finset.univ.filter (fun i : Voter => (sp i).peak ≤ m)) ⊆ prefSet P m x := by
  classical
  intro i hi
  have hpi : (sp i).peak ≤ m := (Finset.mem_filter.mp hi).2
  have hpref : (P i).lt m x := (sp i).right_of_peak m x hpi hmx
  unfold prefSet
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpref⟩

/-- Pivot lemma. If a strict majority of voters have peak `≥ m` and a strict majority have peak
`≤ m`, then `m` is a Condorcet winner.

For odd electorates the median peak satisfies both conditions, giving Black's theorem. -/
theorem condorcetWinner_of_majority_pivot
    {P : Profile Voter Alt} (sp : ∀ i, SinglePeakedRel (P i)) (m : Alt)
    (h_high : 2 * (Finset.univ.filter (fun i : Voter => m ≤ (sp i).peak)).card
              > Fintype.card Voter)
    (h_low : 2 * (Finset.univ.filter (fun i : Voter => (sp i).peak ≤ m)).card
              > Fintype.card Voter) :
    CondorcetWinner P m := by
  intro x hxm
  -- It suffices to show a strict majority strictly prefers `m` to `x`; the side of `x`
  -- relative to `m` selects which majority hypothesis supplies the count bound.
  suffices h_other : (prefSet P x m).card < (prefSet P m x).card by
    unfold pairwiseMajority
    rw [majorityCount_eq_prefSet_card, majorityCount_eq_prefSet_card]
    exact h_other
  have h_total := prefSet_card_add_le P m x
  rcases lt_or_gt_of_ne hxm with hxm_lt | hxm_gt
  · -- `x < m`: voters with peak `≥ m` strictly prefer `m`, and they are a strict majority.
    have h_card := Finset.card_le_card (high_peak_subset_prefSet_left sp hxm_lt)
    omega
  · -- `m < x`: voters with peak `≤ m` strictly prefer `m`, and they are a strict majority.
    have h_card := Finset.card_le_card (low_peak_subset_prefSet_right sp hxm_gt)
    omega

/-- In a `≤`-sorted list, at least `k + 1` entries are `≤` the `k`-th entry: The entry itself
together with all `k` entries before it. -/
private lemma succ_le_countP_le_get {l : List Alt} (hl : List.Pairwise (· ≤ ·) l)
    (k : ℕ) (hk : k < l.length) :
    k + 1 ≤ List.countP (fun a => decide (a ≤ l.get ⟨k, hk⟩)) l := by
  have hmono : ∀ (i j : Fin l.length), i ≤ j → l.get i ≤ l.get j :=
    fun i j hij => (eq_or_lt_of_le hij).elim (fun h => h ▸ le_refl _) hl.rel_get_of_lt
  -- Every entry of the first `k + 1` is `≤` the `k`-th, so `countP` over that prefix is `k + 1`.
  have hall : ∀ x ∈ l.take (k + 1), x ≤ l.get ⟨k, hk⟩ := by
    intro x hx
    rw [List.mem_take_iff_getElem] at hx
    obtain ⟨i, hi_lt, hi_eq⟩ := hx
    have hi_lt_len : i < l.length := lt_of_lt_of_le hi_lt (min_le_right _ _)
    have hi_le_k : i ≤ k := by have := lt_of_lt_of_le hi_lt (min_le_left _ _); omega
    rw [← hi_eq]
    simpa [List.get_eq_getElem] using hmono ⟨i, hi_lt_len⟩ ⟨k, hk⟩ hi_le_k
  have hcount_take :
      List.countP (fun a => decide (a ≤ l.get ⟨k, hk⟩)) (l.take (k + 1)) = k + 1 := by
    rw [List.countP_eq_length.mpr fun a ha => decide_eq_true (hall a ha),
      List.length_take_of_le (by omega)]
  set target := l.get ⟨k, hk⟩ with htarget
  have happend : List.countP (fun a => decide (a ≤ target)) l =
      List.countP (fun a => decide (a ≤ target)) (l.take (k + 1)) +
        List.countP (fun a => decide (a ≤ target)) (l.drop (k + 1)) := by
    conv_lhs => rw [← List.take_append_drop (k + 1) l]
    exact List.countP_append
  omega

/-- In a `≤`-sorted list, at least `length - k` entries are `≥` the `k`-th entry: The entry itself
together with all entries after it. -/
private lemma sub_le_countP_get_le {l : List Alt} (hl : List.Pairwise (· ≤ ·) l)
    (k : ℕ) (hk : k < l.length) :
    l.length - k ≤ List.countP (fun a => decide (l.get ⟨k, hk⟩ ≤ a)) l := by
  have hmono : ∀ (i j : Fin l.length), i ≤ j → l.get i ≤ l.get j :=
    fun i j hij => (eq_or_lt_of_le hij).elim (fun h => h ▸ le_refl _) hl.rel_get_of_lt
  -- Every entry from the `k`-th onward is `≥` the `k`-th, so `countP` over that suffix is
  -- `length - k`.
  have hall : ∀ x ∈ l.drop k, l.get ⟨k, hk⟩ ≤ x := by
    intro x hx
    rw [List.mem_drop_iff_getElem] at hx
    obtain ⟨j, hj_lt, hj_eq⟩ := hx
    have hkj_lt : k + j < l.length := by omega
    rw [← hj_eq]
    simpa [List.get_eq_getElem] using hmono ⟨k, hk⟩ ⟨k + j, hkj_lt⟩ (Nat.le_add_right _ _)
  have hcount_drop :
      List.countP (fun a => decide (l.get ⟨k, hk⟩ ≤ a)) (l.drop k) = l.length - k := by
    rw [List.countP_eq_length.mpr fun a ha => decide_eq_true (hall a ha), List.length_drop]
  set target := l.get ⟨k, hk⟩ with htarget
  have happend : List.countP (fun a => decide (target ≤ a)) l =
      List.countP (fun a => decide (target ≤ a)) (l.take k) +
        List.countP (fun a => decide (target ≤ a)) (l.drop k) := by
    conv_lhs => rw [← List.take_append_drop k l]
    exact List.countP_append
  omega

/-- **Black's Median Voter Theorem.** Every odd-cardinality electorate of voters with single-peaked
preferences over a linearly ordered alternative space admits a Condorcet winner. -/
theorem exists_condorcetWinner_of_singlePeaked
    {P : Profile Voter Alt} (sp : ∀ i, SinglePeakedRel (P i))
    [Nonempty Voter]
    (h_odd : Odd (Fintype.card Voter)) :
    ∃ m : Alt, CondorcetWinner P m := by
  classical
  set peakOf : Voter → Alt := fun i => (sp i).peak with hpeakOf
  set peaks : Multiset Alt :=
    (Finset.univ : Finset Voter).val.map peakOf with hpeaks
  set sorted : List Alt := peaks.sort (fun a b : Alt => a ≤ b) with hsorted
  have hlen : sorted.length = Fintype.card Voter := by
    rw [hsorted, Multiset.length_sort, hpeaks, Multiset.card_map]
    rfl
  set n := Fintype.card Voter with hn
  have hn_pos : 0 < n := Fintype.card_pos
  have hk_lt : n / 2 < sorted.length := by
    rw [hlen]; omega
  set m : Alt := sorted.get ⟨n / 2, hk_lt⟩ with hm
  have hpair : List.Pairwise (· ≤ ·) sorted := by
    rw [hsorted]; exact Multiset.pairwise_sort _ _
  have hcount_filter :
      ∀ (q : Alt → Prop) [DecidablePred q],
        (Finset.univ.filter (fun i : Voter => q (peakOf i))).card =
          List.countP (fun a => decide (q a)) sorted := by
    intro q _
    have h1 : (Finset.univ.filter (fun i : Voter => q (peakOf i))).card =
        (Multiset.filter (fun i : Voter => q (peakOf i))
          (Finset.univ : Finset Voter).val).card := by
      rw [Finset.card_def, Finset.filter_val]
    have h2 : (Multiset.filter (fun i : Voter => q (peakOf i))
        (Finset.univ : Finset Voter).val).card =
        Multiset.countP q peaks := by
      rw [hpeaks]; exact (Multiset.countP_map peakOf _ q).symm
    have hcoe : (sorted : Multiset Alt) = peaks := by
      rw [hsorted]; exact Multiset.sort_eq _ _
    have h3 : Multiset.countP q peaks =
        List.countP (fun a => decide (q a)) sorted := by
      rw [← hcoe, Multiset.coe_countP]
    rw [h1, h2, h3]
  have h_low_card :
      n / 2 + 1 ≤ (Finset.univ.filter (fun i : Voter => peakOf i ≤ m)).card := by
    have := succ_le_countP_le_get hpair (n / 2) hk_lt
    rw [hcount_filter (fun a => a ≤ m)]
    simpa [hm] using this
  have h_high_card :
      sorted.length - n / 2 ≤
        (Finset.univ.filter (fun i : Voter => m ≤ peakOf i)).card := by
    have := sub_le_countP_get_le hpair (n / 2) hk_lt
    rw [hcount_filter (fun a => m ≤ a)]
    simpa [hm] using this
  obtain ⟨ℓ, hℓ⟩ := h_odd
  have hn_eq : n = 2 * ℓ + 1 := by omega
  have hk_val : n / 2 = ℓ := by omega
  have h_high : 2 * (Finset.univ.filter (fun i : Voter => m ≤ peakOf i)).card > n := by
    have hbound : sorted.length - n / 2 = ℓ + 1 := by rw [hlen]; omega
    rw [hbound] at h_high_card
    omega
  have h_low : 2 * (Finset.univ.filter (fun i : Voter => peakOf i ≤ m)).card > n := by
    have hbound : n / 2 + 1 = ℓ + 1 := by omega
    rw [hbound] at h_low_card
    omega
  refine ⟨m, condorcetWinner_of_majority_pivot sp m ?_ ?_⟩
  · simpa [hpeakOf] using h_high
  · simpa [hpeakOf] using h_low

end Econlib.SocialChoice
