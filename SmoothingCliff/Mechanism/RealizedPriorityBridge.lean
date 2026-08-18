import SmoothingCliff.Mechanism.ShockRankEvent

/-!
# The two realized priorities agree pointwise

The last piece of mathematical content in Theorem `thm:stability`.  The
monotonicity development evaluates a bidder's realized priority at her race
rank; the stability development sums slot weights over the interval her own
clock lands in.  Away from ties these are the same number at every sample
point.

The chain is the one assembled in the preceding three files: no tie makes the
rank the count of opponents strictly before, the count is exactly which
interval the clock occupies, and the interval sum therefore collapses to the
single weight at the rank.

What is left of the theorem after this is plumbing rather than content: the
measure must be exhibited as an opponent law times an independent own
coordinate so that the two integrals can be compared by Fubini.
-/

namespace SmoothingCliff.Mechanism

open Finset

/-- An indicator sum over disjoint rank intervals collapses to the weight at
the occupied interval. -/
theorem sum_indicator_rankEvent
    {stats : ConditionedOpponentOrderStats} {slotWeight : ℕ → ℝ} {slots : ℕ}
    {score ownShock : ℝ} {rank : ℕ}
    (hmem : ∀ p, ownShock ∈ conditionedShockRankEvent stats score p ↔ p = rank) :
    conditionedFiniteRacePriority slotWeight slots stats score ownShock =
      priorityAtRank slotWeight slots rank := by
  classical
  rw [conditionedFiniteRacePriority, priorityAtRank]
  by_cases hrank : rank < slots
  · rw [if_pos hrank]
    rw [Finset.sum_eq_single rank]
    · rw [Set.indicator_of_mem ((hmem rank).mpr rfl)]
    · intro p _ hne
      exact Set.indicator_of_notMem (fun hp => hne ((hmem p).mp hp)) _
    · intro hnot
      exact absurd (Finset.mem_range.mpr hrank) hnot
  · rw [if_neg hrank]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hplt : p < slots := Finset.mem_range.mp hp
    refine Set.indicator_of_notMem (fun hmemp => ?_) _
    have := (hmem p).mp hmemp
    omega

/-- **The realized priorities agree.**  Away from ties, the priority the
monotonicity development reads off the race rank equals the priority the
stability development reads off the occupied interval. -/
theorem plEligibleRealizedPriority_eq_conditionedFiniteRacePriority
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (slotWeight : ℕ → ℝ) (slots : ℕ)
    (key : ι → ℝ) (i : ι)
    (hKey : ∀ j, j ≠ i → 0 ≤ key j)
    (hNoTie : ∀ j, j ≠ i → key j ≠ key i)
    (score : ℝ) :
    priorityAtRank slotWeight slots (raceRank key i) =
      conditionedFiniteRacePriority slotWeight slots
        (opponentOrderStats key i hKey) score (Real.exp score * key i) := by
  classical
  refine (sum_indicator_rankEvent (rank := raceRank key i) ?_).symm
  intro p
  rw [opponentOrderStats,
    mem_conditionedShockRankEvent_iff (sortedOpponentKeys_nonnegative key i hKey)
      (sortedOpponentKeys_sorted key i) score (key i) p]
  rw [← raceRank_eq_countBefore key i hNoTie]
  exact eq_comm

end SmoothingCliff.Mechanism
