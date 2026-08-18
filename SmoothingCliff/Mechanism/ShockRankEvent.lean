import SmoothingCliff.Mechanism.RaceRankBridge

/-!
# Interval membership is the rank

The last combinatorial step before the measure-theoretic split.  `RankInterval`
characterizes the count of opponents strictly before a time; the stability
development instead asks whether the own clock lands in the `p`-th interval of
`conditionedShockRankEvent`.  This file shows the two say the same thing, so
that the chain

  no tie  ⇒  rank is the count  ⇒  the count is interval membership

is complete.  What remains of Theorem `thm:stability` is then purely
measure-theoretic: exhibiting the measure as an opponent law times an
independent own coordinate and splitting the integral.
-/

namespace SmoothingCliff.Mechanism

open ConditionedOpponentOrderStats

/-- Scaling by a positive intensity does not change an order comparison. -/
theorem exp_mul_le_exp_mul_iff (score first second : ℝ) :
    Real.exp score * first ≤ Real.exp score * second ↔ first ≤ second := by
  constructor
  · exact fun h => le_of_mul_le_mul_left h (Real.exp_pos score)
  · exact fun h => mul_le_mul_of_nonneg_left h (Real.exp_pos score).le

theorem exp_mul_lt_exp_mul_iff (score first second : ℝ) :
    Real.exp score * first < Real.exp score * second ↔ first < second := by
  constructor
  · exact fun h => lt_of_mul_lt_mul_left h (Real.exp_pos score).le
  · exact fun h => mul_lt_mul_of_pos_left h (Real.exp_pos score)

/-- **Interval membership is the rank.**  The own clock, scaled by the
intensity, lands in the `rank`-th interval exactly when `rank` opponents arrive
strictly before the own arrival time. -/
theorem mem_conditionedShockRankEvent_iff
    {arrival : List ℝ} (hNonneg : ∀ t ∈ arrival, 0 ≤ t)
    (hSorted : arrival.SortedLE) (score time : ℝ) (rank : ℕ) :
    Real.exp score * time ∈
        conditionedShockRankEvent (ofSortedList arrival hNonneg hSorted)
          score rank ↔
      countBefore arrival time = rank := by
  classical
  have hpair := List.sortedLE_iff_pairwise.mp hSorted
  rw [countBefore_eq_iff hpair]
  have hthreshold := ofSortedList_threshold arrival hNonneg hSorted
  cases rank with
  | zero =>
    by_cases hlen : 0 < arrival.length
    · rw [conditionedShockRankEvent]
      simp only [hthreshold, dif_pos hlen]
      constructor
      · intro hmem
        refine ⟨Nat.zero_le _, ?_, ?_⟩
        · intro index hindex
          exact absurd hindex (Nat.not_lt_zero index)
        · intro _
          exact (exp_mul_le_exp_mul_iff score _ _).mp hmem
      · rintro ⟨-, -, habove⟩
        exact (exp_mul_le_exp_mul_iff score _ _).mpr (habove hlen)
    · have hnil : arrival.length = 0 := by omega
      rw [conditionedShockRankEvent]
      simp only [hthreshold, dif_neg (by omega : ¬ 0 < arrival.length)]
      constructor
      · intro _
        exact ⟨by omega, fun index hindex => absurd hindex (Nat.not_lt_zero index),
          fun h => absurd h (by omega)⟩
      · intro _
        trivial
  | succ q =>
    by_cases hq : q < arrival.length
    · by_cases hq' : q + 1 < arrival.length
      · rw [conditionedShockRankEvent]
        simp only [hthreshold, dif_pos hq, dif_pos hq']
        constructor
        · rintro ⟨hlower, hupper⟩
          refine ⟨by omega, ?_, ?_⟩
          · intro index hindex hlen
            have hle : arrival[index] ≤ arrival[q] :=
              hSorted.getElem_le_getElem_of_le (by omega)
            exact lt_of_le_of_lt hle
              ((exp_mul_lt_exp_mul_iff score _ _).mp hlower)
          · intro _
            exact (exp_mul_le_exp_mul_iff score _ _).mp hupper
        · rintro ⟨-, hbelow, habove⟩
          exact ⟨(exp_mul_lt_exp_mul_iff score _ _).mpr
              (hbelow q (by omega) hq),
            (exp_mul_le_exp_mul_iff score _ _).mpr (habove hq')⟩
      · rw [conditionedShockRankEvent]
        simp only [hthreshold, dif_pos hq, dif_neg hq']
        constructor
        · intro hlower
          refine ⟨by omega, ?_, ?_⟩
          · intro index hindex hlen
            have hle : arrival[index] ≤ arrival[q] :=
              hSorted.getElem_le_getElem_of_le (by omega)
            exact lt_of_le_of_lt hle
              ((exp_mul_lt_exp_mul_iff score _ _).mp hlower)
          · intro h
            exact absurd h hq'
        · rintro ⟨-, hbelow, -⟩
          exact (exp_mul_lt_exp_mul_iff score _ _).mpr (hbelow q (by omega) hq)
    · rw [conditionedShockRankEvent]
      simp only [hthreshold, dif_neg hq]
      constructor
      · intro hmem
        exact absurd hmem (Set.notMem_empty _)
      · rintro ⟨hle, -, -⟩
        omega

end SmoothingCliff.Mechanism
