import SmoothingCliff.Mechanism.RankInterval

/-!
# The realized race rank is the count on the sorted opponent list

The first half of block C of Theorem `thm:stability`.  The monotonicity
development ranks by `raceRank`, a count over all agents with the agent order
breaking ties.  The stability development works with `sortedOpponentKeys`, the
sorted list of the opponents' keys.  Away from ties the two agree: the rank is
exactly how many opponent keys fall strictly below the own key.

Ties are null by `TieNull.lean`, so the hypothesis below is satisfied almost
everywhere; combined with the rank-interval identity of `RankInterval.lean`
this identifies the realized rank with the interval the own clock lands in.
What still remains of block C is the Fubini split of the own coordinate from
the opponents'.
-/

namespace SmoothingCliff.Mechanism

open Finset

/-- Away from ties, arriving before is just having a smaller key. -/
theorem arrivesBefore_iff_lt
    {ι : Type*} [LinearOrder ι] {key : ι → ℝ} {i j : ι}
    (hNoTie : key j ≠ key i) :
    ArrivesBefore key j i ↔ key j < key i := by
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact h
    · exact absurd h hNoTie
  · exact fun h => Or.inl h

/-- The agent herself never arrives before herself. -/
theorem not_arrivesBefore_self
    {ι : Type*} [LinearOrder ι] (key : ι → ℝ) (i : ι) :
    ¬ ArrivesBefore key i i := by
  rintro (h | ⟨-, h⟩)
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

/-- Away from ties the race rank counts the opponents with a smaller key. -/
theorem raceRank_eq_card_filter
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (key : ι → ℝ) (i : ι) (hNoTie : ∀ j, j ≠ i → key j ≠ key i) :
    raceRank key i =
      ((univ.erase i).filter fun j => key j < key i).card := by
  classical
  rw [raceRank]
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and, and_true, mem_erase]
  constructor
  · intro hj
    have hne : j ≠ i := by
      rintro rfl
      exact not_arrivesBefore_self key _ hj
    exact ⟨hne, (arrivesBefore_iff_lt (hNoTie j hne)).mp hj⟩
  · rintro ⟨hne, hlt⟩
    exact (arrivesBefore_iff_lt (hNoTie j hne)).mpr hlt

/-- Counting on the sorted opponent list is counting on the opponent set. -/
theorem countBefore_sortedOpponentKeys
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (key : ι → ℝ) (i : ι) (time : ℝ) :
    countBefore (sortedOpponentKeys key i) time =
      ((univ.erase i).filter fun j => key j < time).card := by
  classical
  have hcount : countBefore (sortedOpponentKeys key i) time =
      Multiset.countP (fun entry => decide (entry < time) = true)
        ((univ.erase i).val.map key) := by
    rw [countBefore, sortedOpponentKeys, ← List.countP_eq_length_filter,
      ← Multiset.coe_countP, Multiset.sort_eq]
    simp
  rw [hcount, Multiset.countP_map]
  simp [Finset.filter, Finset.card]

/-- **The race-rank bridge.**  Away from ties, the realized race rank of an
agent equals the number of opponent keys strictly below her own. -/
theorem raceRank_eq_countBefore
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (key : ι → ℝ) (i : ι) (hNoTie : ∀ j, j ≠ i → key j ≠ key i) :
    raceRank key i = countBefore (sortedOpponentKeys key i) (key i) := by
  rw [raceRank_eq_card_filter key i hNoTie,
    countBefore_sortedOpponentKeys key i (key i)]

end SmoothingCliff.Mechanism
