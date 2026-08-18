import SmoothingCliff.Mechanism.TieNull

/-!
# The rank-interval identity

Block B of Theorem `thm:stability`.  The stability development reads a bidder's
rank off which interval her own arrival time lands in, between consecutive
opponent order statistics.  The monotonicity development instead counts how
many opponents arrive strictly before her.  This file proves the two agree.

The content is that in a sorted list the entries below a threshold form a
prefix, so the count of entries below the threshold is exactly the index at
which the threshold would be inserted.  The induction runs on the pairwise
form of sortedness, which `List.sortedLE_iff_pairwise` supplies from the
`SortedLE` used by `ConditionedOpponentOrderStats`.
-/

namespace SmoothingCliff.Mechanism

open scoped Classical in
/-- How many opponents arrive strictly before the given time. -/
noncomputable def countBefore (arrival : List ℝ) (time : ℝ) : ℕ :=
  (arrival.filter fun entry => decide (entry < time)).length

@[simp] theorem countBefore_nil (time : ℝ) : countBefore [] time = 0 := by
  simp [countBefore]

theorem countBefore_cons_of_lt {head : ℝ} {tail : List ℝ} {time : ℝ}
    (hHead : head < time) :
    countBefore (head :: tail) time = countBefore tail time + 1 := by
  simp [countBefore, hHead]

theorem countBefore_cons_of_not_lt {head : ℝ} {tail : List ℝ} {time : ℝ}
    (hHead : ¬ head < time) :
    countBefore (head :: tail) time = countBefore tail time := by
  simp [countBefore, hHead]

theorem countBefore_le_length (arrival : List ℝ) (time : ℝ) :
    countBefore arrival time ≤ arrival.length :=
  List.length_filter_le _ _

/-- In a sorted list an entry at or above the threshold forces the count to
vanish. -/
theorem countBefore_eq_zero_of_head_le
    {head : ℝ} {tail : List ℝ} {time : ℝ}
    (hSorted : (head :: tail).Pairwise (· ≤ ·)) (hHead : ¬ head < time) :
    countBefore (head :: tail) time = 0 := by
  rw [countBefore_cons_of_not_lt hHead]
  have hhead := (List.pairwise_cons.mp hSorted).1
  have hzero : ∀ entry ∈ tail, ¬ entry < time := by
    intro entry hentry
    exact fun hlt => hHead (lt_of_le_of_lt (hhead entry hentry) hlt)
  have hnil : tail.filter (fun entry => decide (entry < time)) = [] := by
    refine List.filter_eq_nil_iff.mpr fun entry hentry => ?_
    simpa using hzero entry hentry
  simp [countBefore, hnil]

/-- Every entry below the count is strictly before the threshold. -/
theorem getElem_lt_of_lt_countBefore :
    ∀ (arrival : List ℝ), arrival.Pairwise (· ≤ ·) →
      ∀ (time : ℝ) (index : ℕ), index < countBefore arrival time →
        ∃ h : index < arrival.length, arrival[index] < time := by
  intro arrival
  induction arrival with
  | nil => intro _ time index hindex; simp at hindex
  | cons head tail ih =>
    intro hSorted time index hindex
    by_cases hHead : head < time
    · rw [countBefore_cons_of_lt hHead] at hindex
      cases index with
      | zero => exact ⟨by simp, by simpa using hHead⟩
      | succ k =>
        have hk : k < countBefore tail time := by omega
        obtain ⟨hlen, hlt⟩ :=
          ih (List.pairwise_cons.mp hSorted).2 time k hk
        refine ⟨by simp; omega, ?_⟩
        simpa using hlt
    · rw [countBefore_eq_zero_of_head_le hSorted hHead] at hindex
      exact absurd hindex (Nat.not_lt_zero index)

/-- Every entry at or beyond the count is at or after the threshold. -/
theorem le_getElem_of_countBefore_le :
    ∀ (arrival : List ℝ), arrival.Pairwise (· ≤ ·) →
      ∀ (time : ℝ) (index : ℕ), countBefore arrival time ≤ index →
        ∀ h : index < arrival.length, time ≤ arrival[index] := by
  intro arrival
  induction arrival with
  | nil => intro _ _ index _ h; simp at h
  | cons head tail ih =>
    intro hSorted time index hindex hlen
    by_cases hHead : head < time
    · rw [countBefore_cons_of_lt hHead] at hindex
      cases index with
      | zero => omega
      | succ k =>
        have hk : countBefore tail time ≤ k := by omega
        have hklen : k < tail.length := by simpa using hlen
        simpa using ih (List.pairwise_cons.mp hSorted).2 time k hk hklen
    · have hge : time ≤ head := le_of_not_gt hHead
      cases index with
      | zero => simpa using hge
      | succ k =>
        have hklen : k < tail.length := by simpa using hlen
        have hmem : tail[k] ∈ tail := List.getElem_mem hklen
        have hle : head ≤ tail[k] := (List.pairwise_cons.mp hSorted).1 _ hmem
        simpa using le_trans hge hle

/-- **The rank-interval identity.**  On a sorted opponent list the count of
opponents strictly before a time is `rank` exactly when the time sits in the
`rank`-th interval: strictly after the first `rank` entries and, when a
`rank`-th entry exists, at or before it. -/
theorem countBefore_eq_iff
    {arrival : List ℝ} (hSorted : arrival.Pairwise (· ≤ ·))
    (time : ℝ) (rank : ℕ) :
    countBefore arrival time = rank ↔
      rank ≤ arrival.length ∧
        (∀ index, index < rank → ∀ h : index < arrival.length,
          arrival[index] < time) ∧
        (∀ h : rank < arrival.length, time ≤ arrival[rank]) := by
  constructor
  · rintro rfl
    refine ⟨countBefore_le_length arrival time, ?_, ?_⟩
    · intro index hlt _
      obtain ⟨_, h⟩ :=
        getElem_lt_of_lt_countBefore arrival hSorted time index hlt
      exact h
    · intro hlen
      exact le_getElem_of_countBefore_le arrival hSorted time _ le_rfl hlen
  · rintro ⟨hle, hbelow, habove⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hlen : countBefore arrival time < arrival.length :=
        lt_of_lt_of_le hlt hle
      have hstrict := hbelow (countBefore arrival time) hlt hlen
      have hweak :=
        le_getElem_of_countBefore_le arrival hSorted time _ le_rfl hlen
      exact absurd hstrict (not_lt_of_ge hweak)
    · obtain ⟨hlen, hstrict⟩ :=
        getElem_lt_of_lt_countBefore arrival hSorted time rank hgt
      exact absurd (habove hlen) (not_le_of_gt hstrict)

/-- The same statement against the `SortedLE` form used by the threshold
record. -/
theorem countBefore_eq_iff_sortedLE
    {arrival : List ℝ} (hSorted : arrival.SortedLE)
    (time : ℝ) (rank : ℕ) :
    countBefore arrival time = rank ↔
      rank ≤ arrival.length ∧
        (∀ index, index < rank → ∀ h : index < arrival.length,
          arrival[index] < time) ∧
        (∀ h : rank < arrival.length, time ≤ arrival[rank]) :=
  countBefore_eq_iff (List.sortedLE_iff_pairwise.mp hSorted) time rank

end SmoothingCliff.Mechanism
