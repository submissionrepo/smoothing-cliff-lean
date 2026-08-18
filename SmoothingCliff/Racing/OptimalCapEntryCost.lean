import SmoothingCliff.Racing.OptimalCapPremium

/-!
# The entry-cost direction of the cap comparative static

Formal target: the last parameter direction of clause (iv) of Proposition
`prop:optcert` in `Smoothing_the_Cliff_ITCS.tex`.

The entry cost is the awkward parameter: it sits in the kink location and in
the bracket at once, so raising it lowers the published investment level while
raising the coefficient multiplying it.  The following closed form makes the
two effects visible.  Writing `u` for the product of premium and cap, one
agent's bracket is

`(u - chi)^+ * ((u + chi) / 2 + w)`,

valid on both sides of the kink because the positive part kills the second
factor exactly where it would be wrong.  The difference between two entry costs
is then flat above the larger kink, rising between the kinks, and zero below
the smaller one, which is monotone.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- One agent's racing bracket as a function of `u = premium * cap`. -/
def entryBurdenTerm (slotWeight entryCost u : ℝ) : ℝ :=
  max (u - entryCost) 0 * ((u + entryCost) / 2 + slotWeight)

/-- The closed form agrees with the factored bracket of
`agentRacingBurden_factored`. -/
theorem entryBurdenTerm_eq_bracket
    (slotWeight entryCost u : ℝ) :
    entryBurdenTerm slotWeight entryCost u =
      max (u - entryCost) 0 *
        (entryCost + slotWeight + max (u - entryCost) 0 / 2) := by
  rcases le_total u entryCost with hle | hle
  · rw [entryBurdenTerm, max_eq_right (by linarith), zero_mul, zero_mul]
  · rw [entryBurdenTerm, max_eq_left (by linarith)]
    ring

/-- Raising the entry cost lowers the bracket by an amount that is monotone in
`u`, hence monotone in the cap. -/
theorem entryBurdenTerm_difference_monotone
    {slotWeight entryLow entryHigh : ℝ}
    (hWeight : 0 ≤ slotWeight) (hLow : 0 ≤ entryLow)
    (hOrder : entryLow ≤ entryHigh) :
    Monotone fun u : ℝ =>
      entryBurdenTerm slotWeight entryLow u -
        entryBurdenTerm slotWeight entryHigh u := by
  intro u u' huu
  dsimp only
  have hHigh : 0 ≤ entryHigh := le_trans hLow hOrder
  have hzero : ∀ chi v : ℝ, v ≤ chi → entryBurdenTerm slotWeight chi v = 0 := by
    intro chi v hv
    rw [entryBurdenTerm, max_eq_right (by linarith : v - chi ≤ 0), zero_mul]
  -- Above the larger kink the difference is the constant
  -- (entryHigh - entryLow) * (slotWeight + (entryLow + entryHigh) / 2).
  have hflat : ∀ v : ℝ, entryHigh ≤ v →
      entryBurdenTerm slotWeight entryLow v -
          entryBurdenTerm slotWeight entryHigh v =
        (entryHigh - entryLow) *
          (slotWeight + (entryLow + entryHigh) / 2) := by
    intro v hv
    rw [entryBurdenTerm, entryBurdenTerm,
      max_eq_left (by linarith : (0 : ℝ) ≤ v - entryHigh),
      max_eq_left (by linarith : (0 : ℝ) ≤ v - entryLow)]
    ring
  -- Below the larger kink the difference is the single rising bracket.
  have hmiddle : ∀ v : ℝ, v ≤ entryHigh →
      entryBurdenTerm slotWeight entryLow v -
          entryBurdenTerm slotWeight entryHigh v =
        entryBurdenTerm slotWeight entryLow v := by
    intro v hv
    rw [hzero entryHigh v hv, sub_zero]
  have hrise : ∀ v v' : ℝ, v ≤ v' → v' ≤ entryHigh →
      entryBurdenTerm slotWeight entryLow v ≤
        entryBurdenTerm slotWeight entryLow v' := by
    intro v v' hvv _
    rcases le_total v entryLow with hv | hv
    · rw [hzero entryLow v hv]
      rcases le_total v' entryLow with hv' | hv'
      · rw [hzero entryLow v' hv']
      · rw [entryBurdenTerm,
          max_eq_left (by linarith : (0 : ℝ) ≤ v' - entryLow)]
        nlinarith
    · rw [entryBurdenTerm, entryBurdenTerm,
        max_eq_left (by linarith : (0 : ℝ) ≤ v - entryLow),
        max_eq_left (by linarith : (0 : ℝ) ≤ v' - entryLow)]
      nlinarith
  rcases le_total entryHigh u with hu | hu
  · have hu' : entryHigh ≤ u' := le_trans hu huu
    rw [hflat u hu, hflat u' hu']
  · rcases le_total entryHigh u' with hu' | hu'
    · rw [hmiddle u hu, hflat u' hu']
      have hbound := hrise u entryHigh hu le_rfl
      have heq : entryBurdenTerm slotWeight entryLow entryHigh =
          (entryHigh - entryLow) *
            (slotWeight + (entryLow + entryHigh) / 2) := by
        rw [entryBurdenTerm,
          max_eq_left (by linarith : (0 : ℝ) ≤ entryHigh - entryLow)]
        ring
      linarith [hbound, heq]
    · rw [hmiddle u hu, hmiddle u' hu']
      exact hrise u u' huu hu'

/-- Raising one agent's entry cost changes the burden by an amount monotone in
the cap, on the nonnegative caps. -/
theorem agentRacingBurden_difference_monotoneOn_in_entryCost
    {slotWeight premium capacity entryLow entryHigh : ℝ}
    (hWeight : 0 ≤ slotWeight) (hPremium : 0 ≤ premium)
    (hCapacity : 0 < capacity)
    (hLow : 0 ≤ entryLow) (hOrder : entryLow ≤ entryHigh) :
    MonotoneOn (fun cap =>
      agentRacingBurden slotWeight premium entryLow capacity cap -
        agentRacingBurden slotWeight premium entryHigh capacity cap)
      (Set.Ici (0 : ℝ)) := by
  have hCapNe : capacity ≠ 0 := ne_of_gt hCapacity
  intro cap _ cap' _ hcap
  simp only [agentRacingBurden_factored hCapNe,
    ← entryBurdenTerm_eq_bracket]
  have hu : premium * cap ≤ premium * cap' :=
    mul_le_mul_of_nonneg_left hcap hPremium
  have hmono := entryBurdenTerm_difference_monotone hWeight hLow hOrder hu
  nlinarith [hmono, hCapacity]

/-- Clause (iv) of `prop:optcert`, entry-cost direction.  Raising every agent's
entry cost weakly raises the optimal published cap. -/
theorem certifiedNetSurplus_maximizer_monotone_in_entryCost
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight : ℝ}
    {premium entryLow entryHigh capacity : ι → ℝ}
    {capLow capHigh : ℝ}
    (hWeight : 0 ≤ slotWeight)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hLow : ∀ i, 0 ≤ entryLow i)
    (hOrder : ∀ i, entryLow i ≤ entryHigh i)
    (hHighMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight premium entryHigh
        capacity) (Set.Ioi 0) capHigh)
    (hLowMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight premium entryLow
        capacity) (Set.Ioi 0) capLow)
    (hHighMem : capHigh ∈ Set.Ioi (0 : ℝ)) (hLowMem : capLow ∈ Set.Ioi (0 : ℝ))
    (hHighUnique : ∀ z ∈ Set.Ioi (0 : ℝ),
      IsMaxOn (certifiedNetSurplus strictPriorityWelfare slotWeight premium
        entryHigh capacity) (Set.Ioi 0) z → z = capHigh) :
    capLow ≤ capHigh := by
  refine isMaxOn_le_of_antitone_difference hHighMax hLowMax hHighMem hLowMem
    ?_ hHighUnique
  intro a ha b hb hab
  set term : ι → ℝ → ℝ := fun i cap =>
    agentRacingBurden slotWeight (premium i) (entryLow i) (capacity i) cap -
      agentRacingBurden slotWeight (premium i) (entryHigh i) (capacity i)
        cap with hterm
  have hburden : ∀ i, term i a ≤ term i b := fun i =>
    agentRacingBurden_difference_monotoneOn_in_entryCost hWeight (hPremium i)
      (hCapacity i) (hLow i) (hOrder i) (Set.mem_Ici.mpr (le_of_lt ha))
      (Set.mem_Ici.mpr (le_of_lt hb)) hab
  have hsum : ∑ i, term i a ≤ ∑ i, term i b :=
    Finset.sum_le_sum fun i _ => hburden i
  simp only [hterm] at hsum
  simp only [certifiedNetSurplus, racingBurden]
  have hexpand : ∀ cap : ℝ,
      (strictPriorityWelfare - smoothingConcession slotWeight cap -
          ∑ i, agentRacingBurden slotWeight (premium i) (entryLow i)
            (capacity i) cap) -
        (strictPriorityWelfare - smoothingConcession slotWeight cap -
          ∑ i, agentRacingBurden slotWeight (premium i) (entryHigh i)
            (capacity i) cap) =
      ∑ i, (agentRacingBurden slotWeight (premium i) (entryHigh i)
          (capacity i) cap -
        agentRacingBurden slotWeight (premium i) (entryLow i)
          (capacity i) cap) := by
    intro cap
    rw [Finset.sum_sub_distrib]
    ring
  rw [hexpand a, hexpand b]
  have hneg : ∀ cap : ℝ,
      ∑ i, (agentRacingBurden slotWeight (premium i) (entryHigh i)
          (capacity i) cap -
        agentRacingBurden slotWeight (premium i) (entryLow i)
          (capacity i) cap) =
      -∑ i, (agentRacingBurden slotWeight (premium i) (entryLow i)
          (capacity i) cap -
        agentRacingBurden slotWeight (premium i) (entryHigh i)
          (capacity i) cap) := by
    intro cap
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hneg a, hneg b]
  linarith

end

end SmoothingCliff.Racing
