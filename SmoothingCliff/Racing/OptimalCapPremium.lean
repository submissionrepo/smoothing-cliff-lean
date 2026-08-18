import SmoothingCliff.Racing.OptimalCapGuarantee

/-!
# The value and reserve directions of the cap comparative static

Formal target: the remaining value direction of clause (iv) of Proposition
`prop:optcert` in `Smoothing_the_Cliff_ITCS.tex`, together with the reserve
direction it implies.

`OptimalCapGuarantee.lean` handles the capacity direction, where the parameter
factors out of the burden.  The premium enters the positive part
`m = ((v-r) S - chi)^+` in both the kink location and the bracket, which is why
the paper argues through the one-sided derivative of `R`.  The argument below
is again ordinal: a difference of positive parts is monotone when the arguments
move right and spread out, and the bracket splits into a linear term and a
square term that both inherit monotonicity.

Raising the reserve lowers every premium, so the reserve direction is the same
statement read in the opposite order.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- A difference of positive parts is monotone when the arguments move right
and spread out.  The ordering hypotheses `a <= b` and `a' <= b'` cannot be
dropped: at `a = 0`, `b = -10`, `a' = 5`, `b' = -5` every other hypothesis
holds and the conclusion fails. -/
theorem posPart_sub_posPart_mono
    {a b a' b' : ℝ} (hbase : a ≤ a') (htop : b ≤ b')
    (hlow : a ≤ b) (hhigh : a' ≤ b')
    (hspread : b - a ≤ b' - a') :
    max b 0 - max a 0 ≤ max b' 0 - max a' 0 := by
  rcases le_total 0 a with ha | ha
  · have hb : 0 ≤ b := le_trans ha hlow
    have ha' : 0 ≤ a' := le_trans ha hbase
    have hb' : 0 ≤ b' := le_trans ha' hhigh
    rw [max_eq_left ha, max_eq_left hb, max_eq_left ha', max_eq_left hb']
    linarith
  · rw [max_eq_right ha]
    rcases le_total 0 a' with ha' | ha'
    · have hb' : 0 ≤ b' := le_trans ha' hhigh
      rw [max_eq_left ha', max_eq_left hb']
      rcases le_total 0 b with hb | hb
      · rw [max_eq_left hb]; linarith
      · rw [max_eq_right hb]; linarith
    · rw [max_eq_right ha']
      rcases le_total 0 b with hb | hb
      · have hb' : 0 ≤ b' := le_trans hb htop
        rw [max_eq_left hb, max_eq_left hb']
        linarith
      · rw [max_eq_right hb]
        have : 0 ≤ max b' 0 := le_max_right _ _
        linarith

/-- The published investment level is monotone in the cap. -/
theorem posPart_premium_monotone
    {entryCost premium : ℝ} (hPremium : 0 ≤ premium) :
    Monotone fun cap : ℝ => max (premium * cap - entryCost) 0 := by
  intro cap cap' hcap
  exact max_le_max
    (sub_le_sub_right (mul_le_mul_of_nonneg_left hcap hPremium) entryCost)
    le_rfl

/-- Raising a premium raises the published investment level by an amount that
is monotone in the cap, on the nonnegative caps. -/
theorem posPart_premium_difference_monotoneOn
    {entryCost premiumLow premiumHigh : ℝ}
    (hLow : 0 ≤ premiumLow) (hOrder : premiumLow ≤ premiumHigh) :
    MonotoneOn (fun cap : ℝ =>
      max (premiumHigh * cap - entryCost) 0 -
        max (premiumLow * cap - entryCost) 0) (Set.Ici (0 : ℝ)) := by
  intro cap hcapMem cap' hcapMem' hcap
  have hCapNonneg : (0 : ℝ) ≤ cap := hcapMem
  have hCapNonneg' : (0 : ℝ) ≤ cap' := hcapMem'
  refine posPart_sub_posPart_mono
    (sub_le_sub_right (mul_le_mul_of_nonneg_left hcap hLow) entryCost)
    (sub_le_sub_right
      (mul_le_mul_of_nonneg_left hcap (le_trans hLow hOrder)) entryCost)
    (sub_le_sub_right (mul_le_mul_of_nonneg_right hOrder hCapNonneg) entryCost)
    (sub_le_sub_right (mul_le_mul_of_nonneg_right hOrder hCapNonneg')
      entryCost) ?_
  have hgap : 0 ≤ premiumHigh - premiumLow := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hcap hgap]

/-- Ordering of the published investment levels at a nonnegative cap. -/
theorem posPart_premium_le
    {entryCost premiumLow premiumHigh cap : ℝ}
    (hCap : 0 ≤ cap) (hOrder : premiumLow ≤ premiumHigh) :
    max (premiumLow * cap - entryCost) 0 ≤
      max (premiumHigh * cap - entryCost) 0 :=
  max_le_max
    (sub_le_sub_right (mul_le_mul_of_nonneg_right hOrder hCap) entryCost)
    le_rfl

/-- Raising one agent's premium changes the burden by an amount monotone in the
cap, on the nonnegative caps.  The bracket splits into a linear term and a
square term, and the square term is a product of nonnegative monotone
functions. -/
theorem agentRacingBurden_difference_monotoneOn_in_premium
    {slotWeight entryCost capacity premiumLow premiumHigh : ℝ}
    (hWeight : 0 ≤ slotWeight) (hEntryCost : 0 ≤ entryCost)
    (hCapacity : 0 < capacity)
    (hLow : 0 ≤ premiumLow) (hOrder : premiumLow ≤ premiumHigh) :
    MonotoneOn (fun cap =>
      agentRacingBurden slotWeight premiumHigh entryCost capacity cap -
        agentRacingBurden slotWeight premiumLow entryCost capacity cap)
      (Set.Ici (0 : ℝ)) := by
  have hCapNe : capacity ≠ 0 := ne_of_gt hCapacity
  intro cap hcapMem cap' hcapMem' hcap
  have hCapNonneg : (0 : ℝ) ≤ cap := hcapMem
  have hCapNonneg' : (0 : ℝ) ≤ cap' := hcapMem'
  simp only [agentRacingBurden_factored hCapNe]
  set mLow := max (premiumLow * cap - entryCost) 0 with hmLow
  set mHigh := max (premiumHigh * cap - entryCost) 0 with hmHigh
  set mLow' := max (premiumLow * cap' - entryCost) 0 with hmLow'
  set mHigh' := max (premiumHigh * cap' - entryCost) 0 with hmHigh'
  have hLowNonneg : 0 ≤ mLow := le_max_right _ _
  have hLowNonneg' : 0 ≤ mLow' := le_max_right _ _
  have hHighNonneg : 0 ≤ mHigh := le_max_right _ _
  have hLowMono : mLow ≤ mLow' := posPart_premium_monotone hLow hcap
  have hHighMono : mHigh ≤ mHigh' :=
    posPart_premium_monotone (le_trans hLow hOrder) hcap
  have hGap : mHigh - mLow ≤ mHigh' - mLow' :=
    posPart_premium_difference_monotoneOn hLow hOrder
      (Set.mem_Ici.mpr hCapNonneg) (Set.mem_Ici.mpr hCapNonneg') hcap
  have hOrderLow : mLow ≤ mHigh := posPart_premium_le hCapNonneg hOrder
  have hOrderLow' : mLow' ≤ mHigh' := posPart_premium_le hCapNonneg' hOrder
  -- The bracket difference is (chi + w) * (mHigh - mLow) + (mHigh^2 - mLow^2)/2.
  have hSquare :
      mHigh * mHigh - mLow * mLow ≤ mHigh' * mHigh' - mLow' * mLow' := by
    have hsum : mHigh + mLow ≤ mHigh' + mLow' := by linarith
    have hdiffNonneg : 0 ≤ mHigh - mLow := by linarith
    nlinarith [hGap, hsum, hdiffNonneg, hLowNonneg, hHighNonneg]
  have hLinear : (entryCost + slotWeight) * (mHigh - mLow) ≤
      (entryCost + slotWeight) * (mHigh' - mLow') := by
    have hcoef : 0 ≤ entryCost + slotWeight := by linarith
    exact mul_le_mul_of_nonneg_left hGap hcoef
  nlinarith [hSquare, hLinear, hCapacity]

/-- Clause (iv) of `prop:optcert`, value direction.  Raising every agent's
premium changes the certified objective by an amount monotone in the cap on the
positive caps, hence weakly lowers the optimal published cap. -/
theorem certifiedNetSurplus_maximizer_antitone_in_premium
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight : ℝ}
    {premiumLow premiumHigh entryCost capacity : ι → ℝ}
    {capLow capHigh : ℝ}
    (hWeight : 0 ≤ slotWeight)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hLow : ∀ i, 0 ≤ premiumLow i)
    (hOrder : ∀ i, premiumLow i ≤ premiumHigh i)
    (hLowMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight premiumLow
        entryCost capacity) (Set.Ioi 0) capLow)
    (hHighMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight premiumHigh
        entryCost capacity) (Set.Ioi 0) capHigh)
    (hLowMem : capLow ∈ Set.Ioi (0 : ℝ)) (hHighMem : capHigh ∈ Set.Ioi (0 : ℝ))
    (hLowUnique : ∀ z ∈ Set.Ioi (0 : ℝ),
      IsMaxOn (certifiedNetSurplus strictPriorityWelfare slotWeight premiumLow
        entryCost capacity) (Set.Ioi 0) z → z = capLow) :
    capHigh ≤ capLow := by
  refine isMaxOn_le_of_antitone_difference hLowMax hHighMax hLowMem hHighMem
    ?_ hLowUnique
  intro a ha b hb hab
  set term : ι → ℝ → ℝ := fun i cap =>
    agentRacingBurden slotWeight (premiumHigh i) (entryCost i) (capacity i)
        cap -
      agentRacingBurden slotWeight (premiumLow i) (entryCost i) (capacity i)
        cap with hterm
  have hburden : ∀ i, term i a ≤ term i b := fun i =>
    agentRacingBurden_difference_monotoneOn_in_premium hWeight (hEntryCost i)
      (hCapacity i) (hLow i) (hOrder i) (Set.mem_Ici.mpr (le_of_lt ha))
      (Set.mem_Ici.mpr (le_of_lt hb)) hab
  have hsum : ∑ i, term i a ≤ ∑ i, term i b :=
    Finset.sum_le_sum fun i _ => hburden i
  simp only [hterm] at hsum
  simp only [certifiedNetSurplus, racingBurden]
  have hexpand : ∀ cap : ℝ,
      (strictPriorityWelfare - smoothingConcession slotWeight cap -
          ∑ i, agentRacingBurden slotWeight (premiumHigh i) (entryCost i)
            (capacity i) cap) -
        (strictPriorityWelfare - smoothingConcession slotWeight cap -
          ∑ i, agentRacingBurden slotWeight (premiumLow i) (entryCost i)
            (capacity i) cap) =
      -∑ i, (agentRacingBurden slotWeight (premiumHigh i) (entryCost i)
          (capacity i) cap -
        agentRacingBurden slotWeight (premiumLow i) (entryCost i)
          (capacity i) cap) := by
    intro cap
    rw [Finset.sum_sub_distrib]
    ring
  rw [hexpand a, hexpand b]
  linarith

/-- Clause (iv) of `prop:optcert`, reserve direction.  Raising the reserve
lowers every premium, so the optimal published cap weakly rises. -/
theorem certifiedNetSurplus_maximizer_monotone_in_reserve
    {ι : Type*} [Fintype ι]
    {strictPriorityWelfare slotWeight reserveLow reserveHigh : ℝ}
    {value entryCost capacity : ι → ℝ}
    {capLow capHigh : ℝ}
    (hWeight : 0 ≤ slotWeight)
    (hEntryCost : ∀ i, 0 ≤ entryCost i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hReserve : reserveLow ≤ reserveHigh)
    (hEligible : ∀ i, reserveHigh ≤ value i)
    (hHighReserveMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        (fun i => value i - reserveHigh) entryCost capacity) (Set.Ioi 0)
      capHigh)
    (hLowReserveMax : IsMaxOn
      (certifiedNetSurplus strictPriorityWelfare slotWeight
        (fun i => value i - reserveLow) entryCost capacity) (Set.Ioi 0)
      capLow)
    (hHighMem : capHigh ∈ Set.Ioi (0 : ℝ)) (hLowMem : capLow ∈ Set.Ioi (0 : ℝ))
    (hHighUnique : ∀ z ∈ Set.Ioi (0 : ℝ),
      IsMaxOn (certifiedNetSurplus strictPriorityWelfare slotWeight
        (fun i => value i - reserveHigh) entryCost capacity) (Set.Ioi 0) z →
        z = capHigh) :
    capLow ≤ capHigh :=
  certifiedNetSurplus_maximizer_antitone_in_premium hWeight hEntryCost
    hCapacity (fun i => by linarith [hEligible i])
    (fun i => by linarith) hHighReserveMax hLowReserveMax hHighMem hLowMem
    hHighUnique

end

end SmoothingCliff.Racing
