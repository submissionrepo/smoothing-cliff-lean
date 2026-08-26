import Mathlib

/-!
# The aggregate branch of the heterogeneous racing floor

This file isolates the finite-sum argument in the aggregate branch of
`prop:sp_floor_hetero`.  The genuinely game-theoretic inputs are kept as
premises:

* each shifted-copy deviation gives a lower bound on one bidder's gross rent;
* the weak-maximum probabilities have total mass at least one;
* equilibrium payoffs are nonnegative and at most one is positive;
* any positive payoff satisfies the exceptional-rent cap; and
* dissipation is aggregate gross rent minus aggregate payoff.

The theorems below prove exactly what follows from those inputs.  In
particular, they do not claim to establish the mixed-equilibrium support or
deviation arguments that produce the premises.
-/

namespace SmoothingCliff.Racing

open scoped BigOperators

noncomputable section

/-- The exceptional-rent cap printed in `prop:sp_floor_hetero`. -/
def heterogeneousExceptionalRentCap
    (slotWeight marginalCost topPremium secondPremium : ℝ) : ℝ :=
  marginalCost * topPremium +
    (slotWeight + marginalCost) * topPremium *
      (topPremium - secondPremium) / secondPremium

/-- The aggregate exceptional-rent branch of the heterogeneous dissipation
floor, including the positive part printed in the paper. -/
def heterogeneousAggregateFloor {ι : Type*} [Fintype ι]
    (slotWeight marginalCost minimumPremium topPremium secondPremium : ℝ) : ℝ :=
  max 0
    ((slotWeight - (Fintype.card ι : ℝ) * marginalCost) * minimumPremium -
      heterogeneousExceptionalRentCap
        slotWeight marginalCost topPremium secondPremium)

/-- The printed exceptional-rent cap is nonnegative on the paper's domain. -/
theorem heterogeneousExceptionalRentCap_nonneg
    {slotWeight marginalCost topPremium secondPremium : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 ≤ marginalCost)
    (hSecond : 0 < secondPremium) (hOrder : secondPremium ≤ topPremium) :
    0 ≤ heterogeneousExceptionalRentCap
      slotWeight marginalCost topPremium secondPremium := by
  have hTop : 0 ≤ topPremium := le_trans hSecond.le hOrder
  have hGap : 0 ≤ topPremium - secondPremium := sub_nonneg.mpr hOrder
  have hRatio : 0 ≤ (topPremium - secondPremium) / secondPremium :=
    div_nonneg hGap hSecond.le
  unfold heterogeneousExceptionalRentCap
  positivity

/-- The terminal algebra in the exceptional-rent argument.  The variable
`supportHeight` records the upper-support quantity bounded by the preceding
equilibrium deviation argument; that argument is deliberately an explicit
premise here. -/
theorem exceptionalRent_intermediate_le_cap
    {slotWeight marginalCost topPremium secondPremium supportHeight : ℝ}
    (hCost : 0 < marginalCost) (hSecond : 0 < secondPremium)
    (hOrder : secondPremium ≤ topPremium)
    (hSupport :
      supportHeight ≤
        topPremium + slotWeight * topPremium / marginalCost) :
    marginalCost * topPremium +
        marginalCost * supportHeight *
          (topPremium - secondPremium) / secondPremium ≤
      heterogeneousExceptionalRentCap
        slotWeight marginalCost topPremium secondPremium := by
  have hScaled :
      marginalCost * supportHeight ≤
        (slotWeight + marginalCost) * topPremium := by
    have h := mul_le_mul_of_nonneg_left hSupport hCost.le
    calc
      marginalCost * supportHeight ≤
          marginalCost *
            (topPremium + slotWeight * topPremium / marginalCost) := h
      _ = (slotWeight + marginalCost) * topPremium := by
        field_simp
        ring
  have hRatio : 0 ≤ (topPremium - secondPremium) / secondPremium :=
    div_nonneg (sub_nonneg.mpr hOrder) hSecond.le
  have hProduct := mul_le_mul_of_nonneg_right hScaled hRatio
  unfold heterogeneousExceptionalRentCap
  calc
    marginalCost * topPremium +
          marginalCost * supportHeight *
            (topPremium - secondPremium) / secondPremium =
        marginalCost * topPremium +
          (marginalCost * supportHeight) *
            ((topPremium - secondPremium) / secondPremium) := by ring
    _ ≤ marginalCost * topPremium +
          ((slotWeight + marginalCost) * topPremium) *
            ((topPremium - secondPremium) / secondPremium) := by
      simpa [add_comm] using
        (add_le_add_left hProduct (marginalCost * topPremium))
    _ = marginalCost * topPremium +
          (slotWeight + marginalCost) * topPremium *
            (topPremium - secondPremium) / secondPremium := by ring

/-- At a common-premium profile the heterogeneity correction vanishes. -/
theorem heterogeneousExceptionalRentCap_commonValue
    {slotWeight marginalCost premium : ℝ} :
    heterogeneousExceptionalRentCap
        slotWeight marginalCost premium premium =
      marginalCost * premium := by
  simp [heterogeneousExceptionalRentCap]

/-- At most one coordinate of `payoff` is strictly positive. -/
def AtMostOnePositive {ι : Type*} (payoff : ι → ℝ) : Prop :=
  ∀ ⦃i j⦄, 0 < payoff i → 0 < payoff j → i = j

/-- Nonnegative payoffs with at most one positive coordinate have aggregate
payoff at most the cap on that exceptional coordinate. -/
theorem sum_payoff_le_exceptionalCap
    {ι : Type*} [Fintype ι] {payoff : ι → ℝ} {cap : ℝ}
    (hCapNonneg : 0 ≤ cap)
    (hPayoffNonneg : ∀ i, 0 ≤ payoff i)
    (hAtMostOne : AtMostOnePositive payoff)
    (hPositiveCap : ∀ i, 0 < payoff i → payoff i ≤ cap) :
    ∑ i, payoff i ≤ cap := by
  classical
  by_cases hPositive : ∃ i, 0 < payoff i
  · obtain ⟨exceptional, hExceptional⟩ := hPositive
    have hZero : ∀ i, i ≠ exceptional → payoff i = 0 := by
      intro i hi
      have hNotPositive : ¬ 0 < payoff i := by
        intro hiPositive
        exact hi (hAtMostOne hiPositive hExceptional)
      exact le_antisymm (le_of_not_gt hNotPositive) (hPayoffNonneg i)
    calc
      ∑ i, payoff i = payoff exceptional := by
        apply Finset.sum_eq_single exceptional
        · intro i _ hi
          exact hZero i hi
        · simp
      _ ≤ cap := hPositiveCap exceptional hExceptional
  · have hZero : ∀ i, payoff i = 0 := by
      intro i
      have hNotPositive : ¬ 0 < payoff i := by
        intro hi
        exact hPositive ⟨i, hi⟩
      exact le_antisymm (le_of_not_gt hNotPositive) (hPayoffNonneg i)
    simpa [hZero] using hCapNonneg

/-- Summing the per-bidder shifted-copy inequalities and using that weak
maxima carry total probability mass at least one yields the aggregate gross
rent floor.  The functions `weakMaximumMass` and `grossRent` are abstract so
that the deviation and probability arguments remain visible as premises. -/
theorem aggregateGrossRent_ge_shiftedCopyFloor
    {ι : Type*} [Fintype ι]
    {slotWeight marginalCost minimumPremium : ℝ}
    (hWeight : 0 ≤ slotWeight) (hMinimum : 0 ≤ minimumPremium)
    (weakMaximumMass grossRent : ι → ℝ)
    (hShiftedCopy : ∀ i,
      slotWeight * minimumPremium * weakMaximumMass i -
          marginalCost * minimumPremium ≤
        grossRent i)
    (hWeakMaximumMass : 1 ≤ ∑ i, weakMaximumMass i) :
    (slotWeight - (Fintype.card ι : ℝ) * marginalCost) * minimumPremium ≤
      ∑ i, grossRent i := by
  have hSum :
      ∑ i,
          (slotWeight * minimumPremium * weakMaximumMass i -
            marginalCost * minimumPremium) ≤
        ∑ i, grossRent i :=
    Finset.sum_le_sum fun i _ => hShiftedCopy i
  have hMassScaled :
      slotWeight * minimumPremium ≤
        slotWeight * minimumPremium * ∑ i, weakMaximumMass i := by
    simpa using
      (mul_le_mul_of_nonneg_left hWeakMaximumMass
        (mul_nonneg hWeight hMinimum))
  have hSumIdentity :
      ∑ i,
          (slotWeight * minimumPremium * weakMaximumMass i -
            marginalCost * minimumPremium) =
        slotWeight * minimumPremium * ∑ i, weakMaximumMass i -
          (Fintype.card ι : ℝ) * marginalCost * minimumPremium := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
    ring_nf
  rw [hSumIdentity] at hSum
  nlinarith

/-- Gross rent minus aggregate payoff inherits the positive part of the
gross-rent floor net of the exceptional payoff cap. -/
theorem dissipation_ge_positivePart_of_grossRent_payoff
    {grossRent aggregatePayoff dissipation grossFloor exceptionalCap : ℝ}
    (hGrossRent : grossFloor ≤ grossRent)
    (hAggregatePayoff : aggregatePayoff ≤ exceptionalCap)
    (hIdentity : dissipation = grossRent - aggregatePayoff)
    (hDissipationNonneg : 0 ≤ dissipation) :
    max 0 (grossFloor - exceptionalCap) ≤ dissipation := by
  rw [max_le_iff]
  constructor
  · exact hDissipationNonneg
  · linarith

/-- **Aggregate branch of `prop:sp_floor_hetero`.**  From the explicit
shifted-copy, weak-maximum, payoff-classification, exceptional-cap, and
accounting premises, dissipation is at least

`[(w₁ - nκ)d_(n) - U_exc]_+`.

This theorem packages the complete finite-sum implication while leaving the
mixed-equilibrium arguments that establish its premises outside its scope. -/
theorem heterogeneousAggregateDissipation_floor
    {ι : Type*} [Fintype ι]
    {slotWeight marginalCost minimumPremium topPremium secondPremium : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 ≤ marginalCost)
    (hMinimum : 0 ≤ minimumPremium)
    (hSecond : 0 < secondPremium) (hOrder : secondPremium ≤ topPremium)
    (weakMaximumMass grossRent payoff : ι → ℝ)
    (dissipation : ℝ)
    (hShiftedCopy : ∀ i,
      slotWeight * minimumPremium * weakMaximumMass i -
          marginalCost * minimumPremium ≤
        grossRent i)
    (hWeakMaximumMass : 1 ≤ ∑ i, weakMaximumMass i)
    (hPayoffNonneg : ∀ i, 0 ≤ payoff i)
    (hAtMostOne : AtMostOnePositive payoff)
    (hPositivePayoffCap : ∀ i, 0 < payoff i →
      payoff i ≤ heterogeneousExceptionalRentCap
        slotWeight marginalCost topPremium secondPremium)
    (hDissipationIdentity :
      dissipation = ∑ i, grossRent i - ∑ i, payoff i)
    (hDissipationNonneg : 0 ≤ dissipation) :
    heterogeneousAggregateFloor (ι := ι)
        slotWeight marginalCost minimumPremium topPremium secondPremium ≤
      dissipation := by
  have hGrossRent := aggregateGrossRent_ge_shiftedCopyFloor
    hWeight hMinimum weakMaximumMass grossRent hShiftedCopy hWeakMaximumMass
  have hCapNonneg := heterogeneousExceptionalRentCap_nonneg
    hWeight hCost hSecond hOrder
  have hAggregatePayoff := sum_payoff_le_exceptionalCap
    hCapNonneg hPayoffNonneg hAtMostOne hPositivePayoffCap
  unfold heterogeneousAggregateFloor
  exact dissipation_ge_positivePart_of_grossRent_payoff
    hGrossRent hAggregatePayoff hDissipationIdentity hDissipationNonneg

end

end SmoothingCliff.Racing
