import SmoothingCliff.Racing.HeterogeneousSelectionFreeFloor
import SmoothingCliff.Racing.HeterogeneousNearTie

/-!
# Selection-free heterogeneous near-tie dominance

This file closes the last logical gap in the profilewise comparison.  The
deterministic water-filling loss identities in `HeterogeneousNearTie` are
combined here with the equilibrium-uniform dissipation theorem, so the final
dominance statements no longer assume an unnamed external floor.
-/

namespace SmoothingCliff.Racing

open SmoothingCliff.Frontier
open scoped BigOperators ENNReal NNReal

noncomputable section

/-- **Selection-free heterogeneous near-tie dominance, interior branch.**
At every heterogeneous mixed Nash equilibrium, the exact same-profile
water-filling loss is dominated by the displayed aggregate/window floor under
the stated near-tie inequality. -/
theorem heterogeneousNash_nearTieDominance_active
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι)
    (weight slope : NNReal) (reserve : ℝ) (premium : ι → ℝ)
    (threshold : ℝ)
    (top second bottom : ι)
    (hLeader : top ∈ A)
    (hInside : ∀ i ∈ A,
      0 < (slope : ℝ) * (premium i - threshold) ∧
        (slope : ℝ) * (premium i - threshold) < (weight : ℝ))
    (hOutside : ∀ i ∉ A,
      (slope : ℝ) * (premium i - threshold) ≤ 0)
    (hMass :
      ∑ i, waterFillAt weight slope premium threshold i = (weight : ℝ))
    {marginalCost strictPriorityNetSurplus : ℝ}
    (hweight : 0 < (weight : ℝ)) (hcost : 0 < marginalCost)
    (hpremium : ∀ i, 0 ≤ premium i)
    (hcard : 2 ≤ Fintype.card ι)
    (strategy : ι → BorelMixedStrategy)
    (hnash : IsHeterogeneousBorelMixedNash (weight : ℝ) marginalCost strategy
      hcard premium)
    (hsecondTop : second ≠ top)
    (htop : ∀ i, premium i ≤ premium top)
    (hsecond : ∀ i, i ≠ top → premium i ≤ premium second)
    (hsecondPositive : 0 < premium second)
    (hbottom : ∀ i, premium bottom ≤ premium i)
    (depth : ℕ)
    (hdepth : (depth : ℝ) * (marginalCost / (weight : ℝ)) ≤ 1)
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤
        oneSlotStrictPriorityFullValue weight reserve premium top -
          heterogeneousExpectedDissipation marginalCost strategy)
    (hNearTie :
      (weight : ℝ) * (premium top - activeMean A premium) -
          (slope : ℝ) *
            ∑ i ∈ A, (premium i - activeMean A premium) ^ 2 <
        heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
          marginalCost (premium bottom) (premium top) (premium second)
          ((depth : ℝ) * (marginalCost / (weight : ℝ)))) :
    strictPriorityNetSurplus <
      oneSlotWaterFillingFullValue weight slope reserve premium threshold := by
  have hFloor :
      heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
          marginalCost (premium bottom) (premium top) (premium second)
          ((depth : ℝ) * (marginalCost / (weight : ℝ))) ≤
        heterogeneousExpectedDissipation marginalCost strategy := by
    simpa [heterogeneousDisplayedDissipationFloor] using
      (heterogeneousNash_selectionFreeFloor hweight hcost strategy hcard
        premium hpremium hnash top second bottom hsecondTop htop hsecond
        hsecondPositive hbottom depth hdepth)
  exact heterogeneousNearTieDominance_of_activeDisplayedFloor
    A weight slope reserve premium threshold top hLeader hInside hOutside hMass
    hStrictPriorityAccounting hFloor hNearTie

/-- **Selection-free heterogeneous near-tie dominance, capped branch.**  If
the leader receives the full slot weight, water filling has zero allocation
loss; positivity of the displayed floor therefore gives strict dominance at
every heterogeneous mixed Nash equilibrium. -/
theorem heterogeneousNash_nearTieDominance_capped
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight slope : NNReal) (reserve : ℝ) (premium : ι → ℝ)
    (threshold : ℝ)
    (top second bottom : ι)
    (hMass :
      ∑ i, waterFillAt weight slope premium threshold i = (weight : ℝ))
    (hCapped :
      waterFillAt weight slope premium threshold top = (weight : ℝ))
    {marginalCost strictPriorityNetSurplus : ℝ}
    (hweight : 0 < (weight : ℝ)) (hcost : 0 < marginalCost)
    (hpremium : ∀ i, 0 ≤ premium i)
    (hcard : 2 ≤ Fintype.card ι)
    (strategy : ι → BorelMixedStrategy)
    (hnash : IsHeterogeneousBorelMixedNash (weight : ℝ) marginalCost strategy
      hcard premium)
    (hsecondTop : second ≠ top)
    (htop : ∀ i, premium i ≤ premium top)
    (hsecond : ∀ i, i ≠ top → premium i ≤ premium second)
    (hsecondPositive : 0 < premium second)
    (hbottom : ∀ i, premium bottom ≤ premium i)
    (depth : ℕ)
    (hdepth : (depth : ℝ) * (marginalCost / (weight : ℝ)) ≤ 1)
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤
        oneSlotStrictPriorityFullValue weight reserve premium top -
          heterogeneousExpectedDissipation marginalCost strategy)
    (hFloorPositive :
      0 < heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
        marginalCost (premium bottom) (premium top) (premium second)
        ((depth : ℝ) * (marginalCost / (weight : ℝ)))) :
    strictPriorityNetSurplus <
      oneSlotWaterFillingFullValue weight slope reserve premium threshold := by
  have hFloor :
      heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
          marginalCost (premium bottom) (premium top) (premium second)
          ((depth : ℝ) * (marginalCost / (weight : ℝ))) ≤
        heterogeneousExpectedDissipation marginalCost strategy := by
    simpa [heterogeneousDisplayedDissipationFloor] using
      (heterogeneousNash_selectionFreeFloor hweight hcost strategy hcard
        premium hpremium hnash top second bottom hsecondTop htop hsecond
        hsecondPositive hbottom depth hdepth)
  exact heterogeneousNearTieDominance_of_cappedDisplayedFloor
    weight slope reserve premium threshold top hMass hCapped
    hStrictPriorityAccounting hFloor hFloorPositive

end

end SmoothingCliff.Racing
