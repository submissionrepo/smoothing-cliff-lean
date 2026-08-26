import SmoothingCliff.Frontier.WaterFillingProfileLoss
import SmoothingCliff.Racing.HeterogeneousAggregateFloor
import SmoothingCliff.Racing.HeterogeneousWindowFloor

/-!
# Heterogeneous profilewise dominance from an explicit dissipation floor

This file isolates the deterministic bridge used by `cor:neartie_region`.
The strict-priority side enters through a named, selection-free lower bound on
dissipation.  The water-filling side is evaluated at the same premium profile,
using the exact active-set loss identity from
`Frontier.WaterFillingProfileLoss`.  Thus the comparison does not replace the
equilibrium floor by a worst-case welfare bound.

Two water-filling regimes are covered.  On an interior active set, the loss is
the leader-to-active-mean term minus the active variance term.  If the leader
is capped at the full slot weight, exact mass makes the loss zero.
-/

open scoped BigOperators

namespace SmoothingCliff.Racing

open SmoothingCliff.Frontier

noncomputable section

/-- Premium allocation value, above the common reserve component, produced by
one-slot budget-spending water filling. -/
def oneSlotWaterFillingValue
    {ι : Type*} [Fintype ι]
    (weight slope : NNReal) (premium : ι → ℝ) (threshold : ℝ) : ℝ :=
  ∑ i, premium i * waterFillAt weight slope premium threshold i

/-- The strict-priority premium-value benchmark, above the common reserve
component, at a designated highest-premium bidder. -/
def oneSlotStrictPriorityValue
    {ι : Type*} (weight : NNReal) (premium : ι → ℝ) (leader : ι) : ℝ :=
  (weight : ℝ) * premium leader

/-- The profilewise allocation loss of water filling relative to strict
priority at `leader`. -/
def oneSlotWaterFillingLoss
    {ι : Type*} [Fintype ι]
    (weight slope : NNReal) (premium : ι → ℝ) (threshold : ℝ)
    (leader : ι) : ℝ :=
  oneSlotStrictPriorityValue weight premium leader -
    oneSlotWaterFillingValue weight slope premium threshold

/-- Full allocation value under water filling.  Exact mass makes the reserve
component common across strict priority and water filling. -/
def oneSlotWaterFillingFullValue
    {ι : Type*} [Fintype ι]
    (weight slope : NNReal) (reserve : ℝ) (premium : ι → ℝ)
    (threshold : ℝ) : ℝ :=
  (weight : ℝ) * reserve +
    oneSlotWaterFillingValue weight slope premium threshold

/-- Full strict-priority allocation value at the designated leader. -/
def oneSlotStrictPriorityFullValue
    {ι : Type*}
    (weight : NNReal) (reserve : ℝ) (premium : ι → ℝ) (leader : ι) : ℝ :=
  (weight : ℝ) * reserve +
    oneSlotStrictPriorityValue weight premium leader

/-- Under exact mass, `oneSlotWaterFillingFullValue` is the literal allocation
value of the full values `reserve + premium i`. -/
theorem oneSlotWaterFillingFullValue_eq_sum
    {ι : Type*} [Fintype ι]
    (weight slope : NNReal) (reserve : ℝ) (premium : ι → ℝ)
    (threshold : ℝ)
    (hMass :
      ∑ i, waterFillAt weight slope premium threshold i = (weight : ℝ)) :
    oneSlotWaterFillingFullValue weight slope reserve premium threshold =
      ∑ i, (reserve + premium i) *
        waterFillAt weight slope premium threshold i := by
  unfold oneSlotWaterFillingFullValue oneSlotWaterFillingValue
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hMass]
  ring

/-- The full strict-priority benchmark is the leader's literal full value. -/
theorem oneSlotStrictPriorityFullValue_eq
    {ι : Type*}
    (weight : NNReal) (reserve : ℝ) (premium : ι → ℝ) (leader : ι) :
    oneSlotStrictPriorityFullValue weight reserve premium leader =
      (weight : ℝ) * (reserve + premium leader) := by
  unfold oneSlotStrictPriorityFullValue oneSlotStrictPriorityValue
  ring

/-- The displayed selection-free floor in `prop:sp_floor_hetero`: the maximum
of the aggregate exceptional-rent branch and the corrected shifted-window
branch.  The normalized cost is the paper's
`q = marginalCost / slotWeight`; `varsigma` remains explicit because its
construction from the integer window depth belongs to the racing argument. -/
def heterogeneousDisplayedDissipationFloor
    {ι : Type*} [Fintype ι]
    (slotWeight marginalCost minimumPremium topPremium secondPremium
      varsigma : ℝ) : ℝ :=
  max
    (heterogeneousAggregateFloor (ι := ι) slotWeight marginalCost
      minimumPremium topPremium secondPremium)
    (heterogeneousShiftedWindowFloor slotWeight
      (marginalCost / slotWeight) varsigma
      secondPremium topPremium)

/-- The two public floor branches combine into the displayed selection-free
floor by taking their maximum. -/
theorem heterogeneousDisplayedDissipationFloor_le
    {ι : Type*} [Fintype ι]
    {slotWeight marginalCost minimumPremium topPremium secondPremium
      varsigma dissipation : ℝ}
    (hAggregate :
      heterogeneousAggregateFloor (ι := ι) slotWeight marginalCost
          minimumPremium topPremium secondPremium ≤
        dissipation)
    (hShiftedWindow :
      heterogeneousShiftedWindowFloor slotWeight
          (marginalCost / slotWeight) varsigma
          secondPremium topPremium ≤
        dissipation) :
    heterogeneousDisplayedDissipationFloor (ι := ι) slotWeight marginalCost
        minimumPremium topPremium secondPremium varsigma ≤
      dissipation := by
  exact max_le hAggregate hShiftedWindow

/-- The purely accounting part of the near-tie comparison.  The hypothesis
`floor ≤ dissipation` is the explicit selection-free equilibrium input; it is
not inferred in this file. -/
theorem conditionalNearTieDominance_of_exactLoss_lt_floor
    {strictPriorityNetSurplus strictPriorityValue waterFillingValue
      dissipation floor : ℝ}
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤ strictPriorityValue - dissipation)
    (hSelectionFreeFloor : floor ≤ dissipation)
    (hExactLoss : strictPriorityValue - waterFillingValue < floor) :
    strictPriorityNetSurplus < waterFillingValue := by
  linarith

/-- Quantitative accounting form of the same bridge.  Net-surplus gain is at
least the selection-free floor minus the exact allocation loss. -/
theorem conditionalNearTieGap_ge_floor_sub_exactLoss
    {strictPriorityNetSurplus strictPriorityValue waterFillingValue
      dissipation floor : ℝ}
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤ strictPriorityValue - dissipation)
    (hSelectionFreeFloor : floor ≤ dissipation) :
    floor - (strictPriorityValue - waterFillingValue) ≤
      waterFillingValue - strictPriorityNetSurplus := by
  linarith

/-- Quantitative interior-active-set comparison with an explicit
selection-free floor. -/
theorem heterogeneousNearTieGap_ge_activeFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι)
    (weight slope : NNReal) (premium : ι → ℝ) (threshold : ℝ)
    (leader : ι)
    (hLeader : leader ∈ A)
    (hInside : ∀ i ∈ A,
      0 < (slope : ℝ) * (premium i - threshold) ∧
        (slope : ℝ) * (premium i - threshold) < (weight : ℝ))
    (hOutside : ∀ i ∉ A,
      (slope : ℝ) * (premium i - threshold) ≤ 0)
    (hMass :
      ∑ i, waterFillAt weight slope premium threshold i = (weight : ℝ))
    {strictPriorityNetSurplus dissipation floor : ℝ}
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤
        oneSlotStrictPriorityValue weight premium leader - dissipation)
    (hSelectionFreeFloor : floor ≤ dissipation) :
    floor -
          ((weight : ℝ) * (premium leader - activeMean A premium) -
            (slope : ℝ) *
              ∑ i ∈ A, (premium i - activeMean A premium) ^ 2) ≤
      oneSlotWaterFillingValue weight slope premium threshold -
        strictPriorityNetSurplus := by
  have hLoss := waterFillAt_active_loss_identity
    A weight slope premium threshold leader hLeader hInside hOutside hMass
  have hLoss' :
      oneSlotStrictPriorityValue weight premium leader -
          oneSlotWaterFillingValue weight slope premium threshold =
        (weight : ℝ) * (premium leader - activeMean A premium) -
          (slope : ℝ) *
            ∑ i ∈ A, (premium i - activeMean A premium) ^ 2 := by
    simpa [oneSlotStrictPriorityValue, oneSlotWaterFillingValue] using hLoss
  have hGap := conditionalNearTieGap_ge_floor_sub_exactLoss
    (waterFillingValue :=
      oneSlotWaterFillingValue weight slope premium threshold)
    hStrictPriorityAccounting hSelectionFreeFloor
  rwa [hLoss'] at hGap

/-- **Conditional heterogeneous near-tie bridge, interior branch.**  If the
selection-free dissipation floor exceeds the exact active-set water-filling
loss at this profile, then water filling has strictly higher net surplus than
the strict-priority outcome. -/
theorem heterogeneousNearTieDominance_of_activeFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι)
    (weight slope : NNReal) (premium : ι → ℝ) (threshold : ℝ)
    (leader : ι)
    (hLeader : leader ∈ A)
    (hInside : ∀ i ∈ A,
      0 < (slope : ℝ) * (premium i - threshold) ∧
        (slope : ℝ) * (premium i - threshold) < (weight : ℝ))
    (hOutside : ∀ i ∉ A,
      (slope : ℝ) * (premium i - threshold) ≤ 0)
    (hMass :
      ∑ i, waterFillAt weight slope premium threshold i = (weight : ℝ))
    {strictPriorityNetSurplus dissipation floor : ℝ}
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤
        oneSlotStrictPriorityValue weight premium leader - dissipation)
    (hSelectionFreeFloor : floor ≤ dissipation)
    (hNearTie :
      (weight : ℝ) * (premium leader - activeMean A premium) -
          (slope : ℝ) *
            ∑ i ∈ A, (premium i - activeMean A premium) ^ 2 <
        floor) :
    strictPriorityNetSurplus <
      oneSlotWaterFillingValue weight slope premium threshold := by
  have hGap := heterogeneousNearTieGap_ge_activeFloor
    A weight slope premium threshold leader hLeader hInside hOutside hMass
    hStrictPriorityAccounting hSelectionFreeFloor
  have hPositive :
      0 < floor -
        ((weight : ℝ) * (premium leader - activeMean A premium) -
          (slope : ℝ) *
            ∑ i ∈ A, (premium i - activeMean A premium) ^ 2) :=
    sub_pos.mpr hNearTie
  exact sub_pos.mp (hPositive.trans_le hGap)

/-- Quantitative capped-leader comparison.  Since allocation loss is zero,
the whole selection-free floor appears in the net-surplus gain. -/
theorem heterogeneousNearTieGap_ge_cappedFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight slope : NNReal) (premium : ι → ℝ) (threshold : ℝ)
    (leader : ι)
    (hMass :
      ∑ i, waterFillAt weight slope premium threshold i = (weight : ℝ))
    (hCapped :
      waterFillAt weight slope premium threshold leader = (weight : ℝ))
    {strictPriorityNetSurplus dissipation floor : ℝ}
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤
        oneSlotStrictPriorityValue weight premium leader - dissipation)
    (hSelectionFreeFloor : floor ≤ dissipation) :
    floor ≤ oneSlotWaterFillingValue weight slope premium threshold -
      strictPriorityNetSurplus := by
  have hLoss := waterFillAt_loss_eq_zero_of_capped
    weight slope premium threshold leader hMass hCapped
  have hLoss' :
      oneSlotStrictPriorityValue weight premium leader -
          oneSlotWaterFillingValue weight slope premium threshold = 0 := by
    simpa [oneSlotStrictPriorityValue, oneSlotWaterFillingValue] using hLoss
  have hGap := conditionalNearTieGap_ge_floor_sub_exactLoss
    (waterFillingValue :=
      oneSlotWaterFillingValue weight slope premium threshold)
    hStrictPriorityAccounting hSelectionFreeFloor
  rwa [hLoss', sub_zero] at hGap

/-- **Conditional heterogeneous near-tie bridge, capped branch.**  When the
leader is capped at the full slot weight, exact mass makes water-filling loss
zero.  Hence every strictly positive selection-free dissipation floor yields
strict dominance. -/
theorem heterogeneousNearTieDominance_of_cappedFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight slope : NNReal) (premium : ι → ℝ) (threshold : ℝ)
    (leader : ι)
    (hMass :
      ∑ i, waterFillAt weight slope premium threshold i = (weight : ℝ))
    (hCapped :
      waterFillAt weight slope premium threshold leader = (weight : ℝ))
    {strictPriorityNetSurplus dissipation floor : ℝ}
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤
        oneSlotStrictPriorityValue weight premium leader - dissipation)
    (hSelectionFreeFloor : floor ≤ dissipation)
    (hFloorPositive : 0 < floor) :
    strictPriorityNetSurplus <
      oneSlotWaterFillingValue weight slope premium threshold := by
  have hGap := heterogeneousNearTieGap_ge_cappedFloor
    weight slope premium threshold leader hMass hCapped
    hStrictPriorityAccounting hSelectionFreeFloor
  exact sub_pos.mp (hFloorPositive.trans_le hGap)

/-- Quantitative interior-active-set form of `cor:neartie_region`, with the
paper's displayed heterogeneous floor rather than an unnamed scalar bound. -/
theorem heterogeneousNearTieGap_ge_activeDisplayedFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι)
    (weight slope : NNReal) (reserve : ℝ) (premium : ι → ℝ)
    (threshold : ℝ)
    (leader : ι)
    (hLeader : leader ∈ A)
    (hInside : ∀ i ∈ A,
      0 < (slope : ℝ) * (premium i - threshold) ∧
        (slope : ℝ) * (premium i - threshold) < (weight : ℝ))
    (hOutside : ∀ i ∉ A,
      (slope : ℝ) * (premium i - threshold) ≤ 0)
    (hMass :
      ∑ i, waterFillAt weight slope premium threshold i = (weight : ℝ))
    {marginalCost minimumPremium topPremium secondPremium varsigma
      strictPriorityNetSurplus dissipation : ℝ}
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤
        oneSlotStrictPriorityFullValue weight reserve premium leader -
          dissipation)
    (hSelectionFreeFloor :
      heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
          marginalCost minimumPremium topPremium secondPremium varsigma ≤
        dissipation) :
    heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
          marginalCost minimumPremium topPremium secondPremium varsigma -
        ((weight : ℝ) * (premium leader - activeMean A premium) -
          (slope : ℝ) *
            ∑ i ∈ A, (premium i - activeMean A premium) ^ 2) ≤
      oneSlotWaterFillingFullValue weight slope reserve premium threshold -
        strictPriorityNetSurplus := by
  have hNormalizedAccounting :
      strictPriorityNetSurplus - (weight : ℝ) * reserve ≤
        oneSlotStrictPriorityValue weight premium leader - dissipation := by
    unfold oneSlotStrictPriorityFullValue at hStrictPriorityAccounting
    linarith
  have hGap := heterogeneousNearTieGap_ge_activeFloor
    A weight slope premium threshold leader hLeader hInside hOutside hMass
    hNormalizedAccounting hSelectionFreeFloor
  unfold oneSlotWaterFillingFullValue
  linarith

/-- Strict interior-active-set dominance whenever the displayed floor exceeds
the same-profile exact water-filling loss. -/
theorem heterogeneousNearTieDominance_of_activeDisplayedFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι)
    (weight slope : NNReal) (reserve : ℝ) (premium : ι → ℝ)
    (threshold : ℝ)
    (leader : ι)
    (hLeader : leader ∈ A)
    (hInside : ∀ i ∈ A,
      0 < (slope : ℝ) * (premium i - threshold) ∧
        (slope : ℝ) * (premium i - threshold) < (weight : ℝ))
    (hOutside : ∀ i ∉ A,
      (slope : ℝ) * (premium i - threshold) ≤ 0)
    (hMass :
      ∑ i, waterFillAt weight slope premium threshold i = (weight : ℝ))
    {marginalCost minimumPremium topPremium secondPremium varsigma
      strictPriorityNetSurplus dissipation : ℝ}
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤
        oneSlotStrictPriorityFullValue weight reserve premium leader -
          dissipation)
    (hSelectionFreeFloor :
      heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
          marginalCost minimumPremium topPremium secondPremium varsigma ≤
        dissipation)
    (hNearTie :
      (weight : ℝ) * (premium leader - activeMean A premium) -
          (slope : ℝ) *
            ∑ i ∈ A, (premium i - activeMean A premium) ^ 2 <
        heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
          marginalCost minimumPremium topPremium secondPremium varsigma) :
    strictPriorityNetSurplus <
      oneSlotWaterFillingFullValue weight slope reserve premium threshold := by
  have hGap := heterogeneousNearTieGap_ge_activeDisplayedFloor
    A weight slope reserve premium threshold leader hLeader hInside hOutside hMass
    hStrictPriorityAccounting hSelectionFreeFloor
  have hPositive :
      0 < heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
          marginalCost minimumPremium topPremium secondPremium varsigma -
        ((weight : ℝ) * (premium leader - activeMean A premium) -
          (slope : ℝ) *
            ∑ i ∈ A, (premium i - activeMean A premium) ^ 2) :=
    sub_pos.mpr hNearTie
  have hFullPositive :
      0 < oneSlotWaterFillingFullValue weight slope reserve premium threshold -
        strictPriorityNetSurplus :=
    hPositive.trans_le hGap
  exact sub_pos.mp hFullPositive

/-- Quantitative capped-leader form of `cor:neartie_region`. -/
theorem heterogeneousNearTieGap_ge_cappedDisplayedFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight slope : NNReal) (reserve : ℝ) (premium : ι → ℝ)
    (threshold : ℝ)
    (leader : ι)
    (hMass :
      ∑ i, waterFillAt weight slope premium threshold i = (weight : ℝ))
    (hCapped :
      waterFillAt weight slope premium threshold leader = (weight : ℝ))
    {marginalCost minimumPremium topPremium secondPremium varsigma
      strictPriorityNetSurplus dissipation : ℝ}
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤
        oneSlotStrictPriorityFullValue weight reserve premium leader -
          dissipation)
    (hSelectionFreeFloor :
      heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
          marginalCost minimumPremium topPremium secondPremium varsigma ≤
        dissipation) :
    heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
        marginalCost minimumPremium topPremium secondPremium varsigma ≤
      oneSlotWaterFillingFullValue weight slope reserve premium threshold -
        strictPriorityNetSurplus := by
  have hNormalizedAccounting :
      strictPriorityNetSurplus - (weight : ℝ) * reserve ≤
        oneSlotStrictPriorityValue weight premium leader - dissipation := by
    unfold oneSlotStrictPriorityFullValue at hStrictPriorityAccounting
    linarith
  have hGap := heterogeneousNearTieGap_ge_cappedFloor
    weight slope premium threshold leader hMass hCapped
    hNormalizedAccounting hSelectionFreeFloor
  unfold oneSlotWaterFillingFullValue
  linarith

/-- Capped-leader strict dominance.  The water-filling loss is zero, so
positivity of the displayed heterogeneous floor is the exact condition. -/
theorem heterogeneousNearTieDominance_of_cappedDisplayedFloor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight slope : NNReal) (reserve : ℝ) (premium : ι → ℝ)
    (threshold : ℝ)
    (leader : ι)
    (hMass :
      ∑ i, waterFillAt weight slope premium threshold i = (weight : ℝ))
    (hCapped :
      waterFillAt weight slope premium threshold leader = (weight : ℝ))
    {marginalCost minimumPremium topPremium secondPremium varsigma
      strictPriorityNetSurplus dissipation : ℝ}
    (hStrictPriorityAccounting :
      strictPriorityNetSurplus ≤
        oneSlotStrictPriorityFullValue weight reserve premium leader -
          dissipation)
    (hSelectionFreeFloor :
      heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
          marginalCost minimumPremium topPremium secondPremium varsigma ≤
        dissipation)
    (hFloorPositive :
      0 < heterogeneousDisplayedDissipationFloor (ι := ι) (weight : ℝ)
        marginalCost minimumPremium topPremium secondPremium varsigma) :
    strictPriorityNetSurplus <
      oneSlotWaterFillingFullValue weight slope reserve premium threshold := by
  have hGap := heterogeneousNearTieGap_ge_cappedDisplayedFloor
    weight slope reserve premium threshold leader hMass hCapped
    hStrictPriorityAccounting hSelectionFreeFloor
  have hFullPositive :
      0 < oneSlotWaterFillingFullValue weight slope reserve premium threshold -
        strictPriorityNetSurplus :=
    hFloorPositive.trans_le hGap
  exact sub_pos.mp hFullPositive

end

end SmoothingCliff.Racing
