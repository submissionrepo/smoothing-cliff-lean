import SmoothingCliff.Racing.HeterogeneousExistenceBridge
import SmoothingCliff.Racing.HeterogeneousAggregateBridge
import SmoothingCliff.Racing.HeterogeneousWindowBridge

/-!
# The heterogeneous selection-free dissipation theorem

This file combines the independent equilibrium arguments: existence on the
unbounded action space, support classification, the exceptional-rent cap, the
aggregate shifted-copy bound, and the shifted-window bound.  The top, runner-up,
and bottom bidders are supplied as order-statistic witnesses.
-/

namespace SmoothingCliff.Racing

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

variable {ι : Type*}

/-- The largest opponent premium equals a supplied order statistic whenever
that bidder is present among the opponents and dominates all of them. -/
theorem opponentTopPremium_eq_of_witness
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i witness : ι) (hwitness : witness ≠ i)
    (hupper : ∀ j, j ≠ i → premium j ≤ premium witness) :
    opponentTopPremium hcard premium i = premium witness := by
  apply le_antisymm
  · unfold opponentTopPremium
    apply Finset.sup'_le
    intro j hj
    exact hupper j (Finset.ne_of_mem_erase hj)
  · exact opponent_premium_le_topPremium hcard premium i witness hwitness

/-- The shifted-window floor is monotone in its bracket when its prefactor is
nonnegative. -/
theorem heterogeneousShiftedWindowFloor_mono_bracket
    {slotWeight q varsigma own₁ opponent₁ own₂ opponent₂ : ℝ}
    (hweight : 0 ≤ slotWeight) (hvarsigma : 0 ≤ varsigma)
    (hbracket :
      heterogeneousShiftedWindowBracket q varsigma own₁ opponent₁ ≤
        heterogeneousShiftedWindowBracket q varsigma own₂ opponent₂) :
    heterogeneousShiftedWindowFloor slotWeight q varsigma own₁ opponent₁ ≤
      heterogeneousShiftedWindowFloor slotWeight q varsigma own₂ opponent₂ := by
  unfold heterogeneousShiftedWindowFloor
  exact mul_le_mul_of_nonneg_left (max_le_max hbracket le_rfl) (by positivity)

/-- Every equilibrium obeys both displayed heterogeneous dissipation floors.
The assumptions identify bidders attaining the largest, second-largest, and
smallest premia. -/
theorem heterogeneousNash_selectionFreeFloor
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hpremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium)
    (top second bottom : ι) (hsecondTop : second ≠ top)
    (htop : ∀ i, premium i ≤ premium top)
    (hsecond : ∀ i, i ≠ top → premium i ≤ premium second)
    (hsecondPositive : 0 < premium second)
    (hbottom : ∀ i, premium bottom ≤ premium i)
    (depth : ℕ)
    (hdepth : (depth : ℝ) * (marginalCost / slotWeight) ≤ 1) :
    max
        (heterogeneousAggregateFloor (ι := ι) slotWeight marginalCost
          (premium bottom) (premium top) (premium second))
        (heterogeneousShiftedWindowFloor slotWeight
          (marginalCost / slotWeight)
          ((depth : ℝ) * (marginalCost / slotWeight))
          (premium second) (premium top)) ≤
      heterogeneousExpectedDissipation marginalCost strategy := by
  have haggregate :
      heterogeneousAggregateFloor (ι := ι) slotWeight marginalCost
          (premium bottom) (premium top) (premium second) ≤
        heterogeneousExpectedDissipation marginalCost strategy := by
    apply heterogeneousNash_aggregateFloor_le_dissipation
      slotWeight marginalCost (premium bottom) (premium top) (premium second)
      strategy hcard premium hweight.le hcost.le (hpremium bottom)
      hbottom hsecondPositive (htop second) hnash
    intro p hpositive
    exact heterogeneousMixedNash_positivePayoff_le_globalExceptionalRentCap
      hweight.le hcost strategy hcard premium hpremium hnash top second
      hsecondTop htop hsecondPositive p hpositive
  have hnonneg : ∀ i, 0 ≤ heterogeneousExpectedPayoff slotWeight marginalCost
      strategy hcard premium i :=
    heterogeneousMixedNash_payoff_nonneg hweight.le strategy hcard premium
      hpremium hnash
  have hatMost := heterogeneousMixedNash_atMostOnePositive hweight.le hcost.le
    strategy hcard premium hpremium hnash
  have hzeroTopTwo :
      heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
          premium second = 0 ∨
        heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
          premium top = 0 := by
    by_cases hsecondZero : heterogeneousExpectedPayoff slotWeight marginalCost
        strategy hcard premium second = 0
    · exact Or.inl hsecondZero
    · right
      apply le_antisymm
      · apply le_of_not_gt
        intro htopPositive
        have hsecondPositivePayoff : 0 <
            heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
              premium second :=
          lt_of_le_of_ne (hnonneg second) (Ne.symm hsecondZero)
        exact hsecondTop (hatMost hsecondPositivePayoff htopPositive)
      · exact hnonneg top
  have hopponentSecond :
      opponentTopPremium hcard premium second = premium top := by
    apply opponentTopPremium_eq_of_witness hcard premium second top
      hsecondTop.symm
    intro j hji
    exact htop j
  have hopponentTop :
      opponentTopPremium hcard premium top = premium second := by
    apply opponentTopPremium_eq_of_witness hcard premium top second
      hsecondTop
    exact hsecond
  have hwindow :
      heterogeneousShiftedWindowFloor slotWeight
          (marginalCost / slotWeight)
          ((depth : ℝ) * (marginalCost / slotWeight))
          (premium second) (premium top) ≤
        heterogeneousExpectedDissipation marginalCost strategy := by
    rcases hzeroTopTwo with hzeroSecond | hzeroTop
    · simpa [hopponentSecond] using
        zeroPayoff_heterogeneousNash_shiftedWindowFloor_le_dissipation
          slotWeight marginalCost strategy hcard premium hpremium second depth
          hweight hcost.le hnash hzeroSecond
    · have htopFloor :=
        zeroPayoff_heterogeneousNash_shiftedWindowFloor_le_dissipation
          slotWeight marginalCost strategy hcard premium hpremium top depth
          hweight hcost.le hnash hzeroTop
      rw [hopponentTop] at htopFloor
      have hbracket := runner_shiftedWindowBracket_le_leader
        (q := marginalCost / slotWeight)
        (varsigma := (depth : ℝ) * (marginalCost / slotWeight))
        (leader := premium top) (runnerUp := premium second)
        (div_nonneg hcost.le hweight.le)
        hdepth
        (htop second)
      exact (heterogeneousShiftedWindowFloor_mono_bracket hweight.le
        (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hcost.le hweight.le))
        hbracket).trans htopFloor
  exact max_le haggregate hwindow

/-- The proposition-level package: an independent Borel mixed equilibrium
exists, every equilibrium has at most one positive-payoff bidder, and every
equilibrium obeys the aggregate/window maximum above. -/
theorem heterogeneousSelectionFreeDissipation
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    (premium : ι → ℝ) (hpremium : ∀ i, 0 ≤ premium i)
    (hcard : 2 ≤ Fintype.card ι)
    (top second bottom : ι) (hsecondTop : second ≠ top)
    (htop : ∀ i, premium i ≤ premium top)
    (hsecond : ∀ i, i ≠ top → premium i ≤ premium second)
    (hsecondPositive : 0 < premium second)
    (hbottom : ∀ i, premium bottom ≤ premium i)
    (depth : ℕ)
    (hdepth : (depth : ℝ) * (marginalCost / slotWeight) ≤ 1) :
    (∃ strategy : ι → BorelMixedStrategy,
      IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
        hcard premium) ∧
    ∀ strategy : ι → BorelMixedStrategy,
      IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
          hcard premium →
      AtMostOnePositive (fun i => heterogeneousExpectedPayoff
          slotWeight marginalCost strategy hcard premium i) ∧
      max
          (heterogeneousAggregateFloor (ι := ι) slotWeight marginalCost
            (premium bottom) (premium top) (premium second))
          (heterogeneousShiftedWindowFloor slotWeight
            (marginalCost / slotWeight)
            ((depth : ℝ) * (marginalCost / slotWeight))
            (premium second) (premium top)) ≤
        heterogeneousExpectedDissipation marginalCost strategy := by
  constructor
  · exact exists_heterogeneousBorelMixedNash
      hweight hcost premium hpremium hcard
  · intro strategy hnash
    exact ⟨heterogeneousMixedNash_atMostOnePositive hweight.le hcost.le
        strategy hcard premium hpremium hnash,
      heterogeneousNash_selectionFreeFloor hweight hcost strategy hcard
        premium hpremium hnash top second bottom hsecondTop htop hsecond
        hsecondPositive hbottom depth hdepth⟩

end

end SmoothingCliff.Racing
