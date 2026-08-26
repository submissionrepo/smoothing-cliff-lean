import SmoothingCliff.Racing.CdfWindow

/-!
# The heterogeneous shifted-window floor

This file isolates the analytic part of the shifted-window branch in the
heterogeneous strict-priority race.  It starts from the window inequality that
a zero-payoff bidder's pure deviations must satisfy.  The Nash-equilibrium and
product-law arguments that produce that premise are deliberately not encoded
here.

For a bidder with premium `di`, let `opponentTop` be the largest opponent
premium and let `opponent` be the law of the opponents' maximum action.  The
deviations `opponentTop + k * di` translate the heterogeneous windows back to
the adjacent intervals `[k * di, (k+1) * di]`.  Summing those inequalities and
using the CDF tail bound yields equation (H7) in the paper, including the
free-head-start correction.  The last lemmas compare the two possible choices
of a zero-payoff bidder among the top two premiums.
-/

namespace SmoothingCliff.Racing

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- The bracket in the heterogeneous shifted-window floor. -/
def heterogeneousShiftedWindowBracket
    (q varsigma ownPremium opponentTop : ℝ) : ℝ :=
  ownPremium * (2 - varsigma - q) -
    2 * q * (opponentTop - ownPremium)

/-- The positive-part shifted-window floor. -/
def heterogeneousShiftedWindowFloor
    (slotWeight q varsigma ownPremium opponentTop : ℝ) : ℝ :=
  slotWeight * varsigma / 2 *
    max (heterogeneousShiftedWindowBracket
      q varsigma ownPremium opponentTop) 0

/-- Pointwise form of the truncated-tail inequality. -/
theorem cutoff_sub_strictPriorityCapturedGap_le_action
    {cutoff : ℝ} (hcutoff : 0 ≤ cutoff) (action : NNReal) :
    cutoff - strictPriorityCapturedGap cutoff cutoff (action : ℝ) ≤
      (action : ℝ) := by
  have haction : 0 ≤ (action : ℝ) := NNReal.zero_le_coe
  by_cases hbelow : (action : ℝ) ≤ cutoff
  · have hdiffNonneg : 0 ≤ cutoff - (action : ℝ) := sub_nonneg.mpr hbelow
    have hdiffLe : cutoff - (action : ℝ) ≤ cutoff := by linarith
    rw [strictPriorityCapturedGap, max_eq_left hdiffNonneg,
      min_eq_left hdiffLe]
    linarith
  · have habove : cutoff ≤ (action : ℝ) := le_of_not_ge hbelow
    have hdiffNonpos : cutoff - (action : ℝ) ≤ 0 := sub_nonpos.mpr habove
    rw [strictPriorityCapturedGap, max_eq_right hdiffNonpos,
      min_eq_left hcutoff]
    simpa using habove

/-- A first moment dominates the CDF tail truncated at any nonnegative
cutoff: `T - ∫₀ᵀ F ≤ E[A]`. -/
theorem cutoff_sub_cdfIntegral_le_meanAction
    (strategy : BorelMixedStrategy) {cutoff : ℝ} (hcutoff : 0 ≤ cutoff) :
    cutoff - (∫ point in (0 : ℝ)..cutoff, strategy.cdfReal point) ≤
      strategy.meanAction := by
  let cutoffAction : NNReal := ⟨cutoff, hcutoff⟩
  have hcaptured : Integrable
      (fun action : NNReal =>
        strictPriorityCapturedGap cutoff cutoff (action : ℝ))
      (strategy.law : Measure NNReal) := by
    simpa [cutoffAction] using
      borelCapturedGapAgainst_integrable cutoffAction strategy cutoffAction
  have hleft : Integrable
      (fun action : NNReal =>
        cutoff - strictPriorityCapturedGap cutoff cutoff (action : ℝ))
      (strategy.law : Measure NNReal) :=
    (integrable_const cutoff).sub hcaptured
  have hintegral := integral_mono_ae hleft strategy.integrable_action
    (Filter.Eventually.of_forall
      (cutoff_sub_strictPriorityCapturedGap_le_action hcutoff))
  have hcdf := borelPureExpectedCapturedGap_eq_intervalIntegral
    hcutoff strategy cutoffAction
  have hcoe : (cutoffAction : ℝ) = cutoff := rfl
  rw [hcoe, sub_self] at hcdf
  have hcdf' :
      borelPureExpectedCapturedGap cutoff strategy cutoffAction =
        ∫ point in (0 : ℝ)..cutoff, strategy.cdfReal point := by
    exact hcdf
  rw [integral_sub (integrable_const cutoff) hcaptured,
    integral_const, probReal_univ, one_smul,
    ← BorelMixedStrategy.meanAction] at hintegral
  rw [← hcdf']
  simpa [borelPureExpectedCapturedGap, cutoffAction] using hintegral

/-- Adjacent intervals of a common width tile the interval from zero to the
last endpoint. -/
theorem sum_tiled_intervalIntegrals
    (integrand : ℝ → ℝ) (width : ℝ) (depth : ℕ)
    (hintegrable : ∀ lower upper,
      IntervalIntegrable integrand volume lower upper) :
    (∑ index ∈ Finset.range depth,
        ∫ point in ((index : ℝ) * width)..(((index : ℝ) + 1) * width),
          integrand point) =
      ∫ point in (0 : ℝ)..((depth : ℝ) * width), integrand point := by
  induction depth with
  | zero => simp
  | succ depth ih =>
      rw [Finset.sum_range_succ, ih]
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hintegrable 0 ((depth : ℝ) * width))
        (hintegrable ((depth : ℝ) * width)
          (((depth : ℝ) + 1) * width))
      simpa [Nat.cast_add, Nat.cast_one] using hadd

/-- Summing the deviations at `opponentTop + k * ownPremium` gives (H6),
before dividing by the slot weight. -/
theorem h5_implies_tiledWindowIntegral_bound
    {slotWeight marginalCost ownPremium opponentTop : ℝ}
    (hpremium : 0 ≤ ownPremium) (hopponentTop : 0 ≤ opponentTop)
    (opponent : BorelMixedStrategy) (depth : ℕ)
    (hwindow : ∀ action : ℝ, 0 ≤ action →
      slotWeight *
          (∫ point in (action - opponentTop)..
              (action - opponentTop + ownPremium),
            opponent.cdfReal point) ≤
        marginalCost * action) :
    slotWeight *
        (∫ point in (0 : ℝ)..((depth : ℝ) * ownPremium),
          opponent.cdfReal point) ≤
      marginalCost *
        ((depth : ℝ) * opponentTop +
          ownPremium * ((depth : ℝ) * ((depth : ℝ) - 1) / 2)) := by
  have hindexed : ∀ index ∈ Finset.range depth,
      slotWeight *
          (∫ point in ((index : ℝ) * ownPremium)..
              (((index : ℝ) + 1) * ownPremium),
            opponent.cdfReal point) ≤
        marginalCost *
          (opponentTop + (index : ℝ) * ownPremium) := by
    intro index _
    have haction :
        0 ≤ opponentTop + (index : ℝ) * ownPremium := by positivity
    have hdeviation := hwindow
      (opponentTop + (index : ℝ) * ownPremium) haction
    have hlower :
        opponentTop + (index : ℝ) * ownPremium - opponentTop =
          (index : ℝ) * ownPremium := by ring
    have hupper :
        (index : ℝ) * ownPremium + ownPremium =
          ((index : ℝ) + 1) * ownPremium := by ring
    rw [hlower, hupper] at hdeviation
    exact hdeviation
  have hsum := Finset.sum_le_sum hindexed
  calc
    slotWeight *
          (∫ point in (0 : ℝ)..((depth : ℝ) * ownPremium),
            opponent.cdfReal point) =
        ∑ index ∈ Finset.range depth,
          slotWeight *
            (∫ point in ((index : ℝ) * ownPremium)..
                (((index : ℝ) + 1) * ownPremium),
              opponent.cdfReal point) := by
        rw [← Finset.mul_sum]
        congr 1
        exact (sum_tiled_intervalIntegrals opponent.cdfReal ownPremium depth
          opponent.intervalIntegrable_cdfReal).symm
    _ ≤ ∑ index ∈ Finset.range depth,
          marginalCost *
            (opponentTop + (index : ℝ) * ownPremium) := hsum
    _ = marginalCost *
          ((depth : ℝ) * opponentTop +
            ownPremium *
              ((depth : ℝ) * ((depth : ℝ) - 1) / 2)) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib,
          Finset.sum_const, Finset.card_range,
          ← Finset.sum_mul, sum_range_natCast_eq]
        simp only [nsmul_eq_mul]
        ring

/-- Exact algebraic conversion from the tiled-tail expression to the paper's
`varsigma = J q` parameterization. -/
theorem tiledTailCost_eq_shiftedWindowRaw
    {slotWeight marginalCost ownPremium opponentTop : ℝ}
    (hweight : slotWeight ≠ 0) (depth : ℕ) :
    marginalCost *
        ((depth : ℝ) * ownPremium -
          (marginalCost / slotWeight) *
            ((depth : ℝ) * opponentTop +
              ownPremium *
                ((depth : ℝ) * ((depth : ℝ) - 1) / 2))) =
      slotWeight * ((depth : ℝ) * (marginalCost / slotWeight)) / 2 *
        heterogeneousShiftedWindowBracket
          (marginalCost / slotWeight)
          ((depth : ℝ) * (marginalCost / slotWeight))
          ownPremium opponentTop := by
  unfold heterogeneousShiftedWindowBracket
  field_simp [hweight]
  ring

/-- Equation (H7).  This theorem begins at the explicit deviation-window
premise (H5); it does not assume or assert that the premise follows from a
general-`n` mixed Nash equilibrium. -/
theorem h5_implies_heterogeneousShiftedWindow_meanAction_bound
    {slotWeight marginalCost ownPremium opponentTop : ℝ}
    (hweight : 0 < slotWeight) (hcost : 0 ≤ marginalCost)
    (hpremium : 0 ≤ ownPremium) (hopponentTop : 0 ≤ opponentTop)
    (opponent : BorelMixedStrategy) (depth : ℕ)
    (hwindow : ∀ action : ℝ, 0 ≤ action →
      slotWeight *
          (∫ point in (action - opponentTop)..
              (action - opponentTop + ownPremium),
            opponent.cdfReal point) ≤
        marginalCost * action) :
    slotWeight * ((depth : ℝ) * (marginalCost / slotWeight)) / 2 *
        heterogeneousShiftedWindowBracket
          (marginalCost / slotWeight)
          ((depth : ℝ) * (marginalCost / slotWeight))
          ownPremium opponentTop ≤
      marginalCost * opponent.meanAction := by
  have hcutoff : 0 ≤ (depth : ℝ) * ownPremium := by positivity
  have htail := cutoff_sub_cdfIntegral_le_meanAction opponent hcutoff
  have htiled := h5_implies_tiledWindowIntegral_bound
    hpremium hopponentTop opponent depth hwindow
  have hintegral :
      (∫ point in (0 : ℝ)..((depth : ℝ) * ownPremium),
          opponent.cdfReal point) ≤
        (marginalCost *
          ((depth : ℝ) * opponentTop +
            ownPremium *
              ((depth : ℝ) * ((depth : ℝ) - 1) / 2))) /
          slotWeight := by
    apply (le_div_iff₀ hweight).2
    simpa [mul_comm] using htiled
  have htailCost :
      marginalCost *
          ((depth : ℝ) * ownPremium -
            (marginalCost / slotWeight) *
              ((depth : ℝ) * opponentTop +
                ownPremium *
                  ((depth : ℝ) * ((depth : ℝ) - 1) / 2))) ≤
        marginalCost * opponent.meanAction := by
    have hrewrite :
        (marginalCost / slotWeight) *
            ((depth : ℝ) * opponentTop +
              ownPremium *
                ((depth : ℝ) * ((depth : ℝ) - 1) / 2)) =
          (marginalCost *
            ((depth : ℝ) * opponentTop +
              ownPremium *
                ((depth : ℝ) * ((depth : ℝ) - 1) / 2))) /
            slotWeight := by ring
    rw [hrewrite]
    calc
      marginalCost *
            ((depth : ℝ) * ownPremium -
              (marginalCost *
                ((depth : ℝ) * opponentTop +
                  ownPremium *
                    ((depth : ℝ) * ((depth : ℝ) - 1) / 2))) /
                slotWeight) ≤
          marginalCost *
            ((depth : ℝ) * ownPremium -
              (∫ point in (0 : ℝ)..((depth : ℝ) * ownPremium),
                opponent.cdfReal point)) :=
        mul_le_mul_of_nonneg_left
          (sub_le_sub_left hintegral ((depth : ℝ) * ownPremium)) hcost
      _ ≤ marginalCost * opponent.meanAction :=
        mul_le_mul_of_nonneg_left htail hcost
  rw [← tiledTailCost_eq_shiftedWindowRaw hweight.ne' depth]
  exact htailCost

/-- Passing from the raw lower bound to the positive-part floor uses only
nonnegative dissipation. -/
theorem heterogeneousShiftedWindowFloor_le_of_raw_le
    {slotWeight q varsigma ownPremium opponentTop dissipation : ℝ}
    (hdissipation : 0 ≤ dissipation)
    (hraw : slotWeight * varsigma / 2 *
        heterogeneousShiftedWindowBracket
          q varsigma ownPremium opponentTop ≤ dissipation) :
    heterogeneousShiftedWindowFloor
        slotWeight q varsigma ownPremium opponentTop ≤ dissipation := by
  unfold heterogeneousShiftedWindowFloor
  by_cases hbracket :
      0 ≤ heterogeneousShiftedWindowBracket
        q varsigma ownPremium opponentTop
  · rw [max_eq_left hbracket]
    exact hraw
  · rw [max_eq_right (le_of_not_ge hbracket), mul_zero]
    exact hdissipation

/-- The direct H5-to-floor wrapper.  The two additional hypotheses say only
that the candidate `dissipation` is nonnegative and dominates the cost of the
opponents' maximum action. -/
theorem h5_implies_heterogeneousShiftedWindowFloor
    {slotWeight marginalCost ownPremium opponentTop dissipation : ℝ}
    (hweight : 0 < slotWeight) (hcost : 0 ≤ marginalCost)
    (hpremium : 0 ≤ ownPremium) (hopponentTop : 0 ≤ opponentTop)
    (opponent : BorelMixedStrategy) (depth : ℕ)
    (hwindow : ∀ action : ℝ, 0 ≤ action →
      slotWeight *
          (∫ point in (action - opponentTop)..
              (action - opponentTop + ownPremium),
            opponent.cdfReal point) ≤
        marginalCost * action)
    (hdissipation : 0 ≤ dissipation)
    (hmeanCost : marginalCost * opponent.meanAction ≤ dissipation) :
    heterogeneousShiftedWindowFloor
        slotWeight (marginalCost / slotWeight)
        ((depth : ℝ) * (marginalCost / slotWeight))
        ownPremium opponentTop ≤ dissipation := by
  have hraw := h5_implies_heterogeneousShiftedWindow_meanAction_bound
    hweight hcost hpremium hopponentTop opponent depth hwindow
  exact heterogeneousShiftedWindowFloor_le_of_raw_le
    hdissipation (hraw.trans hmeanCost)

/-- The top-bidder bracket minus the runner-up bracket is exactly the term
displayed after (H7). -/
theorem leader_sub_runner_shiftedWindowBracket
    (q varsigma leader runnerUp : ℝ) :
    heterogeneousShiftedWindowBracket q varsigma leader runnerUp -
        heterogeneousShiftedWindowBracket q varsigma runnerUp leader =
      (leader - runnerUp) * (2 - varsigma + 3 * q) := by
  unfold heterogeneousShiftedWindowBracket
  ring

/-- Under the paper's range `0 ≤ q` and `varsigma ≤ 1`, the leader's
bracket is at least the runner-up's bracket. -/
theorem runner_shiftedWindowBracket_le_leader
    {q varsigma leader runnerUp : ℝ}
    (hq : 0 ≤ q) (hvarsigma : varsigma ≤ 1)
    (hrank : runnerUp ≤ leader) :
    heterogeneousShiftedWindowBracket q varsigma runnerUp leader ≤
      heterogeneousShiftedWindowBracket q varsigma leader runnerUp := by
  have hgap : 0 ≤ leader - runnerUp := sub_nonneg.mpr hrank
  have hcoefficient : 0 ≤ 2 - varsigma + 3 * q := by linarith
  have hproduct : 0 ≤
      (leader - runnerUp) * (2 - varsigma + 3 * q) :=
    mul_nonneg hgap hcoefficient
  have hdifference : 0 ≤
      heterogeneousShiftedWindowBracket q varsigma leader runnerUp -
        heterogeneousShiftedWindowBracket q varsigma runnerUp leader := by
    rw [leader_sub_runner_shiftedWindowBracket]
    exact hproduct
  exact sub_nonneg.mp hdifference

/-- If the shifted-window raw bound is available for a zero-payoff bidder
among the top two premiums, then the runner-up positive-part floor follows in
either case. -/
theorem topTwo_zeroPayoff_implies_shiftedWindowFloor
    {slotWeight q varsigma leader runnerUp dissipation : ℝ}
    (hweight : 0 ≤ slotWeight) (hq : 0 ≤ q)
    (hvarsigmaNonneg : 0 ≤ varsigma) (hvarsigma : varsigma ≤ 1)
    (hrank : runnerUp ≤ leader) (hdissipation : 0 ≤ dissipation)
    (hzeroTopTwo :
      slotWeight * varsigma / 2 *
          heterogeneousShiftedWindowBracket
            q varsigma runnerUp leader ≤ dissipation ∨
      slotWeight * varsigma / 2 *
          heterogeneousShiftedWindowBracket
            q varsigma leader runnerUp ≤ dissipation) :
    heterogeneousShiftedWindowFloor
        slotWeight q varsigma runnerUp leader ≤ dissipation := by
  have hfactor : 0 ≤ slotWeight * varsigma / 2 := by positivity
  rcases hzeroTopTwo with hrunner | hleader
  · exact heterogeneousShiftedWindowFloor_le_of_raw_le
      hdissipation hrunner
  · have hbracket := runner_shiftedWindowBracket_le_leader
      hq hvarsigma hrank
    have hraw :
        slotWeight * varsigma / 2 *
            heterogeneousShiftedWindowBracket
              q varsigma runnerUp leader ≤ dissipation :=
      (mul_le_mul_of_nonneg_left hbracket hfactor).trans hleader
    exact heterogeneousShiftedWindowFloor_le_of_raw_le
      hdissipation hraw

end

end SmoothingCliff.Racing
