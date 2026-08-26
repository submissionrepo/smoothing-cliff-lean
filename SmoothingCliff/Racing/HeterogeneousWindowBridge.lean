import SmoothingCliff.Racing.HeterogeneousMixedProfile
import SmoothingCliff.Racing.HeterogeneousWindowFloor

/-!
# From heterogeneous Nash equilibrium to the shifted-window floor

This file supplies the game-theoretic bridge deliberately omitted from
`HeterogeneousWindowFloor`.  For one zero-payoff bidder, the Nash deviation
inequality bounds the bidder's true expected captured premium.  The opponents'
maximum effective score is at most their largest value premium plus their
maximum action, so the true captured premium dominates a translated
one-dimensional capped-gap payoff.  Its distribution-function representation
is exactly the shifted window used in (H5).
-/

namespace SmoothingCliff.Racing

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

variable {ι : Type*}

/-- Largest value premium among the opponents of `i`. -/
def opponentTopPremium [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ) (i : ι) : ℝ :=
  (Finset.univ.erase i).sup' (univ_erase_nonempty_of_two hcard i) premium

theorem opponent_premium_le_topPremium [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i j : ι) (hji : j ≠ i) :
    premium j ≤ opponentTopPremium hcard premium i := by
  exact Finset.le_sup' premium
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)

theorem opponentTopPremium_nonneg [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hpremium : ∀ j, 0 ≤ premium j) (i : ι) :
    0 ≤ opponentTopPremium hcard premium i := by
  rcases univ_erase_nonempty_of_two hcard i with ⟨j, hj⟩
  exact (hpremium j).trans
    (Finset.le_sup' premium hj)

/-- The heterogeneous score maximum is dominated by a deterministic premium
shift of the maximum action. -/
theorem opponentMaxEffectiveScore_le_topPremium_add_maxAction
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (profile : ι → NNReal) :
    opponentMaxEffectiveScore hcard premium i profile ≤
      opponentTopPremium hcard premium i +
        (opponentMaxAction hcard i profile : ℝ) := by
  apply opponentMaxEffectiveScore_le hcard premium i profile
  intro j hji
  have hp := opponent_premium_le_topPremium hcard premium i j hji
  have ha : profile j ≤ opponentMaxAction hcard i profile := by
    exact Finset.le_sup' (fun k => profile k)
      (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  exact_mod_cast add_le_add hp ha

/-- The captured band falls as the rival score rises. -/
theorem heterogeneous_strictPriorityCapturedGap_antitone_rival
    {gap action first second : ℝ} (hle : first ≤ second) :
    strictPriorityCapturedGap gap action second ≤
      strictPriorityCapturedGap gap action first := by
  unfold strictPriorityCapturedGap
  refine min_le_min ?_ (le_refl gap)
  exact max_le_max (by linarith) (le_refl 0)

/-- After subtracting the opponents' top premium, the one-dimensional
maximum-action payoff is pointwise below the bidder's true heterogeneous
captured premium. -/
theorem shiftedMaxActionCapturedGap_le_heterogeneousCapturedPremium
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (action : NNReal) (profile : ι → NNReal) :
    strictPriorityCapturedGap (premium i)
        (premium i + (action : ℝ) - opponentTopPremium hcard premium i)
        (opponentMaxAction hcard i profile : ℝ) ≤
      heterogeneousPureCapturedPremium hcard premium i action profile := by
  have hscore := opponentMaxEffectiveScore_le_topPremium_add_maxAction
    hcard premium i profile
  unfold heterogeneousPureCapturedPremium
  have hmono := heterogeneous_strictPriorityCapturedGap_antitone_rival
    (gap := premium i) (action := premium i + (action : ℝ)) hscore
  unfold strictPriorityCapturedGap at hmono ⊢
  convert hmono using 1
  · congr 2
    ring

/-- Pushing the maximum-action random variable forward does not change the
expected translated capped-gap payoff. -/
theorem borelPureExpectedCapturedGap_opponentMaxActionStrategy
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (i : ι)
    (gap : ℝ) (action : NNReal) :
    borelPureExpectedCapturedGap gap
        (opponentMaxActionStrategy strategy hcard i) action =
      ∫ profile : ι → NNReal,
        strictPriorityCapturedGap gap (action : ℝ)
          (opponentMaxAction hcard i profile : ℝ)
        ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
  unfold borelPureExpectedCapturedGap opponentMaxActionStrategy
  have hmeas : AEStronglyMeasurable
      (fun rival : NNReal =>
        strictPriorityCapturedGap gap (action : ℝ) (rival : ℝ))
      (Measure.map (opponentMaxAction hcard i)
        (heterogeneousProfileLaw strategy : Measure (ι → NNReal))) := by
    have hmeas' : Measurable (fun rival : NNReal =>
        strictPriorityCapturedGap gap (action : ℝ) (rival : ℝ)) := by
      unfold strictPriorityCapturedGap
      fun_prop
    exact hmeas'.aestronglyMeasurable
  exact integral_map
    (measurable_opponentMaxAction hcard i).aemeasurable hmeas

/-- The shifted maximum-action payoff is bounded by the true heterogeneous
pure-deviation payoff in expectation. -/
theorem shiftedMaxActionExpectedCapturedGap_le_heterogeneous
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i) (action shiftedAction : NNReal)
    (hshift : (shiftedAction : ℝ) =
      premium i + (action : ℝ) - opponentTopPremium hcard premium i) :
    borelPureExpectedCapturedGap (premium i)
        (opponentMaxActionStrategy strategy hcard i) shiftedAction ≤
      heterogeneousPureExpectedCapturedPremium strategy hcard premium i action := by
  rw [borelPureExpectedCapturedGap_opponentMaxActionStrategy]
  unfold heterogeneousPureExpectedCapturedPremium
  have hleft : Integrable
      (fun profile : ι → NNReal =>
        strictPriorityCapturedGap (premium i) (shiftedAction : ℝ)
          (opponentMaxAction hcard i profile : ℝ))
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
    refine Integrable.mono' (integrable_const (premium i)) ?_ ?_
    · have hmeas : Measurable (fun profile : ι → NNReal =>
          strictPriorityCapturedGap (premium i) (shiftedAction : ℝ)
            (opponentMaxAction hcard i profile : ℝ)) := by
        unfold strictPriorityCapturedGap
        have hmax : Measurable (fun profile : ι → NNReal =>
            (opponentMaxAction hcard i profile : ℝ)) :=
          measurable_coe_nnreal_real.comp
            (measurable_opponentMaxAction hcard i)
        exact (measurable_const.sub hmax).max measurable_const |>.min
          measurable_const
      exact hmeas.aestronglyMeasurable
    · filter_upwards with profile
      rw [Real.norm_eq_abs,
        abs_of_nonneg (strictPriorityCapturedGap_nonneg hpremium)]
      exact strictPriorityCapturedGap_le_gap
  have hright := integrable_heterogeneousPureCapturedPremium
    strategy hcard premium i hpremium action
  apply integral_mono hleft hright
  intro profile
  rw [hshift]
  exact shiftedMaxActionCapturedGap_le_heterogeneousCapturedPremium
    hcard premium i action profile

/-- A zero-payoff heterogeneous Nash bidder satisfies the shifted CDF-window
inequality (H5), with the premium shift supplied by the largest opponent
premium. -/
theorem zeroPayoff_heterogeneousNash_implies_shiftedWindow
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hpremium : ∀ j, 0 ≤ premium j)
    (i : ι)
    (hweight : 0 < slotWeight) (hcost : 0 ≤ marginalCost)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost
      strategy hcard premium)
    (hzero : heterogeneousExpectedPayoff slotWeight marginalCost strategy
      hcard premium i = 0) :
    ∀ action : ℝ, 0 ≤ action →
      slotWeight *
          (∫ point in
              (action - opponentTopPremium hcard premium i)..
              (action - opponentTopPremium hcard premium i + premium i),
            (opponentMaxActionStrategy strategy hcard i).cdfReal point) ≤
        marginalCost * action := by
  intro action haction
  let deviation : NNReal := ⟨action, haction⟩
  have hdeviation := hnash i deviation
  rw [hzero] at hdeviation
  have htrue : slotWeight *
        heterogeneousPureExpectedCapturedPremium strategy hcard premium
          i deviation ≤ marginalCost * action := by
    simpa [heterogeneousPureExpectedPayoff, deviation] using hdeviation
  let shiftedReal := action - opponentTopPremium hcard premium i + premium i
  by_cases hshifted : 0 ≤ shiftedReal
  · let shifted : NNReal := ⟨shiftedReal, hshifted⟩
    have hproxy := shiftedMaxActionExpectedCapturedGap_le_heterogeneous
      strategy hcard premium i (hpremium i) deviation shifted (by
        change action - opponentTopPremium hcard premium i + premium i =
          premium i + action - opponentTopPremium hcard premium i
        ring)
    have hproxyWeighted : slotWeight *
          borelPureExpectedCapturedGap (premium i)
            (opponentMaxActionStrategy strategy hcard i) shifted ≤
        slotWeight *
          heterogeneousPureExpectedCapturedPremium strategy hcard premium
            i deviation :=
      mul_le_mul_of_nonneg_left hproxy hweight.le
    have hwindow := borelPureExpectedCapturedGap_eq_intervalIntegral
      (hpremium i) (opponentMaxActionStrategy strategy hcard i) shifted
    rw [hwindow] at hproxyWeighted
    have hbounds :
        ((shifted : ℝ) - premium i) =
            action - opponentTopPremium hcard premium i ∧
          (shifted : ℝ) =
            action - opponentTopPremium hcard premium i + premium i := by
      constructor
      · change (action - opponentTopPremium hcard premium i + premium i) -
            premium i = action - opponentTopPremium hcard premium i
        ring
      · rfl
    rw [hbounds.1, hbounds.2] at hproxyWeighted
    exact hproxyWeighted.trans htrue
  · have hshiftedNeg : shiftedReal < 0 := lt_of_not_ge hshifted
    have hlower :
        action - opponentTopPremium hcard premium i ≤ shiftedReal := by
      dsimp [shiftedReal]
      linarith [hpremium i]
    have hzeroIntegral :
        (∫ point in
            (action - opponentTopPremium hcard premium i)..
            (action - opponentTopPremium hcard premium i + premium i),
          (opponentMaxActionStrategy strategy hcard i).cdfReal point) = 0 := by
      have hupper :
          action - opponentTopPremium hcard premium i + premium i =
            shiftedReal := by rfl
      rw [hupper]
      calc
        (∫ point in (action - opponentTopPremium hcard premium i)..shiftedReal,
            (opponentMaxActionStrategy strategy hcard i).cdfReal point) =
            ∫ _ in (action - opponentTopPremium hcard premium i)..shiftedReal,
              0 := by
          apply intervalIntegral.integral_congr
          intro point hpoint
          rw [Set.uIcc_of_le hlower] at hpoint
          exact (opponentMaxActionStrategy strategy hcard i).cdfReal_of_neg
            (hpoint.2.trans_lt hshiftedNeg)
        _ = 0 := by simp
    rw [hzeroIntegral, mul_zero]
    exact mul_nonneg hcost haction

/-- Complete zero-payoff-bidder bridge from heterogeneous Nash equilibrium to
the positive-part shifted-window dissipation floor. -/
theorem zeroPayoff_heterogeneousNash_shiftedWindowFloor_le_dissipation
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hpremium : ∀ j, 0 ≤ premium j)
    (i : ι) (depth : ℕ)
    (hweight : 0 < slotWeight) (hcost : 0 ≤ marginalCost)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost
      strategy hcard premium)
    (hzero : heterogeneousExpectedPayoff slotWeight marginalCost strategy
      hcard premium i = 0) :
    heterogeneousShiftedWindowFloor slotWeight
        (marginalCost / slotWeight)
        ((depth : ℝ) * (marginalCost / slotWeight))
        (premium i) (opponentTopPremium hcard premium i) ≤
      heterogeneousExpectedDissipation marginalCost strategy := by
  have hwindow := zeroPayoff_heterogeneousNash_implies_shiftedWindow
    slotWeight marginalCost strategy hcard premium hpremium i
      hweight hcost hnash hzero
  have hdissipation :
      0 ≤ heterogeneousExpectedDissipation marginalCost strategy := by
    unfold heterogeneousExpectedDissipation
    exact mul_nonneg hcost
      (Finset.sum_nonneg fun j _ => (strategy j).meanAction_nonneg)
  exact h5_implies_heterogeneousShiftedWindowFloor
    hweight hcost (hpremium i)
      (opponentTopPremium_nonneg hcard premium hpremium i)
      (opponentMaxActionStrategy strategy hcard i) depth hwindow
      hdissipation
      (marginalCost_mul_opponentMaxMean_le_dissipation
        strategy hcard i hcost)

end

end SmoothingCliff.Racing
