import SmoothingCliff.Racing.HeterogeneousSupport
import SmoothingCliff.Racing.HeterogeneousAggregateFloor

/-!
# Aggregate equilibrium bridge for the heterogeneous race

This file derives the probabilistic and accounting premises of the aggregate
dissipation floor from a genuine independent Borel mixed Nash equilibrium.
The only premises deliberately left to the support-classification layer are
that at most one bidder has positive payoff and that any exceptional positive
payoff obeys the printed heterogeneous rent cap.
-/

namespace SmoothingCliff.Racing

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

variable {ι : Type*}

/-- Indicator that bidder `i` is a weak maximizer of realized effective score.
Ties are included, exactly as in the shifted-copy argument. -/
def heterogeneousWeakMaximumIndicator
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (profile : ι → NNReal) : ℝ :=
  if opponentMaxEffectiveScore hcard premium i profile ≤
      premium i + (profile i : ℝ) then 1 else 0

/-- Probability that bidder `i` is a weak effective-score maximizer. -/
def heterogeneousWeakMaximumMass
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) : ℝ :=
  ∫ profile : ι → NNReal,
    heterogeneousWeakMaximumIndicator hcard premium i profile
      ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal))

/-- Gross rent, before latency expenditure. -/
def heterogeneousGrossRent
    [Fintype ι] [DecidableEq ι]
    (slotWeight : ℝ) (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) : ℝ :=
  slotWeight * heterogeneousExpectedCapturedPremium
    strategy hcard premium i

theorem measurable_heterogeneousWeakMaximumIndicator
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ) (i : ι) :
    Measurable (heterogeneousWeakMaximumIndicator hcard premium i) := by
  unfold heterogeneousWeakMaximumIndicator
  have hleft := measurable_opponentMaxEffectiveScore hcard premium i
  have hright : Measurable (fun profile : ι → NNReal =>
      premium i + (profile i : ℝ)) :=
    measurable_const.add
      (measurable_coe_nnreal_real.comp (measurable_pi_apply i))
  exact Measurable.ite (measurableSet_le hleft hright) measurable_const
    measurable_const

theorem integrable_heterogeneousWeakMaximumIndicator
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ) (i : ι) :
    Integrable (heterogeneousWeakMaximumIndicator hcard premium i)
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_heterogeneousWeakMaximumIndicator hcard premium i).aestronglyMeasurable ?_
  filter_upwards with profile
  unfold heterogeneousWeakMaximumIndicator
  split_ifs <;> norm_num

theorem heterogeneousWeakMaximumIndicator_nonneg
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (profile : ι → NNReal) :
    0 ≤ heterogeneousWeakMaximumIndicator hcard premium i profile := by
  unfold heterogeneousWeakMaximumIndicator
  split_ifs <;> norm_num

/-- At every finite profile, at least one bidder is a weak effective-score
maximizer.  Common atoms only increase the indicator sum. -/
theorem one_le_sum_heterogeneousWeakMaximumIndicator
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (profile : ι → NNReal) :
    1 ≤ ∑ i, heterogeneousWeakMaximumIndicator hcard premium i profile := by
  let score : ι → ℝ := fun i => premium i + (profile i : ℝ)
  have hnonempty : (Finset.univ : Finset ι).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card ι)
  obtain ⟨winner, hwinner, hwinnerMax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) score hnonempty
  have hweak : opponentMaxEffectiveScore hcard premium winner profile ≤
      premium winner + (profile winner : ℝ) := by
    apply opponentMaxEffectiveScore_le hcard premium winner profile
    intro j hj
    exact hwinnerMax j (Finset.mem_univ j)
  have hone : heterogeneousWeakMaximumIndicator hcard premium winner profile = 1 := by
    simp [heterogeneousWeakMaximumIndicator, hweak]
  calc
    1 = heterogeneousWeakMaximumIndicator hcard premium winner profile := hone.symm
    _ ≤ ∑ i, heterogeneousWeakMaximumIndicator hcard premium i profile := by
      exact Finset.single_le_sum
        (fun i _ => heterogeneousWeakMaximumIndicator_nonneg
          hcard premium i profile) (Finset.mem_univ winner)

/-- Weak-maximum probabilities have total mass at least one. -/
theorem one_le_sum_heterogeneousWeakMaximumMass
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ) :
    1 ≤ ∑ i, heterogeneousWeakMaximumMass strategy hcard premium i := by
  have hsum : Integrable (fun profile : ι → NNReal =>
      ∑ i, heterogeneousWeakMaximumIndicator hcard premium i profile)
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
    apply integrable_finsetSum
    intro i hi
    exact integrable_heterogeneousWeakMaximumIndicator strategy hcard premium i
  have hmono := integral_mono (integrable_const (1 : ℝ)) hsum
    (one_le_sum_heterogeneousWeakMaximumIndicator hcard premium)
  rw [integral_finsetSum] at hmono
  · simpa [heterogeneousWeakMaximumMass] using hmono
  · intro i hi
    exact integrable_heterogeneousWeakMaximumIndicator strategy hcard premium i

/-! ## The shifted-copy deviation -/

/-- On a profile where bidder `i` is already a weak effective-score maximizer,
adding `increment` to her action captures at least `increment`, provided the
increment does not exceed her value premium. -/
theorem increment_mul_weakMaximumIndicator_le_shiftedCapturedPremium
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (increment : NNReal)
    (hincrement : (increment : ℝ) ≤ premium i)
    (profile : ι → NNReal) :
    (increment : ℝ) *
        heterogeneousWeakMaximumIndicator hcard premium i profile ≤
      heterogeneousPureCapturedPremium hcard premium i
        (profile i + increment) profile := by
  have hpremium : 0 ≤ premium i := le_trans (by positivity) hincrement
  unfold heterogeneousWeakMaximumIndicator
  split_ifs with hweak
  · simp only [mul_one]
    unfold heterogeneousPureCapturedPremium strictPriorityCapturedGap
    apply le_min
    · apply le_trans ?_ (le_max_left _ _)
      push_cast
      linarith
    · exact hincrement
  · simp only [mul_zero]
    exact strictPriorityCapturedGap_nonneg hpremium

/-- The shifted captured-premium integrand is integrable under the product
profile law. -/
theorem integrable_heterogeneousShiftedCapturedPremium_profile
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (increment : NNReal) (hpremium : 0 ≤ premium i) :
    Integrable
      (fun profile : ι → NNReal =>
        heterogeneousPureCapturedPremium hcard premium i
          (profile i + increment) profile)
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) := by
  have hown : Measurable (fun profile : ι → NNReal =>
      premium i + ((profile i + increment : NNReal) : ℝ)) :=
    measurable_const.add
      (measurable_coe_nnreal_real.comp
        ((measurable_pi_apply i).add measurable_const))
  have hmax := measurable_opponentMaxEffectiveScore hcard premium i
  have hmeas : Measurable (fun profile : ι → NNReal =>
      heterogeneousPureCapturedPremium hcard premium i
        (profile i + increment) profile) := by
    unfold heterogeneousPureCapturedPremium strictPriorityCapturedGap
    exact (hown.sub hmax).max measurable_const |>.min measurable_const
  refine Integrable.mono' (integrable_const (premium i))
    hmeas.aestronglyMeasurable ?_
  filter_upwards with profile
  unfold heterogeneousPureCapturedPremium
  rw [Real.norm_eq_abs,
    abs_of_nonneg (strictPriorityCapturedGap_nonneg hpremium)]
  exact strictPriorityCapturedGap_le_gap

/-- Averaging the shifted-copy pointwise inequality over the independent
profile gives the weak-maximum probability lower bound. -/
theorem weakMaximumMass_mul_increment_le_integral_shiftedCapturedPremium
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (increment : NNReal)
    (hincrement : (increment : ℝ) ≤ premium i) :
    (increment : ℝ) *
        heterogeneousWeakMaximumMass strategy hcard premium i ≤
      ∫ action : NNReal,
        heterogeneousPureExpectedCapturedPremium strategy hcard premium i
          (action + increment)
        ∂((strategy i).law : Measure NNReal) := by
  have hpremium : 0 ≤ premium i := le_trans (by positivity) hincrement
  let shiftedCaptured : (ι → NNReal) → ℝ := fun profile =>
    heterogeneousPureCapturedPremium hcard premium i
      (profile i + increment) profile
  have hshifted : Integrable shiftedCaptured
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) :=
    integrable_heterogeneousShiftedCapturedPremium_profile strategy hcard
      premium i increment hpremium
  have hindicator :=
    (integrable_heterogeneousWeakMaximumIndicator strategy hcard premium i).const_mul
      (increment : ℝ)
  have hmono := integral_mono hindicator hshifted fun profile =>
    increment_mul_weakMaximumIndicator_le_shiftedCapturedPremium
      hcard premium i increment hincrement profile
  have hreplace := integral_updateHeterogeneousCoordinate strategy i
    shiftedCaptured hshifted
  rw [integral_const_mul] at hmono
  change (increment : ℝ) *
      heterogeneousWeakMaximumMass strategy hcard premium i ≤
    ∫ profile, shiftedCaptured profile
      ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal)) at hmono
  rw [hreplace] at hmono
  refine hmono.trans_eq ?_
  apply integral_congr_ae
  filter_upwards with action
  unfold heterogeneousPureExpectedCapturedPremium shiftedCaptured
  apply integral_congr_ae
  filter_upwards with profile
  unfold heterogeneousPureCapturedPremium
  rw [Function.update_self,
    opponentMaxEffectiveScore_update_self hcard premium i profile action]

/-- Shifted pure captured premia are integrable under the bidder's own mixed
law. -/
theorem integrable_shifted_heterogeneousPureExpectedCapturedPremium
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (increment : NNReal) (hpremium : 0 ≤ premium i) :
    Integrable
      (fun action : NNReal =>
        heterogeneousPureExpectedCapturedPremium strategy hcard premium i
          (action + increment))
      ((strategy i).law : Measure NNReal) := by
  have hcomp : Integrable
      (fun p : NNReal × (ι → NNReal) =>
        heterogeneousPureCapturedPremium hcard premium i
          (p.1 + increment) p.2)
      (((strategy i).law : Measure NNReal).prod
        (heterogeneousProfileLaw strategy : Measure (ι → NNReal))) := by
    have hown : Measurable (fun p : NNReal × (ι → NNReal) =>
        premium i + ((p.1 + increment : NNReal) : ℝ)) :=
      measurable_const.add
        (measurable_coe_nnreal_real.comp
          (measurable_fst.add measurable_const))
    have hmax : Measurable (fun p : NNReal × (ι → NNReal) =>
        opponentMaxEffectiveScore hcard premium i p.2) :=
      (measurable_opponentMaxEffectiveScore hcard premium i).comp
        measurable_snd
    have hmeas : Measurable (fun p : NNReal × (ι → NNReal) =>
        heterogeneousPureCapturedPremium hcard premium i
          (p.1 + increment) p.2) := by
      unfold heterogeneousPureCapturedPremium strictPriorityCapturedGap
      exact (hown.sub hmax).max measurable_const |>.min measurable_const
    refine Integrable.mono' (integrable_const (premium i))
      hmeas.aestronglyMeasurable ?_
    filter_upwards with p
    unfold heterogeneousPureCapturedPremium
    rw [Real.norm_eq_abs,
      abs_of_nonneg (strictPriorityCapturedGap_nonneg hpremium)]
    exact strictPriorityCapturedGap_le_gap
  simpa [heterogeneousPureExpectedCapturedPremium] using
    hcomp.integral_prod_left

/-- Translating an action by a fixed nonnegative increment translates its
first moment by the same amount. -/
theorem integral_shiftedAction_eq_meanAction_add
    (strategy : BorelMixedStrategy) (increment : NNReal) :
    (∫ action : NNReal, ((action + increment : NNReal) : ℝ)
        ∂(strategy.law : Measure NNReal)) =
      strategy.meanAction + (increment : ℝ) := by
  simp_rw [NNReal.coe_add]
  rw [integral_add strategy.integrable_action (integrable_const _),
    integral_const]
  simp [BorelMixedStrategy.meanAction]

/-- The shifted pure-deviation payoff is integrable under the bidder's own
mixed law. -/
theorem integrable_shifted_heterogeneousPureExpectedPayoff
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (increment : NNReal) (hpremium : 0 ≤ premium i) :
    Integrable
      (fun action : NNReal =>
        heterogeneousPureExpectedPayoff slotWeight marginalCost strategy hcard
          premium i (action + increment))
      ((strategy i).law : Measure NNReal) := by
  unfold heterogeneousPureExpectedPayoff
  have hcaptured :=
    (integrable_shifted_heterogeneousPureExpectedCapturedPremium strategy hcard
      premium i increment hpremium).const_mul slotWeight
  have haction : Integrable
      (fun action : NNReal => ((action + increment : NNReal) : ℝ))
      ((strategy i).law : Measure NNReal) := by
    simp_rw [NNReal.coe_add]
    exact (strategy i).integrable_action.add (integrable_const _)
  exact hcaptured.sub (haction.const_mul marginalCost)

/-- A genuine Nash equilibrium also dominates the deviation obtained by
drawing from the bidder's equilibrium law and then adding a fixed increment. -/
theorem integral_shiftedPureExpectedPayoff_le_equilibriumPayoff
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (increment : NNReal) (hpremium : 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium) :
    (∫ action : NNReal,
        heterogeneousPureExpectedPayoff slotWeight marginalCost strategy hcard
          premium i (action + increment)
        ∂((strategy i).law : Measure NNReal)) ≤
      heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
        premium i := by
  have hleft := integrable_shifted_heterogeneousPureExpectedPayoff slotWeight
    marginalCost strategy hcard premium i increment hpremium
  have hright : Integrable (fun _ : NNReal =>
      heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
        premium i) ((strategy i).law : Measure NNReal) := integrable_const _
  have hmono := integral_mono hleft hright fun action =>
    hnash i (action + increment)
  simpa using hmono

/-- The actual Nash inequalities imply the per-bidder shifted-copy gross-rent
bound used by the aggregate floor. -/
theorem heterogeneousNash_shiftedCopy_grossRent
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (increment : NNReal)
    (hWeight : 0 ≤ slotWeight)
    (hincrement : (increment : ℝ) ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium) :
    slotWeight * (increment : ℝ) *
          heterogeneousWeakMaximumMass strategy hcard premium i -
        marginalCost * (increment : ℝ) ≤
      heterogeneousGrossRent slotWeight strategy hcard premium i := by
  have hpremium : 0 ≤ premium i := le_trans (by positivity) hincrement
  have hcaptured :=
    weakMaximumMass_mul_increment_le_integral_shiftedCapturedPremium
      strategy hcard premium i increment hincrement
  have hcapturedScaled := mul_le_mul_of_nonneg_left hcaptured hWeight
  have hnashAverage :=
    integral_shiftedPureExpectedPayoff_le_equilibriumPayoff slotWeight
      marginalCost strategy hcard premium i increment hpremium hnash
  have hcapturedIntegrable :=
    integrable_shifted_heterogeneousPureExpectedCapturedPremium strategy hcard
      premium i increment hpremium
  have haction : Integrable
      (fun action : NNReal => ((action + increment : NNReal) : ℝ))
      ((strategy i).law : Measure NNReal) := by
    simp_rw [NNReal.coe_add]
    exact (strategy i).integrable_action.add (integrable_const _)
  unfold heterogeneousPureExpectedPayoff at hnashAverage
  rw [integral_sub (hcapturedIntegrable.const_mul slotWeight)
      (haction.const_mul marginalCost),
    integral_const_mul, integral_const_mul,
    integral_shiftedAction_eq_meanAction_add] at hnashAverage
  unfold heterogeneousExpectedPayoff at hnashAverage
  unfold heterogeneousGrossRent
  nlinarith

/-! ## Accounting and the aggregate floor -/

/-- Aggregate gross rent minus aggregate equilibrium payoff is exactly total
latency expenditure. -/
theorem heterogeneousDissipation_eq_sum_grossRent_sub_sum_payoff
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ) :
    heterogeneousExpectedDissipation marginalCost strategy =
      ∑ i, heterogeneousGrossRent slotWeight strategy hcard premium i -
        ∑ i, heterogeneousExpectedPayoff slotWeight marginalCost strategy
          hcard premium i := by
  unfold heterogeneousExpectedDissipation heterogeneousGrossRent
    heterogeneousExpectedPayoff
  rw [Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum]
  ring

/-- **Aggregate branch derived from a genuine heterogeneous Nash
equilibrium.**  Weak-maximum mass, shifted-copy deviations, payoff
nonnegativity, support classification, and accounting are all discharged
here.  The sole remaining game-specific premise is the exceptional positive
payoff cap. -/
theorem heterogeneousNash_aggregateFloor_le_dissipation
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost minimumPremium topPremium secondPremium : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hWeight : 0 ≤ slotWeight) (hCost : 0 ≤ marginalCost)
    (hMinimum : 0 ≤ minimumPremium)
    (hMinimumBound : ∀ i, minimumPremium ≤ premium i)
    (hSecond : 0 < secondPremium) (hOrder : secondPremium ≤ topPremium)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium)
    (hPositivePayoffCap : ∀ i,
      0 < heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
          premium i →
        heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
            premium i ≤
          heterogeneousExceptionalRentCap slotWeight marginalCost topPremium
            secondPremium) :
    heterogeneousAggregateFloor (ι := ι) slotWeight marginalCost
        minimumPremium topPremium secondPremium ≤
      heterogeneousExpectedDissipation marginalCost strategy := by
  let increment : NNReal := ⟨minimumPremium, hMinimum⟩
  have hPremium : ∀ i, 0 ≤ premium i := fun i =>
    hMinimum.trans (hMinimumBound i)
  have hShiftedCopy : ∀ i,
      slotWeight * minimumPremium *
            heterogeneousWeakMaximumMass strategy hcard premium i -
          marginalCost * minimumPremium ≤
        heterogeneousGrossRent slotWeight strategy hcard premium i := by
    intro i
    simpa [increment] using
      heterogeneousNash_shiftedCopy_grossRent slotWeight marginalCost strategy
        hcard premium i increment hWeight (hMinimumBound i) hnash
  have hWeakMaximumMass :=
    one_le_sum_heterogeneousWeakMaximumMass strategy hcard premium
  have hPayoffNonneg : ∀ i,
      0 ≤ heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
        premium i := fun i =>
    heterogeneousMixedNash_payoff_nonneg hWeight strategy hcard premium
      hPremium hnash i
  have hAtMostOne := heterogeneousMixedNash_atMostOnePositive hWeight hCost
    strategy hcard premium hPremium hnash
  have hIdentity :=
    heterogeneousDissipation_eq_sum_grossRent_sub_sum_payoff slotWeight
      marginalCost strategy hcard premium
  have hDissipationNonneg :
      0 ≤ heterogeneousExpectedDissipation marginalCost strategy := by
    unfold heterogeneousExpectedDissipation
    exact mul_nonneg hCost
      (Finset.sum_nonneg fun i _ => (strategy i).meanAction_nonneg)
  exact heterogeneousAggregateDissipation_floor hWeight hCost hMinimum hSecond
    hOrder
    (heterogeneousWeakMaximumMass strategy hcard premium)
    (heterogeneousGrossRent slotWeight strategy hcard premium)
    (heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard premium)
    (heterogeneousExpectedDissipation marginalCost strategy)
    hShiftedCopy hWeakMaximumMass hPayoffNonneg hAtMostOne
    hPositivePayoffCap hIdentity hDissipationNonneg

end

end SmoothingCliff.Racing
