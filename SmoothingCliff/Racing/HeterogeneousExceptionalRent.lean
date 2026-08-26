import SmoothingCliff.Racing.HeterogeneousSupport
import SmoothingCliff.Racing.SupportBound

/-!
# The exceptional rent in the heterogeneous strict-priority race

This file proves equations (H2)--(H4) of the heterogeneous dissipation floor
from an actual independent Borel mixed Nash equilibrium.  In particular, the
upper-support height, the deviation inequality, and the exceptional bidder's
rent bound are conclusions rather than abstract premises.
-/

namespace SmoothingCliff.Racing

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

variable {ι : Type*}

/-! ## Heterogeneous upper supports -/

/-- The expected captured premium of a pure action never exceeds the bidder's
premium. -/
theorem heterogeneousPureExpectedCapturedPremium_le_premium
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i) (action : NNReal) :
    heterogeneousPureExpectedCapturedPremium strategy hcard premium i action ≤
      premium i := by
  unfold heterogeneousPureExpectedCapturedPremium
  have hint := integrable_heterogeneousPureCapturedPremium strategy hcard
    premium i hpremium action
  have hconst : Integrable (fun _ : ι → NNReal => premium i)
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal)) :=
    integrable_const _
  have hle := integral_mono hint hconst (fun profile => by
    unfold heterogeneousPureCapturedPremium
    exact strictPriorityCapturedGap_le_gap)
  simpa using hle

/-- Every action in a heterogeneous best response's support has cost at most
the whole slot premium. -/
theorem heterogeneous_support_action_cost_le_prize
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium) (i : ι) {action : NNReal}
    (hmem : action ∈ (strategy i).support) :
    marginalCost * (action : ℝ) ≤ slotWeight * premium i := by
  have hpayoff := heterogeneousMixedBestResponse_payoff_eq_on_support
    slotWeight marginalCost strategy hcard premium i (hPremium i) (hnash i)
    action hmem
  have hnonneg := heterogeneousMixedNash_payoff_nonneg hWeight strategy hcard
    premium hPremium hnash i
  have hcaptured := heterogeneousPureExpectedCapturedPremium_le_premium
    strategy hcard premium i (hPremium i) action
  rw [← hpayoff, heterogeneousPureExpectedPayoff] at hnonneg
  nlinarith

/-- A heterogeneous equilibrium support is bounded above by the whole-prize
cost bound. -/
theorem heterogeneous_support_bddAbove
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 < marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium) (i : ι) :
    BddAbove (strategy i).support := by
  refine ⟨(slotWeight * premium i / marginalCost).toNNReal,
    fun action hmem => ?_⟩
  have hbound := heterogeneous_support_action_cost_le_prize hWeight strategy
    hcard premium hPremium hnash i hmem
  have hle : (action : ℝ) ≤ slotWeight * premium i / marginalCost := by
    rw [le_div_iff₀ hCost]
    linarith
  have hnonneg : 0 ≤ slotWeight * premium i / marginalCost :=
    div_nonneg (mul_nonneg hWeight (hPremium i)) hCost.le
  have hcoe : (action : ℝ) ≤
      (((slotWeight * premium i / marginalCost).toNNReal : NNReal) : ℝ) := by
    rw [Real.coe_toNNReal _ hnonneg]
    exact hle
  exact_mod_cast hcoe

/-- The largest action in bidder `i`'s equilibrium support belongs to that
support. -/
theorem heterogeneous_upperSupport_mem_support
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 < marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium) (i : ι) :
    (strategy i).upperSupport ∈ (strategy i).support :=
  IsClosed.csSup_mem (strategy i).support_closed (strategy i).support_nonempty
    (heterogeneous_support_bddAbove hWeight hCost strategy hcard premium
      hPremium hnash i)

/-- Every supported action lies below the heterogeneous upper support. -/
theorem heterogeneous_le_upperSupport
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 < marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium) (i : ι) {action : NNReal}
    (hmem : action ∈ (strategy i).support) :
    action ≤ (strategy i).upperSupport :=
  le_csSup
    (heterogeneous_support_bddAbove hWeight hCost strategy hcard premium
      hPremium hnash i) hmem

/-- Upper endpoint of bidder `i`'s effective-score support. -/
def heterogeneousUpperEffectiveSupport
    (strategy : ι → BorelMixedStrategy) (premium : ι → ℝ) (i : ι) : ℝ :=
  premium i + ((strategy i).upperSupport : ℝ)

/-- A realized effective score is below its marginal upper support almost
surely. -/
theorem heterogeneous_effectiveScore_le_upperSupport_ae
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 < marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium) (i : ι) :
    ∀ᵐ profile : ι → NNReal
        ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal)),
      premium i + (profile i : ℝ) ≤
        heterogeneousUpperEffectiveSupport strategy premium i := by
  filter_upwards [heterogeneous_coordinate_ae_mem_support strategy i]
    with profile hmem
  unfold heterogeneousUpperEffectiveSupport
  have hle := heterogeneous_le_upperSupport hWeight hCost strategy hcard
    premium hPremium hnash i hmem
  have hleReal : (profile i : ℝ) ≤ ((strategy i).upperSupport : ℝ) := by
    exact_mod_cast hle
  simpa [add_comm] using add_le_add_left hleReal (premium i)

/-! ## The event in (H2) -/

/-- The event `E_j`: all bidders other than the exceptional bidder `p` and
the comparison bidder `j` have effective score at most `height`. -/
def heterogeneousExceptionalEvent
    (premium : ι → ℝ) (p j : ι) (height : ℝ) : Set (ι → NNReal) :=
  {profile | ∀ k, k ≠ p → k ≠ j →
    premium k + (profile k : ℝ) ≤ height}

theorem measurableSet_heterogeneousExceptionalEvent
    [Fintype ι] (premium : ι → ℝ) (p j : ι) (height : ℝ) :
    MeasurableSet (heterogeneousExceptionalEvent premium p j height) := by
  change MeasurableSet {profile : ι → NNReal | ∀ k, k ≠ p → k ≠ j →
    premium k + (profile k : ℝ) ≤ height}
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro hkp
  apply MeasurableSet.iInter
  intro hkj
  exact measurableSet_le
    (measurable_const.add
      (measurable_coe_nnreal_real.comp (measurable_pi_apply k)))
    measurable_const

/-- Probability of the event `E_j`. -/
def heterogeneousExceptionalEventMass
    [Fintype ι]
    (strategy : ι → BorelMixedStrategy)
    (premium : ι → ℝ) (p j : ι) (height : ℝ) : ℝ :=
  ((heterogeneousProfileLaw strategy : Measure (ι → NNReal))
    (heterogeneousExceptionalEvent premium p j height)).toReal

theorem heterogeneousExceptionalEventMass_nonneg
    [Fintype ι]
    (strategy : ι → BorelMixedStrategy)
    (premium : ι → ℝ) (p j : ι) (height : ℝ) :
    0 ≤ heterogeneousExceptionalEventMass strategy premium p j height := by
  unfold heterogeneousExceptionalEventMass
  exact ENNReal.toReal_nonneg

/-- On `E_j`, deviating to action `height` wins the comparison bidder's whole
premium, provided the exceptional bidder itself is below its support top. -/
theorem capturedPremium_at_height_eq
    [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (p j : ι) (hpj : p ≠ j) (hjPremium : 0 ≤ premium j)
    {height : ℝ} (hHeight : 0 ≤ height)
    (profile : ι → NNReal)
    (hpTop : premium p + (profile p : ℝ) ≤ height)
    (hEvent : profile ∈ heterogeneousExceptionalEvent premium p j height) :
    heterogeneousPureCapturedPremium hcard premium j height.toNNReal profile =
      premium j := by
  have hOpponent : opponentMaxEffectiveScore hcard premium j profile ≤ height := by
    apply opponentMaxEffectiveScore_le hcard premium j profile
    intro k hkj
    by_cases hkp : k = p
    · subst hkp
      exact hpTop
    · exact hEvent k hkp hkj
  unfold heterogeneousPureCapturedPremium
  rw [Real.coe_toNNReal _ hHeight]
  unfold strictPriorityCapturedGap
  have hdiff : 0 ≤ premium j + height -
      opponentMaxEffectiveScore hcard premium j profile := by linarith
  have hfull : premium j ≤ premium j + height -
      opponentMaxEffectiveScore hcard premium j profile := by linarith
  rw [max_eq_left hdiff, min_eq_right hfull]

/-- **Equation (H2).**  If bidder `j` has zero equilibrium payoff, its
deviation to the exceptional bidder's upper effective-support height yields
the event-probability bound used in the paper. -/
theorem heterogeneous_exceptional_deviation_H2
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 < marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium)
    (p j : ι) (hpj : p ≠ j)
    (hZero : heterogeneousExpectedPayoff slotWeight marginalCost strategy
      hcard premium j = 0) :
    slotWeight * premium j *
        heterogeneousExceptionalEventMass strategy premium p j
          (heterogeneousUpperEffectiveSupport strategy premium p) ≤
      marginalCost * heterogeneousUpperEffectiveSupport strategy premium p := by
  let height := heterogeneousUpperEffectiveSupport strategy premium p
  have hHeight : 0 ≤ height := by
    unfold height heterogeneousUpperEffectiveSupport
    exact add_nonneg (hPremium p) (strategy p).upperSupport.coe_nonneg
  have hTop := heterogeneous_effectiveScore_le_upperSupport_ae hWeight hCost
    strategy hcard premium hPremium hnash p
  have hCaptured :
      premium j * heterogeneousExceptionalEventMass strategy premium p j
          height ≤
        heterogeneousPureExpectedCapturedPremium strategy hcard premium j
          height.toNNReal := by
    let event := heterogeneousExceptionalEvent premium p j height
    let measure := heterogeneousProfileLaw strategy
    have hEventMeas : MeasurableSet event :=
      measurableSet_heterogeneousExceptionalEvent premium p j height
    have hIndicator : Integrable
        (event.indicator (fun _ : ι → NNReal => premium j))
        (measure : Measure (ι → NNReal)) :=
      (integrable_const (premium j)).indicator hEventMeas
    have hCapturedInt := integrable_heterogeneousPureCapturedPremium strategy
      hcard premium j (hPremium j) height.toNNReal
    have hPoint :
        event.indicator (fun _ : ι → NNReal => premium j) ≤ᵐ[
          (measure : Measure (ι → NNReal))]
          heterogeneousPureCapturedPremium hcard premium j height.toNNReal := by
      filter_upwards [hTop] with profile hpTop
      by_cases hEvent : profile ∈ event
      · rw [Set.indicator_of_mem hEvent]
        exact le_of_eq (capturedPremium_at_height_eq hcard premium p j hpj
          (hPremium j) hHeight profile hpTop hEvent).symm
      · simp only [Set.indicator, hEvent, ↓reduceIte]
        unfold heterogeneousPureCapturedPremium
        exact strictPriorityCapturedGap_nonneg (hPremium j)
    have hIntegral := integral_mono_ae hIndicator hCapturedInt hPoint
    have hLeft :
        (∫ profile : ι → NNReal,
            event.indicator (fun _ => premium j) profile
              ∂(measure : Measure (ι → NNReal))) =
          premium j * heterogeneousExceptionalEventMass strategy premium p j
            height := by
      rw [integral_indicator hEventMeas]
      change (∫ _ : ι → NNReal in event, premium j
        ∂(measure : Measure (ι → NNReal))) = _
      rw [setIntegral_const]
      simp [heterogeneousExceptionalEventMass, event, measure,
        Measure.real, mul_comm]
    rw [hLeft] at hIntegral
    exact hIntegral
  have hDeviation := hnash j height.toNNReal
  rw [hZero, heterogeneousPureExpectedPayoff,
    Real.coe_toNNReal _ hHeight] at hDeviation
  have hScaled := mul_le_mul_of_nonneg_left hCaptured hWeight
  dsimp [height] at hDeviation hScaled ⊢
  nlinarith

/-! ## Bounding the exceptional bidder's payoff -/

/-- At its upper support action, the exceptional bidder's captured premium is
bounded by its premium times the mass of `E_j`. -/
theorem heterogeneous_upperCaptured_le_eventMass
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (p j : ι) :
    heterogeneousPureExpectedCapturedPremium strategy hcard premium p
        (strategy p).upperSupport ≤
      premium p * heterogeneousExceptionalEventMass strategy premium p j
        (heterogeneousUpperEffectiveSupport strategy premium p) := by
  let height := heterogeneousUpperEffectiveSupport strategy premium p
  let event := heterogeneousExceptionalEvent premium p j height
  let measure := heterogeneousProfileLaw strategy
  have hEventMeas : MeasurableSet event :=
    measurableSet_heterogeneousExceptionalEvent premium p j height
  have hCapturedInt := integrable_heterogeneousPureCapturedPremium strategy
    hcard premium p (hPremium p) (strategy p).upperSupport
  have hIndicator : Integrable
      (event.indicator (fun _ : ι → NNReal => premium p))
      (measure : Measure (ι → NNReal)) :=
    (integrable_const (premium p)).indicator hEventMeas
  have hPoint :
      heterogeneousPureCapturedPremium hcard premium p
          (strategy p).upperSupport ≤ᵐ[(measure : Measure (ι → NNReal))]
        event.indicator (fun _ : ι → NNReal => premium p) := by
    filter_upwards with profile
    by_cases hEvent : profile ∈ event
    · rw [Set.indicator_of_mem hEvent]
      unfold heterogeneousPureCapturedPremium
      exact strictPriorityCapturedGap_le_gap
    · simp only [Set.indicator, hEvent, ↓reduceIte]
      have hWitness : ∃ k, k ≠ p ∧ k ≠ j ∧
          height < premium k + (profile k : ℝ) := by
        simpa [event, heterogeneousExceptionalEvent, not_forall,
          not_le] using hEvent
      obtain ⟨k, hkp, hkj, hk⟩ := hWitness
      have hOpponent := opponent_effectiveScore_le_max hcard premium p k hkp
        profile
      have hOwn : premium p + ((strategy p).upperSupport : ℝ) = height := by
        rfl
      have hDominated : premium p + ((strategy p).upperSupport : ℝ) ≤
          opponentMaxEffectiveScore hcard premium p profile := by
        linarith
      unfold heterogeneousPureCapturedPremium
      simp [strictPriorityCapturedGap, sub_nonpos.mpr hDominated]
  have hIntegral := integral_mono_ae hCapturedInt hIndicator hPoint
  have hRight :
      (∫ profile : ι → NNReal,
          event.indicator (fun _ => premium p) profile
            ∂(measure : Measure (ι → NNReal))) =
        premium p * heterogeneousExceptionalEventMass strategy premium p j
          height := by
    rw [integral_indicator hEventMeas]
    change (∫ _ : ι → NNReal in event, premium p
      ∂(measure : Measure (ι → NNReal))) = _
    rw [setIntegral_const]
    simp [heterogeneousExceptionalEventMass, event, measure, Measure.real,
      mul_comm]
  unfold heterogeneousPureExpectedCapturedPremium
  rw [hRight] at hIntegral
  exact hIntegral

/-- **Equation (H3).**  A positive-payoff bidder's rent is bounded by the
height of its upper effective support and any zero-payoff comparison bidder. -/
theorem heterogeneous_exceptional_payoff_H3
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 < marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium)
    (p j : ι) (hpj : p ≠ j) (hjPositive : 0 < premium j)
    (hZero : heterogeneousExpectedPayoff slotWeight marginalCost strategy
      hcard premium j = 0) :
    heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard premium p ≤
      marginalCost * premium p +
        marginalCost * heterogeneousUpperEffectiveSupport strategy premium p *
          (premium p - premium j) / premium j := by
  let height := heterogeneousUpperEffectiveSupport strategy premium p
  let eventMass := heterogeneousExceptionalEventMass strategy premium p j height
  have hH2 := heterogeneous_exceptional_deviation_H2 hWeight hCost strategy
    hcard premium hPremium hnash p j hpj hZero
  have hCaptured := heterogeneous_upperCaptured_le_eventMass strategy hcard
    premium hPremium p j
  have hTopMem := heterogeneous_upperSupport_mem_support hWeight hCost strategy
    hcard premium hPremium hnash p
  have hPayoff := heterogeneousMixedBestResponse_payoff_eq_on_support
    slotWeight marginalCost strategy hcard premium p (hPremium p) (hnash p)
    (strategy p).upperSupport hTopMem
  have hScaled := mul_le_mul_of_nonneg_left hCaptured hWeight
  have hRatioNonneg : 0 ≤ premium p / premium j :=
    div_nonneg (hPremium p) hjPositive.le
  have hH2Scaled := mul_le_mul_of_nonneg_right hH2 hRatioNonneg
  have hCancel :
      (slotWeight * premium j * eventMass) * (premium p / premium j) =
        slotWeight * premium p * eventMass := by
    field_simp
  have hScaledEvent :
      slotWeight * premium p * eventMass ≤
        marginalCost * height * (premium p / premium j) := by
    rw [← hCancel]
    exact hH2Scaled
  calc
    heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
        premium p =
      slotWeight * heterogeneousPureExpectedCapturedPremium strategy hcard
          premium p (strategy p).upperSupport -
        marginalCost * ((strategy p).upperSupport : ℝ) := by
      rw [← hPayoff]
      rfl
    _ ≤ slotWeight * (premium p * eventMass) -
          marginalCost * ((strategy p).upperSupport : ℝ) :=
      sub_le_sub_right hScaled _
    _ ≤ marginalCost * height * (premium p / premium j) -
          marginalCost * ((strategy p).upperSupport : ℝ) :=
      by simpa [mul_assoc] using
        (sub_le_sub_right hScaledEvent
          (marginalCost * ((strategy p).upperSupport : ℝ)))
    _ = marginalCost * premium p + marginalCost * height *
          (premium p - premium j) / premium j := by
      dsimp [height]
      unfold heterogeneousUpperEffectiveSupport
      field_simp
      ring

/-- A positive exceptional payoff forces the upper support below the
whole-prize action bound. -/
theorem heterogeneous_positivePayoff_upperSupport_bound
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 < marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium) (p : ι)
    (hPositive : 0 < heterogeneousExpectedPayoff slotWeight marginalCost
      strategy hcard premium p) :
    heterogeneousUpperEffectiveSupport strategy premium p <
      premium p + slotWeight * premium p / marginalCost := by
  have hTopMem := heterogeneous_upperSupport_mem_support hWeight hCost strategy
    hcard premium hPremium hnash p
  have hPayoff := heterogeneousMixedBestResponse_payoff_eq_on_support
    slotWeight marginalCost strategy hcard premium p (hPremium p) (hnash p)
    (strategy p).upperSupport hTopMem
  have hCaptured := heterogeneousPureExpectedCapturedPremium_le_premium
    strategy hcard premium p (hPremium p) (strategy p).upperSupport
  rw [← hPayoff, heterogeneousPureExpectedPayoff] at hPositive
  have hAction : marginalCost * ((strategy p).upperSupport : ℝ) <
      slotWeight * premium p := by
    nlinarith [mul_le_mul_of_nonneg_left hCaptured hWeight]
  have hTop : ((strategy p).upperSupport : ℝ) <
      slotWeight * premium p / marginalCost := by
    rw [lt_div_iff₀ hCost]
    nlinarith
  unfold heterogeneousUpperEffectiveSupport
  linarith

/-- **Equation (H4).**  If the zero-payoff comparison bidder has weakly lower
premium, then the exceptional bidder's payoff is bounded by the displayed
exceptional-rent cap.  No support-height premise remains. -/
theorem heterogeneous_positivePayoff_le_exceptionalRentCap
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 < marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium)
    (p j : ι) (hpj : p ≠ j) (hjPositive : 0 < premium j)
    (hOrder : premium j ≤ premium p)
    (hZero : heterogeneousExpectedPayoff slotWeight marginalCost strategy
      hcard premium j = 0)
    (hPositive : 0 < heterogeneousExpectedPayoff slotWeight marginalCost
      strategy hcard premium p) :
    heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard premium p ≤
      heterogeneousExceptionalRentCap slotWeight marginalCost
        (premium p) (premium j) := by
  have hH3 := heterogeneous_exceptional_payoff_H3 hWeight hCost strategy hcard
    premium hPremium hnash p j hpj hjPositive hZero
  have hHeight := heterogeneous_positivePayoff_upperSupport_bound hWeight hCost
    strategy hcard premium hPremium hnash p hPositive
  exact le_trans hH3 (exceptionalRent_intermediate_le_cap hCost hjPositive
    hOrder hHeight.le)

/-- If the comparison bidder's premium is at least the exceptional bidder's,
the correction term in (H3) is nonpositive and one band's latency cost already
caps the rent. -/
theorem heterogeneous_exceptional_payoff_le_costPremium_of_le
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 < marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium)
    (p j : ι) (hpj : p ≠ j) (hjPositive : 0 < premium j)
    (hOrder : premium p ≤ premium j)
    (hZero : heterogeneousExpectedPayoff slotWeight marginalCost strategy
      hcard premium j = 0) :
    heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard premium p ≤
      marginalCost * premium p := by
  have hH3 := heterogeneous_exceptional_payoff_H3 hWeight hCost strategy hcard
    premium hPremium hnash p j hpj hjPositive hZero
  have hHeight : 0 ≤ heterogeneousUpperEffectiveSupport strategy premium p := by
    unfold heterogeneousUpperEffectiveSupport
    exact add_nonneg (hPremium p) (strategy p).upperSupport.coe_nonneg
  have hRatio : (premium p - premium j) / premium j ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hOrder) hjPositive.le
  have hCorrection :
      marginalCost * heterogeneousUpperEffectiveSupport strategy premium p *
          ((premium p - premium j) / premium j) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg hCost.le hHeight) hRatio
  have hRewrite :
      marginalCost * heterogeneousUpperEffectiveSupport strategy premium p *
          (premium p - premium j) / premium j =
        marginalCost * heterogeneousUpperEffectiveSupport strategy premium p *
          ((premium p - premium j) / premium j) := by ring
  rw [hRewrite] at hH3
  linarith

/-- The order-statistic wrapper for (H4).  `top` and `second` may be the actual
indices attaining the largest and second-largest premia.  The proof in fact
only needs that `top` is largest and that `second` is a distinct bidder with
positive premium.  Every positive equilibrium payoff then obeys the paper's
global exceptional-rent cap. -/
theorem heterogeneousMixedNash_positivePayoff_le_globalExceptionalRentCap
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 < marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium)
    (top second : ι) (hDistinct : second ≠ top)
    (hTop : ∀ i, premium i ≤ premium top)
    (hSecondPositive : 0 < premium second)
    (p : ι)
    (hPositive : 0 < heterogeneousExpectedPayoff slotWeight marginalCost
      strategy hcard premium p) :
    heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard premium p ≤
      heterogeneousExceptionalRentCap slotWeight marginalCost
        (premium top) (premium second) := by
  have hPayoffNonneg := heterogeneousMixedNash_payoff_nonneg hWeight strategy
    hcard premium hPremium hnash
  have hAtMost := heterogeneousMixedNash_atMostOnePositive hWeight hCost.le
    strategy hcard premium hPremium hnash
  by_cases hpTop : p = top
  · subst p
    have hSecondZero : heterogeneousExpectedPayoff slotWeight marginalCost
        strategy hcard premium second = 0 := by
      have hNotPositive : ¬ 0 < heterogeneousExpectedPayoff slotWeight
          marginalCost strategy hcard premium second := by
        intro hs
        have heq := hAtMost hPositive hs
        exact hDistinct heq.symm
      exact le_antisymm (le_of_not_gt hNotPositive) (hPayoffNonneg second)
    exact heterogeneous_positivePayoff_le_exceptionalRentCap hWeight hCost
      strategy hcard premium hPremium hnash top second hDistinct.symm
      hSecondPositive (hTop second) hSecondZero hPositive
  · have hTopZero : heterogeneousExpectedPayoff slotWeight marginalCost
        strategy hcard premium top = 0 := by
      have hNotPositive : ¬ 0 < heterogeneousExpectedPayoff slotWeight
          marginalCost strategy hcard premium top := by
        intro ht
        exact hpTop (hAtMost hPositive ht)
      exact le_antisymm (le_of_not_gt hNotPositive) (hPayoffNonneg top)
    have hLocal := heterogeneous_exceptional_payoff_le_costPremium_of_le
      hWeight hCost strategy hcard premium hPremium hnash p top hpTop
      (lt_of_lt_of_le hSecondPositive (hTop second)) (hTop p) hTopZero
    have hSecondTop : premium second ≤ premium top := hTop second
    have hSumNonneg : 0 ≤ slotWeight + marginalCost :=
      add_nonneg hWeight hCost.le
    have hTopNonneg : 0 ≤ premium top :=
      le_trans hSecondPositive.le hSecondTop
    have hGapNonneg : 0 ≤ premium top - premium second :=
      sub_nonneg.mpr hSecondTop
    have hCorrectionNonneg :
        0 ≤ (slotWeight + marginalCost) * premium top *
          (premium top - premium second) / premium second := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg hSumNonneg hTopNonneg) hGapNonneg)
        hSecondPositive.le
    unfold heterogeneousExceptionalRentCap
    have hCostOrder := mul_le_mul_of_nonneg_left (hTop p) hCost.le
    linarith

end

end SmoothingCliff.Racing
