import SmoothingCliff.Racing.HeterogeneousMixedProfile
import SmoothingCliff.Racing.HeterogeneousAggregateFloor

/-!
# Support classification in the heterogeneous strict-priority race

This file derives the support facts used by the heterogeneous dissipation
floor directly from `IsHeterogeneousBorelMixedNash`.  In particular, the
at-most-one-positive-payoff conclusion is not included as an extra premise.

The argument compares the lower endpoints of the bidders' effective-score
supports.  If bidder `i`'s lower effective score is weakly below that of some
opponent, then at the lower endpoint of `i`'s action support this opponent is
weakly ahead almost surely.  Support indifference and the zero-action
deviation then force bidder `i`'s equilibrium payoff to be zero.  Hence two
distinct bidders cannot both have positive payoff.
-/

namespace SmoothingCliff.Racing

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

noncomputable section

variable {ι : Type*}

/-- Lower endpoint of bidder `i`'s effective-score support. -/
def heterogeneousLowerEffectiveSupport
    (strategy : ι → BorelMixedStrategy) (premium : ι → ℝ) (i : ι) : ℝ :=
  premium i + ((strategy i).lowerSupport : ℝ)

/-- A sampled coordinate of the heterogeneous product profile lies in the
support of its marginal law almost surely. -/
theorem heterogeneous_coordinate_ae_mem_support
    [Fintype ι] (strategy : ι → BorelMixedStrategy) (i : ι) :
    ∀ᵐ profile : ι → NNReal
        ∂(heterogeneousProfileLaw strategy : Measure (ι → NNReal)),
      profile i ∈ (strategy i).support := by
  have heval : MeasurePreserving (Function.eval i)
      (heterogeneousProfileLaw strategy : Measure (ι → NNReal))
      ((strategy i).law : Measure NNReal) := by
    change MeasurePreserving (Function.eval i)
      (Measure.pi fun j : ι => ((strategy j).law : Measure NNReal))
      ((strategy i).law : Measure NNReal)
    exact measurePreserving_eval _ i
  exact heval.quasiMeasurePreserving.ae (strategy i).ae_mem_support

/-- The expected captured premium from action zero is nonnegative. -/
theorem heterogeneousPureExpectedPayoff_zero_nonneg
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i) :
    0 ≤ heterogeneousPureExpectedPayoff slotWeight marginalCost strategy hcard
      premium i 0 := by
  have hCaptured : 0 ≤
      heterogeneousPureExpectedCapturedPremium strategy hcard premium i 0 := by
    unfold heterogeneousPureExpectedCapturedPremium
    apply integral_nonneg
    intro profile
    unfold heterogeneousPureCapturedPremium
    exact strictPriorityCapturedGap_nonneg hpremium
  unfold heterogeneousPureExpectedPayoff
  norm_num
  exact mul_nonneg hWeight hCaptured

/-- Every equilibrium payoff is nonnegative because the pure zero-action
deviation has nonnegative payoff. -/
theorem heterogeneousMixedNash_payoff_nonneg
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium) (i : ι) :
    0 ≤ heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
      premium i := by
  exact le_trans
    (heterogeneousPureExpectedPayoff_zero_nonneg hWeight strategy hcard premium
      i (hPremium i))
    (hnash i 0)

/-- Pure-deviation expected captured premium is continuous in the deviating
action. -/
theorem heterogeneousPureExpectedCapturedPremium_continuous
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i) :
    Continuous
      (heterogeneousPureExpectedCapturedPremium strategy hcard premium i) := by
  unfold heterogeneousPureExpectedCapturedPremium
  apply continuous_of_dominated (bound := fun _ : ι → NNReal => premium i)
  · intro action
    exact
      (measurable_heterogeneousPureCapturedPremium hcard premium i action).aestronglyMeasurable
  · intro action
    filter_upwards with profile
    unfold heterogeneousPureCapturedPremium
    rw [Real.norm_eq_abs,
      abs_of_nonneg (strictPriorityCapturedGap_nonneg hpremium)]
    exact strictPriorityCapturedGap_le_gap
  · exact integrable_const (premium i)
  · filter_upwards with profile
    unfold heterogeneousPureCapturedPremium strictPriorityCapturedGap
    fun_prop

/-- Pure-deviation expected payoffs are continuous in the deviating action. -/
theorem heterogeneousPureExpectedPayoff_continuous
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i) :
    Continuous (heterogeneousPureExpectedPayoff slotWeight marginalCost
      strategy hcard premium i) := by
  unfold heterogeneousPureExpectedPayoff
  exact
    (continuous_const.mul
      (heterogeneousPureExpectedCapturedPremium_continuous strategy hcard
        premium i hpremium)).sub
      (continuous_const.mul continuous_subtype_val)

/-- The own-law family of pure-deviation captured premia is integrable. -/
theorem integrable_heterogeneousPureExpectedCapturedPremium
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i) :
    Integrable
      (heterogeneousPureExpectedCapturedPremium strategy hcard premium i)
      ((strategy i).law : Measure NNReal) := by
  have hcomp : Integrable
      (fun p : NNReal × (ι → NNReal) =>
        heterogeneousPureCapturedPremium hcard premium i p.1 p.2)
      (((strategy i).law : Measure NNReal).prod
        (heterogeneousProfileLaw strategy : Measure (ι → NNReal))) := by
    refine Integrable.mono' (integrable_const (premium i)) ?_ ?_
    · have hown : Measurable (fun p : NNReal × (ι → NNReal) =>
          premium i + (p.1 : ℝ)) :=
        measurable_const.add
          (measurable_coe_nnreal_real.comp measurable_fst)
      have hmax : Measurable (fun p : NNReal × (ι → NNReal) =>
          opponentMaxEffectiveScore hcard premium i p.2) :=
        (measurable_opponentMaxEffectiveScore hcard premium i).comp
          measurable_snd
      have hmeas : Measurable (fun p : NNReal × (ι → NNReal) =>
          heterogeneousPureCapturedPremium hcard premium i p.1 p.2) := by
        unfold heterogeneousPureCapturedPremium strictPriorityCapturedGap
        exact (hown.sub hmax).max measurable_const |>.min measurable_const
      exact hmeas.aestronglyMeasurable
    · filter_upwards with p
      unfold heterogeneousPureCapturedPremium
      rw [Real.norm_eq_abs,
        abs_of_nonneg (strictPriorityCapturedGap_nonneg hpremium)]
      exact strictPriorityCapturedGap_le_gap
  simpa [heterogeneousPureExpectedCapturedPremium] using
    hcomp.integral_prod_left

/-- Pure-deviation payoffs are integrable under the bidder's own equilibrium
law. -/
theorem integrable_heterogeneousPureExpectedPayoff
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i) :
    Integrable
      (heterogeneousPureExpectedPayoff slotWeight marginalCost strategy hcard
        premium i)
      ((strategy i).law : Measure NNReal) := by
  unfold heterogeneousPureExpectedPayoff
  exact
    ((integrable_heterogeneousPureExpectedCapturedPremium strategy hcard
      premium i hpremium).const_mul slotWeight).sub
      ((strategy i).integrable_action.const_mul marginalCost)

/-- A genuine mixed best response is indifferent among all actions in its
topological support. -/
theorem heterogeneousMixedBestResponse_payoff_eq_on_support
    [Fintype ι] [DecidableEq ι]
    (slotWeight marginalCost : ℝ)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i : ι) (hpremium : 0 ≤ premium i)
    (hbest : IsHeterogeneousBorelMixedBestResponse slotWeight marginalCost
      strategy hcard premium i) :
    ∀ action ∈ (strategy i).support,
      heterogeneousPureExpectedPayoff slotWeight marginalCost strategy hcard
          premium i action =
        heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
          premium i := by
  have hintegrable := integrable_heterogeneousPureExpectedPayoff slotWeight
    marginalCost strategy hcard premium i hpremium
  have hconstant : Integrable (fun _ : NNReal =>
      heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
        premium i) ((strategy i).law : Measure NNReal) :=
    integrable_const _
  have hle :
      (fun action : NNReal =>
        heterogeneousPureExpectedPayoff slotWeight marginalCost strategy hcard
          premium i action) ≤ᵐ[((strategy i).law : Measure NNReal)]
        (fun _ => heterogeneousExpectedPayoff slotWeight marginalCost strategy
          hcard premium i) :=
    Filter.Eventually.of_forall hbest
  have hae :
      (fun action : NNReal =>
        heterogeneousPureExpectedPayoff slotWeight marginalCost strategy hcard
          premium i action) =ᵐ[((strategy i).law : Measure NNReal)]
        (fun _ => heterogeneousExpectedPayoff slotWeight marginalCost strategy
          hcard premium i) := by
    apply (integral_eq_iff_of_ae_le hintegrable hconstant hle).mp
    rw [← heterogeneousExpectedPayoff_eq_integral_pure slotWeight marginalCost
      strategy hcard premium i hpremium]
    simp
  exact eq_on_measureSupport_of_continuous_of_ae_eq
    (heterogeneousPureExpectedPayoff_continuous slotWeight marginalCost
      strategy hcard premium i hpremium) hae

/-- If another bidder's lower effective support is weakly higher, then the
captured premium at bidder `i`'s own lower support is zero. -/
theorem heterogeneousPureExpectedCapturedPremium_lower_eq_zero
    [Fintype ι] [DecidableEq ι]
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (i j : ι) (hji : j ≠ i)
    (hpremium : 0 ≤ premium i)
    (hlower : heterogeneousLowerEffectiveSupport strategy premium i ≤
      heterogeneousLowerEffectiveSupport strategy premium j) :
    heterogeneousPureExpectedCapturedPremium strategy hcard premium i
      (strategy i).lowerSupport = 0 := by
  unfold heterogeneousPureExpectedCapturedPremium
  apply integral_eq_zero_of_ae
  filter_upwards [heterogeneous_coordinate_ae_mem_support strategy j]
    with profile hjSupport
  have hjLower : (strategy j).lowerSupport ≤ profile j :=
    (strategy j).lowerSupport_le_of_mem_support hjSupport
  have hjLowerReal : ((strategy j).lowerSupport : ℝ) ≤ (profile j : ℝ) := by
    exact_mod_cast hjLower
  have hOpponent :
      premium j + (profile j : ℝ) ≤
        opponentMaxEffectiveScore hcard premium i profile :=
    opponent_effectiveScore_le_max hcard premium i j hji profile
  have hScore :
      premium i + ((strategy i).lowerSupport : ℝ) ≤
        opponentMaxEffectiveScore hcard premium i profile := by
    unfold heterogeneousLowerEffectiveSupport at hlower
    linarith
  unfold heterogeneousPureCapturedPremium
  simp [strictPriorityCapturedGap, sub_nonpos.mpr hScore, hpremium]

/-- A bidder whose lower effective support is weakly below that of some
opponent has zero equilibrium payoff. -/
theorem heterogeneousMixedNash_payoff_eq_zero_of_lower_le
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 ≤ marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium)
    (i j : ι) (hji : j ≠ i)
    (hlower : heterogeneousLowerEffectiveSupport strategy premium i ≤
      heterogeneousLowerEffectiveSupport strategy premium j) :
    heterogeneousExpectedPayoff slotWeight marginalCost strategy hcard
      premium i = 0 := by
  have hsupport :=
    heterogeneousMixedBestResponse_payoff_eq_on_support slotWeight marginalCost
      strategy hcard premium i (hPremium i) (hnash i)
      (strategy i).lowerSupport (strategy i).lowerSupport_mem_support
  have hcaptured :=
    heterogeneousPureExpectedCapturedPremium_lower_eq_zero strategy hcard
      premium i j hji (hPremium i) hlower
  have hpureNonpos :
      heterogeneousPureExpectedPayoff slotWeight marginalCost strategy hcard
        premium i (strategy i).lowerSupport ≤ 0 := by
    rw [heterogeneousPureExpectedPayoff, hcaptured]
    have haction : 0 ≤ ((strategy i).lowerSupport : ℝ) := by positivity
    nlinarith
  have hnonneg := heterogeneousMixedNash_payoff_nonneg hWeight strategy hcard
    premium hPremium hnash i
  exact le_antisymm (by simpa [hsupport] using hpureNonpos) hnonneg

/-- Positive payoff identifies a strict maximum of the lower effective-score
supports.  This is the support-ordering input to the exceptional-rent branch. -/
theorem heterogeneousLowerEffectiveSupport_lt_of_positivePayoff
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 ≤ marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium)
    (i : ι)
    (hPositive : 0 < heterogeneousExpectedPayoff slotWeight marginalCost
      strategy hcard premium i) :
    ∀ j, j ≠ i →
      heterogeneousLowerEffectiveSupport strategy premium j <
        heterogeneousLowerEffectiveSupport strategy premium i := by
  intro j hji
  apply lt_of_not_ge
  intro hle
  have hzero := heterogeneousMixedNash_payoff_eq_zero_of_lower_le hWeight hCost
    strategy hcard premium hPremium hnash i j hji hle
  linarith

/-- **Support classification for the heterogeneous mixed race.**  At most one
equilibrium payoff is strictly positive. -/
theorem heterogeneousMixedNash_atMostOnePositive
    [Fintype ι] [DecidableEq ι]
    {slotWeight marginalCost : ℝ}
    (hWeight : 0 ≤ slotWeight) (hCost : 0 ≤ marginalCost)
    (strategy : ι → BorelMixedStrategy)
    (hcard : 2 ≤ Fintype.card ι) (premium : ι → ℝ)
    (hPremium : ∀ i, 0 ≤ premium i)
    (hnash : IsHeterogeneousBorelMixedNash slotWeight marginalCost strategy
      hcard premium) :
    AtMostOnePositive (fun i => heterogeneousExpectedPayoff slotWeight
      marginalCost strategy hcard premium i) := by
  intro i j hi hj
  by_contra hij
  have hji : j ≠ i := Ne.symm hij
  have hlt_ji := heterogeneousLowerEffectiveSupport_lt_of_positivePayoff
    hWeight hCost strategy hcard premium hPremium hnash i hi j hji
  have hlt_ij := heterogeneousLowerEffectiveSupport_lt_of_positivePayoff
    hWeight hCost strategy hcard premium hPremium hnash j hj i hij
  exact (not_lt_of_ge hlt_ji.le) hlt_ij

end

end SmoothingCliff.Racing
