import SmoothingCliff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Single-call resampling bounds

This file formalizes Lemmas `lem:wrapper_wedge` and `lem:wrapper_cert` from
*Smoothing the Cliff*.

For the wedge lemma, `badEventProbability n mu = 1 - (1 - mu)^n` is the
probability that at least one of `n` independent coordinates is resampled.
Conditioning on that event turns the deployed allocation into an explicit
two-component mixture.  The payment result uses the full Myerson identity
from zero; equality below the reserve is kept as an explicit premise because
it is the step that reduces the integral to the eligible interval.

For the certificate lemma, total-variation Lipschitz continuity is encoded by
its bounded-test-function dual characterization for probability measures.
With the convention used here, this is the usual probability distance
`sup_A |P A - Q A|`, equivalently the supremum of expectation differences over
measurable functions taking values in `[0, 1]`.
-/

namespace SmoothingCliff.Wrapper

open MeasureTheory
open scoped Interval

/-! ## The resampling event and allocation wedge -/

/-- Probability that at least one of `n` independent coordinates, each
resampled with probability `mu`, is resampled. -/
def badEventProbability (n : ℕ) (mu : ℝ) : ℝ :=
  1 - (1 - mu) ^ n

/-- Conditional-expectation decomposition into the no-resampling and
resampling events. -/
def eventMixture
    (badProbability baseline conditionalBadMean : ℝ) : ℝ :=
  (1 - badProbability) * baseline +
    badProbability * conditionalBadMean

/-- Deployed allocation at a fixed report after conditioning on whether some
coordinate was resampled. -/
def resampledAllocation
    (n : ℕ) (mu baseline conditionalBadMean : ℝ) : ℝ :=
  eventMixture (badEventProbability n mu) baseline conditionalBadMean

/-- Pointwise version of `resampledAllocation` for an allocation curve. -/
def resampledAllocationRule
    (n : ℕ) (mu : ℝ) (base conditionalBadMean : ℝ → ℝ) : ℝ → ℝ :=
  fun bid => resampledAllocation n mu (base bid) (conditionalBadMean bid)

/-- The probability of at least one resampling lies in `[0,1]`. -/
theorem badEventProbability_mem_Icc
    (n : ℕ) (mu : ℝ) (hMu : mu ∈ Set.Icc (0 : ℝ) 1) :
    badEventProbability n mu ∈ Set.Icc (0 : ℝ) 1 := by
  have hBaseNonneg : 0 ≤ 1 - mu := by linarith [hMu.2]
  have hBaseLeOne : 1 - mu ≤ 1 := by linarith [hMu.1]
  have hPowNonneg : 0 ≤ (1 - mu) ^ n := pow_nonneg hBaseNonneg n
  have hPowLeOne : (1 - mu) ^ n ≤ 1 :=
    pow_le_one₀ hBaseNonneg hBaseLeOne
  constructor <;> dsimp [badEventProbability] <;> linarith

/-- Bernoulli's inequality gives the union bound
`1 - (1 - mu)^n ≤ n * mu`.  The lower bound on `mu` is not needed for this
algebraic inequality; it is imposed when the expression is used as a
probability. -/
theorem badEventProbability_le_unionBound
    (n : ℕ) (mu : ℝ) (hMuUpper : mu ≤ 1) :
    badEventProbability n mu ≤ (n : ℝ) * mu := by
  have hBernoulli :=
    one_add_mul_le_pow (a := -mu)
      (by linarith : (-2 : ℝ) ≤ -mu) n
  have hBernoulli' : 1 - (n : ℝ) * mu ≤ (1 - mu) ^ n := by
    simpa [sub_eq_add_neg] using hBernoulli
  dsimp [badEventProbability]
  linarith

/-- If the outcome agrees with the baseline off an event of probability
`badProbability`, and both conditional means lie in `[0,weight]`, then the
expectation moves by at most `badProbability * weight`. -/
theorem allocation_wedge_of_eventMixture
    (badProbability baseline conditionalBadMean weight : ℝ)
    (hBadProbability : badProbability ∈ Set.Icc (0 : ℝ) 1)
    (hBaseline : baseline ∈ Set.Icc (0 : ℝ) weight)
    (hBadMean : conditionalBadMean ∈ Set.Icc (0 : ℝ) weight) :
    |eventMixture badProbability baseline conditionalBadMean - baseline| ≤
      badProbability * weight := by
  have hDifference : |conditionalBadMean - baseline| ≤ weight := by
    rw [abs_le]
    constructor <;>
      linarith [hBaseline.1, hBaseline.2, hBadMean.1, hBadMean.2]
  rw [show eventMixture badProbability baseline conditionalBadMean - baseline =
      badProbability * (conditionalBadMean - baseline) by
        simp only [eventMixture]
        ring,
    abs_mul, abs_of_nonneg hBadProbability.1]
  exact mul_le_mul_of_nonneg_left hDifference hBadProbability.1

/-- First inequality in `lem:wrapper_wedge`. -/
theorem resampling_allocation_wedge
    (n : ℕ) (mu baseline conditionalBadMean weight : ℝ)
    (hMu : mu ∈ Set.Icc (0 : ℝ) 1)
    (hBaseline : baseline ∈ Set.Icc (0 : ℝ) weight)
    (hBadMean : conditionalBadMean ∈ Set.Icc (0 : ℝ) weight) :
    |resampledAllocation n mu baseline conditionalBadMean - baseline| ≤
      badEventProbability n mu * weight := by
  exact allocation_wedge_of_eventMixture
    (badEventProbability n mu) baseline conditionalBadMean weight
    (badEventProbability_mem_Icc n mu hMu) hBaseline hBadMean

/-- Second inequality in `lem:wrapper_wedge`. -/
theorem resampling_allocation_wedge_unionBound
    (n : ℕ) (mu baseline conditionalBadMean weight : ℝ)
    (hMu : mu ∈ Set.Icc (0 : ℝ) 1)
    (hWeight : 0 ≤ weight)
    (hBaseline : baseline ∈ Set.Icc (0 : ℝ) weight)
    (hBadMean : conditionalBadMean ∈ Set.Icc (0 : ℝ) weight) :
    |resampledAllocation n mu baseline conditionalBadMean - baseline| ≤
      (n : ℝ) * mu * weight := by
  calc
    |resampledAllocation n mu baseline conditionalBadMean - baseline| ≤
        badEventProbability n mu * weight :=
      resampling_allocation_wedge
        n mu baseline conditionalBadMean weight hMu hBaseline hBadMean
    _ ≤ ((n : ℝ) * mu) * weight :=
      mul_le_mul_of_nonneg_right
        (badEventProbability_le_unionBound n mu hMu.2) hWeight

/-! ## Myerson payments -/

/-- Myerson payment with the paper's zero normalization. -/
noncomputable def myersonPayment
    (bid : ℝ) (allocation : ℝ → ℝ) : ℝ :=
  bid * allocation bid - ∫ z in (0 : ℝ)..bid, allocation z

/-- The same payment written after restricting the integral to the eligible
interval.  It agrees with `myersonPayment` in differences when the two rules
coincide below the reserve. -/
noncomputable def eligibleMyersonPayment
    (reserve bid : ℝ) (allocation : ℝ → ℝ) : ℝ :=
  bid * allocation bid - ∫ z in reserve..bid, allocation z

/-- Equality below the reserve removes the common ineligible part of the two
Myerson integrals.  In the paper both curves vanish there. -/
theorem myersonPayment_difference_eq_eligible
    (reserve bid : ℝ) (base deployed : ℝ → ℝ)
    (hBaseBelow : IntervalIntegrable base volume 0 reserve)
    (hDeployedBelow : IntervalIntegrable deployed volume 0 reserve)
    (hBaseEligible : IntervalIntegrable base volume reserve bid)
    (hDeployedEligible : IntervalIntegrable deployed volume reserve bid)
    (hBelow : Set.EqOn deployed base (Set.uIcc (0 : ℝ) reserve)) :
    myersonPayment bid deployed - myersonPayment bid base =
      eligibleMyersonPayment reserve bid deployed -
        eligibleMyersonPayment reserve bid base := by
  have hBelowIntegral :
      (∫ z in (0 : ℝ)..reserve, deployed z) =
        ∫ z in (0 : ℝ)..reserve, base z :=
    intervalIntegral.integral_congr hBelow
  have hDeployedSplit :=
    intervalIntegral.integral_add_adjacent_intervals
      hDeployedBelow hDeployedEligible
  have hBaseSplit :=
    intervalIntegral.integral_add_adjacent_intervals
      hBaseBelow hBaseEligible
  simp only [myersonPayment, eligibleMyersonPayment]
  rw [← hDeployedSplit, ← hBaseSplit, hBelowIntegral]
  ring

/-- A uniform allocation wedge `delta` on `[reserve,bid]` gives a
`2 * bidCap * delta` wedge between the eligible Myerson payments. -/
theorem eligibleMyersonPayment_wedge
    (reserve bid bidCap delta : ℝ)
    (base deployed : ℝ → ℝ)
    (hReserveNonneg : 0 ≤ reserve)
    (hBidEligible : reserve ≤ bid)
    (hBidCap : bid ≤ bidCap)
    (hDelta : 0 ≤ delta)
    (hBaseIntegrable : IntervalIntegrable base volume reserve bid)
    (hDeployedIntegrable : IntervalIntegrable deployed volume reserve bid)
    (hAllocationWedge :
      ∀ z ∈ Set.Icc reserve bid, |deployed z - base z| ≤ delta) :
    |eligibleMyersonPayment reserve bid deployed -
        eligibleMyersonPayment reserve bid base| ≤
      2 * bidCap * delta := by
  have hBidNonneg : 0 ≤ bid := le_trans hReserveNonneg hBidEligible
  have hLength : |bid - reserve| ≤ bidCap := by
    rw [abs_of_nonneg (sub_nonneg.mpr hBidEligible)]
    linarith
  have hIntegral :
      |∫ z in reserve..bid, deployed z - base z| ≤
        delta * |bid - reserve| := by
    have hNorm :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (a := reserve) (b := bid) (C := delta)
        (f := fun z => deployed z - base z) (by
          intro z hz
          rw [Set.uIoc_of_le hBidEligible] at hz
          simpa [Real.norm_eq_abs] using
            hAllocationWedge z ⟨le_of_lt hz.1, hz.2⟩)
    simpa [Real.norm_eq_abs] using hNorm
  have hIntegralSub :
      (∫ z in reserve..bid, deployed z - base z) =
        (∫ z in reserve..bid, deployed z) -
          ∫ z in reserve..bid, base z :=
    intervalIntegral.integral_sub hDeployedIntegrable hBaseIntegrable
  have hBidTerm :
      |bid * (deployed bid - base bid)| ≤ bid * delta := by
    rw [abs_mul, abs_of_nonneg hBidNonneg]
    exact mul_le_mul_of_nonneg_left
      (hAllocationWedge bid ⟨hBidEligible, le_rfl⟩) hBidNonneg
  calc
    |eligibleMyersonPayment reserve bid deployed -
        eligibleMyersonPayment reserve bid base| =
        |bid * (deployed bid - base bid) -
          ∫ z in reserve..bid, deployed z - base z| := by
            simp only [eligibleMyersonPayment]
            rw [hIntegralSub]
            ring_nf
    _ ≤ |bid * (deployed bid - base bid)| +
        |∫ z in reserve..bid, deployed z - base z| := abs_sub _ _
    _ ≤ bid * delta + delta * |bid - reserve| :=
      add_le_add hBidTerm hIntegral
    _ ≤ bidCap * delta + delta * bidCap :=
      add_le_add
        (mul_le_mul_of_nonneg_right hBidCap hDelta)
        (mul_le_mul_of_nonneg_left hLength hDelta)
    _ = 2 * bidCap * delta := by ring

/-- The payment part of `lem:wrapper_wedge`, stated for the paper's full
zero-normalized Myerson payments. -/
theorem myersonPayment_wedge
    (reserve bid bidCap delta : ℝ)
    (base deployed : ℝ → ℝ)
    (hReserveNonneg : 0 ≤ reserve)
    (hBidEligible : reserve ≤ bid)
    (hBidCap : bid ≤ bidCap)
    (hDelta : 0 ≤ delta)
    (hBaseBelow : IntervalIntegrable base volume 0 reserve)
    (hDeployedBelow : IntervalIntegrable deployed volume 0 reserve)
    (hBaseEligible : IntervalIntegrable base volume reserve bid)
    (hDeployedEligible : IntervalIntegrable deployed volume reserve bid)
    (hBelow : Set.EqOn deployed base (Set.uIcc (0 : ℝ) reserve))
    (hAllocationWedge :
      ∀ z ∈ Set.Icc reserve bid, |deployed z - base z| ≤ delta) :
    |myersonPayment bid deployed - myersonPayment bid base| ≤
      2 * bidCap * delta := by
  rw [myersonPayment_difference_eq_eligible
    reserve bid base deployed hBaseBelow hDeployedBelow
    hBaseEligible hDeployedEligible hBelow]
  exact eligibleMyersonPayment_wedge
    reserve bid bidCap delta base deployed
    hReserveNonneg hBidEligible hBidCap hDelta
    hBaseEligible hDeployedEligible hAllocationWedge

/-- Complete payment specialization of `lem:wrapper_wedge`.  The two
integrability hypotheses on the deployed curve are the analytic regularity
needed to state its Myerson payment; the paper obtains them from the
self-resampling construction. -/
theorem resampling_payment_wedge
    (n : ℕ) (mu reserve bid bidCap weight : ℝ)
    (base conditionalBadMean : ℝ → ℝ)
    (hMu : mu ∈ Set.Icc (0 : ℝ) 1)
    (hReserveNonneg : 0 ≤ reserve)
    (hBidEligible : reserve ≤ bid)
    (hBidCap : bid ≤ bidCap)
    (hWeight : 0 ≤ weight)
    (hBaseRange :
      ∀ z ∈ Set.Icc reserve bid, base z ∈ Set.Icc (0 : ℝ) weight)
    (hBadMeanRange :
      ∀ z ∈ Set.Icc reserve bid,
        conditionalBadMean z ∈ Set.Icc (0 : ℝ) weight)
    (hBaseBelow : IntervalIntegrable base volume 0 reserve)
    (hDeployedBelow : IntervalIntegrable
      (resampledAllocationRule n mu base conditionalBadMean)
      volume 0 reserve)
    (hBaseEligible : IntervalIntegrable base volume reserve bid)
    (hDeployedEligible : IntervalIntegrable
      (resampledAllocationRule n mu base conditionalBadMean)
      volume reserve bid)
    (hBelow : Set.EqOn
      (resampledAllocationRule n mu base conditionalBadMean) base
      (Set.uIcc (0 : ℝ) reserve)) :
    |myersonPayment bid
          (resampledAllocationRule n mu base conditionalBadMean) -
        myersonPayment bid base| ≤
      2 * bidCap * badEventProbability n mu * weight := by
  have hBadProbability := badEventProbability_mem_Icc n mu hMu
  have hDelta : 0 ≤ badEventProbability n mu * weight :=
    mul_nonneg hBadProbability.1 hWeight
  have hMain := myersonPayment_wedge
    reserve bid bidCap (badEventProbability n mu * weight)
    base (resampledAllocationRule n mu base conditionalBadMean)
    hReserveNonneg hBidEligible hBidCap hDelta
    hBaseBelow hDeployedBelow hBaseEligible hDeployedEligible hBelow
    (by
      intro z hz
      simpa [resampledAllocationRule] using
        resampling_allocation_wedge
          n mu (base z) (conditionalBadMean z) weight
          hMu (hBaseRange z hz) (hBadMeanRange z hz))
  simpa [mul_assoc] using hMain

/-! ## Total-variation certificate -/

/-- Total-variation Lipschitz continuity of a probability kernel, written in
the bounded-test-function dual form.  Quantifying over every nonnegative
bounded measurable payoff makes this exactly the property used in the paper,
without restricting the resampling input to a finite state space. -/
def TVLipschitzKernel
    {Ω : Type*} [MeasurableSpace Ω]
    (kernel : ℝ → ProbabilityMeasure Ω)
    (reserve bidCap lipschitz : ℝ) : Prop :=
  ∀ b ∈ Set.Icc reserve bidCap, ∀ b' ∈ Set.Icc reserve bidCap,
    ∀ (weight : ℝ) (payoff : Ω → ℝ),
      0 ≤ weight →
      Measurable payoff →
      (∀ ω, payoff ω ∈ Set.Icc (0 : ℝ) weight) →
      |(∫ ω, payoff ω ∂(kernel b : Measure Ω)) -
          ∫ ω, payoff ω ∂(kernel b' : Measure Ω)| ≤
        weight * lipschitz * |b - b'|

/-- Expected allocation under the conditional resampling kernel. -/
noncomputable def kernelMean
    {Ω : Type*} [MeasurableSpace Ω]
    (kernel : ℝ → ProbabilityMeasure Ω)
    (payoff : Ω → ℝ) (bid : ℝ) : ℝ :=
  ∫ ω, payoff ω ∂(kernel bid : Measure Ω)

/-- Deployed interim allocation after conditioning on the Bernoulli
resampling indicator for the perturbed coordinate. -/
noncomputable def deployedKernelMixture
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : ℝ) (base : ℝ → ℝ)
    (kernel : ℝ → ProbabilityMeasure Ω)
    (payoff : Ω → ℝ) (bid : ℝ) : ℝ :=
  (1 - mu) * base bid + mu * kernelMean kernel payoff bid

/-- Scalar core of `lem:wrapper_cert`: mix a base Lipschitz curve with a
TV-Lipschitz resampling kernel. -/
theorem deployedKernelMixture_lipschitz
    {Ω : Type*} [MeasurableSpace Ω]
    (mu reserve bidCap baseSensitivity weight kernelSensitivity : ℝ)
    (base : ℝ → ℝ)
    (kernel : ℝ → ProbabilityMeasure Ω)
    (payoff : Ω → ℝ)
    (hMu : mu ∈ Set.Icc (0 : ℝ) 1)
    (hWeight : 0 ≤ weight)
    (hBase :
      ∀ b ∈ Set.Icc reserve bidCap, ∀ b' ∈ Set.Icc reserve bidCap,
        |base b - base b'| ≤ baseSensitivity * |b - b'|)
    (hKernel :
      TVLipschitzKernel kernel reserve bidCap kernelSensitivity)
    (hPayoffMeasurable : Measurable payoff)
    (hPayoffRange : ∀ ω, payoff ω ∈ Set.Icc (0 : ℝ) weight)
    (b b' : ℝ)
    (hBid : b ∈ Set.Icc reserve bidCap)
    (hBid' : b' ∈ Set.Icc reserve bidCap) :
    |deployedKernelMixture mu base kernel payoff b -
        deployedKernelMixture mu base kernel payoff b'| ≤
      ((1 - mu) * baseSensitivity +
        mu * weight * kernelSensitivity) * |b - b'| := by
  have hBaseDiff := hBase b hBid b' hBid'
  have hKernelDiff :=
    hKernel b hBid b' hBid' weight payoff
      hWeight hPayoffMeasurable hPayoffRange
  have hNoResample : 0 ≤ 1 - mu := sub_nonneg.mpr hMu.2
  calc
    |deployedKernelMixture mu base kernel payoff b -
        deployedKernelMixture mu base kernel payoff b'| =
        |(1 - mu) * (base b - base b') +
          mu * (kernelMean kernel payoff b -
            kernelMean kernel payoff b')| := by
            simp only [deployedKernelMixture]
            ring_nf
    _ ≤ |(1 - mu) * (base b - base b')| +
        |mu * (kernelMean kernel payoff b -
          kernelMean kernel payoff b')| :=
      abs_add_le _ _
    _ = (1 - mu) * |base b - base b'| +
        mu * |kernelMean kernel payoff b -
          kernelMean kernel payoff b'| := by
      rw [abs_mul, abs_of_nonneg hNoResample,
        abs_mul, abs_of_nonneg hMu.1]
    _ ≤ (1 - mu) * (baseSensitivity * |b - b'|) +
        mu * (weight * kernelSensitivity * |b - b'|) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hBaseDiff hNoResample)
        (mul_le_mul_of_nonneg_left hKernelDiff hMu.1)
    _ = ((1 - mu) * baseSensitivity +
        mu * weight * kernelSensitivity) * |b - b'| := by ring

/-- Coordinatewise deployed allocation vector.  The finite product norm is
the sup norm, matching the paper's `‖·‖∞`. -/
noncomputable def deployedKernelVector
    {ι Ω : Type*} [MeasurableSpace Ω]
    (mu : ℝ) (base : ℝ → ι → ℝ)
    (kernel : ℝ → ProbabilityMeasure Ω)
    (payoff : ι → Ω → ℝ) (bid : ℝ) : ι → ℝ :=
  fun j => deployedKernelMixture
    mu (fun z => base z j) kernel (payoff j) bid

/-- Vector-valued version of the wrapper certificate. -/
theorem deployedKernelVector_lipschitz
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (mu reserve bidCap baseSensitivity weight kernelSensitivity : ℝ)
    (base : ℝ → ι → ℝ)
    (kernel : ℝ → ProbabilityMeasure Ω)
    (payoff : ι → Ω → ℝ)
    (hMu : mu ∈ Set.Icc (0 : ℝ) 1)
    (hBaseSensitivity : 0 ≤ baseSensitivity)
    (hWeight : 0 ≤ weight)
    (hKernelSensitivity : 0 ≤ kernelSensitivity)
    (hBase :
      ∀ j, ∀ b ∈ Set.Icc reserve bidCap, ∀ b' ∈ Set.Icc reserve bidCap,
        |base b j - base b' j| ≤ baseSensitivity * |b - b'|)
    (hKernel :
      TVLipschitzKernel kernel reserve bidCap kernelSensitivity)
    (hPayoffMeasurable : ∀ j, Measurable (payoff j))
    (hPayoffRange :
      ∀ j ω, payoff j ω ∈ Set.Icc (0 : ℝ) weight)
    (b b' : ℝ)
    (hBid : b ∈ Set.Icc reserve bidCap)
    (hBid' : b' ∈ Set.Icc reserve bidCap) :
    ‖deployedKernelVector mu base kernel payoff b -
        deployedKernelVector mu base kernel payoff b'‖ ≤
      ((1 - mu) * baseSensitivity +
        mu * weight * kernelSensitivity) * |b - b'| := by
  have hNoResample : 0 ≤ 1 - mu := sub_nonneg.mpr hMu.2
  have hCoefficient :
      0 ≤ (1 - mu) * baseSensitivity +
        mu * weight * kernelSensitivity :=
    add_nonneg
      (mul_nonneg hNoResample hBaseSensitivity)
      (mul_nonneg (mul_nonneg hMu.1 hWeight) hKernelSensitivity)
  have hRhs :
      0 ≤ ((1 - mu) * baseSensitivity +
        mu * weight * kernelSensitivity) * |b - b'| :=
    mul_nonneg hCoefficient (abs_nonneg _)
  rw [pi_norm_le_iff_of_nonneg hRhs]
  intro j
  simpa [deployedKernelVector, Real.norm_eq_abs] using
    deployedKernelMixture_lipschitz
      mu reserve bidCap baseSensitivity weight kernelSensitivity
      (fun z => base z j) kernel (payoff j)
      hMu hWeight (hBase j) hKernel
      (hPayoffMeasurable j) (hPayoffRange j)
      b b' hBid hBid'

/-- Base FIRM-L sensitivity appearing in the paper. -/
noncomputable def firmLBaseSensitivity (weight tau : ℝ) : ℝ :=
  weight / (Real.exp 1 * tau)

/-- Exact coefficient in `lem:wrapper_cert`.  Every output coordinate is
allowed its own measurable allocation payoff, while the same conditional
resampling kernel is used for the perturbed input coordinate.  Thus the result
covers both the own and cross coordinates after conditioning on the other
resampling draws, exactly as in the paper's coupling argument. -/
theorem wrapper_certificate
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (mu reserve bidCap tau weight kernelSensitivity : ℝ)
    (base : ℝ → ι → ℝ)
    (kernel : ℝ → ProbabilityMeasure Ω)
    (payoff : ι → Ω → ℝ)
    (hMu : mu ∈ Set.Icc (0 : ℝ) 1)
    (hTau : 0 < tau)
    (hWeight : 0 ≤ weight)
    (hKernelSensitivity : 0 ≤ kernelSensitivity)
    (hBase :
      ∀ j, ∀ b ∈ Set.Icc reserve bidCap, ∀ b' ∈ Set.Icc reserve bidCap,
        |base b j - base b' j| ≤
          firmLBaseSensitivity weight tau * |b - b'|)
    (hKernel :
      TVLipschitzKernel kernel reserve bidCap kernelSensitivity)
    (hPayoffMeasurable : ∀ j, Measurable (payoff j))
    (hPayoffRange :
      ∀ j ω, payoff j ω ∈ Set.Icc (0 : ℝ) weight)
    (b b' : ℝ)
    (hBid : b ∈ Set.Icc reserve bidCap)
    (hBid' : b' ∈ Set.Icc reserve bidCap) :
    ‖deployedKernelVector mu base kernel payoff b -
        deployedKernelVector mu base kernel payoff b'‖ ≤
      ((1 - mu) * firmLBaseSensitivity weight tau +
        mu * weight * kernelSensitivity) * |b - b'| := by
  have hBaseSensitivity : 0 ≤ firmLBaseSensitivity weight tau := by
    exact div_nonneg hWeight
      (le_of_lt (mul_pos (Real.exp_pos 1) hTau))
  exact deployedKernelVector_lipschitz
    mu reserve bidCap (firmLBaseSensitivity weight tau)
    weight kernelSensitivity base kernel payoff
    hMu hBaseSensitivity hWeight hKernelSensitivity
    hBase hKernel hPayoffMeasurable hPayoffRange
    b b' hBid hBid'

end SmoothingCliff.Wrapper
