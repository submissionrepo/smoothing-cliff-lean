import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Sybil-rent certificate

This file formalizes Theorem `thm:sybil` from *Smoothing the Cliff*.

The type `Strategy` in `maximalCoalitionGain` is deliberately arbitrary.  It
may therefore be instantiated by the disjoint union, over all finite numbers
of identities, of their joint bid vectors.  The functions `coalitionWeight`
and `totalTransfer` depend on the chosen strategy but not on the coalition's
true value, exactly as in the affine-envelope argument in the paper.

The second part specializes the general certificate to the one-slot
exponential rule and proves both the closed-form integral and the two bounds
appearing in the theorem.
-/

noncomputable section

namespace SmoothingCliff.Mechanism

open MeasureTheory
open scoped BigOperators

/-- Utility gain of a coalition strategy over truthful single-identity
utility `weight * integral rho`. -/
def coalitionGain {Strategy : Type*}
    (value weight : ℝ) (coalitionWeight totalTransfer : Strategy → ℝ)
    (rho : ℝ → ℝ) (reserve : ℝ) (strategy : Strategy) : ℝ :=
  value * coalitionWeight strategy - totalTransfer strategy -
    weight * ∫ z in reserve..value, rho z

/-- The paper's `G(v)`: the supremum over all coalition strategies of their
gain over truthful single-identity bidding. -/
def maximalCoalitionGain {Strategy : Type*}
    (value weight : ℝ) (coalitionWeight totalTransfer : Strategy → ℝ)
    (rho : ℝ → ℝ) (reserve : ℝ) : ℝ :=
  sSup
    (Set.range
      (coalitionGain value weight coalitionWeight totalTransfer rho reserve))

/-- The reserve-point step in the paper.  The union bound gives
`Q <= sum x_i`; multiplying by a nonnegative reserve and summing the
per-identity truthful-in-expectation inequalities makes coalition utility at
the reserve nonpositive. -/
theorem reserve_coalition_utility_nonpos
    {Identity : Type*} [Fintype Identity]
    (reserve coalitionWeight : ℝ)
    (identityWeight identityTransfer : Identity → ℝ)
    (hReserve : 0 ≤ reserve)
    (hUnion : coalitionWeight ≤ ∑ i, identityWeight i)
    (hIdentity : ∀ i,
      reserve * identityWeight i - identityTransfer i ≤ 0) :
    reserve * coalitionWeight - ∑ i, identityTransfer i ≤ 0 := by
  have hCoalitionWeight :=
    mul_le_mul_of_nonneg_left hUnion hReserve
  have hSummedIdentityUtilities :
      ∑ i, (reserve * identityWeight i - identityTransfer i) ≤
        ∑ _i : Identity, (0 : ℝ) :=
    Finset.sum_le_sum fun i _ => hIdentity i
  simp only [Finset.sum_sub_distrib, Finset.sum_const_zero] at hSummedIdentityUtilities
  rw [← Finset.mul_sum] at hSummedIdentityUtilities
  linarith

/-- General form of Theorem `thm:sybil`.  It requires precisely the two
properties established in the paper before the final subtraction: every
coalition allocation has weight at most `weight`, and every strategy has
nonpositive utility at the reserve. -/
theorem maximalCoalitionGain_le_integral
    {Strategy : Type*}
    (reserve value weight : ℝ)
    (coalitionWeight totalTransfer : Strategy → ℝ) (rho : ℝ → ℝ)
    (hValue : reserve ≤ value) (hWeight : 0 ≤ weight)
    (hCoalitionWeight : ∀ strategy,
      coalitionWeight strategy ∈ Set.Icc (0 : ℝ) weight)
    (hReserveUtility : ∀ strategy,
      reserve * coalitionWeight strategy - totalTransfer strategy ≤ 0)
    (hRhoIntegrable : IntervalIntegrable rho volume reserve value)
    (hRhoProbability : ∀ z ∈ Set.Icc reserve value,
      rho z ∈ Set.Icc (0 : ℝ) 1) :
    maximalCoalitionGain value weight coalitionWeight totalTransfer rho reserve ≤
      weight * ∫ z in reserve..value, (1 - rho z) := by
  have hOneIntegrable :
      IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume reserve value :=
    Continuous.intervalIntegrable (μ := volume) continuous_const reserve value
  have hIntegralIdentity :
      (∫ z in reserve..value, (1 - rho z)) =
        (value - reserve) - ∫ z in reserve..value, rho z := by
    rw [intervalIntegral.integral_sub hOneIntegrable hRhoIntegrable,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul, mul_one]
  apply Real.sSup_le
  · rintro gainValue ⟨strategy, rfl⟩
    have hCoalitionUtility :
        value * coalitionWeight strategy - totalTransfer strategy ≤
          (value - reserve) * weight := by
      have hSlopeBound :=
        mul_le_mul_of_nonneg_left (hCoalitionWeight strategy).2
          (sub_nonneg.mpr hValue)
      have hAffineIdentity :
          value * coalitionWeight strategy - totalTransfer strategy =
            (reserve * coalitionWeight strategy - totalTransfer strategy) +
              (value - reserve) * coalitionWeight strategy := by
        ring
      rw [hAffineIdentity]
      linarith [hReserveUtility strategy, hSlopeBound]
    calc
      coalitionGain value weight coalitionWeight totalTransfer rho reserve strategy
          ≤ (value - reserve) * weight -
              weight * ∫ z in reserve..value, rho z := by
            unfold coalitionGain
            exact sub_le_sub_right hCoalitionUtility _
      _ = weight *
            ((value - reserve) - ∫ z in reserve..value, rho z) := by
          ring
      _ = weight * ∫ z in reserve..value, (1 - rho z) := by
          rw [hIntegralIdentity]
  · exact
      mul_nonneg hWeight
        (intervalIntegral.integral_nonneg hValue fun z hz =>
          sub_nonneg.mpr (hRhoProbability z hz).2)

/-- Inclusion probability of one identity in the one-slot exponential rule,
with opponents' aggregate intensity `congestion`. -/
def oneSlotInclusionProbability
    (reserve temperature congestion bid : ℝ) : ℝ :=
  Real.exp ((bid - reserve) / temperature) /
    (Real.exp ((bid - reserve) / temperature) + congestion)

/-- Failure probability in the algebraically convenient, reserve-normalized
form used to integrate the one-slot certificate. -/
def oneSlotResidual (reserve temperature congestion bid : ℝ) : ℝ :=
  congestion * Real.exp (-(bid - reserve) / temperature) /
    (1 + congestion * Real.exp (-(bid - reserve) / temperature))

theorem oneSlotInclusionProbability_continuous
    (reserve temperature congestion : ℝ) (hCongestion : 0 ≤ congestion) :
    Continuous (oneSlotInclusionProbability reserve temperature congestion) := by
  unfold oneSlotInclusionProbability
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro bid
    positivity

theorem oneSlotInclusionProbability_mem_Icc
    (reserve temperature congestion bid : ℝ)
    (hCongestion : 0 ≤ congestion) :
    oneSlotInclusionProbability reserve temperature congestion bid ∈
      Set.Icc (0 : ℝ) 1 := by
  unfold oneSlotInclusionProbability
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    exact le_add_of_nonneg_right hCongestion

/-- Multiplying numerator and denominator by the inverse exponential gives
the reserve-normalized residual formula. -/
theorem oneSlotOpponentShare_eq_residual
    (reserve temperature congestion bid : ℝ)
    (hCongestion : 0 ≤ congestion) :
    congestion /
        (Real.exp ((bid - reserve) / temperature) + congestion) =
      oneSlotResidual reserve temperature congestion bid := by
  have hOriginalDenominator :
      Real.exp ((bid - reserve) / temperature) + congestion ≠ 0 := by
    positivity
  have hNormalizedDenominator :
      1 + congestion * Real.exp (-(bid - reserve) / temperature) ≠ 0 := by
    positivity
  have hExpProduct :
      Real.exp ((bid - reserve) / temperature) *
          Real.exp (-(bid - reserve) / temperature) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  unfold oneSlotResidual
  rw [div_eq_div_iff hOriginalDenominator hNormalizedDenominator]
  nlinarith [congrArg (fun y : ℝ => congestion * y) hExpProduct]

/-- For one slot, `1-rho` is exactly the normalized residual integrand. -/
theorem oneSlotFailure_eq_residual
    (reserve temperature congestion bid : ℝ)
    (hCongestion : 0 ≤ congestion) :
    1 - oneSlotInclusionProbability reserve temperature congestion bid =
      oneSlotResidual reserve temperature congestion bid := by
  rw [← oneSlotOpponentShare_eq_residual reserve temperature congestion bid
    hCongestion]
  unfold oneSlotInclusionProbability
  have hDenominator :
      Real.exp ((bid - reserve) / temperature) + congestion ≠ 0 := by
    positivity
  field_simp
  ring

/-- Antiderivative for the one-slot failure probability. -/
def oneSlotResidualPrimitive
    (reserve temperature congestion bid : ℝ) : ℝ :=
  -temperature *
    Real.log (1 + congestion * Real.exp (-(bid - reserve) / temperature))

theorem oneSlotResidual_hasDerivAt
    (reserve temperature congestion bid : ℝ)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion) :
    HasDerivAt (oneSlotResidualPrimitive reserve temperature congestion)
      (oneSlotResidual reserve temperature congestion bid) bid := by
  have hTemperatureNe : temperature ≠ 0 := ne_of_gt hTemperature
  have hLinear :
      HasDerivAt (fun y : ℝ => -(y - reserve) / temperature)
        (-1 / temperature) bid := by
    convert (((hasDerivAt_id bid).sub_const reserve).neg.div_const temperature)
      using 1
  have hExp :
      HasDerivAt (fun y : ℝ => Real.exp (-(y - reserve) / temperature))
        (Real.exp (-(bid - reserve) / temperature) * (-1 / temperature)) bid :=
    hLinear.exp
  have hInner :
      HasDerivAt
        (fun y : ℝ =>
          1 + congestion * Real.exp (-(y - reserve) / temperature))
        (congestion *
          (Real.exp (-(bid - reserve) / temperature) * (-1 / temperature)))
        bid := by
    simpa only [Pi.add_apply, zero_add] using
      (hasDerivAt_const bid (1 : ℝ)).add (hExp.const_mul congestion)
  have hInnerPos :
      0 < 1 + congestion * Real.exp (-(bid - reserve) / temperature) := by
    positivity
  have hLog := hInner.log (ne_of_gt hInnerPos)
  have hPrimitive := hLog.const_mul (-temperature)
  change HasDerivAt
    (fun y : ℝ =>
      -temperature *
        Real.log (1 + congestion * Real.exp (-(y - reserve) / temperature)))
    (oneSlotResidual reserve temperature congestion bid) bid
  apply hPrimitive.congr_deriv
  unfold oneSlotResidual
  field_simp

/-- Exact `K=1` integral in Theorem `thm:sybil`, including the slot weight. -/
theorem oneSlotResidual_integral
    (reserve value weight temperature congestion : ℝ)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion) :
    weight * (∫ bid in reserve..value,
      oneSlotResidual reserve temperature congestion bid) =
      weight * temperature *
        Real.log
          ((1 + congestion) /
            (1 + congestion *
              Real.exp (-(value - reserve) / temperature))) := by
  have hContinuous :
      Continuous (oneSlotResidual reserve temperature congestion) := by
    unfold oneSlotResidual
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro bid
      positivity
  have hIntegral :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun bid _ =>
        oneSlotResidual_hasDerivAt reserve temperature congestion bid
          hTemperature hCongestion)
      (hContinuous.intervalIntegrable reserve value)
  have hNumerator : 1 + congestion ≠ 0 := by positivity
  have hDenominator :
      1 + congestion * Real.exp (-(value - reserve) / temperature) ≠ 0 := by
    positivity
  have hClosed :
      (∫ bid in reserve..value,
        oneSlotResidual reserve temperature congestion bid) =
        temperature *
          Real.log
            ((1 + congestion) /
              (1 + congestion *
                Real.exp (-(value - reserve) / temperature))) := by
    rw [hIntegral, Real.log_div hNumerator hDenominator]
    simp only [oneSlotResidualPrimitive]
    have hAtReserve :
        -(reserve - reserve) / temperature = 0 := by
      ring
    rw [hAtReserve, Real.exp_zero, mul_one]
    ring
  rw [hClosed]
  ring

/-- The same exact integral written directly as `integral (1-rho)`. -/
theorem oneSlotFailureIntegral_closedForm
    (reserve value weight temperature congestion : ℝ)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion) :
    weight * (∫ bid in reserve..value,
      (1 - oneSlotInclusionProbability reserve temperature congestion bid)) =
      weight * temperature *
        Real.log
          ((1 + congestion) /
            (1 + congestion *
              Real.exp (-(value - reserve) / temperature))) := by
  have hIntegralsEqual :
      (∫ bid in reserve..value,
        (1 - oneSlotInclusionProbability reserve temperature congestion bid)) =
        ∫ bid in reserve..value,
          oneSlotResidual reserve temperature congestion bid := by
    apply intervalIntegral.integral_congr
    intro bid _
    exact oneSlotFailure_eq_residual reserve temperature congestion bid
      hCongestion
  rw [hIntegralsEqual]
  exact oneSlotResidual_integral reserve value weight temperature congestion
    hTemperature hCongestion

/-- On the eligible interval the one-slot failure probability is at most its
value at the reserve, `congestion/(1+congestion)`. -/
theorem oneSlotResidual_le_reserve_level
    (reserve temperature congestion bid : ℝ)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion)
    (hEligible : reserve ≤ bid) :
    oneSlotResidual reserve temperature congestion bid ≤
      congestion / (1 + congestion) := by
  have hExponent : -(bid - reserve) / temperature ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sub_nonneg.mpr hEligible)) (le_of_lt hTemperature)
  have hExp : Real.exp (-(bid - reserve) / temperature) ≤ 1 := by
    simpa using (Real.exp_le_one_iff.mpr hExponent)
  have hDenominator :
      0 < 1 + congestion * Real.exp (-(bid - reserve) / temperature) := by
    positivity
  have hReserveDenominator : 0 < 1 + congestion := by positivity
  unfold oneSlotResidual
  rw [div_le_div_iff₀ hDenominator hReserveDenominator]
  have hMul := mul_le_mul_of_nonneg_left hExp hCongestion
  nlinarith

/-- Integrating the reserve-level bound gives the value-distance branch of
the paper's certificate. -/
theorem oneSlotResidual_integral_le_linear
    (reserve value temperature congestion : ℝ)
    (hValue : reserve ≤ value)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion) :
    (∫ bid in reserve..value,
      oneSlotResidual reserve temperature congestion bid) ≤
      (value - reserve) * congestion / (1 + congestion) := by
  have hContinuous :
      Continuous (oneSlotResidual reserve temperature congestion) := by
    unfold oneSlotResidual
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro bid
      positivity
  have hResidualIntegrable :
      IntervalIntegrable (oneSlotResidual reserve temperature congestion)
        volume reserve value :=
    hContinuous.intervalIntegrable reserve value
  have hConstantIntegrable :
      IntervalIntegrable (fun _ : ℝ => congestion / (1 + congestion))
        volume reserve value :=
    Continuous.intervalIntegrable (μ := volume) continuous_const reserve value
  have hIntegralLe :=
    intervalIntegral.integral_mono_on hValue hResidualIntegrable
      hConstantIntegrable
      (fun bid hBid =>
        oneSlotResidual_le_reserve_level reserve temperature congestion bid
          hTemperature hCongestion hBid.1)
  rw [intervalIntegral.integral_const] at hIntegralLe
  convert hIntegralLe using 1
  simp only [smul_eq_mul]
  ring

theorem oneSlotClosedForm_le_linear
    (reserve value temperature congestion : ℝ)
    (hValue : reserve ≤ value)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion) :
    temperature *
        Real.log
          ((1 + congestion) /
            (1 + congestion *
              Real.exp (-(value - reserve) / temperature))) ≤
      (value - reserve) * congestion / (1 + congestion) := by
  have hIntegral :=
    oneSlotResidual_integral reserve value 1 temperature congestion
      hTemperature hCongestion
  simp only [one_mul] at hIntegral
  rw [← hIntegral]
  exact
    oneSlotResidual_integral_le_linear reserve value temperature congestion
      hValue hTemperature hCongestion

/-- Dropping the positive denominator inside the logarithmic ratio gives the
temperature-times-log-congestion branch. -/
theorem oneSlotClosedForm_le_temperature
    (reserve value temperature congestion : ℝ)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion) :
    temperature *
        Real.log
          ((1 + congestion) /
            (1 + congestion *
              Real.exp (-(value - reserve) / temperature))) ≤
      temperature * Real.log (1 + congestion) := by
  have hNumeratorPos : 0 < 1 + congestion := by positivity
  have hDenominatorPos :
      0 < 1 + congestion * Real.exp (-(value - reserve) / temperature) := by
    positivity
  have hDenominatorOne :
      1 ≤ 1 + congestion * Real.exp (-(value - reserve) / temperature) := by
    have hProduct :
        0 ≤ congestion * Real.exp (-(value - reserve) / temperature) :=
      mul_nonneg hCongestion (le_of_lt (Real.exp_pos _))
    linarith
  have hRatioPos :
      0 <
        (1 + congestion) /
          (1 + congestion * Real.exp (-(value - reserve) / temperature)) :=
    div_pos hNumeratorPos hDenominatorPos
  have hRatioLe :
      (1 + congestion) /
          (1 + congestion * Real.exp (-(value - reserve) / temperature)) ≤
        1 + congestion := by
    rw [div_le_iff₀ hDenominatorPos]
    nlinarith
  exact
    mul_le_mul_of_nonneg_left
      (Real.log_le_log hRatioPos hRatioLe) (le_of_lt hTemperature)

/-- The exact two-branch analytic bound printed in Theorem `thm:sybil`. -/
theorem oneSlotClosedForm_le_min
    (reserve value weight temperature congestion : ℝ)
    (hValue : reserve ≤ value) (hWeight : 0 ≤ weight)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion) :
    weight * temperature *
        Real.log
          ((1 + congestion) /
            (1 + congestion *
              Real.exp (-(value - reserve) / temperature))) ≤
      weight *
        min ((value - reserve) * congestion / (1 + congestion))
          (temperature * Real.log (1 + congestion)) := by
  rw [mul_min_of_nonneg _ _ hWeight]
  apply le_min
  · calc
      weight * temperature *
          Real.log
            ((1 + congestion) /
              (1 + congestion *
                Real.exp (-(value - reserve) / temperature))) =
          weight *
            (temperature *
              Real.log
                ((1 + congestion) /
                  (1 + congestion *
                    Real.exp (-(value - reserve) / temperature)))) := by
        ring
      _ ≤ weight * ((value - reserve) * congestion / (1 + congestion)) :=
        mul_le_mul_of_nonneg_left
          (oneSlotClosedForm_le_linear reserve value temperature congestion
            hValue hTemperature hCongestion) hWeight
  · calc
      weight * temperature *
          Real.log
            ((1 + congestion) /
              (1 + congestion *
                Real.exp (-(value - reserve) / temperature))) =
          weight *
            (temperature *
              Real.log
                ((1 + congestion) /
                  (1 + congestion *
                    Real.exp (-(value - reserve) / temperature)))) := by
        ring
      _ ≤ weight * (temperature * Real.log (1 + congestion)) :=
        mul_le_mul_of_nonneg_left
          (oneSlotClosedForm_le_temperature reserve value temperature congestion
            hTemperature hCongestion) hWeight

/-- Complete one-slot specialization: the maximal coalition gain is bounded
by the closed form, and the closed form obeys the paper's stated minimum
certificate. -/
theorem oneSlot_sybil_rent_certificate
    {Strategy : Type*}
    (reserve value weight temperature congestion : ℝ)
    (coalitionWeight totalTransfer : Strategy → ℝ)
    (hValue : reserve ≤ value) (hWeight : 0 ≤ weight)
    (hTemperature : 0 < temperature)
    (hCongestion : 0 ≤ congestion)
    (hCoalitionWeight : ∀ strategy,
      coalitionWeight strategy ∈ Set.Icc (0 : ℝ) weight)
    (hReserveUtility : ∀ strategy,
      reserve * coalitionWeight strategy - totalTransfer strategy ≤ 0) :
    maximalCoalitionGain value weight coalitionWeight totalTransfer
          (oneSlotInclusionProbability reserve temperature congestion) reserve ≤
        weight * temperature *
          Real.log
            ((1 + congestion) /
              (1 + congestion *
                Real.exp (-(value - reserve) / temperature))) ∧
      weight * temperature *
          Real.log
            ((1 + congestion) /
              (1 + congestion *
                Real.exp (-(value - reserve) / temperature))) ≤
        weight *
          min ((value - reserve) * congestion / (1 + congestion))
            (temperature * Real.log (1 + congestion)) := by
  have hRhoContinuous :=
    oneSlotInclusionProbability_continuous reserve temperature congestion
      hCongestion
  have hGeneral :=
    maximalCoalitionGain_le_integral reserve value weight coalitionWeight
      totalTransfer
      (oneSlotInclusionProbability reserve temperature congestion)
      hValue hWeight hCoalitionWeight hReserveUtility
      (hRhoContinuous.intervalIntegrable reserve value)
      (fun z _ =>
        oneSlotInclusionProbability_mem_Icc reserve temperature congestion z
          hCongestion)
  constructor
  · calc
      maximalCoalitionGain value weight coalitionWeight totalTransfer
            (oneSlotInclusionProbability reserve temperature congestion) reserve ≤
          weight * (∫ z in reserve..value,
            (1 - oneSlotInclusionProbability reserve temperature congestion z)) :=
        hGeneral
      _ = weight * temperature *
          Real.log
            ((1 + congestion) /
              (1 + congestion *
                Real.exp (-(value - reserve) / temperature))) :=
        oneSlotFailureIntegral_closedForm reserve value weight temperature
          congestion hTemperature hCongestion
  · exact
      oneSlotClosedForm_le_min reserve value weight temperature congestion
        hValue hWeight hTemperature hCongestion

/-! ## The truthful two-identity benchmark -/

/-- Reserve-normalized exponential intensity. -/
def exponentialIntensity (reserve temperature bid : ℝ) : ℝ :=
  Real.exp ((bid - reserve) / temperature)

/-- Interim allocation probability of either split identity while its sibling
keeps the truthful report `value`. -/
def twoIdentityInterimProbability
    (reserve value temperature congestion bid : ℝ) : ℝ :=
  exponentialIntensity reserve temperature bid /
    (exponentialIntensity reserve temperature bid +
      exponentialIntensity reserve temperature value + congestion)

/-- The signed integrand displayed in Remark `rem:sybilsign`. -/
def twoIdentityGainIntegrand
    (reserve value temperature congestion bid : ℝ) : ℝ :=
  exponentialIntensity reserve temperature bid *
      (congestion + exponentialIntensity reserve temperature bid -
        exponentialIntensity reserve temperature value) /
    ((exponentialIntensity reserve temperature bid + congestion) *
      (exponentialIntensity reserve temperature bid +
        exponentialIntensity reserve temperature value + congestion))

/-- Actual truthful two-identity utility minus truthful single-identity
utility.  Each split identity gets its own Myerson-envelope integral while the
sibling remains at `value`. -/
def twoIdentityTruthfulGain
    (reserve value weight temperature congestion : ℝ) : ℝ :=
  2 *
      (weight * ∫ bid in reserve..value,
        twoIdentityInterimProbability reserve value temperature congestion bid) -
    weight * ∫ bid in reserve..value,
      oneSlotInclusionProbability reserve temperature congestion bid

/-- Pointwise common-denominator identity in the proof of
Remark `rem:sybilsign`. -/
theorem twoIdentityGainIntegrand_identity
    (reserve value temperature congestion bid : ℝ)
    (hCongestion : 0 ≤ congestion) :
    2 * twoIdentityInterimProbability reserve value temperature congestion bid -
        oneSlotInclusionProbability reserve temperature congestion bid =
      twoIdentityGainIntegrand reserve value temperature congestion bid := by
  have hSingleDenominator :
      exponentialIntensity reserve temperature bid + congestion ≠ 0 := by
    unfold exponentialIntensity
    positivity
  have hSplitDenominator :
      exponentialIntensity reserve temperature bid +
          exponentialIntensity reserve temperature value + congestion ≠ 0 := by
    unfold exponentialIntensity
    positivity
  unfold twoIdentityInterimProbability oneSlotInclusionProbability
    twoIdentityGainIntegrand exponentialIntensity
  field_simp
  ring

theorem twoIdentityInterimProbability_continuous
    (reserve value temperature congestion : ℝ)
    (hCongestion : 0 ≤ congestion) :
    Continuous
      (twoIdentityInterimProbability reserve value temperature congestion) := by
  unfold twoIdentityInterimProbability exponentialIntensity
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro bid
    positivity

theorem twoIdentityGainIntegrand_continuous
    (reserve value temperature congestion : ℝ)
    (hCongestion : 0 ≤ congestion) :
    Continuous (twoIdentityGainIntegrand reserve value temperature congestion) := by
  unfold twoIdentityGainIntegrand exponentialIntensity
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro bid
    positivity

/-- Exact integral identity for the truthful two-identity gain.  In
particular, the formula is derived from the two envelope utilities rather than
assumed. -/
theorem twoIdentityTruthfulGain_integral
    (reserve value weight temperature congestion : ℝ)
    (hCongestion : 0 ≤ congestion) :
    twoIdentityTruthfulGain reserve value weight temperature congestion =
      weight * ∫ bid in reserve..value,
        twoIdentityGainIntegrand reserve value temperature congestion bid := by
  have hTwoIntegrable :
      IntervalIntegrable
        (twoIdentityInterimProbability reserve value temperature congestion)
        volume reserve value :=
    (twoIdentityInterimProbability_continuous reserve value temperature congestion
      hCongestion).intervalIntegrable reserve value
  have hSingleIntegrable :
      IntervalIntegrable
        (oneSlotInclusionProbability reserve temperature congestion)
        volume reserve value :=
    (oneSlotInclusionProbability_continuous reserve temperature congestion
      hCongestion).intervalIntegrable reserve value
  have hTwiceIntegrable :
      IntervalIntegrable
        (fun bid =>
          2 * twoIdentityInterimProbability reserve value temperature congestion bid)
        volume reserve value :=
    hTwoIntegrable.const_mul 2
  have hIntegralLinear :
      (∫ bid in reserve..value,
          (2 * twoIdentityInterimProbability reserve value temperature congestion bid -
            oneSlotInclusionProbability reserve temperature congestion bid)) =
        2 * (∫ bid in reserve..value,
          twoIdentityInterimProbability reserve value temperature congestion bid) -
          ∫ bid in reserve..value,
            oneSlotInclusionProbability reserve temperature congestion bid := by
    rw [intervalIntegral.integral_sub hTwiceIntegrable hSingleIntegrable,
      intervalIntegral.integral_const_mul]
  have hIntegralAlgebra :
      (∫ bid in reserve..value,
          (2 * twoIdentityInterimProbability reserve value temperature congestion bid -
            oneSlotInclusionProbability reserve temperature congestion bid)) =
        ∫ bid in reserve..value,
          twoIdentityGainIntegrand reserve value temperature congestion bid := by
    apply intervalIntegral.integral_congr
    intro bid _
    exact twoIdentityGainIntegrand_identity reserve value temperature congestion bid
      hCongestion
  calc
    twoIdentityTruthfulGain reserve value weight temperature congestion =
        weight *
          (2 * (∫ bid in reserve..value,
              twoIdentityInterimProbability reserve value temperature congestion bid) -
            ∫ bid in reserve..value,
              oneSlotInclusionProbability reserve temperature congestion bid) := by
      unfold twoIdentityTruthfulGain
      ring
    _ = weight * (∫ bid in reserve..value,
          (2 * twoIdentityInterimProbability reserve value temperature congestion bid -
            oneSlotInclusionProbability reserve temperature congestion bid)) := by
      rw [hIntegralLinear]
    _ = weight * ∫ bid in reserve..value,
          twoIdentityGainIntegrand reserve value temperature congestion bid := by
      rw [hIntegralAlgebra]

theorem exponentialIntensity_one_le
    (reserve temperature bid : ℝ)
    (hTemperature : 0 < temperature) (hEligible : reserve ≤ bid) :
    1 ≤ exponentialIntensity reserve temperature bid := by
  unfold exponentialIntensity
  apply Real.one_le_exp
  exact div_nonneg (sub_nonneg.mpr hEligible) (le_of_lt hTemperature)

theorem exponentialIntensity_one_lt
    (reserve temperature bid : ℝ)
    (hTemperature : 0 < temperature) (hEligible : reserve < bid) :
    1 < exponentialIntensity reserve temperature bid := by
  unfold exponentialIntensity
  rw [Real.one_lt_exp_iff]
  exact div_pos (sub_pos.mpr hEligible) hTemperature

/-- Under the paper's congestion condition, the signed integrand is
nonnegative throughout the eligible interval. -/
theorem twoIdentityGainIntegrand_nonneg
    (reserve value temperature congestion bid : ℝ)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion)
    (hEligible : reserve ≤ bid)
    (hThick : exponentialIntensity reserve temperature value - 1 ≤ congestion) :
    0 ≤ twoIdentityGainIntegrand reserve value temperature congestion bid := by
  have hBidIntensity :=
    exponentialIntensity_one_le reserve temperature bid hTemperature hEligible
  have hSignedFactor :
      0 ≤ congestion + exponentialIntensity reserve temperature bid -
        exponentialIntensity reserve temperature value := by
    linarith
  have hBidPos : 0 < exponentialIntensity reserve temperature bid := by
    unfold exponentialIntensity
    positivity
  have hValuePos : 0 < exponentialIntensity reserve temperature value := by
    unfold exponentialIntensity
    positivity
  have hFirstDenominator :
      0 < exponentialIntensity reserve temperature bid + congestion :=
    add_pos_of_pos_of_nonneg hBidPos hCongestion
  have hSecondDenominator :
      0 < exponentialIntensity reserve temperature bid +
        exponentialIntensity reserve temperature value + congestion := by
    positivity
  unfold twoIdentityGainIntegrand
  exact div_nonneg
    (mul_nonneg (le_of_lt hBidPos) hSignedFactor)
    (mul_nonneg (le_of_lt hFirstDenominator) (le_of_lt hSecondDenominator))

/-- The weak threshold in the remark is enough for strict pointwise
positivity at every bid strictly above the reserve.  This also covers the
threshold-equality case: then the integrand is zero at `reserve` but positive
immediately to its right. -/
theorem twoIdentityGainIntegrand_pos_of_gt_reserve
    (reserve value temperature congestion bid : ℝ)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion)
    (hEligible : reserve < bid)
    (hThick : exponentialIntensity reserve temperature value - 1 ≤ congestion) :
    0 < twoIdentityGainIntegrand reserve value temperature congestion bid := by
  have hBidIntensity :=
    exponentialIntensity_one_lt reserve temperature bid hTemperature hEligible
  have hSignedFactor :
      0 < congestion + exponentialIntensity reserve temperature bid -
        exponentialIntensity reserve temperature value := by
    linarith
  have hBidPos : 0 < exponentialIntensity reserve temperature bid := by
    unfold exponentialIntensity
    positivity
  have hValuePos : 0 < exponentialIntensity reserve temperature value := by
    unfold exponentialIntensity
    positivity
  have hFirstDenominator :
      0 < exponentialIntensity reserve temperature bid + congestion :=
    add_pos_of_pos_of_nonneg hBidPos hCongestion
  have hSecondDenominator :
      0 < exponentialIntensity reserve temperature bid +
        exponentialIntensity reserve temperature value + congestion := by
    positivity
  unfold twoIdentityGainIntegrand
  exact div_pos
    (mul_pos hBidPos hSignedFactor)
    (mul_pos hFirstDenominator hSecondDenominator)

theorem twoIdentityTruthfulGain_nonneg
    (reserve value weight temperature congestion : ℝ)
    (hValue : reserve ≤ value) (hWeight : 0 ≤ weight)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion)
    (hThick : exponentialIntensity reserve temperature value - 1 ≤ congestion) :
    0 ≤ twoIdentityTruthfulGain reserve value weight temperature congestion := by
  rw [twoIdentityTruthfulGain_integral reserve value weight temperature congestion
    hCongestion]
  exact mul_nonneg hWeight
    (intervalIntegral.integral_nonneg hValue fun bid hBid =>
      twoIdentityGainIntegrand_nonneg reserve value temperature congestion bid
        hTemperature hCongestion hBid.1 hThick)

/-- Faithful strict version of the remark: positive slot weight, `value >
reserve`, and the weak congestion threshold imply a strictly positive
two-identity gain. -/
theorem twoIdentityTruthfulGain_pos
    (reserve value weight temperature congestion : ℝ)
    (hValue : reserve < value) (hWeight : 0 < weight)
    (hTemperature : 0 < temperature) (hCongestion : 0 ≤ congestion)
    (hThick : exponentialIntensity reserve temperature value - 1 ≤ congestion) :
    0 < twoIdentityTruthfulGain reserve value weight temperature congestion := by
  rw [twoIdentityTruthfulGain_integral reserve value weight temperature congestion
    hCongestion]
  apply mul_pos hWeight
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((twoIdentityGainIntegrand_continuous reserve value temperature congestion
      hCongestion).intervalIntegrable reserve value)
  · intro bid hBid
    exact twoIdentityGainIntegrand_pos_of_gt_reserve reserve value temperature
      congestion bid hTemperature hCongestion hBid.1 hThick
  · exact hValue

theorem twoIdentityTruthfulGain_at_reserve
    (reserve weight temperature congestion : ℝ) :
    twoIdentityTruthfulGain reserve reserve weight temperature congestion = 0 := by
  unfold twoIdentityTruthfulGain
  simp

/-- With no opponents, truthful splitting is strictly harmful: the sibling's
truthful bid destroys the single identity's information rent.  This is the
finite-temperature version of the dominant-coalition side of the remark. -/
theorem twoIdentityGainIntegrand_neg_of_zero_congestion
    (reserve value temperature bid : ℝ)
    (hTemperature : 0 < temperature) (hBid : bid < value) :
    twoIdentityGainIntegrand reserve value temperature 0 bid < 0 := by
  have hBidIntensityPos :
      0 < exponentialIntensity reserve temperature bid := by
    unfold exponentialIntensity
    positivity
  have hValueIntensityPos :
      0 < exponentialIntensity reserve temperature value := by
    unfold exponentialIntensity
    positivity
  have hIntensityLt :
      exponentialIntensity reserve temperature bid <
        exponentialIntensity reserve temperature value := by
    unfold exponentialIntensity
    rw [Real.exp_lt_exp]
    exact div_lt_div_of_pos_right (sub_lt_sub_right hBid reserve) hTemperature
  have hSignedFactor :
      exponentialIntensity reserve temperature bid -
        exponentialIntensity reserve temperature value < 0 :=
    sub_neg.mpr hIntensityLt
  have hFirstDenominator :
      0 < exponentialIntensity reserve temperature bid + 0 := by
    positivity
  have hSecondDenominator :
      0 < exponentialIntensity reserve temperature bid +
        exponentialIntensity reserve temperature value + 0 := by
    positivity
  unfold twoIdentityGainIntegrand
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hBidIntensityPos (by simpa using hSignedFactor))
    (mul_pos hFirstDenominator hSecondDenominator)

theorem twoIdentityTruthfulGain_neg_of_zero_congestion
    (reserve value weight temperature : ℝ)
    (hValue : reserve < value) (hWeight : 0 < weight)
    (hTemperature : 0 < temperature) :
    twoIdentityTruthfulGain reserve value weight temperature 0 < 0 := by
  rw [twoIdentityTruthfulGain_integral reserve value weight temperature 0
    (le_refl 0)]
  apply mul_neg_of_pos_of_neg hWeight
  have hNegativeIntegralPos :
      0 < ∫ bid in reserve..value,
        -twoIdentityGainIntegrand reserve value temperature 0 bid := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      ((twoIdentityGainIntegrand_continuous reserve value temperature 0
        (le_refl 0)).neg.intervalIntegrable reserve value)
    · intro bid hBid
      exact neg_pos.mpr
        (twoIdentityGainIntegrand_neg_of_zero_congestion reserve value temperature
          bid hTemperature hBid.2)
    · exact hValue
  rw [intervalIntegral.integral_neg] at hNegativeIntegralPos
  linarith

/-- Antiderivative of either split identity's interim probability when there
are no opponents. -/
def twoIdentityZeroCongestionPrimitive
    (reserve value temperature bid : ℝ) : ℝ :=
  temperature *
    Real.log
      (exponentialIntensity reserve temperature bid +
        exponentialIntensity reserve temperature value)

theorem twoIdentityZeroCongestion_hasDerivAt
    (reserve value temperature bid : ℝ) (hTemperature : 0 < temperature) :
    HasDerivAt
      (twoIdentityZeroCongestionPrimitive reserve value temperature)
      (twoIdentityInterimProbability reserve value temperature 0 bid) bid := by
  have hTemperatureNe : temperature ≠ 0 := ne_of_gt hTemperature
  have hLinear :
      HasDerivAt (fun y : ℝ => (y - reserve) / temperature)
        (1 / temperature) bid := by
    convert ((hasDerivAt_id bid).sub_const reserve).div_const temperature using 1
  have hExp :
      HasDerivAt (fun y : ℝ => exponentialIntensity reserve temperature y)
        (exponentialIntensity reserve temperature bid * (1 / temperature)) bid := by
    unfold exponentialIntensity
    exact hLinear.exp
  have hInner :
      HasDerivAt
        (fun y : ℝ =>
          exponentialIntensity reserve temperature y +
            exponentialIntensity reserve temperature value)
        (exponentialIntensity reserve temperature bid * (1 / temperature)) bid := by
    simpa only [zero_add] using
      hExp.add_const (exponentialIntensity reserve temperature value)
  have hInnerPos :
      0 < exponentialIntensity reserve temperature bid +
        exponentialIntensity reserve temperature value := by
    unfold exponentialIntensity
    positivity
  have hPrimitive :=
    (hInner.log (ne_of_gt hInnerPos)).const_mul temperature
  change HasDerivAt
    (fun y : ℝ =>
      temperature *
        Real.log
          (exponentialIntensity reserve temperature y +
            exponentialIntensity reserve temperature value))
    (twoIdentityInterimProbability reserve value temperature 0 bid) bid
  apply hPrimitive.congr_deriv
  unfold twoIdentityInterimProbability
  field_simp
  ring

/-- Closed form of either split identity's envelope integral with no
opponents. -/
theorem twoIdentityInterimProbability_zeroCongestion_integral
    (reserve value temperature : ℝ) (hTemperature : 0 < temperature) :
    (∫ bid in reserve..value,
      twoIdentityInterimProbability reserve value temperature 0 bid) =
      temperature *
        Real.log
          (2 / (1 + Real.exp (-(value - reserve) / temperature))) := by
  have hContinuous :=
    twoIdentityInterimProbability_continuous reserve value temperature 0
      (le_refl 0)
  have hIntegral :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun bid _ =>
        twoIdentityZeroCongestion_hasDerivAt reserve value temperature bid
          hTemperature)
      (hContinuous.intervalIntegrable reserve value)
  rw [hIntegral]
  unfold twoIdentityZeroCongestionPrimitive
  rw [← mul_sub, ← Real.log_div]
  · congr 1
    unfold exponentialIntensity
    simp only [sub_self, zero_div, Real.exp_zero]
    have hValueIntensity :
        Real.exp ((value - reserve) / temperature) ≠ 0 := by
      positivity
    have hNegativeIntensity :
        Real.exp (-(value - reserve) / temperature) =
          (Real.exp ((value - reserve) / temperature))⁻¹ := by
      rw [show -(value - reserve) / temperature =
        -((value - reserve) / temperature) by ring, Real.exp_neg]
    rw [hNegativeIntensity]
    field_simp
    ring_nf
  · unfold exponentialIntensity
    positivity
  · unfold exponentialIntensity
    positivity

theorem oneSlotInclusionProbability_zeroCongestion
    (reserve temperature bid : ℝ) :
    oneSlotInclusionProbability reserve temperature 0 bid = 1 := by
  unfold oneSlotInclusionProbability
  field_simp
  ring

theorem oneSlotInclusionProbability_zeroCongestion_integral
    (reserve value temperature : ℝ) :
    (∫ bid in reserve..value,
      oneSlotInclusionProbability reserve temperature 0 bid) =
      value - reserve := by
  calc
    (∫ bid in reserve..value,
        oneSlotInclusionProbability reserve temperature 0 bid) =
        ∫ _bid in reserve..value, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro bid _
      exact oneSlotInclusionProbability_zeroCongestion reserve temperature bid
    _ = value - reserve := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]

/-- Exact finite-temperature no-opponent formula.  It makes the
self-competition term visible rather than hiding it in a limit argument. -/
theorem twoIdentityTruthfulGain_zeroCongestion_closedForm
    (reserve value weight temperature : ℝ) (hTemperature : 0 < temperature) :
    twoIdentityTruthfulGain reserve value weight temperature 0 =
      weight *
        (2 * temperature *
            Real.log
              (2 / (1 + Real.exp (-(value - reserve) / temperature))) -
          (value - reserve)) := by
  unfold twoIdentityTruthfulGain
  rw [twoIdentityInterimProbability_zeroCongestion_integral reserve value
      temperature hTemperature,
    oneSlotInclusionProbability_zeroCongestion_integral]
  ring

/-- The logarithmic correction in the no-opponent closed form vanishes as
temperature tends to zero from above. -/
theorem zeroCongestion_scaledLog_tendsto_zero
    (reserve value : ℝ) (hValue : reserve ≤ value) :
    Filter.Tendsto
      (fun temperature : ℝ =>
        temperature *
          Real.log
            (2 /
              (1 + Real.exp (-(value - reserve) / temperature))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards [self_mem_nhdsWithin] with temperature hTemperature
    have hTemperaturePos : 0 < temperature := hTemperature
    have hExponent : -(value - reserve) / temperature ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sub_nonneg.mpr hValue)) (le_of_lt hTemperaturePos)
    have hExp : Real.exp (-(value - reserve) / temperature) ≤ 1 :=
      Real.exp_le_one_iff.mpr hExponent
    have hDenominatorPos :
        0 < 1 + Real.exp (-(value - reserve) / temperature) := by
      positivity
    have hDenominatorLe :
        1 + Real.exp (-(value - reserve) / temperature) ≤ 2 := by
      linarith
    have hRatioOne :
        1 ≤ 2 / (1 + Real.exp (-(value - reserve) / temperature)) := by
      rw [le_div_iff₀ hDenominatorPos]
      simpa using hDenominatorLe
    exact mul_nonneg (le_of_lt hTemperaturePos) (Real.log_nonneg hRatioOne)
  · filter_upwards [self_mem_nhdsWithin] with temperature hTemperature
    have hTemperaturePos : 0 < temperature := hTemperature
    have hDenominatorPos :
        0 < 1 + Real.exp (-(value - reserve) / temperature) := by
      positivity
    have hDenominatorOne :
        1 ≤ 1 + Real.exp (-(value - reserve) / temperature) := by
      linarith [Real.exp_pos (-(value - reserve) / temperature)]
    have hRatioPos :
        0 < 2 / (1 + Real.exp (-(value - reserve) / temperature)) := by
      positivity
    have hRatioTwo :
        2 / (1 + Real.exp (-(value - reserve) / temperature)) ≤ 2 := by
      rw [div_le_iff₀ hDenominatorPos]
      nlinarith
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log hRatioPos hRatioTwo) (le_of_lt hTemperaturePos)
  · have hIdentity :
        Filter.Tendsto (fun temperature : ℝ => temperature)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa only [id_eq] using
        (continuousWithinAt_id :
          ContinuousWithinAt (fun temperature : ℝ => temperature) (Set.Ioi 0) 0)
    have hProduct := hIdentity.mul_const (Real.log 2)
    simpa using hProduct

/-- Formal counterexample to an unconditional zero strict-priority limit.
With no opponents, truthful splitting converges to the negative rent loss
`-weight * (value-reserve)`. -/
theorem twoIdentityTruthfulGain_zeroCongestion_tendsto
    (reserve value weight : ℝ) (hValue : reserve ≤ value) :
    Filter.Tendsto
      (fun temperature : ℝ =>
        twoIdentityTruthfulGain reserve value weight temperature 0)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-weight * (value - reserve))) := by
  have hScaledLog :=
    zeroCongestion_scaledLog_tendsto_zero reserve value hValue
  have hTwice :
      Filter.Tendsto
        (fun temperature : ℝ =>
          2 *
            (temperature *
              Real.log
                (2 /
                  (1 + Real.exp (-(value - reserve) / temperature)))))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hScaledLog.const_mul 2
  have hSubtract :
      Filter.Tendsto
        (fun temperature : ℝ =>
          2 *
              (temperature *
                Real.log
                  (2 /
                    (1 + Real.exp (-(value - reserve) / temperature)))) -
            (value - reserve))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(value - reserve))) := by
    simpa using hTwice.sub_const (value - reserve)
  have hFormula :
      Filter.Tendsto
        (fun temperature : ℝ =>
          weight *
            (2 *
                (temperature *
                  Real.log
                    (2 /
                      (1 + Real.exp (-(value - reserve) / temperature)))) -
              (value - reserve)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (weight * (-(value - reserve)))) :=
    hSubtract.const_mul weight
  have hGain :
      Filter.Tendsto
        (fun temperature : ℝ =>
          twoIdentityTruthfulGain reserve value weight temperature 0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (weight * (-(value - reserve)))) := by
    apply tendsto_nhdsWithin_congr (s := Set.Ioi 0) _ hFormula
    intro temperature hTemperature
    simpa [mul_assoc] using
      (twoIdentityTruthfulGain_zeroCongestion_closedForm reserve value weight
        temperature hTemperature).symm
  convert hGain using 1
  ring_nf

/-- Under the nondegenerate parameters used in the remark, the no-opponent
strict-priority limit is strictly negative and hence is not zero. -/
theorem twoIdentityTruthfulGain_zeroCongestion_strictPriority_counterexample
    (reserve value weight : ℝ)
    (hValue : reserve < value) (hWeight : 0 < weight) :
    Filter.Tendsto
        (fun temperature : ℝ =>
          twoIdentityTruthfulGain reserve value weight temperature 0)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (-weight * (value - reserve))) ∧
      -weight * (value - reserve) < 0 := by
  constructor
  · exact twoIdentityTruthfulGain_zeroCongestion_tendsto reserve value weight
      (le_of_lt hValue)
  · nlinarith [mul_pos hWeight (sub_pos.mpr hValue)]

/-! ### Genuine lottery limit -/

/-- Aggregate intensity of an arbitrary finite collection of fixed opponent
bids. -/
def opponentAggregateIntensity
    {Opponent : Type*} [Fintype Opponent]
    (reserve temperature : ℝ) (opponentBid : Opponent → ℝ) : ℝ :=
  ∑ i, exponentialIntensity reserve temperature (opponentBid i)

theorem opponentAggregateIntensity_nonneg
    {Opponent : Type*} [Fintype Opponent]
    (reserve temperature : ℝ) (opponentBid : Opponent → ℝ) :
    0 ≤ opponentAggregateIntensity reserve temperature opponentBid := by
  unfold opponentAggregateIntensity
  exact Finset.sum_nonneg fun i _ => le_of_lt (by
    unfold exponentialIntensity
    positivity)

/-- Every fixed bid's reserve-normalized intensity tends to one in the
high-temperature limit. -/
theorem exponentialIntensity_tendsto_lottery
    (reserve bid : ℝ) :
    Filter.Tendsto
      (fun temperature : ℝ => exponentialIntensity reserve temperature bid)
      Filter.atTop (nhds 1) := by
  have hInverse :
      Filter.Tendsto (fun temperature : ℝ => temperature⁻¹)
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hScaled := hInverse.const_mul (bid - reserve)
  have hExponent :
      Filter.Tendsto (fun temperature : ℝ => (bid - reserve) / temperature)
        Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using hScaled
  unfold exponentialIntensity
  simpa using Real.continuous_exp.continuousAt.tendsto.comp hExponent

/-- Consequently, aggregate opponent intensity tends to the number of
opponents. -/
theorem opponentAggregateIntensity_tendsto_lottery
    {Opponent : Type*} [Fintype Opponent]
    (reserve : ℝ) (opponentBid : Opponent → ℝ) :
    Filter.Tendsto
      (fun temperature : ℝ =>
        opponentAggregateIntensity reserve temperature opponentBid)
      Filter.atTop (nhds (Fintype.card Opponent : ℝ)) := by
  have hSum :=
    tendsto_finsetSum Finset.univ
      (fun i _ =>
        exponentialIntensity_tendsto_lottery reserve (opponentBid i))
  simpa [opponentAggregateIntensity] using hSum

/-- Pointwise lottery limit of the signed two-identity integrand. -/
theorem twoIdentityGainIntegrand_tendsto_lottery
    {Opponent : Type*} [Fintype Opponent]
    (reserve value bid : ℝ) (opponentBid : Opponent → ℝ) :
    Filter.Tendsto
      (fun temperature : ℝ =>
        twoIdentityGainIntegrand reserve value temperature
          (opponentAggregateIntensity reserve temperature opponentBid) bid)
      Filter.atTop
      (nhds
        ((Fintype.card Opponent : ℝ) /
          (((Fintype.card Opponent : ℝ) + 1) *
            ((Fintype.card Opponent : ℝ) + 2)))) := by
  let opponents : ℝ := Fintype.card Opponent
  have hBid := exponentialIntensity_tendsto_lottery reserve bid
  have hValue := exponentialIntensity_tendsto_lottery reserve value
  have hCongestion :=
    opponentAggregateIntensity_tendsto_lottery reserve opponentBid
  have hNumerator :=
    hBid.mul ((hCongestion.add hBid).sub hValue)
  have hFirstDenominator := hBid.add hCongestion
  have hSecondDenominator := (hBid.add hValue).add hCongestion
  have hDenominator := hFirstDenominator.mul hSecondDenominator
  have hDenominatorNe :
      (1 + opponents) * (1 + 1 + opponents) ≠ 0 := by
    dsimp [opponents]
    positivity
  have hRatio := hNumerator.div hDenominator hDenominatorNe
  unfold twoIdentityGainIntegrand
  convert hRatio using 1
  all_goals ring_nf

theorem twoIdentityInterimProbability_mem_Icc
    (reserve value temperature congestion bid : ℝ)
    (hCongestion : 0 ≤ congestion) :
    twoIdentityInterimProbability reserve value temperature congestion bid ∈
      Set.Icc (0 : ℝ) 1 := by
  unfold twoIdentityInterimProbability exponentialIntensity
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    have hRemainder :
        0 ≤ Real.exp ((value - reserve) / temperature) + congestion := by
      positivity
    linarith

/-- A temperature-independent integrable dominator for the lottery-limit
argument.  It follows from writing the gain integrand as twice one probability
minus another, both in `[0,1]`. -/
theorem twoIdentityGainIntegrand_norm_le_three
    (reserve value temperature congestion bid : ℝ)
    (hCongestion : 0 ≤ congestion) :
    ‖twoIdentityGainIntegrand reserve value temperature congestion bid‖ ≤ 3 := by
  rw [← twoIdentityGainIntegrand_identity reserve value temperature congestion bid
    hCongestion]
  have hTwo :=
    twoIdentityInterimProbability_mem_Icc reserve value temperature congestion bid
      hCongestion
  have hSingle :=
    oneSlotInclusionProbability_mem_Icc reserve temperature congestion bid
      hCongestion
  rcases hTwo with ⟨hTwoNonneg, hTwoLe⟩
  rcases hSingle with ⟨hSingleNonneg, hSingleLe⟩
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- Dominated convergence upgrades the pointwise lottery limit to the full
gain integral. -/
theorem twoIdentityGainIntegral_tendsto_lottery
    {Opponent : Type*} [Fintype Opponent]
    (reserve value : ℝ) (opponentBid : Opponent → ℝ) :
    Filter.Tendsto
      (fun temperature : ℝ =>
        ∫ bid in reserve..value,
          twoIdentityGainIntegrand reserve value temperature
            (opponentAggregateIntensity reserve temperature opponentBid) bid)
      Filter.atTop
      (nhds
        ((value - reserve) * (Fintype.card Opponent : ℝ) /
          (((Fintype.card Opponent : ℝ) + 1) *
            ((Fintype.card Opponent : ℝ) + 2)))) := by
  let limitRate : ℝ :=
    (Fintype.card Opponent : ℝ) /
      (((Fintype.card Opponent : ℝ) + 1) *
        ((Fintype.card Opponent : ℝ) + 2))
  have hDominated :=
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (a := reserve) (b := value) (l := Filter.atTop)
      (f := fun _bid : ℝ => limitRate)
      (F := fun temperature bid =>
        twoIdentityGainIntegrand reserve value temperature
          (opponentAggregateIntensity reserve temperature opponentBid) bid)
      (bound := fun _bid : ℝ => 3)
      (by
        filter_upwards [] with temperature
        exact
          (twoIdentityGainIntegrand_continuous reserve value temperature
            (opponentAggregateIntensity reserve temperature opponentBid)
            (opponentAggregateIntensity_nonneg reserve temperature opponentBid)
          ).aestronglyMeasurable)
      (by
        filter_upwards [] with temperature
        filter_upwards [] with bid
        intro _hBid
        exact
          twoIdentityGainIntegrand_norm_le_three reserve value temperature
            (opponentAggregateIntensity reserve temperature opponentBid) bid
            (opponentAggregateIntensity_nonneg reserve temperature opponentBid))
      (Continuous.intervalIntegrable (μ := volume) continuous_const reserve value)
      (by
        filter_upwards [] with bid
        intro _hBid
        exact
          twoIdentityGainIntegrand_tendsto_lottery reserve value bid opponentBid)
  convert hDominated using 1
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  dsimp [limitRate]
  ring_nf

/-- Genuine high-temperature limit of the two-identity truthful gain.  The
opponents' fixed bids may be arbitrary; symmetry is unnecessary because every
finite intensity tends to one. -/
theorem twoIdentityTruthfulGain_tendsto_lottery
    {Opponent : Type*} [Fintype Opponent]
    (reserve value weight : ℝ) (opponentBid : Opponent → ℝ) :
    Filter.Tendsto
      (fun temperature : ℝ =>
        twoIdentityTruthfulGain reserve value weight temperature
          (opponentAggregateIntensity reserve temperature opponentBid))
      Filter.atTop
      (nhds
        (weight * (value - reserve) * (Fintype.card Opponent : ℝ) /
          (((Fintype.card Opponent : ℝ) + 1) *
            ((Fintype.card Opponent : ℝ) + 2)))) := by
  have hIntegral :=
    (twoIdentityGainIntegral_tendsto_lottery reserve value opponentBid).const_mul
      weight
  have hGain :
      Filter.Tendsto
        (fun temperature : ℝ =>
          twoIdentityTruthfulGain reserve value weight temperature
            (opponentAggregateIntensity reserve temperature opponentBid))
        Filter.atTop
        (nhds
          (weight *
            ((value - reserve) * (Fintype.card Opponent : ℝ) /
              (((Fintype.card Opponent : ℝ) + 1) *
                ((Fintype.card Opponent : ℝ) + 2))))) := by
    apply hIntegral.congr
    intro temperature
    exact
      (twoIdentityTruthfulGain_integral reserve value weight temperature
        (opponentAggregateIntensity reserve temperature opponentBid)
        (opponentAggregateIntensity_nonneg reserve temperature opponentBid)).symm
  convert hGain using 1
  ring_nf

/-- Algebraic value of the gain rate when every intensity has reached its
lottery-limit value one. -/
theorem lottery_twoIdentity_gain_rate
    (opponents : ℕ) :
    2 / ((opponents : ℝ) + 2) - 1 / ((opponents : ℝ) + 1) =
      (opponents : ℝ) /
        (((opponents : ℝ) + 1) * ((opponents : ℝ) + 2)) := by
  have hOne : (opponents : ℝ) + 1 ≠ 0 := by positivity
  have hTwo : (opponents : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Integrating the constant lottery-limit rate gives the expression printed
in Remark `rem:sybilsign`. -/
theorem lottery_twoIdentity_gain
    (reserve value weight : ℝ) (opponents : ℕ) :
    weight * (∫ _bid in reserve..value,
        (2 / ((opponents : ℝ) + 2) - 1 / ((opponents : ℝ) + 1))) =
      weight * (value - reserve) * (opponents : ℝ) /
        (((opponents : ℝ) + 1) * ((opponents : ℝ) + 2)) := by
  rw [lottery_twoIdentity_gain_rate opponents,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

end SmoothingCliff.Mechanism
