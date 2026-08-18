import SmoothingCliff.Mechanism.Sybil

/-!
# The strict-priority branch of Remark `rem:sybilsign`

Remark `rem:sybilsign` in `Smoothing_the_Cliff_ITCS.tex` records that the
`tau -> 0+` limit of the truthful two-identity gain

`G2(v) = w1 * integral_r^v  a(z) * (L + a(z) - a(v)) /
            ((a(z) + L) * (a(z) + a(v) + L))  dz`,  `a(z) = exp ((z - r) / tau)`,

*depends on the opponents' top order statistic*: it is zero when some opponent
bids at least `v`, and equals `-w1 * (v - r)` against no eligible opponent.

`SmoothingCliff.Mechanism.Sybil` already settles the second branch
(`twoIdentityTruthfulGain_zeroCongestion_closedForm`,
`twoIdentityTruthfulGain_zeroCongestion_tendsto`,
`twoIdentityTruthfulGain_zeroCongestion_strictPriority_counterexample`).
This file settles the first one.

`twoIdentityTruthfulGain` carries the aggregate opponent intensity `L` as a
parameter, so "some opponent bids at least `v`" is expressed here as
`exponentialIntensity reserve tau value <= L`, that is `L >= a(v)`: the single
opponent bidding `b_max >= v` already contributes `exp ((b_max - r) / tau) >=
a(v)` to the aggregate.  Because `a(v) = exp ((v - r) / tau)` blows up as
`tau -> 0+`, that hypothesis cannot hold along the limit for a *constant* `L`;
the congestion therefore enters as a family `congestion : R -> R` indexed by
the temperature.  `twoIdentityTruthfulGain_strictPriority_tendsto_of_top_bid`
instantiates the family at the genuine aggregate
`opponentAggregateIntensity`, where the hypothesis is literally that some
opponent bids at least `value`.

The proof is a two-sided squeeze rather than dominated convergence, which
gives the quantitative rate as a by-product:

* the integrand is nonnegative on `[r, v]` (already available, since
  `L >= a(v)` implies the remark's thick-market threshold `L >= a(v) - 1`);
* pointwise it is at most `a(z) / a(v) = exp ((z - v) / tau)`, uniformly in
  the congestion;
* hence `0 <= integral_r^v <= tau * (1 - exp (-(v - r) / tau)) <= tau`, so
  `|G2(v)| <= |w1| * tau -> 0`.
-/

noncomputable section

namespace SmoothingCliff.Mechanism

open MeasureTheory

/-! ## Elementary intensity facts -/

/-- Reserve-normalized intensities are positive. -/
theorem exponentialIntensity_pos (reserve temperature bid : ℝ) :
    0 < exponentialIntensity reserve temperature bid := by
  unfold exponentialIntensity
  positivity

/-- Ratio of two intensities at a common temperature. -/
theorem exponentialIntensity_div (reserve temperature bid value : ℝ) :
    exponentialIntensity reserve temperature bid /
        exponentialIntensity reserve temperature value =
      Real.exp ((bid - value) / temperature) := by
  unfold exponentialIntensity
  rw [← Real.exp_sub]
  congr 1
  ring

/-- At a positive temperature the intensity is monotone in the bid. -/
theorem exponentialIntensity_le_of_le
    (reserve temperature bid bid' : ℝ)
    (hTemperature : 0 < temperature) (hBid : bid ≤ bid') :
    exponentialIntensity reserve temperature bid ≤
      exponentialIntensity reserve temperature bid' := by
  unfold exponentialIntensity
  rw [Real.exp_le_exp]
  gcongr

/-! ## The pointwise strict-priority bound -/

/-- Uniformly in the congestion, the signed two-identity integrand is at most
`a(bid) / a(value) = exp ((bid - value) / tau)`.  This is the pointwise input
to the strict-priority limit: for `bid < value` the right-hand side collapses
to zero as `tau -> 0+`. -/
theorem twoIdentityGainIntegrand_le_exp
    (reserve value temperature congestion bid : ℝ)
    (hCongestion : 0 ≤ congestion) :
    twoIdentityGainIntegrand reserve value temperature congestion bid ≤
      Real.exp ((bid - value) / temperature) := by
  set intensityBid := exponentialIntensity reserve temperature bid with hIntensityBid
  set intensityValue := exponentialIntensity reserve temperature value with hIntensityValue
  have hBidPos : 0 < intensityBid := exponentialIntensity_pos reserve temperature bid
  have hValuePos : 0 < intensityValue := exponentialIntensity_pos reserve temperature value
  have hFirstDenominator : 0 < intensityBid + congestion := by linarith
  have hSecondDenominator : 0 < intensityBid + intensityValue + congestion := by linarith
  have hDenominator :
      0 < (intensityBid + congestion) * (intensityBid + intensityValue + congestion) :=
    mul_pos hFirstDenominator hSecondDenominator
  have hRatio :
      intensityBid / intensityValue = Real.exp ((bid - value) / temperature) :=
    exponentialIntensity_div reserve temperature bid value
  rw [← hRatio]
  unfold twoIdentityGainIntegrand
  rw [← hIntensityBid, ← hIntensityValue, div_le_div_iff₀ hDenominator hValuePos]
  nlinarith [mul_nonneg hBidPos.le (sq_nonneg (intensityBid + congestion)),
    mul_nonneg hBidPos.le (sq_nonneg intensityValue)]

/-! ## The dominating integral -/

/-- Exact value of the dominating integral. -/
theorem integral_exp_shifted
    (reserve value temperature : ℝ) (hTemperature : 0 < temperature) :
    (∫ z in reserve..value, Real.exp ((z - value) / temperature)) =
      temperature * (1 - Real.exp ((reserve - value) / temperature)) := by
  have hTemperatureNe : temperature ≠ 0 := ne_of_gt hTemperature
  have hDeriv : ∀ z ∈ Set.uIcc reserve value,
      HasDerivAt (fun y : ℝ => temperature * Real.exp ((y - value) / temperature))
        (Real.exp ((z - value) / temperature)) z := by
    intro z _
    have hLinear :
        HasDerivAt (fun y : ℝ => (y - value) / temperature) (1 / temperature) z := by
      simpa using ((hasDerivAt_id z).sub_const value).div_const temperature
    have hScaled := (hLinear.exp).const_mul temperature
    convert hScaled using 1
    field_simp
  have hIntegrable :
      IntervalIntegrable (fun z : ℝ => Real.exp ((z - value) / temperature))
        volume reserve value := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hIntegrable]
  simp only [sub_self, zero_div, Real.exp_zero, mul_one]
  ring

/-! ## The two-sided bound on the gain integral -/

/-- Under `L >= a(v)` the gain integral is nonnegative: this is the remark's
thick-market sign, since `L >= a(v)` is stronger than the threshold
`L >= a(v) - 1`. -/
theorem twoIdentityGainIntegral_strictPriority_nonneg
    (reserve value temperature congestion : ℝ)
    (hValue : reserve ≤ value) (hTemperature : 0 < temperature)
    (hDominant : exponentialIntensity reserve temperature value ≤ congestion) :
    0 ≤ ∫ bid in reserve..value,
      twoIdentityGainIntegrand reserve value temperature congestion bid := by
  have hValuePos : 0 < exponentialIntensity reserve temperature value :=
    exponentialIntensity_pos reserve temperature value
  have hCongestion : 0 ≤ congestion := le_trans hValuePos.le hDominant
  have hThick : exponentialIntensity reserve temperature value - 1 ≤ congestion := by
    linarith
  exact intervalIntegral.integral_nonneg hValue fun bid hBid =>
    twoIdentityGainIntegrand_nonneg reserve value temperature congestion bid
      hTemperature hCongestion hBid.1 hThick

/-- The strict-priority rate: the gain integral is at most the temperature,
uniformly in the congestion level. -/
theorem twoIdentityGainIntegral_le_temperature
    (reserve value temperature congestion : ℝ)
    (hValue : reserve ≤ value) (hTemperature : 0 < temperature)
    (hCongestion : 0 ≤ congestion) :
    (∫ bid in reserve..value,
        twoIdentityGainIntegrand reserve value temperature congestion bid) ≤
      temperature := by
  have hIntegrandIntegrable :
      IntervalIntegrable
        (twoIdentityGainIntegrand reserve value temperature congestion)
        volume reserve value :=
    (twoIdentityGainIntegrand_continuous reserve value temperature congestion
      hCongestion).intervalIntegrable reserve value
  have hExpIntegrable :
      IntervalIntegrable (fun z : ℝ => Real.exp ((z - value) / temperature))
        volume reserve value := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hMono :
      (∫ bid in reserve..value,
          twoIdentityGainIntegrand reserve value temperature congestion bid) ≤
        ∫ bid in reserve..value, Real.exp ((bid - value) / temperature) :=
    intervalIntegral.integral_mono_on hValue hIntegrandIntegrable hExpIntegrable
      fun bid _ =>
        twoIdentityGainIntegrand_le_exp reserve value temperature congestion bid
          hCongestion
  have hExpIntegral := integral_exp_shifted reserve value temperature hTemperature
  have hExpNonneg : 0 ≤ Real.exp ((reserve - value) / temperature) :=
    (Real.exp_pos _).le
  nlinarith [hMono, hExpIntegral, hExpNonneg, hTemperature]

/-- Quantitative strict-priority bound on the gain itself.  It is the whole
content of the first branch of the remark: with an opponent at least as
aggressive as the coalition, the two-identity gain is squeezed between `0` and
`|w1| * tau`. -/
theorem twoIdentityTruthfulGain_strictPriority_abs_le
    (reserve value weight temperature congestion : ℝ)
    (hValue : reserve ≤ value) (hTemperature : 0 < temperature)
    (hDominant : exponentialIntensity reserve temperature value ≤ congestion) :
    |twoIdentityTruthfulGain reserve value weight temperature congestion| ≤
      |weight| * temperature := by
  have hValuePos : 0 < exponentialIntensity reserve temperature value :=
    exponentialIntensity_pos reserve temperature value
  have hCongestion : 0 ≤ congestion := le_trans hValuePos.le hDominant
  have hNonneg :=
    twoIdentityGainIntegral_strictPriority_nonneg reserve value temperature congestion
      hValue hTemperature hDominant
  have hLe :=
    twoIdentityGainIntegral_le_temperature reserve value temperature congestion
      hValue hTemperature hCongestion
  rw [twoIdentityTruthfulGain_integral reserve value weight temperature congestion
    hCongestion, abs_mul, abs_of_nonneg hNonneg]
  exact mul_le_mul_of_nonneg_left hLe (abs_nonneg weight)

/-- The bound is not vacuous.  At every positive temperature the dominated
coalition's two-identity gain is *strictly* positive, because `L >= a(v)`
implies the remark's thick-market threshold.  The strict-priority limit below
is therefore a genuine decay of positive splitting rents, not a statement
about a quantity that already vanishes. -/
theorem twoIdentityTruthfulGain_strictPriority_pos
    (reserve value weight temperature congestion : ℝ)
    (hValue : reserve < value) (hWeight : 0 < weight) (hTemperature : 0 < temperature)
    (hDominant : exponentialIntensity reserve temperature value ≤ congestion) :
    0 < twoIdentityTruthfulGain reserve value weight temperature congestion := by
  have hValuePos : 0 < exponentialIntensity reserve temperature value :=
    exponentialIntensity_pos reserve temperature value
  have hCongestion : 0 ≤ congestion := le_trans hValuePos.le hDominant
  exact twoIdentityTruthfulGain_pos reserve value weight temperature congestion
    hValue hWeight hTemperature hCongestion (by linarith)

/-! ## The strict-priority limit -/

/-- **First branch of Remark `rem:sybilsign`.**  If at every temperature the
aggregate opponent intensity dominates the coalition's own intensity at
`value` -- that is `L(tau) >= a(v)`, which is exactly "some opponent bids at
least `v`" -- then the truthful two-identity gain tends to `0` in the
strict-priority limit `tau -> 0+`.

This is the full filter limit along `nhdsWithin 0 (Set.Ioi 0)`, not merely a
sequential one, and no sign condition on `weight` is needed. -/
theorem twoIdentityTruthfulGain_strictPriority_tendsto
    (reserve value weight : ℝ) (congestion : ℝ → ℝ)
    (hValue : reserve ≤ value)
    (hDominant : ∀ temperature : ℝ, 0 < temperature →
      exponentialIntensity reserve temperature value ≤ congestion temperature) :
    Filter.Tendsto
      (fun temperature : ℝ =>
        twoIdentityTruthfulGain reserve value weight temperature
          (congestion temperature))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hBoundTendsto :
      Filter.Tendsto (fun temperature : ℝ => |weight| * temperature)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hContinuous :
        ContinuousWithinAt (fun temperature : ℝ => |weight| * temperature)
          (Set.Ioi 0) 0 :=
      (continuous_const.mul continuous_id).continuousWithinAt
    simpa using hContinuous.tendsto
  apply squeeze_zero_norm' _ hBoundTendsto
  filter_upwards [self_mem_nhdsWithin] with temperature hTemperature
  have hTemperaturePos : 0 < temperature := hTemperature
  rw [Real.norm_eq_abs]
  exact twoIdentityTruthfulGain_strictPriority_abs_le reserve value weight temperature
    (congestion temperature) hValue hTemperaturePos
    (hDominant temperature hTemperaturePos)

/-! ## Instantiation at genuine opponents -/

/-- One opponent bidding at least `value` already dominates the coalition's own
intensity at `value`. -/
theorem exponentialIntensity_le_opponentAggregateIntensity
    {Opponent : Type*} [Fintype Opponent]
    (reserve temperature value : ℝ) (opponentBid : Opponent → ℝ)
    (top : Opponent) (hTop : value ≤ opponentBid top)
    (hTemperature : 0 < temperature) :
    exponentialIntensity reserve temperature value ≤
      opponentAggregateIntensity reserve temperature opponentBid := by
  have hTopIntensity :
      exponentialIntensity reserve temperature value ≤
        exponentialIntensity reserve temperature (opponentBid top) :=
    exponentialIntensity_le_of_le reserve temperature value (opponentBid top)
      hTemperature hTop
  have hSum :
      exponentialIntensity reserve temperature (opponentBid top) ≤
        ∑ i, exponentialIntensity reserve temperature (opponentBid i) :=
    Finset.single_le_sum
      (f := fun i => exponentialIntensity reserve temperature (opponentBid i))
      (fun i _ => (exponentialIntensity_pos reserve temperature (opponentBid i)).le)
      (Finset.mem_univ top)
  exact le_trans hTopIntensity hSum

/-- **First branch of Remark `rem:sybilsign`, stated on the opponents.**  With
arbitrary fixed opponent bids of which at least one is at least `value`, the
truthful two-identity gain vanishes in the strict-priority limit. -/
theorem twoIdentityTruthfulGain_strictPriority_tendsto_of_top_bid
    {Opponent : Type*} [Fintype Opponent]
    (reserve value weight : ℝ) (opponentBid : Opponent → ℝ)
    (top : Opponent) (hValue : reserve ≤ value) (hTop : value ≤ opponentBid top) :
    Filter.Tendsto
      (fun temperature : ℝ =>
        twoIdentityTruthfulGain reserve value weight temperature
          (opponentAggregateIntensity reserve temperature opponentBid))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  twoIdentityTruthfulGain_strictPriority_tendsto reserve value weight
    (fun temperature => opponentAggregateIntensity reserve temperature opponentBid)
    hValue
    fun temperature hTemperature =>
      exponentialIntensity_le_opponentAggregateIntensity reserve temperature value
        opponentBid top hTop hTemperature

/-! ## The remark's dichotomy -/

/-- The remark's claim in one statement: the strict-priority limit really does
depend on the opponents' top order statistic.  Against an opponent bidding at
least `value` the limit is `0`; against no eligible opponent it is
`-w1 * (v - r)`, which is nonzero whenever the coalition has a strictly
positive rent to lose. -/
theorem twoIdentityTruthfulGain_strictPriority_dichotomy
    {Opponent : Type*} [Fintype Opponent]
    (reserve value weight : ℝ) (opponentBid : Opponent → ℝ)
    (top : Opponent) (hValue : reserve < value) (hWeight : 0 < weight)
    (hTop : value ≤ opponentBid top) :
    Filter.Tendsto
        (fun temperature : ℝ =>
          twoIdentityTruthfulGain reserve value weight temperature
            (opponentAggregateIntensity reserve temperature opponentBid))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto
        (fun temperature : ℝ =>
          twoIdentityTruthfulGain reserve value weight temperature 0)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-weight * (value - reserve))) ∧
      -weight * (value - reserve) ≠ 0 := by
  refine ⟨twoIdentityTruthfulGain_strictPriority_tendsto_of_top_bid reserve value weight
      opponentBid top hValue.le hTop,
    twoIdentityTruthfulGain_zeroCongestion_tendsto reserve value weight hValue.le, ?_⟩
  have hPositive : 0 < weight * (value - reserve) :=
    mul_pos hWeight (sub_pos.mpr hValue)
  intro hZero
  nlinarith [hPositive, hZero]

end SmoothingCliff.Mechanism
