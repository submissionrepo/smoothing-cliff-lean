import SmoothingCliff.Racing.StrictPriority
import SmoothingCliff.Racing.RentDissipation
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# Net-surplus comparison for two heterogeneous bidders

This file formalizes the core of Proposition `prop:netsurplus` in
*Smoothing the Cliff*.  Write `gap = v-r` and `delta = v₁-v₂`, so the high
and low values are `v+delta` and `v` and their contested bands are
`gap+delta` and `gap`.
-/

namespace SmoothingCliff.Racing

noncomputable section

/-- Strict-priority payoff when the focal bidder starts with an effective
score shift relative to the rival. -/
def shiftedStrictPriorityPayoff
    (slotWeight band shift marginalCost own rival : ℝ) : ℝ :=
  slotWeight * strictPriorityCapturedGap band (own + shift) rival -
    marginalCost * own

/-- The higher-value bidder's payoff. -/
def highValueStrictPriorityPayoff
    (slotWeight gap delta marginalCost own rival : ℝ) : ℝ :=
  shiftedStrictPriorityPayoff slotWeight (gap + delta) delta
    marginalCost own rival

/-- The lower-value bidder's payoff. -/
def lowValueStrictPriorityPayoff
    (slotWeight gap delta marginalCost own rival : ℝ) : ℝ :=
  shiftedStrictPriorityPayoff slotWeight gap (-delta)
    marginalCost own rival

/-- Pure Nash equilibrium of the heterogeneous strict-priority race. -/
def HeterogeneousStrictPriorityPureNash
    (slotWeight gap delta marginalCost first second : ℝ) : Prop :=
  NonnegativeBestResponse
      (fun deviation => highValueStrictPriorityPayoff
        slotWeight gap delta marginalCost deviation second) first ∧
    NonnegativeBestResponse
      (fun deviation => lowValueStrictPriorityPayoff
        slotWeight gap delta marginalCost deviation first) second

/-- A bidder who is currently ahead but has not filled her contested band
can profitably extend the lead when `κ < w₁`.  Therefore every leading best
response saturates its band. -/
theorem shifted_leader_bestResponse_saturates
    {slotWeight band shift marginalCost own rival : ℝ}
    (hBand : 0 < band)
    (hCostWeight : marginalCost < slotWeight)
    (hLead : 0 < own + shift - rival)
    (hBest : NonnegativeBestResponse
      (fun deviation => shiftedStrictPriorityPayoff
        slotWeight band shift marginalCost deviation rival) own) :
    band ≤ own + shift - rival := by
  by_contra hNot
  have hBelow : own + shift - rival < band := lt_of_not_ge hNot
  let deviation := own + (band - (own + shift - rival))
  have hIncrement : 0 < band - (own + shift - rival) := sub_pos.mpr hBelow
  have hDeviation : 0 ≤ deviation := by
    dsimp [deviation]
    linarith [hBest.1]
  have hOptimal :
      shiftedStrictPriorityPayoff slotWeight band shift marginalCost
          deviation rival ≤
        shiftedStrictPriorityPayoff slotWeight band shift marginalCost own rival :=
    hBest.2 hDeviation
  have hCurrentPositive : 0 ≤ own + shift - rival := hLead.le
  have hDeviationLead : deviation + shift - rival = band := by
    dsimp [deviation]
    ring
  unfold shiftedStrictPriorityPayoff at hOptimal
  unfold strictPriorityCapturedGap at hOptimal
  rw [max_eq_left hCurrentPositive, min_eq_left hBelow.le,
    hDeviationLead, max_eq_left hBand.le, min_self] at hOptimal
  nlinarith

/-- Against zero low-bidder investment, the high bidder's unique response is
the baseline contested band `v-r`. -/
theorem highValue_bestResponse_to_zero
    {slotWeight gap delta marginalCost : ℝ}
    (hGap : 0 < gap) (hDelta : 0 ≤ delta)
    (hCost : 0 < marginalCost) (hCostWeight : marginalCost < slotWeight) :
    NonnegativeBestResponse
      (fun action => highValueStrictPriorityPayoff
        slotWeight gap delta marginalCost action 0) gap := by
  refine ⟨hGap.le, ?_⟩
  intro deviation hDeviation
  change highValueStrictPriorityPayoff slotWeight gap delta marginalCost
      deviation 0 ≤
    highValueStrictPriorityPayoff slotWeight gap delta marginalCost gap 0
  unfold highValueStrictPriorityPayoff shiftedStrictPriorityPayoff
  unfold strictPriorityCapturedGap
  simp only [sub_zero]
  have hBand : 0 < gap + delta := add_pos_of_pos_of_nonneg hGap hDelta
  rw [max_eq_left hBand.le, min_self]
  by_cases hBelow : deviation ≤ gap
  · have hDevShift : 0 ≤ deviation + delta := add_nonneg hDeviation hDelta
    have hWithin : deviation + delta ≤ gap + delta := by linarith
    rw [max_eq_left hDevShift, min_eq_left hWithin]
    nlinarith
  · have hBeyond : gap + delta ≤ deviation + delta := by linarith
    rw [min_eq_right (le_trans hBeyond (le_max_left _ _))]
    nlinarith

/-- Against the high bidder's action `v-r`, zero is the lower bidder's unique
best response in the maintained region `κ>w₁/2`. -/
theorem lowValue_bestResponse_to_high_gap
    {slotWeight gap delta marginalCost : ℝ}
    (hGap : 0 < gap) (hDelta : 0 ≤ delta)
    (hHalfCost : slotWeight / 2 < marginalCost)
    (hCostWeight : marginalCost < slotWeight) :
    NonnegativeBestResponse
      (fun action => lowValueStrictPriorityPayoff
        slotWeight gap delta marginalCost action gap) 0 := by
  have hCost : 0 < marginalCost := by nlinarith
  refine ⟨le_refl 0, ?_⟩
  intro deviation hDeviation
  have hDeviationNonneg : 0 ≤ deviation := hDeviation
  change lowValueStrictPriorityPayoff slotWeight gap delta marginalCost
      deviation gap ≤
    lowValueStrictPriorityPayoff slotWeight gap delta marginalCost 0 gap
  unfold lowValueStrictPriorityPayoff shiftedStrictPriorityPayoff
  unfold strictPriorityCapturedGap
  have hZeroLead : 0 + -delta - gap ≤ 0 := by linarith
  rw [max_eq_right hZeroLead, min_eq_left hGap.le]
  by_cases hNoLead : deviation + -delta - gap ≤ 0
  · rw [max_eq_right hNoLead, min_eq_left hGap.le]
    nlinarith
  · have hLead : 0 ≤ deviation + -delta - gap := le_of_not_ge hNoLead
    rw [max_eq_left hLead]
    by_cases hWithin : deviation + -delta - gap ≤ gap
    · rw [min_eq_left hWithin]
      nlinarith
    · rw [min_eq_right (le_of_not_ge hWithin)]
      nlinarith

/-- Proposition `prop:netsurplus` (i), displayed equilibrium. -/
theorem heterogeneous_strictPriority_equilibrium
    {slotWeight gap delta marginalCost : ℝ}
    (hGap : 0 < gap) (hDelta : 0 ≤ delta)
    (hHalfCost : slotWeight / 2 < marginalCost)
    (hCostWeight : marginalCost < slotWeight) :
    HeterogeneousStrictPriorityPureNash
      slotWeight gap delta marginalCost gap 0 := by
  exact ⟨
    highValue_bestResponse_to_zero hGap hDelta (by nlinarith) hCostWeight,
    lowValue_bestResponse_to_high_gap hGap hDelta hHalfCost hCostWeight⟩

/-- An effective-score tie cannot be a pure equilibrium when `κ<w₁`: the
high bidder can buy one more baseline contested band. -/
theorem heterogeneous_strictPriority_no_effective_tie
    {slotWeight gap delta marginalCost first second : ℝ}
    (hGap : 0 < gap) (hDelta : 0 ≤ delta)
    (hCostWeight : marginalCost < slotWeight)
    (hNash : HeterogeneousStrictPriorityPureNash
      slotWeight gap delta marginalCost first second) :
    first + delta ≠ second := by
  intro hTie
  have hDeviation : 0 ≤ first + gap := add_nonneg hNash.1.1 hGap.le
  have hOptimal :
      highValueStrictPriorityPayoff slotWeight gap delta marginalCost
          (first + gap) second ≤
        highValueStrictPriorityPayoff slotWeight gap delta marginalCost
          first second := hNash.1.2 hDeviation
  have hCurrentLead : first + delta - second = 0 := by linarith
  have hDeviationLead : first + gap + delta - second = gap := by linarith
  have hBand : 0 < gap + delta := add_pos_of_pos_of_nonneg hGap hDelta
  unfold highValueStrictPriorityPayoff shiftedStrictPriorityPayoff at hOptimal
  unfold strictPriorityCapturedGap at hOptimal
  rw [hCurrentLead, max_self, min_eq_left hBand.le,
    hDeviationLead, max_eq_left hGap.le,
    min_eq_left (by linarith : gap ≤ gap + delta)] at hOptimal
  nlinarith

/-- Every heterogeneous pure equilibrium invests at least one baseline
contested band in total. -/
theorem heterogeneous_pureNash_action_sum_ge_gap
    {slotWeight gap delta marginalCost first second : ℝ}
    (hGap : 0 < gap) (hDelta : 0 ≤ delta)
    (hCostWeight : marginalCost < slotWeight)
    (hNash : HeterogeneousStrictPriorityPureNash
      slotWeight gap delta marginalCost first second) :
    gap ≤ first + second := by
  have hNoTie := heterogeneous_strictPriority_no_effective_tie
    hGap hDelta hCostWeight hNash
  by_cases hHighLeads : second < first + delta
  · have hLead : 0 < first + delta - second := sub_pos.mpr hHighLeads
    have hSaturates := shifted_leader_bestResponse_saturates
      (add_pos_of_pos_of_nonneg hGap hDelta) hCostWeight hLead hNash.1
    linarith [hNash.2.1]
  · have hLowLeads : first + delta < second :=
      lt_of_le_of_ne (le_of_not_gt hHighLeads) hNoTie
    have hLead : 0 < second + -delta - first := by linarith
    have hSaturates := shifted_leader_bestResponse_saturates
      hGap hCostWeight hLead hNash.2
    linarith [hNash.1.1]

/-- Proposition `prop:netsurplus` (i), equilibrium-selection-free pure
dissipation bound. -/
theorem heterogeneous_pureNash_dissipation_ge
    {slotWeight gap delta marginalCost first second : ℝ}
    (hGap : 0 < gap) (hDelta : 0 ≤ delta)
    (hCost : 0 < marginalCost) (hCostWeight : marginalCost < slotWeight)
    (hNash : HeterogeneousStrictPriorityPureNash
      slotWeight gap delta marginalCost first second) :
    marginalCost * gap ≤
      strictPriorityDissipation marginalCost first second := by
  unfold strictPriorityDissipation
  exact mul_le_mul_of_nonneg_left
    (heterogeneous_pureNash_action_sum_ge_gap
      hGap hDelta hCostWeight hNash) hCost.le

/-- Realized allocation value under the strict-inequality tie convention. -/
def heterogeneousStrictPriorityAllocationValue
    (slotWeight lowValue delta first second : ℝ) : ℝ :=
  if second < first + delta then slotWeight * (lowValue + delta)
  else if first + delta < second then slotWeight * lowValue else 0

theorem heterogeneousStrictPriorityAllocationValue_le
    {slotWeight lowValue delta first second : ℝ}
    (hWeight : 0 ≤ slotWeight) (hValue : 0 ≤ lowValue)
    (hDelta : 0 ≤ delta) :
    heterogeneousStrictPriorityAllocationValue
        slotWeight lowValue delta first second ≤
      slotWeight * (lowValue + delta) := by
  unfold heterogeneousStrictPriorityAllocationValue
  split_ifs
  · exact le_rfl
  · exact mul_le_mul_of_nonneg_left (by linarith) hWeight
  · exact mul_nonneg hWeight (add_nonneg hValue hDelta)

/-- Net surplus is allocation value minus burned latency resources. -/
def heterogeneousStrictPriorityNetSurplus
    (slotWeight lowValue delta marginalCost first second : ℝ) : ℝ :=
  heterogeneousStrictPriorityAllocationValue
      slotWeight lowValue delta first second -
    strictPriorityDissipation marginalCost first second

/-- Every pure strict-priority equilibrium satisfies the paper's net-surplus
upper bound. -/
theorem heterogeneous_pureNash_netSurplus_le
    {slotWeight lowValue gap delta marginalCost first second : ℝ}
    (hWeight : 0 ≤ slotWeight) (hValue : 0 ≤ lowValue)
    (hGap : 0 < gap) (hDelta : 0 ≤ delta)
    (hCost : 0 < marginalCost) (hCostWeight : marginalCost < slotWeight)
    (hNash : HeterogeneousStrictPriorityPureNash
      slotWeight gap delta marginalCost first second) :
    heterogeneousStrictPriorityNetSurplus
        slotWeight lowValue delta marginalCost first second ≤
      slotWeight * (lowValue + delta) - marginalCost * gap := by
  have hAllocation := heterogeneousStrictPriorityAllocationValue_le
    hWeight hValue hDelta (first := first) (second := second)
  have hDissipation := heterogeneous_pureNash_dissipation_ge
    hGap hDelta hCost hCostWeight hNash
  unfold heterogeneousStrictPriorityNetSurplus
  linarith

/-- Subtracting the sharp tangent `x/4` from the sigmoid. -/
def sigmoidMinusQuarter (x : ℝ) : ℝ := Real.sigmoid x - x / 4

theorem sigmoidMinusQuarter_hasDerivAt (x : ℝ) :
    HasDerivAt sigmoidMinusQuarter
      (Real.sigmoid x * (1 - Real.sigmoid x) - 1 / 4) x := by
  unfold sigmoidMinusQuarter
  simpa using (Real.hasDerivAt_sigmoid x).sub
    ((hasDerivAt_id x).div_const 4)

theorem sigmoidMinusQuarter_deriv_neg {x : ℝ} (hx : x ≠ 0) :
    deriv sigmoidMinusQuarter x < 0 := by
  have hSigmoidNe : Real.sigmoid x ≠ 1 / 2 := by
    intro hHalf
    have hEq : Real.sigmoid x = Real.sigmoid 0 := by
      simpa [Real.sigmoid_zero] using hHalf
    exact hx (Real.sigmoid_inj.mp hEq)
  rw [(sigmoidMinusQuarter_hasDerivAt x).deriv]
  have hSquare : 0 < (Real.sigmoid x - 1 / 2) ^ 2 :=
    sq_pos_of_ne_zero (sub_ne_zero.mpr hSigmoidNe)
  nlinarith

/-- The sigmoid's global `1/4` slope bound is strict on every non-degenerate
interval. -/
theorem sigmoidMinusQuarter_strictAnti : StrictAnti sigmoidMinusQuarter := by
  have hContinuous : Continuous sigmoidMinusQuarter :=
    continuous_sigmoid.sub (continuous_id.div_const 4)
  have hLeft : StrictAntiOn sigmoidMinusQuarter (Set.Iic 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Iic 0) hContinuous.continuousOn
    intro x hx
    have hxNeg : x < 0 := by
      simpa only [interior_Iic, Set.mem_Iio] using hx
    exact sigmoidMinusQuarter_deriv_neg (ne_of_lt hxNeg)
  have hRight : StrictAntiOn sigmoidMinusQuarter (Set.Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 0) hContinuous.continuousOn
    intro x hx
    have hxPos : 0 < x := by
      simpa only [interior_Ici, Set.mem_Ioi] using hx
    exact sigmoidMinusQuarter_deriv_neg (ne_of_gt hxPos)
  intro x y hxy
  by_cases hy : y ≤ 0
  · exact hLeft (le_trans (le_of_lt hxy) hy) hy hxy
  · have hyPos : 0 < y := lt_of_not_ge hy
    by_cases hx : 0 ≤ x
    · exact hRight hx hyPos.le hxy
    · have hxNeg : x < 0 := lt_of_not_ge hx
      exact (hRight (by simp) hyPos.le hyPos).trans
        (hLeft hxNeg.le (by simp) hxNeg)

theorem sigmoid_sub_sigmoid_lt_quarter_slope
    {x y : ℝ} (hxy : x < y) :
    Real.sigmoid y - Real.sigmoid x < (y - x) / 4 := by
  have h := sigmoidMinusQuarter_strictAnti hxy
  unfold sigmoidMinusQuarter at h
  linarith

/-- Exact one-opponent, one-slot PL interim allocation. -/
def twoBidderPLAllocation
    (slotWeight temperature opponentScore score : ℝ) : ℝ :=
  slotWeight * Real.sigmoid ((score - opponentScore) / temperature)

theorem twoBidderPLAllocation_continuous
    (slotWeight temperature opponentScore : ℝ) :
    Continuous (twoBidderPLAllocation slotWeight temperature opponentScore) := by
  unfold twoBidderPLAllocation
  fun_prop

/-- The exact logistic allocation spread is strictly below the sharp
`w₁/(4τ)` secant certificate whenever `reserve < value`. -/
theorem twoBidderPLAllocation_spread_lt
    {slotWeight temperature opponentScore reserve value action : ℝ}
    (hWeight : 0 < slotWeight) (hTemperature : 0 < temperature)
    (hValue : reserve < value) :
    twoBidderPLAllocation slotWeight temperature opponentScore (value + action) -
        twoBidderPLAllocation slotWeight temperature opponentScore
          (reserve + action) <
      (value - reserve) * slotWeight / (4 * temperature) := by
  let x := (reserve + action - opponentScore) / temperature
  let y := (value + action - opponentScore) / temperature
  have hxy : x < y := by
    dsimp [x, y]
    exact (div_lt_div_iff_of_pos_right hTemperature).2 (by linarith)
  have hSigmoid := sigmoid_sub_sigmoid_lt_quarter_slope hxy
  have hScaled := mul_lt_mul_of_pos_left hSigmoid hWeight
  unfold twoBidderPLAllocation
  change slotWeight * Real.sigmoid y - slotWeight * Real.sigmoid x < _
  calc
    slotWeight * Real.sigmoid y - slotWeight * Real.sigmoid x =
        slotWeight * (Real.sigmoid y - Real.sigmoid x) := by ring
    _ < slotWeight * ((y - x) / 4) := hScaled
    _ = (value - reserve) * slotWeight / (4 * temperature) := by
      dsimp [x, y]
      field_simp [ne_of_gt hTemperature]
      ring

/-- Linear latency cost used in Proposition `prop:netsurplus`. -/
def linearAdvantageCost (marginalCost action : ℝ) : ℝ :=
  marginalCost * action

theorem linearAdvantageCost_hasDerivAt
    (marginalCost action : ℝ) :
    HasDerivAt (linearAdvantageCost marginalCost) marginalCost action := by
  simpa [linearAdvantageCost] using (hasDerivAt_id action).const_mul marginalCost

/-- The certificate temperature `τ† = w₁ dmax /(4κ)`. -/
def certificateTemperature
    (slotWeight maxPremium marginalCost : ℝ) : ℝ :=
  slotWeight * maxPremium / (4 * marginalCost)

theorem spread_certificate_le_marginalCost
    {slotWeight premium maxPremium marginalCost temperature : ℝ}
    (hWeight : 0 < slotWeight)
    (hPremiumMax : premium ≤ maxPremium) (hCost : 0 < marginalCost)
    (hTemperature : 0 < temperature)
    (hCertificate :
      certificateTemperature slotWeight maxPremium marginalCost ≤ temperature) :
    premium * slotWeight / (4 * temperature) ≤ marginalCost := by
  have hMaxScaled :
      slotWeight * maxPremium ≤ temperature * (4 * marginalCost) := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hCost)).mp
    simpa [certificateTemperature, mul_comm] using hCertificate
  have hPremiumScaled : slotWeight * premium ≤ slotWeight * maxPremium :=
    mul_le_mul_of_nonneg_left hPremiumMax hWeight.le
  apply (div_le_iff₀ (mul_pos (by norm_num) hTemperature)).2
  calc
    premium * slotWeight = slotWeight * premium := by ring
    _ ≤ slotWeight * maxPremium := hPremiumScaled
    _ ≤ temperature * (4 * marginalCost) := hMaxScaled
    _ = marginalCost * (4 * temperature) := by ring

/-- Even at `τ=τ†`, linear-cost utility is strictly decreasing.  The strict
sigmoid secant bound above supplies the strictness that a weak global
Lipschitz certificate alone cannot provide. -/
theorem twoBidderPLUtility_strictAnti_at_certificate
    {slotWeight reserve value opponentScore maxPremium marginalCost
      temperature : ℝ}
    (hWeight : 0 < slotWeight) (hValue : reserve < value)
    (hPremiumMax : value - reserve ≤ maxPremium)
    (hCost : 0 < marginalCost) (hTemperature : 0 < temperature)
    (hCertificate :
      certificateTemperature slotWeight maxPremium marginalCost ≤ temperature) :
    StrictAnti (advantageUtility
      (twoBidderPLAllocation slotWeight temperature opponentScore)
      (linearAdvantageCost marginalCost) reserve value) := by
  let allocation := twoBidderPLAllocation slotWeight temperature opponentScore
  let utility := advantageUtility allocation
    (linearAdvantageCost marginalCost) reserve value
  apply strictAnti_of_hasDerivAt_neg
  · intro action
    exact advantageUtility_hasDerivAt allocation
      (linearAdvantageCost marginalCost)
      (twoBidderPLAllocation_continuous slotWeight temperature opponentScore)
      (linearAdvantageCost_hasDerivAt marginalCost action)
  · intro action
    have hSpread := twoBidderPLAllocation_spread_lt
      (opponentScore := opponentScore) (action := action)
      hWeight hTemperature hValue
    have hThreshold := spread_certificate_le_marginalCost
      hWeight hPremiumMax hCost hTemperature
      hCertificate
    dsimp [allocation]
    linarith

/-- Explicit strict-dominance interface: for every opponent score, every
positive investment loses strictly to zero throughout the closed certificate
region. -/
theorem twoBidderPL_positiveAction_strictlyDominatedByZero
    {slotWeight reserve value opponentScore maxPremium marginalCost
      temperature action : ℝ}
    (hWeight : 0 < slotWeight) (hValue : reserve < value)
    (hPremiumMax : value - reserve ≤ maxPremium)
    (hCost : 0 < marginalCost) (hTemperature : 0 < temperature)
    (hCertificate :
      certificateTemperature slotWeight maxPremium marginalCost ≤ temperature)
    (hAction : 0 < action) :
    advantageUtility
          (twoBidderPLAllocation slotWeight temperature opponentScore)
          (linearAdvantageCost marginalCost) reserve value action <
      advantageUtility
          (twoBidderPLAllocation slotWeight temperature opponentScore)
          (linearAdvantageCost marginalCost) reserve value 0 := by
  exact twoBidderPLUtility_strictAnti_at_certificate
    hWeight hValue hPremiumMax hCost hTemperature hCertificate hAction

/-- Zero is the unique best response, uniformly in the opponent's effective
score, throughout the closed certificate region. -/
theorem twoBidderPL_bestResponse_iff_zero_at_certificate
    {slotWeight reserve value opponentScore maxPremium marginalCost
      temperature action : ℝ}
    (hWeight : 0 < slotWeight) (hValue : reserve < value)
    (hPremiumMax : value - reserve ≤ maxPremium)
    (hCost : 0 < marginalCost) (hTemperature : 0 < temperature)
    (hCertificate :
      certificateTemperature slotWeight maxPremium marginalCost ≤ temperature) :
    NonnegativeBestResponse
      (advantageUtility
        (twoBidderPLAllocation slotWeight temperature opponentScore)
        (linearAdvantageCost marginalCost) reserve value) action ↔ action = 0 := by
  have hStrict := twoBidderPLUtility_strictAnti_at_certificate
    (opponentScore := opponentScore)
    hWeight hValue hPremiumMax hCost hTemperature hCertificate
  constructor
  · intro hBest
    apply le_antisymm _ hBest.1
    by_contra hNot
    have hPositive : 0 < action := lt_of_not_ge hNot
    have hLoss := hStrict hPositive
    have hOptimal := hBest.2 (by simp : (0 : ℝ) ∈ Set.Ici 0)
    exact (not_lt_of_ge hOptimal) hLoss
  · rintro rfl
    refine ⟨le_refl 0, ?_⟩
    intro deviation hDeviation
    have hDevNonneg : 0 ≤ deviation := hDeviation
    rcases eq_or_lt_of_le hDevNonneg with hZero | hPositive
    · simp [hZero]
    · exact (hStrict hPositive).le

/-- Exact two-player PL pure Nash predicate for the investment stage. -/
def TwoBidderPLPureNash
    (slotWeight reserve lowValue delta marginalCost temperature first second : ℝ) :
    Prop :=
  NonnegativeBestResponse
      (advantageUtility
        (twoBidderPLAllocation slotWeight temperature (lowValue + second))
        (linearAdvantageCost marginalCost) reserve (lowValue + delta)) first ∧
    NonnegativeBestResponse
      (advantageUtility
        (twoBidderPLAllocation slotWeight temperature
          (lowValue + delta + first))
        (linearAdvantageCost marginalCost) reserve lowValue) second

/-- In the certificate region, `(0,0)` is the unique pure equilibrium.  Since
each zero action is uniformly strictly dominant, the same conclusion applies
before equilibrium to every iterated-rationalizability procedure. -/
theorem twoBidderPL_pureNash_iff_zero_at_certificate
    {slotWeight reserve lowValue gap delta marginalCost temperature first second : ℝ}
    (hWeight : 0 < slotWeight) (hGap : 0 < gap) (hDelta : 0 ≤ delta)
    (hValue : lowValue = reserve + gap)
    (hCost : 0 < marginalCost) (hTemperature : 0 < temperature)
    (hCertificate : certificateTemperature slotWeight (gap + delta)
      marginalCost ≤ temperature) :
    TwoBidderPLPureNash slotWeight reserve lowValue delta marginalCost
        temperature first second ↔
      first = 0 ∧ second = 0 := by
  subst lowValue
  constructor
  · intro hNash
    have hFirst := (twoBidderPL_bestResponse_iff_zero_at_certificate
      hWeight (by linarith : reserve < reserve + gap + delta)
      (by linarith : reserve + gap + delta - reserve ≤ gap + delta)
      hCost hTemperature hCertificate).mp hNash.1
    subst first
    have hSecond := (twoBidderPL_bestResponse_iff_zero_at_certificate
      hWeight (by linarith : reserve < reserve + gap)
      (by linarith : reserve + gap - reserve ≤ gap + delta)
      hCost hTemperature hCertificate).mp hNash.2
    exact ⟨rfl, hSecond⟩
  · rintro ⟨rfl, rfl⟩
    constructor
    · apply (twoBidderPL_bestResponse_iff_zero_at_certificate
        hWeight (by linarith : reserve < reserve + gap + delta)
        (by linarith : reserve + gap + delta - reserve ≤ gap + delta)
        hCost hTemperature hCertificate).mpr rfl
    · apply (twoBidderPL_bestResponse_iff_zero_at_certificate
        hWeight (by linarith : reserve < reserve + gap)
        (by linarith : reserve + gap - reserve ≤ gap + delta)
        hCost hTemperature hCertificate).mpr rfl

/-- Net surplus at zero investment under the two-bidder PL allocation. -/
def zeroInvestmentPLNetSurplus
    (slotWeight lowValue delta temperature : ℝ) : ℝ :=
  slotWeight * ((lowValue + delta) * Real.sigmoid (delta / temperature) +
    lowValue * Real.sigmoid (-delta / temperature))

/-- Proposition `prop:netsurplus` (ii), exact logistic welfare formula. -/
theorem zeroInvestmentPLNetSurplus_eq
    (slotWeight lowValue delta temperature : ℝ) :
    zeroInvestmentPLNetSurplus slotWeight lowValue delta temperature =
      slotWeight * (lowValue + delta) -
        slotWeight * delta * Real.sigmoid (-delta / temperature) := by
  unfold zeroInvestmentPLNetSurplus
  have hArg : -delta / temperature = -(delta / temperature) := by ring
  rw [hArg, Real.sigmoid_neg]
  ring

/-- Net surplus under a uniform lottery and zero investment. -/
def uniformLotteryNetSurplus
    (slotWeight lowValue delta : ℝ) : ℝ :=
  slotWeight * (lowValue + delta) - slotWeight * delta / 2

/-- The finite-temperature zero-investment PL formula converges to the
uniform-lottery endpoint as `τ → ∞`. -/
theorem zeroInvestmentPLNetSurplus_tendsto_uniformLottery
    (slotWeight lowValue delta : ℝ) :
    Filter.Tendsto
      (fun temperature : ℝ =>
        zeroInvestmentPLNetSurplus slotWeight lowValue delta temperature)
      Filter.atTop
      (nhds (uniformLotteryNetSurplus slotWeight lowValue delta)) := by
  have hArg : Filter.Tendsto (fun temperature : ℝ => -delta / temperature)
      Filter.atTop (nhds 0) := by
    have hId : Filter.Tendsto (fun temperature : ℝ => temperature)
        Filter.atTop Filter.atTop := by
      simpa only [id_eq] using
        (Filter.tendsto_id : Filter.Tendsto (id : ℝ → ℝ)
          Filter.atTop Filter.atTop)
    exact hId.const_div_atTop (-delta)
  have hSigmoid :
      Filter.Tendsto (fun temperature : ℝ =>
        Real.sigmoid (-delta / temperature)) Filter.atTop (nhds (1 / 2)) := by
    simpa only [Function.comp_apply, Real.sigmoid_zero, one_div] using
      continuous_sigmoid.continuousAt.tendsto.comp hArg
  have hLoss :
      Filter.Tendsto (fun temperature : ℝ =>
        slotWeight * delta * Real.sigmoid (-delta / temperature))
        Filter.atTop (nhds (slotWeight * delta * (1 / 2))) :=
    tendsto_const_nhds.mul hSigmoid
  have hSurplus :
      Filter.Tendsto (fun temperature : ℝ =>
        slotWeight * (lowValue + delta) -
          slotWeight * delta * Real.sigmoid (-delta / temperature))
        Filter.atTop
        (nhds (slotWeight * (lowValue + delta) - slotWeight * delta * (1 / 2))) :=
    tendsto_const_nhds.sub hLoss
  simpa only [zeroInvestmentPLNetSurplus_eq, uniformLotteryNetSurplus,
    div_eq_mul_inv, one_mul, mul_assoc] using hSurplus

theorem sigmoid_neg_div_le_half
    {delta temperature : ℝ} (hDelta : 0 ≤ delta) (hTemperature : 0 < temperature) :
    Real.sigmoid (-delta / temperature) ≤ 1 / 2 := by
  have hArg : -delta / temperature ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hDelta) hTemperature.le
  calc
    Real.sigmoid (-delta / temperature) ≤ Real.sigmoid 0 :=
      Real.sigmoid_le hArg
    _ = 1 / 2 := by norm_num [Real.sigmoid_zero]

theorem sigmoid_neg_div_lt_half
    {delta temperature : ℝ} (hDelta : 0 < delta) (hTemperature : 0 < temperature) :
    Real.sigmoid (-delta / temperature) < 1 / 2 := by
  have hNegative : -delta < 0 := by linarith
  have hArg : -delta / temperature < 0 :=
    div_neg_of_neg_of_pos hNegative hTemperature
  calc
    Real.sigmoid (-delta / temperature) < Real.sigmoid 0 :=
      Real.sigmoid_lt hArg
    _ = 1 / 2 := by norm_num [Real.sigmoid_zero]

/-- At zero investment, PL net surplus exceeds the uniform-lottery limit at
every positive finite temperature when values differ. -/
theorem uniformLotteryNetSurplus_lt_zeroInvestmentPL
    {slotWeight lowValue delta temperature : ℝ}
    (hWeight : 0 < slotWeight) (hDelta : 0 < delta)
    (hTemperature : 0 < temperature) :
    uniformLotteryNetSurplus slotWeight lowValue delta <
      zeroInvestmentPLNetSurplus slotWeight lowValue delta temperature := by
  rw [zeroInvestmentPLNetSurplus_eq]
  unfold uniformLotteryNetSurplus
  have hSigmoid := sigmoid_neg_div_lt_half hDelta hTemperature
  have hProduct : 0 < slotWeight * delta := mul_pos hWeight hDelta
  nlinarith

/-- The sharp comparison before replacing the logistic loss by its `1/2`
upper bound. -/
theorem zeroInvestmentPL_minus_strictPriority_ge_exactLoss
    {slotWeight lowValue gap delta marginalCost temperature first second : ℝ}
    (hWeight : 0 < slotWeight) (hValue : 0 ≤ lowValue)
    (hGap : 0 < gap) (hDelta : 0 ≤ delta)
    (hCost : 0 < marginalCost) (hCostWeight : marginalCost < slotWeight)
    (hNash : HeterogeneousStrictPriorityPureNash
      slotWeight gap delta marginalCost first second) :
    marginalCost * gap -
        slotWeight * delta * Real.sigmoid (-delta / temperature) ≤
      zeroInvestmentPLNetSurplus slotWeight lowValue delta temperature -
        heterogeneousStrictPriorityNetSurplus
          slotWeight lowValue delta marginalCost first second := by
  have hSP := heterogeneous_pureNash_netSurplus_le hWeight.le hValue
    hGap hDelta hCost hCostWeight hNash
  rw [zeroInvestmentPLNetSurplus_eq]
  linarith

/-- Proposition `prop:netsurplus` (iii), the full displayed chain for any
pure strict-priority equilibrium, evaluated at the zero-investment PL
outcome. -/
theorem zeroInvestmentPL_dominance_chain
    {slotWeight lowValue gap delta marginalCost temperature first second : ℝ}
    (hWeight : 0 < slotWeight) (hValue : 0 ≤ lowValue)
    (hGap : 0 < gap) (hDelta : 0 ≤ delta) (hContested : delta ≤ gap)
    (hHalfCost : slotWeight / 2 < marginalCost)
    (hCostWeight : marginalCost < slotWeight)
    (hTemperature : 0 < temperature)
    (hNash : HeterogeneousStrictPriorityPureNash
      slotWeight gap delta marginalCost first second) :
    marginalCost * gap - slotWeight * delta / 2 ≤
        zeroInvestmentPLNetSurplus slotWeight lowValue delta temperature -
          heterogeneousStrictPriorityNetSurplus
            slotWeight lowValue delta marginalCost first second ∧
      (marginalCost - slotWeight / 2) * gap ≤
        zeroInvestmentPLNetSurplus slotWeight lowValue delta temperature -
          heterogeneousStrictPriorityNetSurplus
            slotWeight lowValue delta marginalCost first second ∧
      0 < zeroInvestmentPLNetSurplus slotWeight lowValue delta temperature -
          heterogeneousStrictPriorityNetSurplus
            slotWeight lowValue delta marginalCost first second := by
  have hCost : 0 < marginalCost := by nlinarith
  have hSP := heterogeneous_pureNash_netSurplus_le hWeight.le hValue
    hGap hDelta hCost hCostWeight hNash
  have hSigmoid := sigmoid_neg_div_le_half hDelta hTemperature
  rw [zeroInvestmentPLNetSurplus_eq]
  have hWeightedSigmoid :
      slotWeight * delta * Real.sigmoid (-delta / temperature) ≤
        slotWeight * delta / 2 := by
    have hNonneg : 0 ≤ slotWeight * delta :=
      mul_nonneg hWeight.le hDelta
    simpa [div_eq_mul_inv, mul_assoc] using
      (mul_le_mul_of_nonneg_left hSigmoid hNonneg)
  have hFirstBound :
      marginalCost * gap - slotWeight * delta / 2 ≤
        slotWeight * (lowValue + delta) -
          slotWeight * delta * Real.sigmoid (-delta / temperature) -
            heterogeneousStrictPriorityNetSurplus
              slotWeight lowValue delta marginalCost first second := by
    linarith
  have hDeltaScaled : slotWeight * delta ≤ slotWeight * gap :=
    mul_le_mul_of_nonneg_left hContested hWeight.le
  have hSecondBase :
      (marginalCost - slotWeight / 2) * gap ≤
        marginalCost * gap - slotWeight * delta / 2 := by
    nlinarith
  constructor
  · exact hFirstBound
  · constructor
    · exact hSecondBase.trans hFirstBound
    · have hStrict : 0 < (marginalCost - slotWeight / 2) * gap :=
        mul_pos (sub_pos.mpr hHalfCost) hGap
      exact hStrict.trans_le (hSecondBase.trans hFirstBound)

/-- The `τ=∞` endpoint is a uniform lottery.  Under the contested-slot and
high-cost hypotheses it too strictly dominates every pure strict-priority
equilibrium. -/
theorem uniformLottery_dominates_strictPriority
    {slotWeight lowValue gap delta marginalCost first second : ℝ}
    (hWeight : 0 < slotWeight) (hValue : 0 ≤ lowValue)
    (hGap : 0 < gap) (hDelta : 0 ≤ delta) (hContested : delta ≤ gap)
    (hHalfCost : slotWeight / 2 < marginalCost)
    (hCostWeight : marginalCost < slotWeight)
    (hNash : HeterogeneousStrictPriorityPureNash
      slotWeight gap delta marginalCost first second) :
    0 < uniformLotteryNetSurplus slotWeight lowValue delta -
      heterogeneousStrictPriorityNetSurplus
        slotWeight lowValue delta marginalCost first second := by
  have hCost : 0 < marginalCost := by nlinarith
  have hSP := heterogeneous_pureNash_netSurplus_le hWeight.le hValue
    hGap hDelta hCost hCostWeight hNash
  have hDeltaScaled : slotWeight * delta ≤ slotWeight * gap :=
    mul_le_mul_of_nonneg_left hContested hWeight.le
  have hLower :
      (marginalCost - slotWeight / 2) * gap ≤
        uniformLotteryNetSurplus slotWeight lowValue delta -
          heterogeneousStrictPriorityNetSurplus
            slotWeight lowValue delta marginalCost first second := by
    unfold uniformLotteryNetSurplus
    nlinarith
  have hPositive : 0 < (marginalCost - slotWeight / 2) * gap :=
    mul_pos (sub_pos.mpr hHalfCost) hGap
  exact hPositive.trans_le hLower

/-- Inside the certified region, the preceding comparison applies to the
unique PL equilibrium rather than merely to a stipulated zero-investment
outcome. -/
theorem certifiedPL_unique_equilibrium_and_dominance
    {slotWeight reserve lowValue gap delta marginalCost temperature first second : ℝ}
    (hWeight : 0 < slotWeight) (hReserve : 0 ≤ reserve)
    (hGap : 0 < gap) (hDelta : 0 ≤ delta) (hContested : delta ≤ gap)
    (hValue : lowValue = reserve + gap)
    (hHalfCost : slotWeight / 2 < marginalCost)
    (hCostWeight : marginalCost < slotWeight)
    (hTemperature : 0 < temperature)
    (hCertificate : certificateTemperature slotWeight (gap + delta)
      marginalCost ≤ temperature)
    (hSPNash : HeterogeneousStrictPriorityPureNash
      slotWeight gap delta marginalCost first second) :
    (∀ firstAction secondAction,
      TwoBidderPLPureNash slotWeight reserve lowValue delta marginalCost
          temperature firstAction secondAction ↔
        firstAction = 0 ∧ secondAction = 0) ∧
      0 < zeroInvestmentPLNetSurplus slotWeight lowValue delta temperature -
        heterogeneousStrictPriorityNetSurplus
          slotWeight lowValue delta marginalCost first second := by
  constructor
  · intro firstAction secondAction
    exact twoBidderPL_pureNash_iff_zero_at_certificate hWeight hGap hDelta
      hValue (by nlinarith) hTemperature hCertificate
  · apply (zeroInvestmentPL_dominance_chain hWeight
      (by subst lowValue; linarith) hGap hDelta hContested hHalfCost
      hCostWeight hTemperature hSPNash).2.2

/-- At the finite certificate boundary, zero-investment PL strictly beats
both an arbitrary pure strict-priority equilibrium and the uniform-lottery
endpoint. -/
theorem certificate_boundary_beats_strictPriority_and_uniform
    {slotWeight lowValue gap delta marginalCost first second : ℝ}
    (hWeight : 0 < slotWeight) (hValue : 0 ≤ lowValue)
    (hGap : 0 < gap) (hDelta : 0 < delta) (hContested : delta ≤ gap)
    (hHalfCost : slotWeight / 2 < marginalCost)
    (hCostWeight : marginalCost < slotWeight)
    (hNash : HeterogeneousStrictPriorityPureNash
      slotWeight gap delta marginalCost first second) :
    let threshold := certificateTemperature slotWeight (gap + delta) marginalCost
    heterogeneousStrictPriorityNetSurplus
          slotWeight lowValue delta marginalCost first second <
        zeroInvestmentPLNetSurplus slotWeight lowValue delta threshold ∧
      uniformLotteryNetSurplus slotWeight lowValue delta <
        zeroInvestmentPLNetSurplus slotWeight lowValue delta threshold := by
  dsimp only
  have hCost : 0 < marginalCost := by nlinarith
  have hThreshold :
      0 < certificateTemperature slotWeight (gap + delta) marginalCost := by
    unfold certificateTemperature
    positivity
  constructor
  · exact sub_pos.mp
      (zeroInvestmentPL_dominance_chain hWeight hValue hGap hDelta.le hContested
        hHalfCost hCostWeight hThreshold hNash).2.2
  · exact uniformLotteryNetSurplus_lt_zeroInvestmentPL
      hWeight hDelta hThreshold

/-- For `delta>0`, zero-investment PL net surplus is strictly decreasing in
temperature on `(0,∞)`. -/
theorem zeroInvestmentPLNetSurplus_strictAntiOn
    {slotWeight lowValue delta : ℝ}
    (hWeight : 0 < slotWeight) (hDelta : 0 < delta) :
    StrictAntiOn
      (zeroInvestmentPLNetSurplus slotWeight lowValue delta) (Set.Ioi 0) := by
  intro firstTemperature hFirst secondTemperature hSecond hOrder
  have hArg : -delta / firstTemperature < -delta / secondTemperature := by
    apply (div_lt_div_iff₀ hFirst hSecond).2
    exact mul_lt_mul_of_neg_left hOrder (by linarith)
  have hSigmoid := Real.sigmoid_lt hArg
  rw [zeroInvestmentPLNetSurplus_eq, zeroInvestmentPLNetSurplus_eq]
  have hProduct : 0 < slotWeight * delta := mul_pos hWeight hDelta
  nlinarith

/-- The certificate boundary is the unique maximizer within the entire
closed certified region. -/
theorem certificateTemperature_unique_max_on_certifiedRegion
    {slotWeight lowValue gap delta marginalCost : ℝ}
    (hWeight : 0 < slotWeight) (hGap : 0 < gap) (hDelta : 0 < delta)
    (hCost : 0 < marginalCost) :
    let threshold := certificateTemperature slotWeight (gap + delta) marginalCost
    IsMaxOn (zeroInvestmentPLNetSurplus slotWeight lowValue delta)
      (Set.Ici threshold) threshold ∧
    ∀ temperature ∈ Set.Ici threshold,
      zeroInvestmentPLNetSurplus slotWeight lowValue delta temperature =
        zeroInvestmentPLNetSurplus slotWeight lowValue delta threshold →
      temperature = threshold := by
  dsimp only
  have hThreshold :
      0 < certificateTemperature slotWeight (gap + delta) marginalCost := by
    unfold certificateTemperature
    positivity
  have hStrict := zeroInvestmentPLNetSurplus_strictAntiOn
    (lowValue := lowValue) hWeight hDelta
  constructor
  · intro temperature hTemperature
    rcases eq_or_lt_of_le
      (show certificateTemperature slotWeight (gap + delta) marginalCost ≤
        temperature from hTemperature) with hEq | hLt
    · simp [hEq]
    · exact (hStrict hThreshold (hThreshold.trans hLt) hLt).le
  · intro temperature hTemperature hEqual
    rcases eq_or_lt_of_le
      (show certificateTemperature slotWeight (gap + delta) marginalCost ≤
        temperature from hTemperature) with hEq | hLt
    · exact hEq.symm
    · exact False.elim
        ((hStrict hThreshold (hThreshold.trans hLt) hLt).ne hEqual)

/-- Any global maximizer of any positive-temperature objective that agrees
with the certified closed form above `τ†` must lie weakly below `τ†`.  This is
the precise conclusion available without constructing equilibria below the
certificate. -/
theorem global_maximizer_le_certificateTemperature
    {slotWeight lowValue gap delta marginalCost : ℝ}
    (hWeight : 0 < slotWeight) (hGap : 0 < gap) (hDelta : 0 < delta)
    (hCost : 0 < marginalCost)
    (objective : ℝ → ℝ) {maximizer : ℝ} (hMaximizer : 0 < maximizer)
    (hAgrees : ∀ temperature,
      certificateTemperature slotWeight (gap + delta) marginalCost ≤ temperature →
      objective temperature =
        zeroInvestmentPLNetSurplus slotWeight lowValue delta temperature)
    (hMax : IsMaxOn objective (Set.Ioi 0) maximizer) :
    maximizer ≤ certificateTemperature slotWeight (gap + delta) marginalCost := by
  let threshold := certificateTemperature slotWeight (gap + delta) marginalCost
  have hThreshold : 0 < threshold := by
    dsimp [threshold, certificateTemperature]
    positivity
  by_contra hNot
  have hAbove : threshold < maximizer := lt_of_not_ge hNot
  have hStrict := zeroInvestmentPLNetSurplus_strictAntiOn
    (lowValue := lowValue) hWeight hDelta
    hThreshold hMaximizer hAbove
  have hThresholdAgreement := hAgrees threshold (le_refl threshold)
  have hMaxAgreement := hAgrees maximizer hAbove.le
  have hOptimal := hMax hThreshold
  change objective threshold ≤ objective maximizer at hOptimal
  rw [hThresholdAgreement, hMaxAgreement] at hOptimal
  exact (not_lt_of_ge hOptimal) hStrict

end

end SmoothingCliff.Racing
