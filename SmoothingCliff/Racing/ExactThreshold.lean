import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# The analytic core of the exact temperature threshold

This file formalizes the closed-form and pointwise-optimization claims in
Proposition `prop:exact_threshold` of *Smoothing the Cliff*.  For a contested
band `d = v_i - r`, the marginal allocation-value window is

`σ ((d + y) / τ) - σ (y / τ)`.

We prove its actual global maximum, not an inequality assumed as a premise,
derive the exact closed-form threshold equivalence, compare that threshold
with the older derivative certificate, and establish the ratio's comparative
statics and endpoint limits.

The run-up-average branch `M_i` additionally requires an integral optimization
and an attainment/uniqueness argument.  It is intentionally not encoded here
as an economic dominance claim without that infrastructure.
-/

namespace SmoothingCliff.Racing

noncomputable section

/-- `L(q) = log ((1+q)/(1-q))`, twice the inverse hyperbolic tangent. -/
def logOdds (q : ℝ) : ℝ :=
  Real.log ((1 + q) / (1 - q))

/-- The paper's closed-form temperature `τ°`. -/
def tauCircle (contestedBand slotWeight cost : ℝ) : ℝ :=
  contestedBand / (2 * logOdds (cost / slotWeight))

/-- The earlier one-slot derivative certificate `τ†`. -/
def tauDagger (contestedBand slotWeight cost : ℝ) : ℝ :=
  slotWeight * contestedBand / (4 * cost)

/-- The ratio `τ°/τ†`, expressed using normalized cost `q = κ/w₁`. -/
def thresholdRatio (q : ℝ) : ℝ :=
  2 * q / logOdds q

/-- A logistic marginal-value window of width `d`. -/
def marginalWindow (d temperature position : ℝ) : ℝ :=
  Real.sigmoid ((d + position) / temperature) -
    Real.sigmoid (position / temperature)

/-- The same window in the paper's feasible coordinates: run-up position
`s ≥ 0` and opponent investment `a_j ≥ 0`, with opponent band `d_j`. -/
def feasibleMarginalWindow
    (d opponentBand temperature runUp opponentInvestment : ℝ) : ℝ :=
  marginalWindow d temperature
    (runUp - opponentBand - opponentInvestment)

/-- The pointwise marginal value after multiplying by the slot weight. -/
def pointwiseMarginalValue
    (slotWeight contestedBand temperature : ℝ) : ℝ :=
  slotWeight *
    (2 * Real.sigmoid (contestedBand / (2 * temperature)) - 1)

theorem logOdds_pos {q : ℝ} (hq : 0 < q) (hqOne : q < 1) :
    0 < logOdds q := by
  unfold logOdds
  apply Real.log_pos
  rw [one_lt_div (by linarith : 0 < 1 - q)]
  linarith

/-- The strict lower series bound used to show `τ° < τ†`. -/
theorem two_mul_lt_logOdds {q : ℝ} (hq : 0 < q) (hqOne : q < 1) :
    2 * q < logOdds q := by
  unfold logOdds
  have hSeries := Real.sum_range_le_log_div (le_of_lt hq) hqOne 2
  norm_num [Finset.sum_range_succ] at hSeries
  have hCubic : 0 < q ^ 3 / 3 :=
    div_pos (pow_pos hq _) (by norm_num)
  linarith

/-- A complementary upper bound on `L(q)`, used for the derivative sign and
the cheap-technology endpoint limit. -/
theorem logOdds_lt_two_mul_div_one_sub_sq
    {q : ℝ} (hq : 0 < q) (hqOne : q < 1) :
    logOdds q < 2 * q / (1 - q ^ 2) := by
  unfold logOdds
  have hSeries := Real.log_div_le_sum_range_add (le_of_lt hq) hqOne 2
  norm_num [Finset.sum_range_succ] at hSeries
  have hDenominator : 0 < 1 - q ^ 2 := by nlinarith
  have hGap : 0 < 2 * q ^ 3 / 3 :=
    div_pos (mul_pos (by norm_num) (pow_pos hq _)) (by norm_num)
  have hIdentity :
      q / (1 - q ^ 2) -
          (q + q ^ 3 / 3 + q ^ 5 / (1 - q ^ 2)) =
        2 * q ^ 3 / 3 := by
    field_simp [ne_of_gt hDenominator]
    ring
  have hHalf :
      1 / 2 * Real.log ((1 + q) / (1 - q)) <
        q / (1 - q ^ 2) := by
    linarith
  calc
    Real.log ((1 + q) / (1 - q)) =
        2 * (1 / 2 * Real.log ((1 + q) / (1 - q))) := by ring
    _ < 2 * (q / (1 - q ^ 2)) :=
      mul_lt_mul_of_pos_left hHalf (by norm_num)
    _ = 2 * q / (1 - q ^ 2) := by ring

/-- A positive-variable algebraic form of the centered-window inequality.
The residual after clearing denominators is `(1-z*x)^2`. -/
theorem inv_window_le_center
    {x z : ℝ} (hx : 0 < x) (hz : 0 < z) (hzOne : z ≤ 1) :
    (1 + z ^ 2 * x)⁻¹ - (1 + x)⁻¹ ≤
      (1 + z)⁻¹ - (1 + z⁻¹)⁻¹ := by
  have hOneX : 0 < 1 + x := by linarith
  have hOneZX : 0 < 1 + z ^ 2 * x := by positivity
  have hOneZ : 0 < 1 + z := by linarith
  have hLeft :
      (1 + z ^ 2 * x)⁻¹ - (1 + x)⁻¹ =
        x * (1 - z ^ 2) / ((1 + z ^ 2 * x) * (1 + x)) := by
    field_simp
    ring
  have hRight :
      (1 + z)⁻¹ - (1 + z⁻¹)⁻¹ = (1 - z) / (1 + z) := by
    field_simp [ne_of_gt hz]
    ring
  rw [hLeft, hRight]
  apply (div_le_div_iff₀ (mul_pos hOneZX hOneX) hOneZ).2
  have hSquare : 0 ≤ (1 - z * x) ^ 2 := sq_nonneg _
  have hFactor : 0 ≤ 1 - z := sub_nonneg.mpr hzOne
  have hIdentity :
      (1 - z) *
          ((1 + z ^ 2 * x) * (1 + x) - x * (1 + z) ^ 2) =
        (1 - z) * (1 - z * x) ^ 2 := by
    ring
  nlinarith [mul_nonneg hFactor hSquare]

/-- Every logistic window is bounded by the centered window. -/
theorem marginalWindow_le_center
    {d temperature position : ℝ}
    (hTemperature : 0 < temperature) (hBand : 0 ≤ d) :
    marginalWindow d temperature position ≤
      2 * Real.sigmoid (d / (2 * temperature)) - 1 := by
  let x := Real.exp (-(position / temperature))
  let z := Real.exp (-(d / (2 * temperature)))
  have hx : 0 < x := Real.exp_pos _
  have hz : 0 < z := Real.exp_pos _
  have hExponent : -(d / (2 * temperature)) ≤ 0 :=
    neg_nonpos.mpr
      (div_nonneg hBand
        (le_of_lt (mul_pos (by norm_num) hTemperature)))
  have hzOne : z ≤ 1 := by
    dsimp [z]
    rw [← Real.exp_zero]
    exact (Real.exp_le_exp).2 hExponent
  have hAlgebra := inv_window_le_center hx hz hzOne
  unfold marginalWindow Real.sigmoid
  have hFirstExponent :
      Real.exp (-((d + position) / temperature)) = z ^ 2 * x := by
    dsimp [z, x]
    rw [show -((d + position) / temperature) =
        -(d / (2 * temperature)) + (-(d / (2 * temperature))) +
          (-(position / temperature)) by
      field_simp
      ring]
    rw [Real.exp_add, Real.exp_add]
    ring
  have hxDef : Real.exp (-(position / temperature)) = x := by simp [x]
  have hzDef : Real.exp (-(d / (2 * temperature))) = z := by simp [z]
  rw [hFirstExponent, hxDef, hzDef]
  have hCenter :
      (1 + z)⁻¹ - (1 + z⁻¹)⁻¹ = 2 * (1 + z)⁻¹ - 1 := by
    field_simp [ne_of_gt hz]
    ring
  rw [← hCenter]
  exact hAlgebra

/-- The center attains the upper bound. -/
theorem marginalWindow_center
    {d temperature : ℝ} (hTemperature : temperature ≠ 0) :
    marginalWindow d temperature (-d / 2) =
      2 * Real.sigmoid (d / (2 * temperature)) - 1 := by
  unfold marginalWindow
  have hFirst : (d + -d / 2) / temperature =
      d / (2 * temperature) := by
    field_simp
    ring
  have hSecond : (-d / 2) / temperature =
      -(d / (2 * temperature)) := by
    field_simp
  rw [hFirst, hSecond, Real.sigmoid_neg]
  ring

/-- The displayed pointwise value is an actual global maximum over positions,
not merely a supremum or an assumed bound. -/
theorem marginalWindow_isGreatest
    {d temperature : ℝ}
    (hTemperature : 0 < temperature) (hBand : 0 ≤ d) :
    IsGreatest (Set.range (marginalWindow d temperature))
      (2 * Real.sigmoid (d / (2 * temperature)) - 1) := by
  constructor
  · exact ⟨-d / 2, marginalWindow_center (ne_of_gt hTemperature)⟩
  · rintro value ⟨position, rfl⟩
    exact marginalWindow_le_center hTemperature hBand

/-- The paper's feasibility restrictions `s ≥ 0`, `a_j ≥ 0` do not lower the
pointwise maximum.  A concrete maximizing pair is obtained by placing the
window center at `s-d_j-a_j = -d/2`. -/
theorem feasibleMarginalWindow_isGreatest
    {d opponentBand temperature : ℝ}
    (hTemperature : 0 < temperature)
    (hBand : 0 ≤ d) :
    IsGreatest
      {value | ∃ runUp, 0 ≤ runUp ∧
        ∃ opponentInvestment, 0 ≤ opponentInvestment ∧
          value = feasibleMarginalWindow d opponentBand temperature
            runUp opponentInvestment}
      (2 * Real.sigmoid (d / (2 * temperature)) - 1) := by
  constructor
  · by_cases hCenterLeft : d / 2 ≤ opponentBand
    · refine ⟨opponentBand - d / 2, sub_nonneg.mpr hCenterLeft,
          0, le_rfl, ?_⟩
      unfold feasibleMarginalWindow
      have hPosition : opponentBand - d / 2 - opponentBand - 0 = -d / 2 := by
        ring
      rw [hPosition]
      exact (marginalWindow_center (ne_of_gt hTemperature)).symm
    · have hCenterRight : opponentBand < d / 2 := lt_of_not_ge hCenterLeft
      refine ⟨0, le_rfl, d / 2 - opponentBand,
          sub_nonneg.mpr (le_of_lt hCenterRight), ?_⟩
      unfold feasibleMarginalWindow
      have hPosition : 0 - opponentBand - (d / 2 - opponentBand) = -d / 2 := by
        ring
      rw [hPosition]
      exact (marginalWindow_center (ne_of_gt hTemperature)).symm
  · rintro value ⟨runUp, -, opponentInvestment, -, rfl⟩
    unfold feasibleMarginalWindow
    exact marginalWindow_le_center hTemperature hBand

/-- Multiplying by a positive slot weight preserves the exact pointwise
maximum quoted in the proposition. -/
theorem weightedFeasibleMarginalWindow_isGreatest
    {slotWeight d opponentBand temperature : ℝ}
    (hWeight : 0 < slotWeight)
    (hTemperature : 0 < temperature)
    (hBand : 0 ≤ d) :
    IsGreatest
      {value | ∃ runUp, 0 ≤ runUp ∧
        ∃ opponentInvestment, 0 ≤ opponentInvestment ∧
          value = slotWeight * feasibleMarginalWindow d opponentBand
            temperature runUp opponentInvestment}
      (pointwiseMarginalValue slotWeight d temperature) := by
  have hMaximum := feasibleMarginalWindow_isGreatest
    (opponentBand := opponentBand) hTemperature hBand
  constructor
  · obtain ⟨runUp, hRunUp, opponentInvestment, hOpponentInvestment,
        hAttain⟩ := hMaximum.1
    refine ⟨runUp, hRunUp, opponentInvestment, hOpponentInvestment, ?_⟩
    rw [pointwiseMarginalValue, ← hAttain]
  · rintro value ⟨runUp, hRunUp, opponentInvestment, hOpponentInvestment, rfl⟩
    unfold pointwiseMarginalValue
    exact mul_le_mul_of_nonneg_left
      (hMaximum.2 ⟨runUp, hRunUp,
        opponentInvestment, hOpponentInvestment, rfl⟩)
      (le_of_lt hWeight)

/-- Logistic algebra converts the centered-window inequality into log odds. -/
theorem two_sigmoid_sub_one_le_iff_logOdds
    {x q : ℝ} (hq : 0 < q) (hqOne : q < 1) :
    2 * Real.sigmoid x - 1 ≤ q ↔ x ≤ logOdds q := by
  have hOneMinus : 0 < 1 - q := by linarith
  have hOnePlus : 0 < 1 + q := by linarith
  have hRatio : 0 < (1 + q) / (1 - q) :=
    div_pos hOnePlus hOneMinus
  unfold logOdds
  rw [Real.le_log_iff_exp_le hRatio]
  unfold Real.sigmoid
  let exponential := Real.exp (-x)
  have hExponential : 0 < exponential := Real.exp_pos _
  have hDenominator : 0 < 1 + exponential := by linarith
  have hProduct : exponential * Real.exp x = 1 := by
    dsimp [exponential]
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  change 2 * (1 + exponential)⁻¹ - 1 ≤ q ↔
    Real.exp x ≤ (1 + q) / (1 - q)
  constructor
  · intro h
    have hDiv : 2 / (1 + exponential) ≤ q + 1 := by
      rw [div_eq_mul_inv]
      linarith
    have hCross : 2 ≤ (q + 1) * (1 + exponential) :=
      (div_le_iff₀ hDenominator).1 hDiv
    have hCore : 1 - q ≤ (1 + q) * exponential := by nlinarith
    apply (le_div_iff₀ hOneMinus).2
    have hScaled := mul_le_mul_of_nonneg_right hCore
      (le_of_lt (Real.exp_pos x))
    nlinarith
  · intro h
    have hCore : (1 - q) * Real.exp x ≤ 1 + q := by
      simpa [mul_comm] using (le_div_iff₀ hOneMinus).1 h
    have hScaled := mul_le_mul_of_nonneg_left hCore
      (le_of_lt hExponential)
    have hBack : 1 - q ≤ (1 + q) * exponential := by nlinarith
    have hCross : 2 ≤ (q + 1) * (1 + exponential) := by nlinarith
    have hDiv : 2 / (1 + exponential) ≤ q + 1 :=
      (div_le_iff₀ hDenominator).2 hCross
    rw [div_eq_mul_inv] at hDiv
    linarith

/-- Exact closed-form certificate: the pointwise marginal-value maximum is at
most cost iff `τ ≥ τ°`. -/
theorem pointwiseMarginalValue_le_cost_iff
    {slotWeight contestedBand cost temperature : ℝ}
    (hWeight : 0 < slotWeight)
    (hCost : 0 < cost) (hCostWeight : cost < slotWeight)
    (hTemperature : 0 < temperature) :
    pointwiseMarginalValue slotWeight contestedBand temperature ≤ cost ↔
      tauCircle contestedBand slotWeight cost ≤ temperature := by
  let q := cost / slotWeight
  have hq : 0 < q := div_pos hCost hWeight
  have hqOne : q < 1 := (div_lt_one hWeight).2 hCostWeight
  have hLogOdds : 0 < logOdds q := logOdds_pos hq hqOne
  have hScale :
      pointwiseMarginalValue slotWeight contestedBand temperature ≤ cost ↔
        2 * Real.sigmoid (contestedBand / (2 * temperature)) - 1 ≤ q := by
    unfold pointwiseMarginalValue
    dsimp [q]
    simpa [mul_comm] using
      (le_div_iff₀ hWeight :
        2 * Real.sigmoid (contestedBand / (2 * temperature)) - 1 ≤
            cost / slotWeight ↔ _).symm
  rw [hScale, two_sigmoid_sub_one_le_iff_logOdds hq hqOne]
  unfold tauCircle
  change contestedBand / (2 * temperature) ≤ logOdds q ↔
    contestedBand / (2 * logOdds q) ≤ temperature
  constructor
  · intro h
    have hCross :=
      (div_le_iff₀ (mul_pos (by norm_num) hTemperature)).1 h
    apply (div_le_iff₀ (mul_pos (by norm_num) hLogOdds)).2
    nlinarith
  · intro h
    have hCross :=
      (div_le_iff₀ (mul_pos (by norm_num) hLogOdds)).1 h
    apply (div_le_iff₀ (mul_pos (by norm_num) hTemperature)).2
    nlinarith

theorem tauCircle_pos
    {contestedBand slotWeight cost : ℝ}
    (hBand : 0 < contestedBand)
    (hWeight : 0 < slotWeight)
    (hCost : 0 < cost) (hCostWeight : cost < slotWeight) :
    0 < tauCircle contestedBand slotWeight cost := by
  have hq : 0 < cost / slotWeight := div_pos hCost hWeight
  have hqOne : cost / slotWeight < 1 :=
    (div_lt_one hWeight).2 hCostWeight
  exact div_pos hBand
    (mul_pos (by norm_num) (logOdds_pos hq hqOne))

/-- The closed-form threshold is strictly below the earlier derivative
certificate throughout `0 < κ < w₁`. -/
theorem tauCircle_lt_tauDagger
    {contestedBand slotWeight cost : ℝ}
    (hBand : 0 < contestedBand)
    (hWeight : 0 < slotWeight)
    (hCost : 0 < cost) (hCostWeight : cost < slotWeight) :
    tauCircle contestedBand slotWeight cost <
      tauDagger contestedBand slotWeight cost := by
  let q := cost / slotWeight
  have hq : 0 < q := div_pos hCost hWeight
  have hqOne : q < 1 := (div_lt_one hWeight).2 hCostWeight
  have hLog : 0 < logOdds q := logOdds_pos hq hqOne
  have hStrict : 2 * q < logOdds q := two_mul_lt_logOdds hq hqOne
  have hInverse : (logOdds q)⁻¹ < (2 * q)⁻¹ :=
    by
      simpa [one_div] using
        one_div_lt_one_div_of_lt (mul_pos (by norm_num) hq) hStrict
  have hScaled := mul_lt_mul_of_pos_left hInverse
    (div_pos hBand (by norm_num : (0 : ℝ) < 2))
  unfold tauCircle tauDagger
  change contestedBand / (2 * logOdds q) <
    slotWeight * contestedBand / (4 * cost)
  calc
    contestedBand / (2 * logOdds q) =
        (contestedBand / 2) * (logOdds q)⁻¹ := by
      field_simp [ne_of_gt hLog]
    _ < (contestedBand / 2) * (2 * q)⁻¹ := hScaled
    _ = slotWeight * contestedBand / (4 * cost) := by
      dsimp [q]
      field_simp [ne_of_gt hWeight, ne_of_gt hCost]
      ring

/-- Exact algebraic ratio from the paper. -/
theorem tauCircle_div_tauDagger
    {contestedBand slotWeight cost : ℝ}
    (hBand : 0 < contestedBand)
    (hWeight : 0 < slotWeight)
    (hCost : 0 < cost) (hCostWeight : cost < slotWeight) :
    tauCircle contestedBand slotWeight cost /
        tauDagger contestedBand slotWeight cost =
      thresholdRatio (cost / slotWeight) := by
  have hq : 0 < cost / slotWeight := div_pos hCost hWeight
  have hqOne : cost / slotWeight < 1 :=
    (div_lt_one hWeight).2 hCostWeight
  have hLog : 0 < logOdds (cost / slotWeight) :=
    logOdds_pos hq hqOne
  unfold tauCircle tauDagger thresholdRatio
  field_simp [ne_of_gt hBand, ne_of_gt hWeight, ne_of_gt hCost,
    ne_of_gt hLog]
  ring

theorem logOdds_hasDerivAt
    {q : ℝ} (hqNegOne : -1 < q) (hqOne : q < 1) :
    HasDerivAt logOdds (2 / (1 - q ^ 2)) q := by
  have hNumerator : HasDerivAt (fun x : ℝ => 1 + x) 1 q := by
    simpa only [Pi.add_apply, id_eq, zero_add] using
      (hasDerivAt_const q 1).add (hasDerivAt_id q)
  have hDenominator : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      (hasDerivAt_const q 1).sub (hasDerivAt_id q)
  have hDenominatorNe : 1 - q ≠ 0 :=
    ne_of_gt (sub_pos.mpr hqOne)
  have hNumeratorNe : 1 + q ≠ 0 := ne_of_gt (by linarith)
  have hSquareDenominator : 0 < 1 - q ^ 2 := by nlinarith
  have hRatioPos : 0 < (1 + q) / (1 - q) :=
    div_pos (by linarith) (by linarith)
  have hLog := (hNumerator.div hDenominator hDenominatorNe).log
    (ne_of_gt hRatioPos)
  change HasDerivAt (fun y => Real.log ((1 + y) / (1 - y)))
    (((1 * (1 - q) - (1 + q) * (-1)) / (1 - q) ^ 2) /
      ((1 + q) / (1 - q))) q at hLog
  unfold logOdds
  convert hLog using 1
  field_simp [hDenominatorNe, hNumeratorNe,
    ne_of_gt hSquareDenominator]
  ring

theorem thresholdRatio_hasDerivAt
    {q : ℝ} (hq : 0 < q) (hqOne : q < 1) :
    HasDerivAt thresholdRatio
      ((2 * logOdds q - 4 * q / (1 - q ^ 2)) /
        (logOdds q) ^ 2) q := by
  have hNumerator : HasDerivAt (fun x : ℝ => 2 * x) 2 q := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id q).const_mul 2
  have hLog := logOdds_hasDerivAt (by linarith : -1 < q) hqOne
  have hRatio := hNumerator.div hLog
    (ne_of_gt (logOdds_pos hq hqOne))
  unfold thresholdRatio
  convert hRatio using 1
  ring

/-- The normalized ratio is strictly decreasing in racing cost. -/
theorem thresholdRatio_strictAnti :
    StrictAntiOn thresholdRatio (Set.Ioo 0 1) := by
  have hContinuous : ContinuousOn thresholdRatio (Set.Ioo 0 1) := by
    intro q hq
    change 0 < q ∧ q < 1 at hq
    exact (thresholdRatio_hasDerivAt hq.1 hq.2).continuousAt.continuousWithinAt
  let slope : ℝ → ℝ := fun q =>
    (2 * logOdds q - 4 * q / (1 - q ^ 2)) / (logOdds q) ^ 2
  apply strictAntiOn_of_hasDerivWithinAt_neg
    (convex_Ioo 0 1) hContinuous
  · intro q hq
    rw [interior_Ioo] at hq
    change 0 < q ∧ q < 1 at hq
    exact (thresholdRatio_hasDerivAt hq.1 hq.2).hasDerivWithinAt
  · intro q hq
    rw [interior_Ioo] at hq
    change 0 < q ∧ q < 1 at hq
    have hUpper := logOdds_lt_two_mul_div_one_sub_sq hq.1 hq.2
    have hPositive := logOdds_pos hq.1 hq.2
    have hTwice :
        4 * q / (1 - q ^ 2) = 2 * (2 * q / (1 - q ^ 2)) := by
      ring
    have hNumerator :
        2 * logOdds q - 4 * q / (1 - q ^ 2) < 0 := by
      rw [hTwice]
      linarith
    exact div_neg_of_neg_of_pos hNumerator (sq_pos_of_pos hPositive)

/-- Cheap racing technology: `τ°/τ† → 1`. -/
theorem thresholdRatio_tendsto_zero :
    Filter.Tendsto thresholdRatio
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 1) := by
  have hLowerTendsto : Filter.Tendsto (fun q : ℝ => 1 - q ^ 2)
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds 1) := by
    have hContinuous : ContinuousAt (fun q : ℝ => 1 - q ^ 2) 0 := by
      fun_prop
    simpa using hContinuous.tendsto.mono_left inf_le_left
  have hUpperTendsto : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 (Set.Ioo 0 1)) (nhds (1 : ℝ)) := tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (f := thresholdRatio) (g := fun q : ℝ => 1 - q ^ 2)
    (h := fun _ : ℝ => 1) hLowerTendsto hUpperTendsto ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    change 0 < q ∧ q < 1 at hq
    have hLog := logOdds_pos hq.1 hq.2
    have hUpper := logOdds_lt_two_mul_div_one_sub_sq hq.1 hq.2
    have hDenominator : 0 < 1 - q ^ 2 := by nlinarith
    unfold thresholdRatio
    apply (le_div_iff₀ hLog).2
    have hScaled := mul_lt_mul_of_pos_right hUpper hDenominator
    have hCancel :
        2 * q / (1 - q ^ 2) * (1 - q ^ 2) = 2 * q := by
      field_simp [ne_of_gt hDenominator]
    rw [hCancel] at hScaled
    nlinarith
  · filter_upwards [self_mem_nhdsWithin] with q hq
    change 0 < q ∧ q < 1 at hq
    unfold thresholdRatio
    exact le_of_lt
      ((div_lt_one (logOdds_pos hq.1 hq.2)).2
        (two_mul_lt_logOdds hq.1 hq.2))

/-- Racing cost approaching the slot weight: `τ°/τ† → 0`. -/
theorem thresholdRatio_tendsto_one :
    Filter.Tendsto thresholdRatio
      (nhdsWithin 1 (Set.Ioo 0 1)) (nhds 0) := by
  let filter := nhdsWithin (1 : ℝ) (Set.Ioo 0 1)
  have hDenominator : Filter.Tendsto (fun q : ℝ => 1 - q) filter
      (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · have hContinuous : ContinuousAt (fun q : ℝ => 1 - q) 1 := by
        fun_prop
      simpa [filter] using hContinuous.tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with q hq
      change 0 < q ∧ q < 1 at hq
      change 0 < 1 - q
      linarith
  have hInverse : Filter.Tendsto (fun q : ℝ => (1 - q)⁻¹)
      filter Filter.atTop := by
    simpa only [Pi.inv_apply] using
      hDenominator.inv_tendsto_nhdsGT_zero
  have hRatioLower :
      (fun q : ℝ => (1 - q)⁻¹) ≤ᶠ[filter]
        (fun q => (1 + q) / (1 - q)) := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    change 0 < q ∧ q < 1 at hq
    rw [div_eq_mul_inv]
    exact le_mul_of_one_le_left
      (inv_nonneg.mpr (by linarith)) (by linarith)
  have hRatioTop : Filter.Tendsto
      (fun q : ℝ => (1 + q) / (1 - q)) filter Filter.atTop :=
    Filter.tendsto_atTop_mono' filter hRatioLower hInverse
  have hLogTop : Filter.Tendsto logOdds filter Filter.atTop := by
    unfold logOdds
    exact Real.tendsto_log_atTop.comp hRatioTop
  have hNumerator : Filter.Tendsto (fun q : ℝ => 2 * q)
      filter (nhds 2) := by
    have hContinuous : ContinuousAt (fun q : ℝ => 2 * q) 1 := by
      fun_prop
    simpa [filter] using hContinuous.tendsto.mono_left inf_le_left
  unfold thresholdRatio
  exact hNumerator.div_atTop hLogTop

/-- The threshold is strictly increasing in the contested band. -/
theorem tauCircle_strictMono_contestedBand
    {smaller larger slotWeight cost : ℝ}
    (hBands : smaller < larger)
    (hWeight : 0 < slotWeight)
    (hCost : 0 < cost) (hCostWeight : cost < slotWeight) :
    tauCircle smaller slotWeight cost < tauCircle larger slotWeight cost := by
  have hq : 0 < cost / slotWeight := div_pos hCost hWeight
  have hqOne : cost / slotWeight < 1 :=
    (div_lt_one hWeight).2 hCostWeight
  unfold tauCircle
  exact div_lt_div_of_pos_right hBands
    (mul_pos (by norm_num) (logOdds_pos hq hqOne))

/-- `L(q)` is strictly increasing on normalized costs `(0,1)`. -/
theorem logOdds_strictMonoOn : StrictMonoOn logOdds (Set.Ioo 0 1) := by
  intro first hFirst second hSecond hOrder
  change 0 < first ∧ first < 1 at hFirst
  change 0 < second ∧ second < 1 at hSecond
  have hFraction := Real.strictMonoOn_one_add_div_one_sub
    (show first ∈ Set.Ioo (-1 : ℝ) 1 by exact ⟨by linarith, hFirst.2⟩)
    (show second ∈ Set.Ioo (-1 : ℝ) 1 by exact ⟨by linarith, hSecond.2⟩)
    hOrder
  unfold logOdds
  exact Real.strictMonoOn_log
    (show (1 + first) / (1 - first) ∈ Set.Ioi (0 : ℝ) by
      exact div_pos (by linarith) (sub_pos.mpr hFirst.2))
    (show (1 + second) / (1 - second) ∈ Set.Ioi (0 : ℝ) by
      exact div_pos (by linarith) (sub_pos.mpr hSecond.2))
    hFraction

/-- The threshold is strictly decreasing in racing cost. -/
theorem tauCircle_strictAnti_cost
    {contestedBand slotWeight smallerCost largerCost : ℝ}
    (hBand : 0 < contestedBand)
    (hWeight : 0 < slotWeight)
    (hSmaller : 0 < smallerCost)
    (hCosts : smallerCost < largerCost)
    (hLargerWeight : largerCost < slotWeight) :
    tauCircle contestedBand slotWeight largerCost <
      tauCircle contestedBand slotWeight smallerCost := by
  have hLarger : 0 < largerCost := lt_trans hSmaller hCosts
  have hqSmall : 0 < smallerCost / slotWeight := div_pos hSmaller hWeight
  have hqLarge : largerCost / slotWeight < 1 :=
    (div_lt_one hWeight).2 hLargerWeight
  have hqOrder : smallerCost / slotWeight < largerCost / slotWeight :=
    div_lt_div_of_pos_right hCosts hWeight
  have hLogOrder := logOdds_strictMonoOn
    ⟨hqSmall, lt_trans hqOrder hqLarge⟩ ⟨lt_trans hqSmall hqOrder, hqLarge⟩
    hqOrder
  unfold tauCircle
  exact div_lt_div_of_pos_left hBand
    (mul_pos (by norm_num) (logOdds_pos hqSmall (lt_trans hqOrder hqLarge)))
    (mul_lt_mul_of_pos_left hLogOrder (by norm_num))

/-- Holding cost fixed, a larger slot weight raises `τ°`. -/
theorem tauCircle_strictMono_slotWeight
    {contestedBand cost smallerWeight largerWeight : ℝ}
    (hBand : 0 < contestedBand)
    (hCost : 0 < cost)
    (hCostSmaller : cost < smallerWeight)
    (hWeights : smallerWeight < largerWeight) :
    tauCircle contestedBand smallerWeight cost <
      tauCircle contestedBand largerWeight cost := by
  have hSmallerWeight : 0 < smallerWeight := lt_trans hCost hCostSmaller
  have hLargerWeight : 0 < largerWeight :=
    lt_trans hSmallerWeight hWeights
  have hqOrder : cost / largerWeight < cost / smallerWeight :=
    (div_lt_div_iff₀ hLargerWeight hSmallerWeight).2
      (by nlinarith)
  have hqLargePos : 0 < cost / largerWeight :=
    div_pos hCost hLargerWeight
  have hqSmallOne : cost / smallerWeight < 1 :=
    (div_lt_one hSmallerWeight).2 hCostSmaller
  have hLogOrder := logOdds_strictMonoOn
    ⟨hqLargePos, lt_trans hqOrder hqSmallOne⟩
    ⟨lt_trans hqLargePos hqOrder, hqSmallOne⟩ hqOrder
  unfold tauCircle
  exact div_lt_div_of_pos_left hBand
    (mul_pos (by norm_num)
      (logOdds_pos hqLargePos (lt_trans hqOrder hqSmallOne)))
    (mul_lt_mul_of_pos_left hLogOrder (by norm_num))

end

end SmoothingCliff.Racing
