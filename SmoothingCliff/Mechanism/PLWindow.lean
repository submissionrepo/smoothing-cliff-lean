import SmoothingCliff.Mechanism.OneSlotStability
import SmoothingCliff.Racing.ExactThreshold

/-!
# Exact one-slot PL range budgets

Against any finite collection of opponents, only their total Luce intensity
matters.  The focal allocation is therefore a horizontally translated logistic
curve.  This file composes that reduction with the exact centered-window result
from `Racing.ExactThreshold` and formalizes Corollary
`cor:pl-window-general-n`.
-/

namespace SmoothingCliff.Mechanism

open SmoothingCliff
open SmoothingCliff.Racing

noncomputable section

/-- Location of the logistic curve induced by a positive total opponent
intensity. -/
def oneSlotOpponentLocation
    (reserve temperature opponentIntensity : ℝ) : ℝ :=
  reserve + temperature * Real.log opponentIntensity

/-- Total Luce intensity of a finite opponent profile. -/
def opponentTotalLuceIntensity
    {ι : Type*} [Fintype ι] {reserve : ℝ}
    (temperature : ℝ) (b : EligibleProfile ι reserve) : ℝ :=
  ∑ j, luceIntensity reserve temperature (b j)

theorem opponentTotalLuceIntensity_pos
    {ι : Type*} [Fintype ι] [Nonempty ι] {reserve temperature : ℝ}
    (b : EligibleProfile ι reserve) :
    0 < opponentTotalLuceIntensity temperature b := by
  unfold opponentTotalLuceIntensity
  exact Finset.sum_pos (fun j hj => luceIntensity_pos reserve temperature (b j))
    Finset.univ_nonempty

/-- Every total intensity at least the number of eligible opponents is
realized by an equal-bid eligible profile. -/
theorem exists_eligible_opponents_with_total_intensity
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {reserve temperature total : ℝ}
    (hTemperature : 0 < temperature)
    (hTotal : (Fintype.card ι : ℝ) ≤ total) :
    ∃ b : EligibleProfile ι reserve,
      opponentTotalLuceIntensity temperature b = total := by
  let m : ℝ := Fintype.card ι
  have hm : 0 < m := by dsimp [m]; positivity
  have hratio : 1 ≤ total / m := (le_div_iff₀ hm).2 (by simpa [m] using hTotal)
  have hratioPos : 0 < total / m := lt_of_lt_of_le zero_lt_one hratio
  let commonBid : ℝ := reserve + temperature * Real.log (total / m)
  have hcommon : reserve ≤ commonBid := by
    dsimp [commonBid]
    have hlog : 0 ≤ Real.log (total / m) := Real.log_nonneg hratio
    have hproduct := mul_nonneg hTemperature.le hlog
    linarith
  let b : EligibleProfile ι reserve := fun _ => ⟨commonBid, hcommon⟩
  refine ⟨b, ?_⟩
  unfold opponentTotalLuceIntensity luceIntensity
  have hEach : ∀ j : ι,
      Real.exp (((b j : ℝ) - reserve) / temperature) = total / m := by
    intro j
    dsimp [b, commonBid]
    rw [show (reserve + temperature * Real.log (total / m) - reserve) /
        temperature = Real.log (total / m) by
      field_simp [ne_of_gt hTemperature]
      ring]
    exact Real.exp_log hratioPos
  rw [Finset.sum_congr rfl (fun j hj => hEach j), Finset.sum_const,
    nsmul_eq_mul]
  dsimp [m]
  field_simp

/-- A one-slot Luce probability is a translated logistic curve. -/
theorem oneSlotLuceProbability_eq_sigmoid
    {reserve temperature opponentIntensity bid : ℝ}
    (hTemperature : temperature ≠ 0) (hOpponent : 0 < opponentIntensity) :
    oneSlotLuceProbability reserve temperature opponentIntensity bid =
      Real.sigmoid
        ((bid - oneSlotOpponentLocation reserve temperature opponentIntensity) /
          temperature) := by
  have hIntensity : luceIntensity reserve temperature bid ≠ 0 :=
    ne_of_gt (luceIntensity_pos reserve temperature bid)
  have hExp :
      Real.exp
          (-((bid - oneSlotOpponentLocation reserve temperature opponentIntensity) /
            temperature)) =
        opponentIntensity / luceIntensity reserve temperature bid := by
    unfold oneSlotOpponentLocation luceIntensity
    rw [show
      -((bid - (reserve + temperature * Real.log opponentIntensity)) /
          temperature) =
        Real.log opponentIntensity - (bid - reserve) / temperature by
          field_simp
          ring]
    rw [Real.exp_sub, Real.exp_log hOpponent]
  unfold oneSlotLuceProbability Real.sigmoid
  rw [hExp]
  field_simp

/-- The allocation gain over a bid window is exactly the corresponding
logistic window. -/
theorem oneSlotLuceAllocation_window_eq
    {weight reserve temperature opponentIntensity start width : ℝ}
    (hTemperature : temperature ≠ 0) (hOpponent : 0 < opponentIntensity) :
    oneSlotLuceAllocation weight reserve temperature opponentIntensity
        (start + width) -
      oneSlotLuceAllocation weight reserve temperature opponentIntensity start =
        weight * marginalWindow width temperature
          (start - oneSlotOpponentLocation reserve temperature opponentIntensity) := by
  rw [oneSlotLuceAllocation, oneSlotLuceAllocation,
    oneSlotLuceProbability_eq_sigmoid hTemperature hOpponent,
    oneSlotLuceProbability_eq_sigmoid hTemperature hOpponent]
  unfold marginalWindow
  ring_nf

/-- Every length-`width` one-slot PL allocation window obeys the sharp
centered-logistic bound, independently of the number of opponents. -/
theorem oneSlotLuceAllocation_window_le
    {weight reserve temperature opponentIntensity start width : ℝ}
    (hWeight : 0 ≤ weight) (hTemperature : 0 < temperature)
    (hOpponent : 0 < opponentIntensity) (hWidth : 0 ≤ width) :
    oneSlotLuceAllocation weight reserve temperature opponentIntensity
        (start + width) -
      oneSlotLuceAllocation weight reserve temperature opponentIntensity start ≤
        weight * (2 * Real.sigmoid (width / (2 * temperature)) - 1) := by
  rw [oneSlotLuceAllocation_window_eq (ne_of_gt hTemperature) hOpponent]
  exact mul_le_mul_of_nonneg_left
    (marginalWindow_le_center hTemperature hWidth) hWeight

/-- The bound is not only a supremum: after shifting total opponent intensity,
the window can be centered and equality is attained. -/
theorem exists_opponentIntensity_window_eq_center
    {weight reserve temperature start width : ℝ}
    (hTemperature : 0 < temperature) :
    ∃ opponentIntensity : ℝ, 0 < opponentIntensity ∧
      oneSlotLuceAllocation weight reserve temperature opponentIntensity
          (start + width) -
        oneSlotLuceAllocation weight reserve temperature opponentIntensity start =
          weight * (2 * Real.sigmoid (width / (2 * temperature)) - 1) := by
  let opponentIntensity :=
    Real.exp ((start + width / 2 - reserve) / temperature)
  refine ⟨opponentIntensity, Real.exp_pos _, ?_⟩
  rw [oneSlotLuceAllocation_window_eq (ne_of_gt hTemperature) (Real.exp_pos _)]
  have hLocation :
      oneSlotOpponentLocation reserve temperature opponentIntensity =
        start + width / 2 := by
    unfold oneSlotOpponentLocation opponentIntensity
    rw [Real.log_exp]
    field_simp
    ring
  rw [hLocation]
  have hPosition : start - (start + width / 2) = -width / 2 := by ring
  rw [hPosition, marginalWindow_center (ne_of_gt hTemperature)]

/-- For every finite nonempty opponent set, an eligible opponent profile and
eligible starting bid attain the centered-window bound. -/
theorem exists_eligible_opponent_profile_window_eq_center
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {weight reserve temperature width : ℝ}
    (hTemperature : 0 < temperature) (hWidth : 0 ≤ width) :
    ∃ start : ℝ, reserve ≤ start ∧
      ∃ b : EligibleProfile ι reserve,
        oneSlotLuceAllocation weight reserve temperature
            (opponentTotalLuceIntensity temperature b) (start + width) -
          oneSlotLuceAllocation weight reserve temperature
            (opponentTotalLuceIntensity temperature b) start =
          weight * (2 * Real.sigmoid (width / (2 * temperature)) - 1) := by
  let m : ℝ := Fintype.card ι
  have hm : 0 < m := by dsimp [m]; positivity
  let start : ℝ := reserve + temperature * Real.log m
  have hstart : reserve ≤ start := by
    have hmOne : 1 ≤ m := by
      dsimp [m]
      exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
    have hlog : 0 ≤ Real.log m := Real.log_nonneg hmOne
    dsimp [start]
    have hproduct := mul_nonneg hTemperature.le hlog
    linarith
  let total : ℝ :=
    Real.exp ((start + width / 2 - reserve) / temperature)
  have htotalFormula :
      total = m * Real.exp (width / (2 * temperature)) := by
    dsimp [total, start]
    rw [show
      (reserve + temperature * Real.log m + width / 2 - reserve) / temperature =
        Real.log m + width / (2 * temperature) by
      field_simp [ne_of_gt hTemperature]
      ring]
    rw [Real.exp_add, Real.exp_log hm]
  have hExpOne : 1 ≤ Real.exp (width / (2 * temperature)) := by
    rw [← Real.exp_zero]
    apply Real.exp_le_exp.mpr
    positivity
  have htotal : m ≤ total := by
    rw [htotalFormula]
    nlinarith
  obtain ⟨b, hb⟩ := exists_eligible_opponents_with_total_intensity
    (ι := ι) hTemperature (by simpa [m] using htotal)
  refine ⟨start, hstart, b, ?_⟩
  rw [hb]
  rw [oneSlotLuceAllocation_window_eq (ne_of_gt hTemperature) (Real.exp_pos _)]
  have hLocation : oneSlotOpponentLocation reserve temperature total =
      start + width / 2 := by
    unfold oneSlotOpponentLocation total
    rw [Real.log_exp]
    field_simp [ne_of_gt hTemperature]
    ring
  rw [hLocation]
  have hPosition : start - (start + width / 2) = -width / 2 := by ring
  rw [hPosition, marginalWindow_center (ne_of_gt hTemperature)]

theorem two_sigmoid_logOdds_sub_one
    {q : ℝ} (hq : 0 < q) (hqOne : q < 1) :
    2 * Real.sigmoid (logOdds q) - 1 = q := by
  have hOneMinus : 0 < 1 - q := by linarith
  have hOnePlus : 0 < 1 + q := by linarith
  have hRatio : 0 < (1 + q) / (1 - q) := div_pos hOnePlus hOneMinus
  have hExp : Real.exp (-(logOdds q)) = (1 - q) / (1 + q) := by
    unfold logOdds
    rw [Real.exp_neg, Real.exp_log hRatio]
    field_simp
  unfold Real.sigmoid
  rw [hExp]
  field_simp
  ring

/-- At the paper's closed-form temperature `τ°`, the largest allocation gain
over a window of length `contestedBand` is exactly `cost`. -/
theorem tauCircle_window_budget_eq
    {slotWeight contestedBand cost : ℝ}
    (hBand : 0 < contestedBand) (hWeight : 0 < slotWeight)
    (hCost : 0 < cost) (hCostWeight : cost < slotWeight) :
    slotWeight *
        (2 * Real.sigmoid
          (contestedBand /
            (2 * tauCircle contestedBand slotWeight cost)) - 1) = cost := by
  let q := cost / slotWeight
  have hq : 0 < q := div_pos hCost hWeight
  have hqOne : q < 1 := (div_lt_one hWeight).2 hCostWeight
  have hLog : logOdds q ≠ 0 := ne_of_gt (logOdds_pos hq hqOne)
  have hArgument :
      contestedBand / (2 * tauCircle contestedBand slotWeight cost) =
        logOdds q := by
    unfold tauCircle
    dsimp [q]
    field_simp [ne_of_gt hBand, hLog]
  rw [hArgument, two_sigmoid_logOdds_sub_one hq hqOne]
  dsimp [q]
  field_simp

/-- Corollary `cor:pl-window-general-n`, coefficient form.  The conclusion is
uniform in the opponents because they enter only through their positive total
intensity. -/
theorem oneSlotPL_global_window_budget_at_tauCircle
    {slotWeight contestedBand cost reserve opponentIntensity start width : ℝ}
    (hBand : 0 < contestedBand) (hWeight : 0 < slotWeight)
    (hCost : 0 < cost) (hCostWeight : cost < slotWeight)
    (hOpponent : 0 < opponentIntensity)
    (hWidth : 0 ≤ width)
    (hWidthBand : width ≤ contestedBand) :
    oneSlotLuceAllocation slotWeight reserve
          (tauCircle contestedBand slotWeight cost) opponentIntensity
          (start + width) -
        oneSlotLuceAllocation slotWeight reserve
          (tauCircle contestedBand slotWeight cost) opponentIntensity start ≤
      cost := by
  have hTau := tauCircle_pos hBand hWeight hCost hCostWeight
  have hWindow := oneSlotLuceAllocation_window_le
    (reserve := reserve) (start := start) hWeight.le hTau hOpponent hWidth
  have hSigmoidMono :
      2 * Real.sigmoid (width / (2 * tauCircle contestedBand slotWeight cost)) - 1 ≤
        2 * Real.sigmoid
          (contestedBand / (2 * tauCircle contestedBand slotWeight cost)) - 1 := by
    have hden : 0 < 2 * tauCircle contestedBand slotWeight cost :=
      mul_pos (by norm_num) hTau
    have harg := (div_le_div_iff_of_pos_right hden).2 hWidthBand
    have hmono := Real.sigmoid_monotone harg
    linarith
  calc
    oneSlotLuceAllocation slotWeight reserve
          (tauCircle contestedBand slotWeight cost) opponentIntensity
          (start + width) -
        oneSlotLuceAllocation slotWeight reserve
          (tauCircle contestedBand slotWeight cost) opponentIntensity start ≤
      slotWeight *
        (2 * Real.sigmoid
          (width / (2 * tauCircle contestedBand slotWeight cost)) - 1) := hWindow
    _ ≤ slotWeight *
        (2 * Real.sigmoid
          (contestedBand / (2 * tauCircle contestedBand slotWeight cost)) - 1) :=
      mul_le_mul_of_nonneg_left hSigmoidMono hWeight.le
    _ = cost := tauCircle_window_budget_eq hBand hWeight hCost hCostWeight

end

end SmoothingCliff.Mechanism
