import SmoothingCliff.Basic
import SmoothingCliff.Mechanism.Intensity
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Exact one-slot Luce stability

This file formalizes Corollary `cor:tight-K1` in
`Smoothing_the_Cliff_ITCS.tex`.  All opponents are summarized by their total
Luce intensity.  The final theorem is stated on `EligibleBid reserve`, so its
domain is exactly the paper's eligible interval `[reserve, infinity)`.
-/

namespace SmoothingCliff.Mechanism

open SmoothingCliff

/-- The one-slot Luce winning probability against a fixed total intensity of
eligible opponents. -/
noncomputable def oneSlotLuceProbability
    (reserve temperature opponentIntensity bid : ℝ) : ℝ :=
  luceIntensity reserve temperature bid /
    (luceIntensity reserve temperature bid + opponentIntensity)

/-- Expected one-slot priority of weight `weight`. -/
noncomputable def oneSlotLuceAllocation
    (weight reserve temperature opponentIntensity bid : ℝ) : ℝ :=
  weight * oneSlotLuceProbability reserve temperature opponentIntensity bid

/-- The paper's exact uniform own-bid Lipschitz constant `w₁ / (4 τ)`. -/
noncomputable def oneSlotLipschitzConstant
    (weight temperature : ℝ) (hWeight : 0 ≤ weight)
    (hTemperature : 0 < temperature) : NNReal :=
  ⟨weight / (4 * temperature), by positivity⟩

@[simp] theorem coe_oneSlotLipschitzConstant
    (weight temperature : ℝ) (hWeight : 0 ≤ weight)
    (hTemperature : 0 < temperature) :
    (oneSlotLipschitzConstant weight temperature hWeight hTemperature : ℝ) =
      weight / (4 * temperature) := rfl

theorem oneSlotLuceProbability_nonneg
    {reserve temperature opponentIntensity bid : ℝ}
    (hOpponent : 0 ≤ opponentIntensity) :
    0 ≤ oneSlotLuceProbability reserve temperature opponentIntensity bid := by
  apply div_nonneg
  · exact (luceIntensity_pos reserve temperature bid).le
  · exact (add_pos_of_pos_of_nonneg
      (luceIntensity_pos reserve temperature bid) hOpponent).le

theorem oneSlotLuceProbability_le_one
    {reserve temperature opponentIntensity bid : ℝ}
    (hOpponent : 0 ≤ opponentIntensity) :
    oneSlotLuceProbability reserve temperature opponentIntensity bid ≤ 1 := by
  apply (div_le_one
    (add_pos_of_pos_of_nonneg
      (luceIntensity_pos reserve temperature bid) hOpponent)).2
  exact le_add_of_nonneg_right hOpponent

/-- A tied focal intensity and opponent total intensity give winning
probability one half.  In particular, this is the two-eligible-agent equal-bid
profile used for sharpness in the paper. -/
theorem oneSlotLuceProbability_balanced
    (reserve temperature bid : ℝ) :
    oneSlotLuceProbability reserve temperature
      (luceIntensity reserve temperature bid) bid = 1 / 2 := by
  have hne : luceIntensity reserve temperature bid ≠ 0 :=
    ne_of_gt (luceIntensity_pos reserve temperature bid)
  simp only [oneSlotLuceProbability]
  field_simp [hne]
  norm_num

/-- Algebraic sharpness of the Bernoulli variance bound. -/
theorem quadratic_variance_le_quarter (q : ℝ) :
    q * (1 - q) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (q - 1 / 2)]

theorem hasDerivAt_luceIntensity
    (reserve temperature bid : ℝ) :
    HasDerivAt (luceIntensity reserve temperature)
      (luceIntensity reserve temperature bid / temperature) bid := by
  have hlin :
      HasDerivAt (fun z : ℝ => (z - reserve) / temperature)
        (1 / temperature) bid := by
    simpa using ((hasDerivAt_id bid).sub_const reserve).div_const temperature
  simpa [luceIntensity, div_eq_mul_inv] using hlin.exp

/-- Exact own-bid derivative of the one-slot Luce probability. -/
theorem hasDerivAt_oneSlotLuceProbability
    {reserve temperature opponentIntensity bid : ℝ}
    (hTemperature : 0 < temperature)
    (hOpponent : 0 ≤ opponentIntensity) :
    HasDerivAt
      (oneSlotLuceProbability reserve temperature opponentIntensity)
      (oneSlotLuceProbability reserve temperature opponentIntensity bid *
        (1 - oneSlotLuceProbability reserve temperature opponentIntensity bid) /
        temperature)
      bid := by
  have he := hasDerivAt_luceIntensity reserve temperature bid
  have hden :
      luceIntensity reserve temperature bid + opponentIntensity ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg
      (luceIntensity_pos reserve temperature bid) hOpponent)
  have hquot := he.div (he.add_const opponentIntensity) hden
  convert hquot using 1
  simp only [oneSlotLuceProbability]
  field_simp [hden, ne_of_gt hTemperature]

/-- Exact own-bid derivative after multiplying the winning probability by the
slot weight. -/
theorem hasDerivAt_oneSlotLuceAllocation
    {weight reserve temperature opponentIntensity bid : ℝ}
    (hTemperature : 0 < temperature)
    (hOpponent : 0 ≤ opponentIntensity) :
    HasDerivAt
      (oneSlotLuceAllocation weight reserve temperature opponentIntensity)
      (weight * oneSlotLuceProbability reserve temperature opponentIntensity bid *
        (1 - oneSlotLuceProbability reserve temperature opponentIntensity bid) /
        temperature)
      bid := by
  have hq := hasDerivAt_oneSlotLuceProbability
    (reserve := reserve) (temperature := temperature)
    (opponentIntensity := opponentIntensity) (bid := bid)
    hTemperature hOpponent
  change HasDerivAt
    (fun z => weight *
      oneSlotLuceProbability reserve temperature opponentIntensity z)
    (weight * oneSlotLuceProbability reserve temperature opponentIntensity bid *
      (1 - oneSlotLuceProbability reserve temperature opponentIntensity bid) /
      temperature)
    bid
  convert hq.const_mul weight using 1
  ring

/-- At the balanced profile the allocation derivative reaches
`w₁ / (4 τ)`, establishing sharpness of the pointwise derivative bound. -/
theorem hasDerivAt_oneSlotLuceAllocation_balanced
    {weight reserve temperature bid : ℝ}
    (hTemperature : 0 < temperature) :
    HasDerivAt
      (oneSlotLuceAllocation weight reserve temperature
        (luceIntensity reserve temperature bid))
      (weight / (4 * temperature))
      bid := by
  have h := hasDerivAt_oneSlotLuceAllocation
    (weight := weight) (reserve := reserve) (temperature := temperature)
    (opponentIntensity := luceIntensity reserve temperature bid) (bid := bid)
    hTemperature (luceIntensity_pos reserve temperature bid).le
  rw [oneSlotLuceProbability_balanced] at h
  convert h using 1
  ring

/-- The exact derivative is nonnegative and bounded above by `w₁ / (4 τ)`. -/
theorem oneSlotLuceAllocation_derivative_bounds
    {weight reserve temperature opponentIntensity bid : ℝ}
    (hWeight : 0 ≤ weight)
    (hTemperature : 0 < temperature)
    (hOpponent : 0 ≤ opponentIntensity) :
    0 ≤ weight * oneSlotLuceProbability reserve temperature opponentIntensity bid *
        (1 - oneSlotLuceProbability reserve temperature opponentIntensity bid) /
        temperature ∧
      weight * oneSlotLuceProbability reserve temperature opponentIntensity bid *
        (1 - oneSlotLuceProbability reserve temperature opponentIntensity bid) /
        temperature ≤
      weight / (4 * temperature) := by
  let q := oneSlotLuceProbability reserve temperature opponentIntensity bid
  have hq0 : 0 ≤ q := oneSlotLuceProbability_nonneg hOpponent
  have hq1 : q ≤ 1 := oneSlotLuceProbability_le_one hOpponent
  have hvar0 : 0 ≤ q * (1 - q) :=
    mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hvar4 : q * (1 - q) ≤ 1 / 4 :=
    quadratic_variance_le_quarter q
  constructor
  · dsimp [q] at hvar0 ⊢
    positivity
  · dsimp [q] at hvar4 ⊢
    calc
      weight * oneSlotLuceProbability reserve temperature opponentIntensity bid *
          (1 - oneSlotLuceProbability reserve temperature opponentIntensity bid) /
          temperature =
          weight *
            (oneSlotLuceProbability reserve temperature opponentIntensity bid *
              (1 - oneSlotLuceProbability reserve temperature opponentIntensity bid)) /
            temperature := by ring
      _ ≤ weight * (1 / 4) / temperature := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hvar4 hWeight) hTemperature.le
      _ = weight / (4 * temperature) := by ring

theorem oneSlotLuceAllocation_derivative_norm_le
    {weight reserve temperature opponentIntensity bid : ℝ}
    (hWeight : 0 ≤ weight)
    (hTemperature : 0 < temperature)
    (hOpponent : 0 ≤ opponentIntensity) :
    ‖weight * oneSlotLuceProbability reserve temperature opponentIntensity bid *
        (1 - oneSlotLuceProbability reserve temperature opponentIntensity bid) /
        temperature‖ ≤
      weight / (4 * temperature) := by
  rw [Real.norm_eq_abs, abs_of_nonneg
    (oneSlotLuceAllocation_derivative_bounds hWeight hTemperature hOpponent).1]
  exact (oneSlotLuceAllocation_derivative_bounds
    hWeight hTemperature hOpponent).2

/-- Mean-value-theorem form of the tight one-slot constant on the eligible
interval. -/
theorem oneSlotLuceAllocation_lipschitzOn_eligible
    {weight reserve temperature opponentIntensity : ℝ}
    (hWeight : 0 ≤ weight)
    (hTemperature : 0 < temperature)
    (hOpponent : 0 ≤ opponentIntensity) :
    LipschitzOnWith
      (oneSlotLipschitzConstant weight temperature hWeight hTemperature)
      (oneSlotLuceAllocation weight reserve temperature opponentIntensity)
      (Set.Ici reserve) := by
  refine (convex_Ici reserve).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun bid =>
      weight * oneSlotLuceProbability reserve temperature opponentIntensity bid *
        (1 - oneSlotLuceProbability reserve temperature opponentIntensity bid) /
        temperature) ?_ ?_
  · intro bid _hbid
    exact (hasDerivAt_oneSlotLuceAllocation
      hTemperature hOpponent).hasDerivWithinAt
  · intro bid _hbid
    apply NNReal.coe_le_coe.mp
    change ‖weight * oneSlotLuceProbability reserve temperature opponentIntensity bid *
        (1 - oneSlotLuceProbability reserve temperature opponentIntensity bid) /
        temperature‖ ≤ weight / (4 * temperature)
    exact oneSlotLuceAllocation_derivative_norm_le
      hWeight hTemperature hOpponent

/-- Corollary `cor:tight-K1`: on eligible bids, the one-slot Luce allocation is
`w₁ / (4 τ)`-Lipschitz for every fixed nonnegative total opponent intensity. -/
theorem oneSlotLuceAllocation_lipschitz_eligible
    {weight reserve temperature opponentIntensity : ℝ}
    (hWeight : 0 ≤ weight)
    (hTemperature : 0 < temperature)
    (hOpponent : 0 ≤ opponentIntensity) :
    LipschitzWith
      (oneSlotLipschitzConstant weight temperature hWeight hTemperature)
      (fun bid : EligibleBid reserve =>
        oneSlotLuceAllocation weight reserve temperature opponentIntensity bid) := by
  simpa using
    (oneSlotLuceAllocation_lipschitzOn_eligible
      hWeight hTemperature hOpponent).to_restrict

end SmoothingCliff.Mechanism
