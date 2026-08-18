import SmoothingCliff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The marginal value of latency advantage

Formal target: Lemma `lem:spread` in `Smoothing_the_Cliff_ITCS.tex`.
The opponents' effective scores are fixed, so `allocation : ℝ → ℝ` is the
paper's one-dimensional interim allocation `tilde x_i`.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- Truthful interim utility when latency advantage shifts the allocation score
but not the payment identity. -/
def advantageUtility (allocation cost : ℝ → ℝ)
    (reserve value advantage : ℝ) : ℝ :=
  (∫ z in reserve..value, allocation (z + advantage)) - cost advantage

/-- FTC bridge for Lemma `lem:spread`. Continuity of the allocation and the
cost derivative are explicit premises. Allocation differentiability is not
needed: after translating the integral, both endpoints move at unit speed. -/
theorem advantageUtility_hasDerivAt
    (allocation cost : ℝ → ℝ) (hAllocation : Continuous allocation)
    {reserve value advantage marginalCost : ℝ}
    (hCost : HasDerivAt cost marginalCost advantage) :
    HasDerivAt (advantageUtility allocation cost reserve value)
      (allocation (value + advantage) -
        allocation (reserve + advantage) - marginalCost) advantage := by
  have hmoving :
      HasDerivAt
        (fun y => (∫ z in reserve + y..value + y, allocation z) - cost y)
        (allocation (value + advantage) -
          allocation (reserve + advantage) - marginalCost) advantage := by
    let primitive : ℝ → ℝ :=
      fun u => ∫ z in (0 : ℝ)..u, allocation z
    have hprimitive (t : ℝ) :
        HasDerivAt primitive (allocation t) t := by
      dsimp [primitive]
      apply intervalIntegral.integral_hasDerivAt_right
      · exact hAllocation.intervalIntegrable _ _
      · exact hAllocation.stronglyMeasurable.stronglyMeasurableAtFilter
      · exact hAllocation.continuousAt
    have hshift (q : ℝ) :
        HasDerivAt (fun y : ℝ => q + y) 1 advantage := by
      simpa only [id_eq] using (hasDerivAt_id advantage).const_add q
    have hvalue :
        HasDerivAt (fun y => primitive (value + y))
          (allocation (value + advantage)) advantage := by
      simpa using
        (hprimitive (value + advantage)).comp advantage (hshift value)
    have hreserve :
        HasDerivAt (fun y => primitive (reserve + y))
          (allocation (reserve + advantage)) advantage := by
      simpa using
        (hprimitive (reserve + advantage)).comp advantage (hshift reserve)
    have hsub := (hvalue.sub hreserve).sub hCost
    convert hsub using 1
    funext y
    dsimp [primitive]
    rw [intervalIntegral.integral_interval_sub_left
      (hAllocation.intervalIntegrable _ _)
      (hAllocation.intervalIntegrable _ _)]
  change HasDerivAt
    (fun y => (∫ z in reserve..value, allocation (z + y)) - cost y)
    (allocation (value + advantage) -
      allocation (reserve + advantage) - marginalCost) advantage
  convert hmoving using 1
  funext y
  rw [intervalIntegral.integral_comp_add_right]

/-- Derivative form of `advantageUtility_hasDerivAt`, matching the displayed
formula in Lemma `lem:spread`. -/
theorem deriv_advantageUtility
    (allocation cost : ℝ → ℝ) (hAllocation : Continuous allocation)
    {reserve value advantage marginalCost : ℝ}
    (hCost : HasDerivAt cost marginalCost advantage) :
    deriv (advantageUtility allocation cost reserve value) advantage =
      allocation (value + advantage) -
        allocation (reserve + advantage) - marginalCost :=
  (advantageUtility_hasDerivAt allocation cost hAllocation hCost).deriv

/-- Under monotonicity, the range bound, and the published own-score
Lipschitz certificate, the endpoint allocation spread is between zero and the
minimum of the top prize and the Lipschitz bound. -/
theorem allocationSpread_bounds
    (allocation : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value advantage : ℝ} (hValue : reserve ≤ value) :
    0 ≤ allocation (value + advantage) - allocation (reserve + advantage) ∧
    allocation (value + advantage) - allocation (reserve + advantage) ≤
      min (weight : ℝ) ((value - reserve) * (sensitivity : ℝ)) := by
  have hEndpoints : reserve + advantage ≤ value + advantage := by
    linarith
  have hnonneg :
      0 ≤ allocation (value + advantage) - allocation (reserve + advantage) :=
    sub_nonneg.mpr (hMono hEndpoints)
  have hweight :
      allocation (value + advantage) -
          allocation (reserve + advantage) ≤ weight := by
    linarith [hRange (value + advantage), hRange (reserve + advantage)]
  have hlip :=
    hLip.dist_le_mul (value + advantage) (reserve + advantage)
  have hsensitivity :
      allocation (value + advantage) - allocation (reserve + advantage) ≤
        (value - reserve) * (sensitivity : ℝ) := by
    rw [Real.dist_eq, Real.dist_eq,
      abs_of_nonneg hnonneg,
      abs_of_nonneg (sub_nonneg.mpr hEndpoints)] at hlip
    calc
      allocation (value + advantage) - allocation (reserve + advantage) ≤
          (sensitivity : ℝ) *
            ((value + advantage) - (reserve + advantage)) := hlip
      _ = (value - reserve) * (sensitivity : ℝ) := by ring
  exact ⟨hnonneg, le_min hweight hsensitivity⟩

/-- Paper-level generic form of Lemma `lem:spread`. The Lipschitz premise
supplies the continuity needed by the FTC bridge. -/
theorem marginalValue_and_spread_bounds
    (allocation cost : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value advantage marginalCost : ℝ}
    (hValue : reserve ≤ value)
    (hCost : HasDerivAt cost marginalCost advantage) :
    HasDerivAt (advantageUtility allocation cost reserve value)
      (allocation (value + advantage) -
        allocation (reserve + advantage) - marginalCost) advantage ∧
    0 ≤ allocation (value + advantage) - allocation (reserve + advantage) ∧
    allocation (value + advantage) - allocation (reserve + advantage) ≤
      min (weight : ℝ) ((value - reserve) * (sensitivity : ℝ)) := by
  refine ⟨advantageUtility_hasDerivAt allocation cost hLip.continuous hCost, ?_⟩
  exact allocationSpread_bounds allocation weight sensitivity
    hMono hRange hLip hValue

/-- Euler's number, packaged as a nonnegative real for a Lipschitz constant. -/
def eulerNNReal : NNReal :=
  ⟨Real.exp 1, (Real.exp_pos 1).le⟩

/-- The paper's PL own-score certificate `w₁ / (e * τ)`. -/
def plSensitivity (weight temperature : NNReal) : NNReal :=
  weight / (eulerNNReal * temperature)

/-- Substituting the PL certificate into `allocationSpread_bounds` gives the
displayed bound in Lemma `lem:spread`. Positivity of temperature is stated
explicitly because the paper defines PL only for `τ > 0`. -/
theorem plAllocationSpread_bounds
    (allocation : ℝ → ℝ) (weight temperature : NNReal)
    (_hTemperature : 0 < temperature)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith (plSensitivity weight temperature) allocation)
    {reserve value advantage : ℝ} (hValue : reserve ≤ value) :
    0 ≤ allocation (value + advantage) - allocation (reserve + advantage) ∧
    allocation (value + advantage) - allocation (reserve + advantage) ≤
      min (weight : ℝ)
        (((value - reserve) * (weight : ℝ)) /
          (Real.exp 1 * (temperature : ℝ))) := by
  have h := allocationSpread_bounds allocation weight
    (plSensitivity weight temperature) hMono hRange hLip
    (reserve := reserve) (value := value) (advantage := advantage) hValue
  have hslope :
      (plSensitivity weight temperature : ℝ) =
        (weight : ℝ) / (Real.exp 1 * (temperature : ℝ)) := rfl
  rw [hslope] at h
  refine ⟨h.1, ?_⟩
  simpa only [mul_div_assoc] using h.2

/-- Full PL specialization of Lemma `lem:spread`: the utility derivative and
the exact `min {w₁, (v-r)w₁/(eτ)}` spread bound. -/
theorem plMarginalValue_and_spread_bounds
    (allocation cost : ℝ → ℝ) (weight temperature : NNReal)
    (hTemperature : 0 < temperature)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith (plSensitivity weight temperature) allocation)
    {reserve value advantage marginalCost : ℝ}
    (hValue : reserve ≤ value)
    (hCost : HasDerivAt cost marginalCost advantage) :
    HasDerivAt (advantageUtility allocation cost reserve value)
      (allocation (value + advantage) -
        allocation (reserve + advantage) - marginalCost) advantage ∧
    0 ≤ allocation (value + advantage) - allocation (reserve + advantage) ∧
    allocation (value + advantage) - allocation (reserve + advantage) ≤
      min (weight : ℝ)
        (((value - reserve) * (weight : ℝ)) /
          (Real.exp 1 * (temperature : ℝ))) := by
  refine ⟨advantageUtility_hasDerivAt allocation cost hLip.continuous hCost, ?_⟩
  exact plAllocationSpread_bounds allocation weight temperature hTemperature
    hMono hRange hLip hValue

end

end SmoothingCliff.Racing
