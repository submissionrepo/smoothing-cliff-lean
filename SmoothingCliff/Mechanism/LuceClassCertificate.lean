import SmoothingCliff.Mechanism.LuceClass
import SmoothingCliff.Mechanism.OneSlotStability
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The one-slot Luce cap and the log-slope bound

This file supplies the equivalence half of Corollary `cor:luceclass`.  For a
positive differentiable intensity, the one-slot allocation derivative is

`w₁ (α'/α) q(1-q)`.

The Bernoulli factor is at most `1/4`, and an opponent total equal to the focal
intensity attains `q=1/2`.  Hence a uniform allocation cap `𝒮` is equivalent to
the pointwise log-slope bound `(log α)' ≤ 4𝒮/w₁`.
-/

namespace SmoothingCliff.LuceOptimality

open SmoothingCliff
open SmoothingCliff.Mechanism
open SmoothingCliff.Racing

noncomputable section

/-- One-slot Luce probability for a generic positive intensity. -/
def genericOneSlotLuceProbability
    (α : ℝ → ℝ) (opponentIntensity bid : ℝ) : ℝ :=
  α bid / (α bid + opponentIntensity)

/-- One-slot allocation for a generic positive intensity. -/
def genericOneSlotLuceAllocation
    (weight : ℝ) (α : ℝ → ℝ) (opponentIntensity bid : ℝ) : ℝ :=
  weight * genericOneSlotLuceProbability α opponentIntensity bid

/-- The regularity used by the cap equivalence.  Continuous differentiability
is represented by an explicit continuous derivative witness. -/
def EligiblePositiveC1Intensity
    (reserve : ℝ) (α dα : ℝ → ℝ) : Prop :=
  (∀ b, HasDerivAt α (dα b) b) ∧
  Continuous dα ∧
  (∀ b, reserve ≤ b → 0 < α b) ∧
  ∀ b, reserve ≤ b → 0 ≤ dα b

/-- Uniform eligible-region own-bid cap over every positive total opponent
intensity. -/
def GenericOneSlotLuceCap
    (reserve weight : ℝ) (sensitivity : NNReal) (α : ℝ → ℝ) : Prop :=
  ∀ opponentIntensity, 0 < opponentIntensity →
    LipschitzOnWith sensitivity
      (genericOneSlotLuceAllocation weight α opponentIntensity)
      (Set.Ici reserve)

theorem genericOneSlotLuceProbability_nonneg
    {α : ℝ → ℝ} {opponentIntensity bid : ℝ}
    (hα : 0 < α bid) (hOpponent : 0 ≤ opponentIntensity) :
    0 ≤ genericOneSlotLuceProbability α opponentIntensity bid := by
  unfold genericOneSlotLuceProbability
  positivity

theorem genericOneSlotLuceProbability_le_one
    {α : ℝ → ℝ} {opponentIntensity bid : ℝ}
    (hα : 0 < α bid) (hOpponent : 0 ≤ opponentIntensity) :
    genericOneSlotLuceProbability α opponentIntensity bid ≤ 1 := by
  unfold genericOneSlotLuceProbability
  exact (div_le_one (add_pos_of_pos_of_nonneg hα hOpponent)).2
    (le_add_of_nonneg_right hOpponent)

theorem genericOneSlotLuceProbability_balanced
    {α : ℝ → ℝ} {bid : ℝ} (hα : α bid ≠ 0) :
    genericOneSlotLuceProbability α (α bid) bid = 1 / 2 := by
  unfold genericOneSlotLuceProbability
  field_simp
  norm_num

/-- Exact derivative of a generic one-slot Luce allocation. -/
theorem hasDerivAt_genericOneSlotLuceAllocation
    {weight opponentIntensity bid : ℝ} {α dα : ℝ → ℝ}
    (hαDeriv : HasDerivAt α (dα bid) bid)
    (hαPos : 0 < α bid) (hOpponent : 0 ≤ opponentIntensity) :
    HasDerivAt (genericOneSlotLuceAllocation weight α opponentIntensity)
      (weight * (dα bid / α bid) *
        (genericOneSlotLuceProbability α opponentIntensity bid) *
        (1 - genericOneSlotLuceProbability α opponentIntensity bid)) bid := by
  have hden : α bid + opponentIntensity ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hαPos hOpponent)
  have hquot := hαDeriv.div (hαDeriv.add_const opponentIntensity) hden
  have hscaled := hquot.const_mul weight
  unfold genericOneSlotLuceAllocation
  convert hscaled using 1
  unfold genericOneSlotLuceProbability
  field_simp [ne_of_gt hαPos, hden]

theorem genericOneSlotLuceAllocation_balanced_derivative
    {weight bid : ℝ} {α dα : ℝ → ℝ}
    (hαDeriv : HasDerivAt α (dα bid) bid) (hαPos : 0 < α bid) :
    HasDerivAt (genericOneSlotLuceAllocation weight α (α bid))
      (weight * (dα bid / α bid) / 4) bid := by
  have h := hasDerivAt_genericOneSlotLuceAllocation
    (weight := weight) (opponentIntensity := α bid)
    hαDeriv hαPos hαPos.le
  rw [genericOneSlotLuceProbability_balanced (ne_of_gt hαPos)] at h
  convert h using 1
  ring

/-- A log-slope bound implies the allocation cap by the mean value theorem. -/
theorem genericOneSlotLuceCap_of_logSlope
    {reserve weight : ℝ} {sensitivity : NNReal} {α dα : ℝ → ℝ}
    (hWeight : 0 < weight)
    (hI : EligiblePositiveC1Intensity reserve α dα)
    (hLogSlope : ∀ b, reserve ≤ b →
      dα b / α b ≤ 4 * (sensitivity : ℝ) / weight) :
    GenericOneSlotLuceCap reserve weight sensitivity α := by
  intro opponentIntensity hOpponent
  refine (convex_Ici reserve).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun b =>
      weight * (dα b / α b) *
        genericOneSlotLuceProbability α opponentIntensity b *
        (1 - genericOneSlotLuceProbability α opponentIntensity b)) ?_ ?_
  · intro b hb
    exact (hasDerivAt_genericOneSlotLuceAllocation
      (hI.1 b) (hI.2.2.1 b hb) hOpponent.le).hasDerivWithinAt
  · intro b hb
    apply NNReal.coe_le_coe.mp
    let q := genericOneSlotLuceProbability α opponentIntensity b
    let ell := dα b / α b
    have hq0 : 0 ≤ q := genericOneSlotLuceProbability_nonneg
      (hI.2.2.1 b hb) hOpponent.le
    have hq1 : q ≤ 1 := genericOneSlotLuceProbability_le_one
      (hI.2.2.1 b hb) hOpponent.le
    have hvar0 : 0 ≤ q * (1 - q) :=
      mul_nonneg hq0 (sub_nonneg.mpr hq1)
    have hvar4 : q * (1 - q) ≤ 1 / 4 :=
      quadratic_variance_le_quarter q
    have hell0 : 0 ≤ ell := div_nonneg (hI.2.2.2 b hb) (hI.2.2.1 b hb).le
    have hscaled0 : 0 ≤ weight * ell := mul_nonneg hWeight.le hell0
    have hscaled4 : weight * ell ≤ 4 * (sensitivity : ℝ) := by
      have h := (le_div_iff₀ hWeight).1 (hLogSlope b hb)
      nlinarith
    have hproduct : (weight * ell) * (q * (1 - q)) ≤ (sensitivity : ℝ) := by
      calc
        (weight * ell) * (q * (1 - q)) ≤
            (4 * (sensitivity : ℝ)) * (1 / 4) :=
          mul_le_mul hscaled4 hvar4 hvar0
            (mul_nonneg (by norm_num) sensitivity.coe_nonneg)
        _ = (sensitivity : ℝ) := by ring
    change ‖weight * ell * q * (1 - q)‖ ≤ (sensitivity : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · simpa [mul_assoc] using hproduct
    · positivity

/-- Conversely, the allocation cap recovers the sharp log-slope bound by
balancing focal and opponent intensity. -/
theorem logSlope_of_genericOneSlotLuceCap
    {reserve weight : ℝ} {sensitivity : NNReal} {α dα : ℝ → ℝ}
    (hWeight : 0 < weight)
    (hI : EligiblePositiveC1Intensity reserve α dα)
    (hCap : GenericOneSlotLuceCap reserve weight sensitivity α) :
    ∀ b, reserve ≤ b →
      dα b / α b ≤ 4 * (sensitivity : ℝ) / weight := by
  have hInterior : ∀ b, reserve < b →
      dα b / α b ≤ 4 * (sensitivity : ℝ) / weight := by
    intro b hb
    have hαPos := hI.2.2.1 b hb.le
    have hDeriv := genericOneSlotLuceAllocation_balanced_derivative
      (weight := weight) (hI.1 b) hαPos
    have hNorm := hDeriv.le_of_lipschitzOn (Ici_mem_nhds hb)
      (hCap (α b) hαPos)
    have hell0 : 0 ≤ dα b / α b :=
      div_nonneg (hI.2.2.2 b hb.le) hαPos.le
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hNorm
    apply (le_div_iff₀ hWeight).2
    nlinarith
  have hBoundary :
      dα reserve / α reserve ≤ 4 * (sensitivity : ℝ) / weight := by
    let g : ℝ → ℝ := fun b => dα b / α b
    have hαReserve := hI.2.2.1 reserve le_rfl
    have hgContinuous : ContinuousAt g reserve := by
      exact hI.2.1.continuousAt.div (hI.1 reserve).continuousAt
        (ne_of_gt hαReserve)
    let seq : ℕ → ℝ := fun n => reserve + 1 / ((n : ℝ) + 1)
    have hseq : Filter.Tendsto seq Filter.atTop (nhds reserve) := by
      have hzero :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [seq] using tendsto_const_nhds.add hzero
    have hgTendsto : Filter.Tendsto (fun n => g (seq n)) Filter.atTop
        (nhds (g reserve)) := hgContinuous.tendsto.comp hseq
    apply le_of_tendsto hgTendsto
    filter_upwards with n
    apply hInterior (seq n)
    dsimp [seq]
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hone : 0 < (1 : ℝ) / ((n : ℝ) + 1) := one_div_pos.mpr hden
    linarith
  intro b hb
  rcases hb.eq_or_lt with hEq | hLt
  · subst b
    exact hBoundary
  · exact hInterior b hLt

/-- Corollary `cor:luceclass`, equivalence half. -/
theorem genericOneSlotLuceCap_iff_logSlope
    {reserve weight : ℝ} {sensitivity : NNReal} {α dα : ℝ → ℝ}
    (hWeight : 0 < weight)
    (hI : EligiblePositiveC1Intensity reserve α dα) :
    GenericOneSlotLuceCap reserve weight sensitivity α ↔
      ∀ b, reserve ≤ b →
        dα b / α b ≤ 4 * (sensitivity : ℝ) / weight := by
  constructor
  · exact logSlope_of_genericOneSlotLuceCap hWeight hI
  · exact genericOneSlotLuceCap_of_logSlope hWeight hI

set_option maxHeartbeats 800000 in
/-- Corollary `cor:luceclass` packaged end to end: the cap is equivalent to
the log-slope constraint, and every capped intensity incurs the matched
logarithmic witness loss. -/
theorem luceClass_cap_equivalence_and_matched_premium
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (reserve base weight : ℝ) (sensitivity : NNReal) (α dα : ℝ → ℝ)
    (hWeight : 0 < weight) (hSensitivity : 0 < sensitivity)
    (hI : EligiblePositiveC1Intensity reserve α dα)
    (hMono : MonotoneOn α (Set.Ici reserve))
    (hEligibleWitness : ∀ o : Option ι, reserve ≤
      oneLeaderPLValue base (matchedPLTemperature weight sensitivity)
        (fun _ : ι => Real.log (Fintype.card ι : ℝ)) o) :
    (GenericOneSlotLuceCap reserve weight sensitivity α ↔
      ∀ b, reserve ≤ b →
        dα b / α b ≤ 4 * (sensitivity : ℝ) / weight) ∧
    (GenericOneSlotLuceCap reserve weight sensitivity α →
      weight ^ 2 * Real.log (Fintype.card ι : ℝ) /
          (8 * (sensitivity : ℝ)) ≤
        weight * base -
          oneSlotLuceWelfare weight
            (oneLeaderPLValue base (matchedPLTemperature weight sensitivity)
              (fun _ : ι => Real.log (Fintype.card ι : ℝ)))
            (fun o => α (oneLeaderPLValue base
              (matchedPLTemperature weight sensitivity)
              (fun _ : ι => Real.log (Fintype.card ι : ℝ)) o))) := by
  constructor
  · exact genericOneSlotLuceCap_iff_logSlope hWeight hI
  · intro hCap
    have hLog :=
      (genericOneSlotLuceCap_iff_logSlope hWeight hI).mp hCap
    have hEligible : EligibleC1Intensity reserve
        (matchedPLTemperature weight sensitivity) α dα := by
      refine ⟨hI.1, hMono, hI.2.2.1, ?_⟩
      intro b hb
      have h := hLog b hb
      unfold matchedPLTemperature
      have hSensReal : (0 : ℝ) < sensitivity := by exact_mod_cast hSensitivity
      field_simp [ne_of_gt hWeight, ne_of_gt hSensReal] at h ⊢
      nlinarith
    exact luceClass_matched_log_premium reserve base weight sensitivity α dα
      hWeight hSensitivity hEligible hEligibleWitness

end

end SmoothingCliff.LuceOptimality
