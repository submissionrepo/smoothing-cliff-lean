import SmoothingCliff.Racing.ZeroPayoffFloor

/-!
# The payoff identity of the strict-priority race

Exactly one of the two players captures band, and the amount is the winning
margin capped at the contested band.  So the two captured amounts sum to the
capped absolute difference, and the two payoffs sum to the allocated contested
surplus minus the dissipation.

This is the identity the paper uses to read dissipation off the payoffs, both
in the lattice equilibrium and in the classification of the whole equilibrium
set.  It is stated here on its own because it needs none of the support
analysis that the positive-payoff classification requires.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

/-- **The pointwise identity.**  The two captured bands sum to the capped
absolute difference of the investments. -/
theorem strictPriorityCapturedGap_add_symm
    {gap own rival : ℝ} (hgap : 0 ≤ gap) :
    strictPriorityCapturedGap gap own rival +
        strictPriorityCapturedGap gap rival own =
      min |own - rival| gap := by
  rcases le_total rival own with hle | hle
  · rw [strictPriorityCapturedGap, strictPriorityCapturedGap,
      max_eq_left (by linarith : (0 : ℝ) ≤ own - rival),
      max_eq_right (by linarith : rival - own ≤ 0),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ own - rival),
      min_eq_left hgap]
    ring
  · rw [strictPriorityCapturedGap, strictPriorityCapturedGap,
      max_eq_right (by linarith : own - rival ≤ 0),
      max_eq_left (by linarith : (0 : ℝ) ≤ rival - own),
      abs_of_nonpos (by linarith : own - rival ≤ 0), neg_sub,
      min_eq_left hgap]
    exact zero_add _

/-- The capped absolute difference never exceeds the contested band. -/
theorem min_abs_le_gap {gap own rival : ℝ} :
    min |own - rival| gap ≤ gap :=
  min_le_right _ _

/-- **The payoff identity in expectation.**  With independent draws, the two
expected captured bands sum to the expected capped absolute difference. -/
theorem borelExpectedCapturedGap_add_symm
    {gap : ℝ} (hgap : 0 ≤ gap) (first second : BorelMixedStrategy)
    (hIntegrableFirst : Integrable
      (fun profile : NNReal × NNReal =>
        strictPriorityCapturedGap gap (profile.1 : ℝ) (profile.2 : ℝ))
      ((first.law : Measure NNReal).prod (second.law : Measure NNReal)))
    (hIntegrableSecond : Integrable
      (fun profile : NNReal × NNReal =>
        strictPriorityCapturedGap gap (profile.2 : ℝ) (profile.1 : ℝ))
      ((first.law : Measure NNReal).prod (second.law : Measure NNReal))) :
    borelExpectedCapturedGap gap first second +
        borelExpectedCapturedGap gap second first =
      ∫ profile : NNReal × NNReal,
        min |(profile.1 : ℝ) - (profile.2 : ℝ)| gap
        ∂((first.law : Measure NNReal).prod (second.law : Measure NNReal)) := by
  have hswap : borelExpectedCapturedGap gap second first =
      ∫ profile : NNReal × NNReal,
        strictPriorityCapturedGap gap (profile.2 : ℝ) (profile.1 : ℝ)
        ∂((first.law : Measure NNReal).prod (second.law : Measure NNReal)) := by
    rw [borelExpectedCapturedGap]
    exact (integral_prod_swap _).symm
  rw [borelExpectedCapturedGap, hswap, ← integral_add hIntegrableFirst
    hIntegrableSecond]
  refine integral_congr_ae ?_
  filter_upwards with profile
  exact strictPriorityCapturedGap_add_symm hgap

/-- **The payoff identity.**  The two expected payoffs sum to the allocated
contested surplus minus the dissipation. -/
theorem borelExpectedPayoff_add_symm
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (first second : BorelMixedStrategy)
    (hIntegrableFirst : Integrable
      (fun profile : NNReal × NNReal =>
        strictPriorityCapturedGap gap (profile.1 : ℝ) (profile.2 : ℝ))
      ((first.law : Measure NNReal).prod (second.law : Measure NNReal)))
    (hIntegrableSecond : Integrable
      (fun profile : NNReal × NNReal =>
        strictPriorityCapturedGap gap (profile.2 : ℝ) (profile.1 : ℝ))
      ((first.law : Measure NNReal).prod (second.law : Measure NNReal))) :
    borelExpectedPayoff slotWeight gap marginalCost first second +
        borelExpectedPayoff slotWeight gap marginalCost second first =
      slotWeight *
          (∫ profile : NNReal × NNReal,
            min |(profile.1 : ℝ) - (profile.2 : ℝ)| gap
            ∂((first.law : Measure NNReal).prod
              (second.law : Measure NNReal))) -
        borelExpectedDissipation marginalCost first second := by
  rw [borelExpectedPayoff, borelExpectedPayoff, borelExpectedDissipation,
    ← borelExpectedCapturedGap_add_symm hgap first second hIntegrableFirst
      hIntegrableSecond]
  ring

end SmoothingCliff.Racing
