import SmoothingCliff.Mechanism.Axiomatization
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Scale invariance selects the Tullock family

Formal target: Remark `rem:tullock` in `Smoothing_the_Cliff_ITCS.tex`.

With a positive reserve, replacing translation invariance by invariance to
common rescalings of eligible bids selects the power-form contest success
function instead of the exponential.  The paper's argument is the same Cauchy
functional equation applied after a logarithm, and that is exactly how it is
formalized here: rescaling bids is translating log-bids, so the intensity
composed with the exponential falls under
`translation_ratio_invariance_iff_exponential`, and undoing the logarithm turns
the exponential form into a power.
-/

namespace SmoothingCliff.Mechanism

noncomputable section

/-- The intensity read as a function of the log-bid. -/
def logBidIntensity (alpha : ℝ → ℝ) : ℝ → ℝ :=
  fun t => alpha (Real.exp t)

/-- Common rescalings of eligible bids leave every pairwise Luce odds ratio
unchanged.  Eligible bids are written as `reserve * exp x` with `x` a
nonnegative log-offset, so a common rescaling by `exp c` is a common shift of
the offsets. -/
def ScaleRatioInvariant (reserve : ℝ) (alpha : ℝ → ℝ) : Prop :=
  TranslationRatioInvariant (Real.log reserve) (logBidIntensity alpha)

/-- The power form on the eligible region. -/
def PowerOnEligible (reserve : ℝ) (alpha : ℝ → ℝ) : Prop :=
  ∃ c0 tildeTau : ℝ, 0 < c0 ∧ 0 < tildeTau ∧
    ∀ x : NNReal,
      alpha (reserve * Real.exp (x : ℝ)) =
        c0 * (reserve * Real.exp (x : ℝ)) ^ (1 / tildeTau : ℝ)

/-- Eligible bids in log coordinates. -/
theorem exp_log_offset {reserve : ℝ} (hReserve : 0 < reserve) (x : NNReal) :
    Real.exp (Real.log reserve + (x : ℝ)) = reserve * Real.exp (x : ℝ) := by
  rw [Real.exp_add, Real.exp_log hReserve]

/-- **Remark `rem:tullock`.**  Within the sequential Luce class with a positive
reserve, invariance to common rescalings of eligible bids is equivalent to the
power-form intensity. -/
theorem scale_ratio_invariance_iff_power
    {reserve : ℝ} {alpha : ℝ → ℝ} (hReserve : 0 < reserve)
    (hpos : ∀ x : NNReal,
      0 < EligibleIntensity (Real.log reserve) (logBidIntensity alpha) x)
    (hcont : Continuous
      (EligibleIntensity (Real.log reserve) (logBidIntensity alpha)))
    (hstrict : StrictMono
      (EligibleIntensity (Real.log reserve) (logBidIntensity alpha))) :
    ScaleRatioInvariant reserve alpha ↔ PowerOnEligible reserve alpha := by
  rw [ScaleRatioInvariant,
    translation_ratio_invariance_iff_exponential hpos hcont hstrict]
  constructor
  · rintro ⟨c0, tau, hc0, htau, hform⟩
    refine ⟨c0, tau, hc0, htau, fun x => ?_⟩
    have hx := hform x
    simp only [EligibleIntensity, logBidIntensity] at hx
    rw [exp_log_offset hReserve x] at hx
    rw [hx]
    congr 1
    rw [Real.rpow_def_of_pos (by positivity), ← exp_log_offset hReserve x,
      Real.log_exp]
    ring_nf
  · rintro ⟨c0, tildeTau, hc0, hTildeTau, hform⟩
    refine ⟨c0, tildeTau, hc0, hTildeTau, fun x => ?_⟩
    have hx := hform x
    simp only [EligibleIntensity, logBidIntensity]
    rw [exp_log_offset hReserve x, hx]
    congr 1
    rw [Real.rpow_def_of_pos (by positivity), ← exp_log_offset hReserve x,
      Real.log_exp]
    ring_nf

end

end SmoothingCliff.Mechanism
