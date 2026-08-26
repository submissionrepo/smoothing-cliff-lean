import SmoothingCliff.Racing.HeterogeneousSelectionFreeFloor
import SmoothingCliff.Racing.ThickMarketWaterFillingLoss
import SmoothingCliff.Racing.ThickMarketWindowLimit
import SmoothingCliff.Racing.ThickMarketNetSurplusLimit

/-!
# Unconditional domination in a thick market

This file joins the two sides of the thick-market comparison.  The canonical
water-filling loss vanishes at the square-root rate proved in
`ThickMarketWaterFillingLoss`.  On the strict-priority side, the pointwise
selection-free window floor may be integrated against any measurable
equilibrium selection.  Its affine part depends only on the expected top two
order statistics and converges to a positive endpoint constant.

The final theorem is deliberately stated at the measurable-selection
interface: the selected equilibrium enters only through an integrable
dissipation function satisfying the pointwise floor.  Thus no equilibrium
classification or choice of a particular equilibrium is used.
-/

namespace SmoothingCliff.Racing

open MeasureTheory Set Filter Topology
open SmoothingCliff.Frontier

noncomputable section

/-- The expectation-level affine window floor.  It is the integral of the
untruncated window expression, as shown below. -/
def expectedHeterogeneousWindowRawFloor
    (F : Measure ℝ) (slotWeight q varsigma : ℝ) (n : ℕ) : ℝ :=
  slotWeight * varsigma / 2 *
    heterogeneousShiftedWindowBracket q varsigma
      (expectedRunnerUp F n) (expectedProfileTop F n)

theorem integrable_heterogeneousWindowRawFloor
    (F : Measure ℝ) [IsProbabilityMeasure F]
    {endpoint slotWeight q varsigma : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) (n : ℕ) :
    Integrable
      (fun profile : Fin (n + 2) → ℝ =>
        slotWeight * varsigma / 2 *
          heterogeneousShiftedWindowBracket q varsigma
            (runnerUp (ι := Fin (n + 2)) (by simp) profile)
            (profileTop (ι := Fin (n + 2)) profile))
      (profileLaw (ι := Fin (n + 2)) F) := by
  have hrunner := integrable_runnerUp (ι := Fin (n + 2))
    (by simp) F hSupport
  have htop := integrable_profileTop (ι := Fin (n + 2)) F hSupport
  have hgap := htop.sub hrunner
  have hbracket : Integrable
      (fun profile : Fin (n + 2) → ℝ =>
        heterogeneousShiftedWindowBracket q varsigma
          (runnerUp (ι := Fin (n + 2)) (by simp) profile)
          (profileTop (ι := Fin (n + 2)) profile))
      (profileLaw (ι := Fin (n + 2)) F) := by
    unfold heterogeneousShiftedWindowBracket
    exact (hrunner.mul_const (2 - varsigma - q)).sub
      (hgap.const_mul (2 * q))
  exact hbracket.const_mul (slotWeight * varsigma / 2)

/-- The integral of the affine window expression equals the same expression
evaluated at the expected runner-up and expected leader. -/
theorem integral_heterogeneousWindowRawFloor_eq
    (F : Measure ℝ) [IsProbabilityMeasure F]
    {endpoint slotWeight q varsigma : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint) (n : ℕ) :
    (∫ profile : Fin (n + 2) → ℝ,
        slotWeight * varsigma / 2 *
          heterogeneousShiftedWindowBracket q varsigma
            (runnerUp (ι := Fin (n + 2)) (by simp) profile)
            (profileTop (ι := Fin (n + 2)) profile)
      ∂profileLaw (ι := Fin (n + 2)) F) =
      expectedHeterogeneousWindowRawFloor F slotWeight q varsigma n := by
  have hrunner := integrable_runnerUp (ι := Fin (n + 2))
    (by simp) F hSupport
  have htop := integrable_profileTop (ι := Fin (n + 2)) F hSupport
  have hfirst : Integrable
      (fun profile : Fin (n + 2) → ℝ =>
        runnerUp (ι := Fin (n + 2)) (by simp) profile *
          (2 - varsigma - q))
      (profileLaw (ι := Fin (n + 2)) F) :=
    hrunner.mul_const (2 - varsigma - q)
  have hsecond : Integrable
      (fun profile : Fin (n + 2) → ℝ =>
        2 * q * (profileTop (ι := Fin (n + 2)) profile -
          runnerUp (ι := Fin (n + 2)) (by simp) profile))
      (profileLaw (ι := Fin (n + 2)) F) :=
    (htop.sub hrunner).const_mul (2 * q)
  unfold expectedHeterogeneousWindowRawFloor
  rw [integral_const_mul]
  unfold heterogeneousShiftedWindowBracket
  rw [integral_sub hfirst hsecond, integral_mul_const,
    integral_const_mul, integral_sub htop hrunner]
  rfl

/-- Integrating any pointwise dissipation quantity above the positive-part
window floor yields the affine expectation-level lower bound. -/
theorem expectedHeterogeneousWindowRawFloor_le_integral_dissipation
    (F : Measure ℝ) [IsProbabilityMeasure F]
    {endpoint slotWeight q varsigma : ℝ}
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint)
    (hweight : 0 ≤ slotWeight) (hvarsigma : 0 ≤ varsigma)
    (n : ℕ) (dissipation : (Fin (n + 2) → ℝ) → ℝ)
    (hDissipationIntegrable : Integrable dissipation
      (profileLaw (ι := Fin (n + 2)) F))
    (hPointwise : ∀ᵐ profile ∂profileLaw (ι := Fin (n + 2)) F,
      heterogeneousShiftedWindowFloor slotWeight q varsigma
          (runnerUp (ι := Fin (n + 2)) (by simp) profile)
          (profileTop (ι := Fin (n + 2)) profile) ≤
        dissipation profile) :
    expectedHeterogeneousWindowRawFloor F slotWeight q varsigma n ≤
      ∫ profile, dissipation profile
        ∂profileLaw (ι := Fin (n + 2)) F := by
  have hRawIntegrable := integrable_heterogeneousWindowRawFloor
    F (slotWeight := slotWeight) (q := q) (varsigma := varsigma)
      hSupport n
  rw [← integral_heterogeneousWindowRawFloor_eq F hSupport n]
  apply integral_mono_ae hRawIntegrable hDissipationIntegrable
  filter_upwards [hPointwise] with profile hfloor
  have hprefactor : 0 ≤ slotWeight * varsigma / 2 := by positivity
  have hrawLeFloor :
      slotWeight * varsigma / 2 *
          heterogeneousShiftedWindowBracket q varsigma
            (runnerUp (ι := Fin (n + 2)) (by simp) profile)
            (profileTop (ι := Fin (n + 2)) profile) ≤
        heterogeneousShiftedWindowFloor slotWeight q varsigma
          (runnerUp (ι := Fin (n + 2)) (by simp) profile)
          (profileTop (ι := Fin (n + 2)) profile) := by
    unfold heterogeneousShiftedWindowFloor
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) hprefactor
  exact hrawLeFloor.trans hfloor

/-- The expectation-level affine window floor converges to the common-endpoint
constant. -/
theorem expectedHeterogeneousWindowRawFloor_tendsto_endpoint
    (F : Measure ℝ) [IsProbabilityMeasure F]
    {endpoint tailConstant tailRadius slotWeight q varsigma : ℝ}
    (hTailConstant : 0 < tailConstant) (hTailRadius : 0 < tailRadius)
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint)
    (hTail : ∀ epsilon, 0 < epsilon → epsilon ≤ tailRadius →
      tailConstant * epsilon ≤ F.real (Set.Ici (endpoint - epsilon))) :
    Tendsto
      (expectedHeterogeneousWindowRawFloor F slotWeight q varsigma)
      atTop
      (𝓝 (slotWeight * endpoint / 2 *
        (varsigma * (2 - varsigma - q)))) := by
  have hrunner := expectedRunnerUp_tendsto_endpoint F
    hTailConstant hTailRadius hSupport hTail
  have hleader := expectedProfileTop_tendsto_endpoint F
    hTailConstant hTailRadius hSupport hTail
  have hbracket := heterogeneousShiftedWindowBracket_tendsto_endpoint
    (q := q) (varsigma := varsigma) hrunner hleader
  have hscaled := hbracket.const_mul (slotWeight * varsigma / 2)
  change Tendsto
    (fun n => slotWeight * varsigma / 2 *
      heterogeneousShiftedWindowBracket q varsigma
        (expectedRunnerUp F n) (expectedProfileTop F n))
    atTop
    (𝓝 (slotWeight * endpoint / 2 *
      (varsigma * (2 - varsigma - q))))
  convert hscaled using 1
  ring_nf

/-- Final thick-market comparison.  For every market size, `dissipation n`
may be the expenditure generated by an arbitrary measurable strict-priority
equilibrium selection.  The only equilibrium input is its pointwise
selection-free window floor.  Any expected net-surplus gain above expected
dissipation minus canonical water-filling loss is eventually positive and
eventually exceeds every strict level below the endpoint floor. -/
theorem eventually_thickMarket_netSurplusGain_pos
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (weight sensitivity : NNReal)
    (hweight : 0 < weight) (hsensitivity : 0 < sensitivity)
    {endpoint tailConstant tailRadius q varsigma : ℝ}
    (hendpoint : 0 < endpoint)
    (hTailConstant : 0 < tailConstant) (hTailRadius : 0 < tailRadius)
    (hSupport : ∀ᵐ value ∂F, value ∈ Set.Icc 0 endpoint)
    (hTail : ∀ epsilon, 0 < epsilon → epsilon ≤ tailRadius →
      tailConstant * epsilon ≤ F.real (Set.Ici (endpoint - epsilon)))
    (hvarsigma : 0 < varsigma)
    (hcoefficient : 0 < 2 - varsigma - q)
    (dissipation : (n : ℕ) → (Fin (n + 2) → ℝ) → ℝ)
    (hDissipationIntegrable : ∀ n, Integrable (dissipation n)
      (profileLaw (ι := Fin (n + 2)) F))
    (hPointwise : ∀ n,
      ∀ᵐ profile ∂profileLaw (ι := Fin (n + 2)) F,
        heterogeneousShiftedWindowFloor (weight : ℝ) q varsigma
            (runnerUp (ι := Fin (n + 2)) (by simp) profile)
            (profileTop (ι := Fin (n + 2)) profile) ≤
          dissipation n profile)
    (gain : ℕ → ℝ)
    (hgain : ∀ n,
      (∫ profile, dissipation n profile
          ∂profileLaw (ι := Fin (n + 2)) F) -
          expectedThickMarketWaterFillingLoss
            F weight sensitivity hsensitivity endpoint n ≤
        gain n) :
    (∀ᶠ n in atTop, 0 < gain n) ∧
      ∀ epsilon, 0 < epsilon →
        ∀ᶠ n in atTop,
          (weight : ℝ) * endpoint / 2 *
                (varsigma * (2 - varsigma - q)) - epsilon ≤
            gain n := by
  have hfloor := expectedHeterogeneousWindowRawFloor_tendsto_endpoint
    F hTailConstant hTailRadius hSupport hTail
      (slotWeight := (weight : ℝ)) (q := q) (varsigma := varsigma)
  have hTailNonneg : ∀ x, 0 ≤ x → x ≤ tailRadius →
      tailConstant * x ≤ F.real (Set.Ici (endpoint - x)) := by
    intro x hx hxradius
    rcases hx.eq_or_lt with rfl | hxpos
    · simp
    · exact hTail x hxpos hxradius
  have hloss := expectedThickMarketWaterFillingLoss_tendsto_zero
    F weight sensitivity hweight hsensitivity hendpoint hTailConstant
      hTailRadius hTailNonneg
  have hweightReal : (0 : ℝ) < (weight : ℝ) := by exact_mod_cast hweight
  have hlimit : 0 < (weight : ℝ) * endpoint / 2 *
      (varsigma * (2 - varsigma - q)) := by positivity
  have hrawGain : ∀ n,
      expectedHeterogeneousWindowRawFloor F (weight : ℝ) q varsigma n -
          expectedThickMarketWaterFillingLoss
            F weight sensitivity hsensitivity endpoint n ≤
        gain n := by
    intro n
    have hfloorLe :=
      expectedHeterogeneousWindowRawFloor_le_integral_dissipation
        F hSupport hweightReal.le hvarsigma.le n (dissipation n)
          (hDissipationIntegrable n) (hPointwise n)
    exact (sub_le_sub_right hfloorLe _).trans (hgain n)
  constructor
  · exact eventually_netSurplusGain_pos hfloor hloss hlimit hrawGain
  · intro epsilon hepsilon
    exact eventually_netSurplusGain_ge_limit_sub_epsilon
      hfloor hloss hrawGain hepsilon

end

end SmoothingCliff.Racing
