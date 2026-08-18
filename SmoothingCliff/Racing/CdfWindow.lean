import SmoothingCliff.Racing.LayerCake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The contested window of the distribution function

The expected captured band is an average of the opponent's distribution
function over a window of width one contested band, ending at the own action.
Written that way it is an integral of a bounded monotone function over a moving
interval, so it is monotone and Lipschitz with the band as constant, and its
derivative is the increment of the distribution function across the window.

That increment is what the equilibrium condition of `prop:sp_allequilibria`
(iii) pins to the cost ratio, and the resulting recursion across windows is the
lattice structure of the support.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

namespace BorelMixedStrategy

/-- The real-valued distribution function of the action law. -/
noncomputable def cdfReal (strategy : BorelMixedStrategy) (x : ℝ) : ℝ :=
  (strategy.cdf x).toReal

theorem cdf_ne_top (strategy : BorelMixedStrategy) (x : ℝ) :
    strategy.cdf x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (strategy.cdf_le_one x)

theorem cdfReal_nonneg (strategy : BorelMixedStrategy) (x : ℝ) :
    0 ≤ strategy.cdfReal x := ENNReal.toReal_nonneg

theorem cdfReal_le_one (strategy : BorelMixedStrategy) (x : ℝ) :
    strategy.cdfReal x ≤ 1 := by
  rw [cdfReal, ← ENNReal.toReal_one]
  exact ENNReal.toReal_mono ENNReal.one_ne_top (strategy.cdf_le_one x)

theorem cdfReal_mono (strategy : BorelMixedStrategy) :
    Monotone strategy.cdfReal := fun _ _ hxy =>
  ENNReal.toReal_mono (strategy.cdf_ne_top _) (strategy.cdf_mono hxy)

theorem cdfReal_of_neg (strategy : BorelMixedStrategy) {x : ℝ} (hx : x < 0) :
    strategy.cdfReal x = 0 := by
  rw [cdfReal, strategy.cdf_of_neg hx, ENNReal.toReal_zero]

theorem measurable_cdfReal (strategy : BorelMixedStrategy) :
    Measurable strategy.cdfReal :=
  strategy.cdfReal_mono.measurable

theorem intervalIntegrable_cdfReal
    (strategy : BorelMixedStrategy) (lower upper : ℝ) :
    IntervalIntegrable strategy.cdfReal volume lower upper :=
  strategy.cdfReal_mono.intervalIntegrable

end BorelMixedStrategy

/-- The distribution-function representation in the strategy's own notation. -/
theorem borelPureExpectedCapturedGap_eq_integral_cdfReal
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy)
    (action : NNReal) :
    borelPureExpectedCapturedGap gap opponent action =
      ∫ level in Set.Icc (0 : ℝ) gap,
        opponent.cdfReal ((action : ℝ) - level) := by
  rw [borelPureExpectedCapturedGap_eq_integral_cdf hgap]
  refine integral_congr_ae ?_
  filter_upwards with level
  have hset : {rival : NNReal | (rival : ℝ) + level ≤ (action : ℝ)} =
      {rival : NNReal | (rival : ℝ) ≤ (action : ℝ) - level} := by
    ext rival
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [BorelMixedStrategy.cdfReal, BorelMixedStrategy.cdf, hset]

/-- **The window form.**  The expected captured band is the integral of the
opponent's distribution function over the window of width one contested band
ending at the own action. -/
theorem borelPureExpectedCapturedGap_eq_intervalIntegral
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy)
    (action : NNReal) :
    borelPureExpectedCapturedGap gap opponent action =
      ∫ point in ((action : ℝ) - gap)..(action : ℝ), opponent.cdfReal point := by
  rw [borelPureExpectedCapturedGap_eq_integral_cdfReal hgap,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hgap,
    intervalIntegral.integral_comp_sub_left opponent.cdfReal ((action : ℝ)),
    sub_zero]

namespace BorelMixedStrategy

/-- The primitive of the distribution function, taken from the origin. -/
noncomputable def cdfPrimitive (strategy : BorelMixedStrategy) (x : ℝ) : ℝ :=
  ∫ point in (0 : ℝ)..x, strategy.cdfReal point

theorem stronglyMeasurableAtFilter_cdfReal
    (strategy : BorelMixedStrategy) (x : ℝ) :
    StronglyMeasurableAtFilter strategy.cdfReal (nhds x) volume :=
  ⟨Set.univ, Filter.univ_mem,
    strategy.measurable_cdfReal.aestronglyMeasurable⟩

/-- At a continuity point the primitive differentiates back to the
distribution function. -/
theorem hasDerivAt_cdfPrimitive (strategy : BorelMixedStrategy) {x : ℝ}
    (hx : ContinuousAt strategy.cdfReal x) :
    HasDerivAt strategy.cdfPrimitive (strategy.cdfReal x) x :=
  intervalIntegral.integral_hasDerivAt_right
    (strategy.intervalIntegrable_cdfReal 0 x)
    (strategy.stronglyMeasurableAtFilter_cdfReal x) hx

/-- The window integral as a difference of primitives. -/
theorem window_eq_primitive_sub (strategy : BorelMixedStrategy) (gap x : ℝ) :
    (∫ point in (x - gap)..x, strategy.cdfReal point) =
      strategy.cdfPrimitive x - strategy.cdfPrimitive (x - gap) := by
  rw [cdfPrimitive, cdfPrimitive, eq_sub_iff_add_eq, add_comm]
  exact intervalIntegral.integral_add_adjacent_intervals
    (strategy.intervalIntegrable_cdfReal 0 (x - gap))
    (strategy.intervalIntegrable_cdfReal (x - gap) x)

/-- **The window derivative.**  Where the distribution function is continuous
at both ends of the window, the window integral differentiates to the increment
of the distribution function across the window. -/
theorem hasDerivAt_window (strategy : BorelMixedStrategy) {gap x : ℝ}
    (hx : ContinuousAt strategy.cdfReal x)
    (hxgap : ContinuousAt strategy.cdfReal (x - gap)) :
    HasDerivAt
        (fun own : ℝ => ∫ point in (own - gap)..own, strategy.cdfReal point)
      (strategy.cdfReal x - strategy.cdfReal (x - gap)) x := by
  have hshift : HasDerivAt (fun own : ℝ => own - gap) 1 x :=
    (hasDerivAt_id x).sub_const gap
  have hleft := strategy.hasDerivAt_cdfPrimitive hx
  have hright := (strategy.hasDerivAt_cdfPrimitive hxgap).comp x hshift
  simp only [mul_one] at hright
  have hfun :
      (fun own : ℝ => ∫ point in (own - gap)..own, strategy.cdfReal point) =
        fun own : ℝ =>
          strategy.cdfPrimitive own - strategy.cdfPrimitive (own - gap) :=
    funext fun own => strategy.window_eq_primitive_sub gap own
  rw [hfun]
  exact hleft.sub hright

/-- **The window derivative holds almost everywhere.**  A monotone
distribution function has countably many discontinuities, and the window reads
it at two shifted points. -/
theorem ae_hasDerivAt_window (strategy : BorelMixedStrategy) (gap : ℝ) :
    ∀ᵐ x : ℝ, HasDerivAt
        (fun own : ℝ => ∫ point in (own - gap)..own, strategy.cdfReal point)
      (strategy.cdfReal x - strategy.cdfReal (x - gap)) x := by
  have hcount := strategy.cdfReal_mono.countable_not_continuousAt
  have hshift : ((fun x : ℝ => x - gap) ⁻¹'
      {x : ℝ | ¬ContinuousAt strategy.cdfReal x}).Countable :=
    hcount.preimage (fun _ _ h => sub_left_inj.mp h)
  have hnull := (hcount.union hshift).measure_zero volume
  have hae : ∀ᵐ x : ℝ, x ∉ {x : ℝ | ¬ContinuousAt strategy.cdfReal x} ∪
      (fun x : ℝ => x - gap) ⁻¹' {x : ℝ | ¬ContinuousAt strategy.cdfReal x} :=
    MeasureTheory.measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [hae] with x hx
  simp only [Set.mem_union, Set.mem_preimage, Set.mem_setOf_eq, not_or,
    not_not] at hx
  exact strategy.hasDerivAt_window hx.1 hx.2

end BorelMixedStrategy

end SmoothingCliff.Racing
