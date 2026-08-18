import SmoothingCliff.Racing.PayoffIdentity

/-!
# The layer-cake form of the captured band

Entry point to the support analysis behind part (iii) of
`prop:sp_allequilibria`.  The paper writes the expected captured band as an
integral of the opponent's distribution function over one contested band and
reads the equilibrium support recursion off the resulting derivative.  The
identity behind that display is the layer-cake one proved here: the captured
band is the size of the set of levels the winning margin clears, cut off at the
contested band.

Stating it as a measure rather than an interval integral keeps the proof to two
set identities.  Turning it into the integral of the distribution function is a
Fubini exchange against the opponent's law, which is the next step.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

/-- The levels a nonpositive margin clears within the band are a single point
at most. -/
theorem levelSet_subset_singleton {gap margin : ℝ} (hmargin : margin ≤ 0) :
    Set.Icc (0 : ℝ) gap ∩ Set.Iic margin ⊆ {0} := by
  rintro x ⟨hx, hxm⟩
  have hlow : (0 : ℝ) ≤ x := hx.1
  have hhigh : x ≤ 0 := le_trans hxm hmargin
  exact le_antisymm hhigh hlow

/-- The levels a nonnegative margin clears within the band form an initial
segment. -/
theorem levelSet_eq_Icc {gap margin : ℝ} :
    Set.Icc (0 : ℝ) gap ∩ Set.Iic margin = Set.Icc 0 (min gap margin) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, le_min_iff]
  constructor
  · rintro ⟨⟨hlow, hhigh⟩, hxm⟩
    exact ⟨hlow, hhigh, hxm⟩
  · rintro ⟨hlow, hhigh, hxm⟩
    exact ⟨⟨hlow, hhigh⟩, hxm⟩

/-- **The layer cake.**  The captured band is the size of the set of levels the
winning margin clears, cut off at the contested band. -/
theorem strictPriorityCapturedGap_eq_measureReal
    {gap own rival : ℝ} (hgap : 0 ≤ gap) :
    (volume (Set.Icc (0 : ℝ) gap ∩ Set.Iic (own - rival))).toReal =
      strictPriorityCapturedGap gap own rival := by
  rcases le_total (own - rival) 0 with hmargin | hmargin
  · have hnull : volume (Set.Icc (0 : ℝ) gap ∩ Set.Iic (own - rival)) = 0 :=
      measure_mono_null (levelSet_subset_singleton hmargin)
        (measure_singleton 0)
    rw [hnull, strictPriorityCapturedGap, max_eq_right hmargin,
      min_eq_left hgap]
    simp
  · rw [levelSet_eq_Icc, Real.volume_Icc,
      strictPriorityCapturedGap, max_eq_left hmargin, min_comm gap (own - rival),
      sub_zero]
    exact ENNReal.toReal_ofReal (le_min hmargin hgap)

end SmoothingCliff.Racing

namespace SmoothingCliff.Racing

open MeasureTheory

/-! ### From the layer cake to the distribution function

The captured band is the measure of a level set, so it is the integral of an
indicator, and Tonelli exchanges that integral with the expectation over the
opponent's law.  The inner integral is then the opponent's distribution
function, which is the representation the support recursion differentiates. -/

/-- The captured band as an integral of an indicator over the levels. -/
theorem strictPriorityCapturedGap_eq_integral_indicator
    {gap own rival : ℝ} (hgap : 0 ≤ gap) :
    ∫ level in Set.Icc (0 : ℝ) gap,
        (Set.Iic (own - rival)).indicator (fun _ => (1 : ℝ)) level =
      strictPriorityCapturedGap gap own rival := by
  rw [integral_indicator measurableSet_Iic, MeasureTheory.integral_const,
    smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
    Measure.restrict_apply measurableSet_Iic, Set.inter_comm]
  exact strictPriorityCapturedGap_eq_measureReal hgap

/-- The joint level set is measurable: it is a half-space for the sum. -/
theorem measurableSet_jointLevelSet (action : ℝ) :
    MeasurableSet {profile : NNReal × ℝ |
      (profile.1 : ℝ) + profile.2 ≤ action} := by
  have hmeas : Measurable fun profile : NNReal × ℝ =>
      (profile.1 : ℝ) + profile.2 :=
    (measurable_fst.coe_nnreal_real).add measurable_snd
  exact hmeas measurableSet_Iic

/-- The indicator of the joint level set, uncurried. -/
theorem indicator_uncurry_eq (action : ℝ) (rival : NNReal) (level : ℝ) :
    (Set.Iic (action - (rival : ℝ))).indicator (fun _ => (1 : ℝ)) level =
      {profile : NNReal × ℝ | (profile.1 : ℝ) + profile.2 ≤ action}.indicator
        (fun _ => (1 : ℝ)) (rival, level) := by
  have hiff : (level ≤ action - (rival : ℝ)) ↔ ((rival : ℝ) + level ≤ action) := by
    constructor <;> intro h <;> linarith
  simp only [Set.indicator_apply, Set.mem_Iic, Set.mem_setOf_eq, hiff]

/-- The pointwise integrand is nonnegative, which is what Tonelli needs. -/
theorem indicator_levelSet_nonneg
    (margin level : ℝ) :
    0 ≤ (Set.Iic margin).indicator (fun _ => (1 : ℝ)) level :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) level

/-- The level measure is finite, which is what makes the indicator integrable
on the product. -/
instance isFiniteMeasure_levelRestrict (gap : ℝ) :
    IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) gap)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-- **The distribution-function representation.**  The expected captured band
is the integral, over one contested band of levels, of the opponent's
probability of falling below the remaining margin. -/
theorem borelPureExpectedCapturedGap_eq_integral_cdf
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy)
    (action : NNReal) :
    borelPureExpectedCapturedGap gap opponent action =
      ∫ level in Set.Icc (0 : ℝ) gap,
        ((opponent.law : Measure NNReal)
          {rival : NNReal | (rival : ℝ) + level ≤ (action : ℝ)}).toReal := by
  classical
  have hmeasSet := measurableSet_jointLevelSet (action : ℝ)
  have hintegrable :
      Integrable
        (Function.uncurry fun (rival : NNReal) (level : ℝ) =>
          {profile : NNReal × ℝ |
              (profile.1 : ℝ) + profile.2 ≤ (action : ℝ)}.indicator
            (fun _ => (1 : ℝ)) (rival, level))
        ((opponent.law : Measure NNReal).prod
          (volume.restrict (Set.Icc (0 : ℝ) gap))) := by
    have hconst : Integrable (fun _ : NNReal × ℝ => (1 : ℝ))
        ((opponent.law : Measure NNReal).prod
          (volume.restrict (Set.Icc (0 : ℝ) gap))) := integrable_const 1
    simpa [Function.uncurry] using hconst.indicator hmeasSet
  have hstep : borelPureExpectedCapturedGap gap opponent action =
      ∫ rival : NNReal, (∫ level : ℝ in Set.Icc (0 : ℝ) gap,
        {profile : NNReal × ℝ |
            (profile.1 : ℝ) + profile.2 ≤ (action : ℝ)}.indicator
          (fun _ => (1 : ℝ)) (rival, level))
        ∂(opponent.law : Measure NNReal) := by
    rw [borelPureExpectedCapturedGap]
    refine integral_congr_ae ?_
    filter_upwards with rival
    rw [← strictPriorityCapturedGap_eq_integral_indicator hgap]
    refine integral_congr_ae ?_
    filter_upwards with level
    exact indicator_uncurry_eq (action : ℝ) rival level
  rw [hstep, integral_integral_swap hintegrable]
  refine integral_congr_ae ?_
  filter_upwards with level
  have hmeas : MeasurableSet
      {rival : NNReal | (rival : ℝ) + level ≤ (action : ℝ)} :=
    (measurable_coe_nnreal_real.add measurable_const) measurableSet_Iic
  rw [← measureReal_def, ← integral_indicator_one hmeas]
  refine integral_congr_ae ?_
  filter_upwards with rival
  simp [Set.indicator_apply, Set.mem_setOf_eq]

end SmoothingCliff.Racing
