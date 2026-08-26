import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Moments.Basic

/-!
# Candidate-threshold mass in a thick market

This file isolates the concentration step in the bounded-i.i.d. thick-market
argument.  If `Y` is the distance of a value from the upper endpoint and
`delta` is a candidate band width, the mass contributed at that threshold is

`candidateSlack delta Y = (delta - Y)₊`.

The upper-tail lower bound gives the sharp first-moment estimate
`E[(delta-Y)₊] ≥ c * delta² / 2`.  A chord bound for the negative exponential,
followed by independence and Chernoff's inequality, yields an exponentially
small lower-tail probability for the sum.  In the paper's scaling
`delta = C / sqrt n`, the exponent is of order `sqrt n`.
-/

namespace SmoothingCliff.Racing

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators

noncomputable section

variable {Ω ι : Type*}

/-- Contribution of one draw to allocation mass at a candidate threshold. -/
def candidateSlack (delta : ℝ) (Y : Ω → ℝ) : Ω → ℝ :=
  fun ω => max (delta - Y ω) 0

theorem candidateSlack_measurable [MeasurableSpace Ω] {delta : ℝ} {Y : Ω → ℝ}
    (hY : Measurable Y) : Measurable (candidateSlack delta Y) := by
  exact (measurable_const.sub hY).max measurable_const

theorem candidateSlack_nonneg (delta : ℝ) (Y : Ω → ℝ) (ω : Ω) :
    0 ≤ candidateSlack delta Y ω := by
  exact le_max_right _ _

theorem candidateSlack_le_delta {delta : ℝ} {Y : Ω → ℝ}
    (hdelta : 0 ≤ delta) (hYnonneg : ∀ ω, 0 ≤ Y ω) (ω : Ω) :
    candidateSlack delta Y ω ≤ delta := by
  rw [candidateSlack]
  exact max_le (by linarith [hYnonneg ω]) hdelta

/-- At a positive level, the slack tail is exactly the upper-endpoint tail of
the original shortfall variable. -/
theorem candidateSlack_tail_event {delta t : ℝ} {Y : Ω → ℝ} (ht : 0 < t) :
    {ω | t ≤ candidateSlack delta Y ω} = {ω | Y ω ≤ delta - t} := by
  ext ω
  simp only [Set.mem_setOf_eq, candidateSlack]
  constructor
  · intro h
    by_cases hmain : delta - Y ω ≤ 0
    · rw [max_eq_right hmain] at h
      linarith
    · rw [max_eq_left (le_of_not_ge hmain)] at h
      linarith
  · intro h
    have hmain : t ≤ delta - Y ω := by linarith
    exact le_trans hmain (le_max_left _ _)

/-- The candidate slack is integrable because it lies in `[0, delta]`. -/
theorem candidateSlack_integrable
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {delta : ℝ} {Y : Ω → ℝ} (hdelta : 0 ≤ delta)
    (hY : Measurable Y) (hYnonneg : ∀ ω, 0 ≤ Y ω) :
    Integrable (candidateSlack delta Y) μ := by
  refine Integrable.of_bound (candidateSlack_measurable hY).aestronglyMeasurable delta ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (candidateSlack_nonneg delta Y ω)]
  exact candidateSlack_le_delta hdelta hYnonneg ω

/-- Coordinatewise candidate slacks inherit independence from the endpoint
shortfalls. -/
theorem iIndepFun_candidateSlack
    [MeasurableSpace Ω] {mu : Measure Ω} [Fintype ι]
    {delta : ℝ} {Y : ι → Ω → ℝ}
    (hIndep : iIndepFun Y mu) :
    iIndepFun (fun i => candidateSlack delta (Y i)) mu := by
  have hComp := hIndep.comp
    (fun _i : ι => fun y : ℝ => max (delta - y) 0)
    (fun _i => (measurable_const.sub measurable_id).max measurable_const)
  simpa only [candidateSlack, Function.comp_apply] using hComp

/-- A bounded upper-tail condition implies the sharp layer-cake mean bound
`E[(delta-Y)₊] ≥ c delta² / 2`. -/
theorem candidateSlack_expectation_lowerBound
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {delta c : ℝ} {Y : Ω → ℝ}
    (hdelta : 0 ≤ delta)
    (hY : Measurable Y) (hYnonneg : ∀ ω, 0 ≤ Y ω)
    (hTail : ∀ x, 0 ≤ x → x ≤ delta →
      c * x ≤ μ.real {ω | Y ω ≤ x}) :
    c * delta ^ 2 / 2 ≤ ∫ ω, candidateSlack delta Y ω ∂μ := by
  let X := candidateSlack delta Y
  have hXint : Integrable X μ :=
    candidateSlack_integrable hdelta hY hYnonneg
  have hXnonneg : 0 ≤ᵐ[μ] X :=
    ae_of_all μ (candidateSlack_nonneg delta Y)
  have hXle : X ≤ᵐ[μ] fun _ => delta :=
    ae_of_all μ (candidateSlack_le_delta hdelta hYnonneg)
  have hLayer :
      (∫ ω, X ω ∂μ) =
        ∫ t in Ioc 0 delta, μ.real {ω | t ≤ X ω} :=
    hXint.integral_eq_integral_Ioc_meas_le hXnonneg hXle
  have hLowerInt : IntegrableOn (fun t : ℝ => c * (delta - t)) (Ioc 0 delta) := by
    exact (continuous_const.mul (continuous_const.sub continuous_id)).integrableOn_Ioc
  have hTailAntitone : Antitone (fun t : ℝ => μ.real {ω | t ≤ X ω}) := by
    intro a b hab
    exact measureReal_mono fun _ h => le_trans hab h
  have hTailInt : IntegrableOn (fun t : ℝ => μ.real {ω | t ≤ X ω}) (Ioc 0 delta) := by
    refine IntegrableOn.of_bound measure_Ioc_lt_top
      hTailAntitone.measurable.aestronglyMeasurable 1 ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hPointwise : ∀ t ∈ Ioc (0 : ℝ) delta,
      c * (delta - t) ≤ μ.real {ω | t ≤ X ω} := by
    rintro t ⟨ht0, htdelta⟩
    rw [candidateSlack_tail_event ht0]
    exact hTail (delta - t) (sub_nonneg.mpr htdelta) (by linarith)
  have hIntegralLe :
      (∫ t in Ioc 0 delta, c * (delta - t)) ≤
        ∫ t in Ioc 0 delta, μ.real {ω | t ≤ X ω} :=
    setIntegral_mono_on hLowerInt hTailInt measurableSet_Ioc hPointwise
  have hLinearIntegral :
      (∫ t in Ioc 0 delta, c * (delta - t)) = c * delta ^ 2 / 2 := by
    rw [← intervalIntegral.integral_of_le hdelta]
    have hDeriv : ∀ x ∈ Set.uIcc (0 : ℝ) delta,
        HasDerivAt (fun t : ℝ => c * (delta * t - t ^ 2 / 2))
          (c * (delta - x)) x := by
      intro x _
      have hLinear : HasDerivAt (fun t : ℝ => delta * t) delta x := by
        simpa using (hasDerivAt_id x).const_mul delta
      have hSquare : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
        simpa using ((hasDerivAt_id x).pow 2).div_const 2
      exact HasDerivAt.const_mul c (hLinear.sub hSquare)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv
      ((continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable 0 delta)]
    ring
  rw [hLayer]
  rw [← hLinearIntegral]
  exact hIntegralLe

/-- The negative exponential lies below its chord between `0` and `delta`.
This is the bounded-variable inequality that replaces an appeal to Bernstein's
inequality. -/
theorem exp_negative_chord
    {delta z x : ℝ} (hdelta : 0 < delta)
    (hx0 : 0 ≤ x) (hxdelta : x ≤ delta) :
    Real.exp ((-z / delta) * x) ≤
      1 - ((1 - Real.exp (-z)) / delta) * x := by
  let q : ℝ := x / delta
  have hq0 : 0 ≤ q := div_nonneg hx0 hdelta.le
  have hq1 : q ≤ 1 := (div_le_one hdelta).2 hxdelta
  have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ))
    (Set.mem_univ (-z)) (sub_nonneg.mpr hq1) hq0 (by dsimp [q]; ring)
  dsimp [q] at hconv
  convert hconv using 1 <;> simp <;> ring

/-- A mean lower bound and bounded support give a negative-MGF bound. -/
theorem candidateSlack_mgf_le
    [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {delta c z : ℝ} {X : Ω → ℝ}
    (hdelta : 0 < delta) (hz : 0 ≤ z)
    (hX : Measurable X) (hXnonneg : ∀ ω, 0 ≤ X ω)
    (hXle : ∀ ω, X ω ≤ delta)
    (hMean : c * delta ^ 2 / 2 ≤ ∫ ω, X ω ∂μ) :
    mgf X μ (-z / delta) ≤
      Real.exp (-(c * delta / 2 * (1 - Real.exp (-z)))) := by
  let slope := (1 - Real.exp (-z)) / delta
  have hslope : 0 ≤ slope := by
    dsimp [slope]
    exact div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz))) hdelta.le
  have hXint : Integrable X μ := by
    refine Integrable.of_bound hX.aestronglyMeasurable delta ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hXnonneg ω)]
    exact hXle ω
  have hExpInt : Integrable (fun ω => Real.exp ((-z / delta) * X ω)) μ := by
    refine Integrable.of_bound ((hX.const_mul (-z / delta)).exp.aestronglyMeasurable) 1 ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hdelta.le) (hXnonneg ω))
  have hChordInt : Integrable (fun ω => 1 - slope * X ω) μ :=
    (integrable_const 1).sub (hXint.const_mul slope)
  have hPointwise : ∀ ω,
      Real.exp ((-z / delta) * X ω) ≤ 1 - slope * X ω := by
    intro ω
    simpa [slope] using exp_negative_chord hdelta (hXnonneg ω) (hXle ω)
  calc
    mgf X μ (-z / delta)
        = ∫ ω, Real.exp ((-z / delta) * X ω) ∂μ := rfl
    _ ≤ ∫ ω, (1 - slope * X ω) ∂μ :=
      integral_mono hExpInt hChordInt hPointwise
    _ = 1 - slope * (∫ ω, X ω ∂μ) := by
      rw [integral_sub, integral_const, probReal_univ, one_smul,
        integral_const_mul]
      exacts [integrable_const 1, hXint.const_mul slope]
    _ ≤ 1 - slope * (c * delta ^ 2 / 2) := by
      gcongr
    _ = 1 - (c * delta / 2 * (1 - Real.exp (-z))) := by
      dsimp [slope]
      field_simp
    _ ≤ Real.exp (-(c * delta / 2 * (1 - Real.exp (-z)))) :=
      Real.one_sub_le_exp_neg _

/-- Chernoff lower-tail bound for a finite independent family of candidate
slacks.  The parameter `q` is the retained fraction of the deterministic
first-moment lower bound. -/
theorem independent_candidateSlack_sum_lowerTail
    [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {delta c z q : ℝ} {X : ι → Ω → ℝ}
    (hdelta : 0 < delta) (hz : 0 ≤ z)
    (hX : ∀ i, Measurable (X i))
    (hXnonneg : ∀ i ω, 0 ≤ X i ω)
    (hXle : ∀ i ω, X i ω ≤ delta)
    (hMean : ∀ i, c * delta ^ 2 / 2 ≤ ∫ ω, X i ω ∂μ)
    (hIndep : iIndepFun X μ) :
    μ.real {ω | (∑ i, X i ω) ≤
        q * Fintype.card ι * c * delta ^ 2 / 2} ≤
      Real.exp (-(Fintype.card ι * c * delta / 2 *
        (1 - Real.exp (-z) - q * z))) := by
  let S : Ω → ℝ := fun ω => ∑ i, X i ω
  let t : ℝ := -z / delta
  let threshold : ℝ := q * Fintype.card ι * c * delta ^ 2 / 2
  have ht : t ≤ 0 := by
    dsimp [t]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) hdelta.le
  have hSmeas : Measurable S := by
    dsimp [S]
    fun_prop
  have hSint : Integrable (fun ω => Real.exp (t * S ω)) μ := by
    apply integrable_exp_mul_of_mem_Icc hSmeas.aemeasurable
    filter_upwards with ω
    constructor
    · exact Finset.sum_nonneg fun i _ => hXnonneg i ω
    · calc
        ∑ i, X i ω ≤ ∑ _i : ι, delta :=
          Finset.sum_le_sum fun i _ => hXle i ω
        _ = Fintype.card ι * delta := by simp
  have hmgf : mgf S μ t = ∏ i, mgf (X i) μ t := by
    have hSeq : S = ∑ i, X i := by
      ext ω
      simp [S]
    rw [hSeq]
    exact hIndep.mgf_sum hX Finset.univ (t := t)
  have hEach : ∀ i, mgf (X i) μ t ≤
      Real.exp (-(c * delta / 2 * (1 - Real.exp (-z)))) := by
    intro i
    simpa [t] using candidateSlack_mgf_le hdelta hz (hX i)
      (hXnonneg i) (hXle i) (hMean i)
  have hProd : (∏ i, mgf (X i) μ t) ≤
      ∏ _i : ι, Real.exp (-(c * delta / 2 * (1 - Real.exp (-z)))) := by
    exact Finset.prod_le_prod (fun i _ => mgf_nonneg) fun i _ => hEach i
  calc
    μ.real {ω | S ω ≤ threshold}
        ≤ Real.exp (-t * threshold) * mgf S μ t :=
      measure_le_le_exp_mul_mgf threshold ht hSint
    _ ≤ Real.exp (-t * threshold) *
        (∏ _i : ι, Real.exp (-(c * delta / 2 * (1 - Real.exp (-z))))) := by
      rw [hmgf]
      exact mul_le_mul_of_nonneg_left hProd (Real.exp_pos _).le
    _ = Real.exp (-(Fintype.card ι * c * delta / 2 *
        (1 - Real.exp (-z) - q * z))) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul, ← Real.exp_add]
      dsimp [t, threshold]
      field_simp
      congr 1
      ring

/-- Upper-endpoint tail mass plus independence implies the candidate-slack
Chernoff bound directly, without separately postulating the first moments. -/
theorem independent_candidateSlack_from_tail_sum_lowerTail
    [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {delta c z q : ℝ} {Y : ι → Ω → ℝ}
    (hdelta : 0 < delta) (hz : 0 ≤ z)
    (hY : ∀ i, Measurable (Y i))
    (hYnonneg : ∀ i ω, 0 ≤ Y i ω)
    (hTail : ∀ i x, 0 ≤ x → x ≤ delta →
      c * x ≤ μ.real {ω | Y i ω ≤ x})
    (hIndep : iIndepFun Y μ) :
    μ.real {ω | (∑ i, candidateSlack delta (Y i) ω) ≤
        q * Fintype.card ι * c * delta ^ 2 / 2} ≤
      Real.exp (-(Fintype.card ι * c * delta / 2 *
        (1 - Real.exp (-z) - q * z))) := by
  apply independent_candidateSlack_sum_lowerTail hdelta hz
  · exact fun i => candidateSlack_measurable (hY i)
  · exact fun i ω => candidateSlack_nonneg delta (Y i) ω
  · exact fun i ω => candidateSlack_le_delta hdelta.le (hYnonneg i) ω
  · intro i
    exact candidateSlack_expectation_lowerBound hdelta.le (hY i)
      (hYnonneg i) (hTail i)
  · exact iIndepFun_candidateSlack hIndep

/-! ## Candidate mass and the induced welfare-loss bound -/

/-- Allocation mass available at a proposed water-filling threshold. -/
def candidateMass [Fintype ι] (scale : ℝ) (X : ι → Ω → ℝ) : Ω → ℝ :=
  fun ω => scale * ∑ i, X i ω

theorem candidateMass_measurable
    [MeasurableSpace Ω] [Fintype ι] {scale : ℝ} {X : ι → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) : Measurable (candidateMass scale X) := by
  unfold candidateMass
  fun_prop

/-- If the target mass lies below a retained fraction of the deterministic
mean lower bound, the Chernoff estimate controls failure of the candidate
threshold.  This is the probability statement used in (M2). -/
theorem independent_candidateMass_failure_le
    [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {delta c z q scale target : ℝ} {X : ι → Ω → ℝ}
    (hdelta : 0 < delta) (hz : 0 ≤ z)
    (hscale : 0 < scale)
    (hX : ∀ i, Measurable (X i))
    (hXnonneg : ∀ i ω, 0 ≤ X i ω)
    (hXle : ∀ i ω, X i ω ≤ delta)
    (hMean : ∀ i, c * delta ^ 2 / 2 ≤ ∫ ω, X i ω ∂μ)
    (hIndep : iIndepFun X μ)
    (hTarget : target ≤
      scale * (q * Fintype.card ι * c * delta ^ 2 / 2)) :
    μ.real {ω | candidateMass scale X ω < target} ≤
      Real.exp (-(Fintype.card ι * c * delta / 2 *
        (1 - Real.exp (-z) - q * z))) := by
  have hsubset : {ω | candidateMass scale X ω < target} ⊆
      {ω | (∑ i, X i ω) ≤
        q * Fintype.card ι * c * delta ^ 2 / 2} := by
    intro ω hbad
    simp only [Set.mem_setOf_eq, candidateMass] at hbad ⊢
    have hmass : scale * ∑ i, X i ω <
        scale * (q * Fintype.card ι * c * delta ^ 2 / 2) :=
      hbad.trans_le hTarget
    nlinarith
  calc
    μ.real {ω | candidateMass scale X ω < target}
        ≤ μ.real {ω | (∑ i, X i ω) ≤
            q * Fintype.card ι * c * delta ^ 2 / 2} :=
      measureReal_mono hsubset
    _ ≤ Real.exp (-(Fintype.card ι * c * delta / 2 *
          (1 - Real.exp (-z) - q * z))) :=
      independent_candidateSlack_sum_lowerTail hdelta hz hX hXnonneg
        hXle hMean hIndep

/-- Candidate-mass failure bound specialized to endpoint shortfalls satisfying
the paper's local linear upper-tail assumption. -/
theorem independent_candidateSlackMass_failure_le
    [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {delta c z q scale target : ℝ} {Y : ι → Ω → ℝ}
    (hdelta : 0 < delta) (hz : 0 ≤ z) (hscale : 0 < scale)
    (hY : ∀ i, Measurable (Y i))
    (hYnonneg : ∀ i ω, 0 ≤ Y i ω)
    (hTail : ∀ i x, 0 ≤ x → x ≤ delta →
      c * x ≤ μ.real {ω | Y i ω ≤ x})
    (hIndep : iIndepFun Y μ)
    (hTarget : target ≤
      scale * (q * Fintype.card ι * c * delta ^ 2 / 2)) :
    μ.real {ω |
        candidateMass scale (fun i => candidateSlack delta (Y i)) ω < target} ≤
      Real.exp (-(Fintype.card ι * c * delta / 2 *
        (1 - Real.exp (-z) - q * z))) := by
  apply independent_candidateMass_failure_le hdelta hz hscale
  · exact fun i => candidateSlack_measurable (hY i)
  · exact fun i ω => candidateSlack_nonneg delta (Y i) ω
  · exact fun i ω => candidateSlack_le_delta hdelta.le (hYnonneg i) ω
  · intro i
    exact candidateSlack_expectation_lowerBound hdelta.le (hY i)
      (hYnonneg i) (hTail i)
  · exact iIndepFun_candidateSlack hIndep
  · exact hTarget

/-- Splitting according to success of a candidate threshold gives the finite
expectation estimate behind (M3).  The hypotheses isolate the two
water-filling facts: loss is at most `weight * delta` when candidate mass is
enough, and is always at most `weight * endpoint`. -/
theorem integral_loss_le_candidateMass_failure
    [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {delta endpoint weight scale target : ℝ}
    {X : ι → Ω → ℝ} {loss : Ω → ℝ}
    (hdelta : 0 ≤ delta) (hweight : 0 ≤ weight)
    (hX : ∀ i, Measurable (X i))
    (hLossInt : Integrable loss μ)
    (hLossGlobal : ∀ ω, loss ω ≤ weight * endpoint)
    (hLossGood : ∀ ω, target ≤ candidateMass scale X ω →
      loss ω ≤ weight * delta) :
    (∫ ω, loss ω ∂μ) ≤
      weight * delta + weight * endpoint *
        μ.real {ω | candidateMass scale X ω < target} := by
  let bad : Set Ω := {ω | candidateMass scale X ω < target}
  have hBadMeas : MeasurableSet bad :=
    measurableSet_lt (candidateMass_measurable hX) measurable_const
  have hRhsInt : Integrable
      (fun ω => weight * delta +
        weight * endpoint * bad.indicator (fun _ => (1 : ℝ)) ω) μ := by
    fun_prop
  have hPointwise : ∀ ω, loss ω ≤
      weight * delta +
        weight * endpoint * bad.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω
    by_cases hbad : ω ∈ bad
    · simp [hbad]
      exact (hLossGlobal ω).trans (le_add_of_nonneg_left (mul_nonneg hweight hdelta))
    · simp [hbad]
      exact hLossGood ω (le_of_not_gt hbad)
  calc
    (∫ ω, loss ω ∂μ) ≤
        ∫ ω, (weight * delta +
          weight * endpoint * bad.indicator (fun _ => (1 : ℝ)) ω) ∂μ :=
      integral_mono hLossInt hRhsInt hPointwise
    _ = weight * delta + weight * endpoint * μ.real bad := by
      have hind : (∫ ω, bad.indicator (fun _ => (1 : ℝ)) ω ∂μ) =
          μ.real bad := by
        simpa using integral_indicator_one (μ := μ) hBadMeas
      rw [integral_add, integral_const, probReal_univ, one_smul,
        integral_const_mul, hind]
      exacts [integrable_const _,
        ((integrable_const (1 : ℝ)).indicator hBadMeas).const_mul
          (weight * endpoint)]

/-- Combining candidate-mass concentration with the good/bad-event loss split
gives the paper's finite exponential remainder. -/
theorem independent_candidateMass_integral_loss_le
    [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {delta endpoint weight c z q scale target : ℝ}
    {X : ι → Ω → ℝ} {loss : Ω → ℝ}
    (hdelta : 0 < delta) (hendpoint : 0 ≤ endpoint)
    (hweight : 0 ≤ weight) (hz : 0 ≤ z)
    (hscale : 0 < scale)
    (hX : ∀ i, Measurable (X i))
    (hXnonneg : ∀ i ω, 0 ≤ X i ω)
    (hXle : ∀ i ω, X i ω ≤ delta)
    (hMean : ∀ i, c * delta ^ 2 / 2 ≤ ∫ ω, X i ω ∂μ)
    (hIndep : iIndepFun X μ)
    (hTarget : target ≤
      scale * (q * Fintype.card ι * c * delta ^ 2 / 2))
    (hLossInt : Integrable loss μ)
    (hLossGlobal : ∀ ω, loss ω ≤ weight * endpoint)
    (hLossGood : ∀ ω, target ≤ candidateMass scale X ω →
      loss ω ≤ weight * delta) :
    (∫ ω, loss ω ∂μ) ≤
      weight * delta + weight * endpoint *
        Real.exp (-(Fintype.card ι * c * delta / 2 *
          (1 - Real.exp (-z) - q * z))) := by
  have hsplit := integral_loss_le_candidateMass_failure hdelta.le
    hweight hX hLossInt hLossGlobal hLossGood
  have hfailure := independent_candidateMass_failure_le hdelta hz hscale
    hX hXnonneg hXle hMean hIndep hTarget
  calc
    (∫ ω, loss ω ∂μ) ≤ weight * delta + weight * endpoint *
        μ.real {ω | candidateMass scale X ω < target} := hsplit
    _ ≤ weight * delta + weight * endpoint *
        Real.exp (-(Fintype.card ι * c * delta / 2 *
          (1 - Real.exp (-z) - q * z))) := by
      gcongr

/-- The complete finite expected-loss bound under the local endpoint-tail
condition.  Taking `Y i` to be the distance of bidder `i` from the public
upper endpoint and `loss` to be the water-filling allocation loss gives (M3)
once the two deterministic loss bounds are supplied. -/
theorem independent_candidateSlackMass_integral_loss_le
    [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {delta endpoint weight c z q scale target : ℝ}
    {Y : ι → Ω → ℝ} {loss : Ω → ℝ}
    (hdelta : 0 < delta) (hendpoint : 0 ≤ endpoint)
    (hweight : 0 ≤ weight) (hz : 0 ≤ z) (hscale : 0 < scale)
    (hY : ∀ i, Measurable (Y i))
    (hYnonneg : ∀ i ω, 0 ≤ Y i ω)
    (hTail : ∀ i x, 0 ≤ x → x ≤ delta →
      c * x ≤ μ.real {ω | Y i ω ≤ x})
    (hIndep : iIndepFun Y μ)
    (hTarget : target ≤
      scale * (q * Fintype.card ι * c * delta ^ 2 / 2))
    (hLossInt : Integrable loss μ)
    (hLossGlobal : ∀ ω, loss ω ≤ weight * endpoint)
    (hLossGood : ∀ ω,
      target ≤ candidateMass scale (fun i => candidateSlack delta (Y i)) ω →
        loss ω ≤ weight * delta) :
    (∫ ω, loss ω ∂μ) ≤
      weight * delta + weight * endpoint *
        Real.exp (-(Fintype.card ι * c * delta / 2 *
          (1 - Real.exp (-z) - q * z))) := by
  apply independent_candidateMass_integral_loss_le
    (X := fun i => candidateSlack delta (Y i)) (target := target)
    hdelta hendpoint hweight hz hscale
  · exact fun i => candidateSlack_measurable (delta := delta) (hY i)
  · exact fun i ω => candidateSlack_nonneg delta (Y i) ω
  · exact fun i ω => candidateSlack_le_delta hdelta.le (hYnonneg i) ω
  · intro i
    exact candidateSlack_expectation_lowerBound hdelta.le (hY i)
      (hYnonneg i) (hTail i)
  · exact iIndepFun_candidateSlack hIndep
  · exact hTarget
  · exact hLossInt
  · exact hLossGlobal
  · exact hLossGood

/-! ## The square-root scaling -/

/-- An exponentially small candidate-threshold failure remains negligible
after multiplication by `sqrt n`. -/
theorem sqrt_mul_exp_neg_sqrt_tendsto_zero {rate : ℝ} (hrate : 0 < rate) :
    Tendsto
      (fun n : ℕ => Real.sqrt (n : ℝ) *
        Real.exp (-rate * Real.sqrt (n : ℝ)))
      atTop (nhds 0) := by
  have hSqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hReal := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) rate hrate
  have hComp := hReal.comp hSqrt
  simpa using hComp

/-- Epsilon form of the square-root expected-loss estimate.  It is the final
analytic step after (M3): any loss bounded by `weight*C/sqrt n` plus an
exponentially small bad-event remainder has scaled limsup at most `weight*C`.
The formulation is deliberately independent of a particular choice of sample
space at each market size. -/
theorem eventually_sqrt_mul_loss_le_of_exp_remainder
    {lossBound : ℕ → ℝ} {weight C endpoint rate : ℝ}
    (hrate : 0 < rate)
    (hBound : ∀ᶠ n : ℕ in atTop,
      lossBound n ≤ weight * C / Real.sqrt (n : ℝ) +
        weight * endpoint * Real.exp (-rate * Real.sqrt (n : ℝ)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (n : ℝ) * lossBound n ≤ weight * C + epsilon := by
  have hRemainder : Tendsto
      (fun n : ℕ => weight * endpoint *
        (Real.sqrt (n : ℝ) * Real.exp (-rate * Real.sqrt (n : ℝ))))
      atTop (nhds 0) := by
    simpa using
      (sqrt_mul_exp_neg_sqrt_tendsto_zero hrate).const_mul (weight * endpoint)
  have hSmall := (tendsto_order.mp hRemainder).2 epsilon hepsilon
  filter_upwards [hBound, hSmall, eventually_gt_atTop (0 : ℕ)] with n hn hrem hnpos
  have hSqrtPos : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 hnpos)
  calc
    Real.sqrt (n : ℝ) * lossBound n ≤
        Real.sqrt (n : ℝ) *
          (weight * C / Real.sqrt (n : ℝ) +
            weight * endpoint * Real.exp (-rate * Real.sqrt (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hn hSqrtPos.le
    _ = weight * C + weight * endpoint *
        (Real.sqrt (n : ℝ) *
          Real.exp (-rate * Real.sqrt (n : ℝ))) := by
      field_simp
    _ ≤ weight * C + epsilon := by
      linarith

end

end SmoothingCliff.Racing
