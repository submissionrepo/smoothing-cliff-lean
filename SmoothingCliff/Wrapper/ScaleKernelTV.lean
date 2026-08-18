import SmoothingCliff.Wrapper.Resampling
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The scale-family resampling kernel and its total-variation sensitivity

The remark formalized here resamples an eligible report as `χ = b · V`, with `V`
drawn from a fixed density `g` on `[0,1)`, and states that half the
total-variation norm of the law's derivative in `b` is `c_g / b`, where
`c_g = (A + g(1⁻))/2` and `A = ∫₀¹ |g u + u g'(u)| du`; publishing the pair
`(μ, g)` then publishes the deployed sensitivity
`(1 - μ) w₁/(e τ) + μ w₁ c_g / r` on the eligible region.

The kernel is `scaleKernel`, a `ProbabilityMeasure`-valued map, and the
distance used throughout is `halfL1`, half the `L¹` distance of the two
densities; `abs_integral_sub_le_halfL1` turns it into the
bounded-test-function dual form that `TVLipschitzKernel` and
`wrapper_certificate` consume.

Main results, in the order they are built:

* `l1_scaleDensity_decomposition`: the exact change of variables, splitting
  the `L¹` distance into an overlap term on `[0, b/b')` and a boundary term on
  `[b/b', 1)`.
* `overlap_le_varA_mul_log`: the overlap term is at most `A log(b'/b)`.
* `boundary_eq_inv_integral` and `boundary_le`: the boundary term as an
  integral over the scale ratio, and its bound `M (1 - b/b')` for any `M`
  dominating `g` on `[b/b', 1)`.
* `halfL1_scaleDensity_le`: the finite bound `(A + M)/2 · (b' - b)/b`, with
  `halfL1_scaleDensity_le_reserve` its symmetric, reserve-normalized form.
* `halfL1_scaleDensity_le_log` and `halfL1_scaleDensity_le_cg`: the remark's
  displayed inequality, first as `c_g log(b'/b)` and then as `c_g (b' - b)/r`,
  with no hypothesis the printed remark does not already carry.
* `eventually_halfL1_le_local_rate` and `eventually_halfL1_div_le_local_rate`:
  the local rate `c_g / b`, with no extra hypothesis.
* `uniformGen` and `halfL1_uniform`: for `g ≡ 1` one computes `A = 1`,
  `g(1⁻) = 1`, `c_g = 1` and the exact distance `(b' - b)/b'`;
  `tendsto_halfL1_uniform_div` shows the local rate is attained, and
  `uniform_not_le_varA_only` refutes the boundary-free constant `A/2`.
* `tvLipschitzKernel_scaleKernel` and `wrapper_certificate_scaleKernel`: the
  kernel premise of `wrapper_certificate` and the deployed certificate it
  yields.

Two observations about the printed remark.

*The displayed finite bound needs a hypothesis the remark does not carry.*
The boundary term of the decomposition is `sup_{[b/b',1)} g · (1 - b/b')`, not
`g(1⁻) · (1 - b/b')`; the two agree only when `g` is dominated near `1` by its
endpoint value, for instance when `g` is nondecreasing there.  So
`halfL1_scaleDensity_le_cg` and `tvLipschitzKernel_scaleKernel_cg` take that
domination as an explicit hypothesis, and the unconditional statement is
`halfL1_scaleDensity_le`, with the supremum `M` in place of `g(1⁻)`.  No
counterexample to the displayed inequality is claimed: what is established is
that the remark's argument does not deliver it without the extra assumption.
The local claim `c_g / b` is correct as printed and is proved here without it.

*The boundary term is not negligible.*  For the uniform generator it is
exactly half of the total variation, so replacing `c_g` by `A/2` fails already
at `b = 1`, `b' = 3/2`, where half the total variation is `1/3 > 1/4`.

A `ScaleGen` is differentiable on all of `ℝ`, so the endpoint limit `g(1⁻)`
is the value `g 1`; `ScaleGen.tendsto_endpoint` records this.
-/

namespace SmoothingCliff.Wrapper

open MeasureTheory Set
open scoped ENNReal

/-! ## The generator -/

/-- The paper's generator `g`. -/
structure ScaleGen where
  /-- the density on `[0,1)` -/
  g : ℝ → ℝ
  /-- its derivative -/
  g' : ℝ → ℝ
  hasDerivAt' : ∀ x, HasDerivAt g (g' x) x
  continuous_g' : Continuous g'
  nonneg' : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ g u
  normalized : ∫ u in (0 : ℝ)..1, g u = 1

namespace ScaleGen

variable (G : ScaleGen)

theorem continuous_g : Continuous G.g :=
  continuous_iff_continuousAt.2 fun x => (G.hasDerivAt' x).continuousAt

end ScaleGen

/-! ## The scale density -/

/-- Density of `χ = b · V` when `V` has density `g` on `[0,1)`. -/
noncomputable def scaleDensity (g : ℝ → ℝ) (b : ℝ) : ℝ → ℝ :=
  (Ico (0 : ℝ) b).indicator (fun y => g (y / b) / b)

theorem scaleDensity_of_mem {g : ℝ → ℝ} {b x : ℝ} (hx : x ∈ Ico (0 : ℝ) b) :
    scaleDensity g b x = g (x / b) / b :=
  Set.indicator_of_mem hx _

theorem scaleDensity_of_notMem {g : ℝ → ℝ} {b x : ℝ} (hx : x ∉ Ico (0 : ℝ) b) :
    scaleDensity g b x = 0 :=
  Set.indicator_of_notMem hx _

theorem measurable_scaleDensity {g : ℝ → ℝ} (hg : Measurable g) (b : ℝ) :
    Measurable (scaleDensity g b) :=
  (((hg.comp (measurable_id.div_const b))).div_const b).indicator measurableSet_Ico

theorem continuousOn_scaleDensityAux {g : ℝ → ℝ} (hg : Continuous g) (b : ℝ) :
    Continuous (fun y : ℝ => g (y / b) / b) :=
  (hg.comp (continuous_id.div_const b)).div_const b

theorem scaleDensity_nonneg (G : ScaleGen) {b : ℝ} (hb : 0 < b) (x : ℝ) :
    0 ≤ scaleDensity G.g b x := by
  by_cases hx : x ∈ Ico (0 : ℝ) b
  · rw [scaleDensity_of_mem hx]
    have hmem : x / b ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hx.1 hb.le, (div_le_one hb).2 hx.2.le⟩
    exact div_nonneg (G.nonneg' _ hmem) hb.le
  · rw [scaleDensity_of_notMem hx]

theorem integrableOn_scaleDensityAux {g : ℝ → ℝ} (hg : Continuous g) (b : ℝ) :
    IntegrableOn (fun y : ℝ => g (y / b) / b) (Ico (0 : ℝ) b) := by
  exact ((continuousOn_scaleDensityAux hg b).continuousOn.integrableOn_Icc).mono_set
    Ico_subset_Icc_self

theorem integrable_scaleDensity {g : ℝ → ℝ} (hg : Continuous g) (b : ℝ) :
    Integrable (scaleDensity g b) := by
  exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_scaleDensityAux hg b)

/-- The scale density integrates to one: it is a genuine probability density. -/
theorem integral_scaleDensity (G : ScaleGen) {b : ℝ} (hb : 0 < b) :
    ∫ x, scaleDensity G.g b x = 1 := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  rw [show scaleDensity G.g b = (Ico (0:ℝ) b).indicator (fun y => G.g (y / b) / b) from rfl,
    integral_indicator measurableSet_Ico,
    integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb.le]
  have hsub : ∫ x in (0 : ℝ)..b, G.g (x / b) / b
      = (∫ x in (0 : ℝ)..b, G.g (x / b)) / b := by
    simp [intervalIntegral.integral_div]
  rw [hsub, intervalIntegral.integral_comp_div (f := G.g) hb0]
  simp [G.normalized, hb0]

/-! ## The kernel as a probability measure -/

/-- Law of the resampled report `χ = b · V`. -/
noncomputable def scaleMeasure (g : ℝ → ℝ) (b : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (scaleDensity g b x))

theorem isProbabilityMeasure_scaleMeasure (G : ScaleGen) {b : ℝ} (hb : 0 < b) :
    IsProbabilityMeasure (scaleMeasure G.g b) := by
  constructor
  rw [scaleMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_scaleDensity G.continuous_g b)
      (Filter.Eventually.of_forall (scaleDensity_nonneg G hb)),
    integral_scaleDensity G hb, ENNReal.ofReal_one]

/-- Integration against the scale law is integration against its density. -/
theorem integral_scaleMeasure (G : ScaleGen) {b : ℝ} (hb : 0 < b) (f : ℝ → ℝ) :
    ∫ x, f x ∂(scaleMeasure G.g b) = ∫ x, scaleDensity G.g b x * f x := by
  have hmeas : Measurable fun x => Real.toNNReal (scaleDensity G.g b x) :=
    measurable_real_toNNReal.comp
      (measurable_scaleDensity G.continuous_g.measurable b)
  have hrw : scaleMeasure G.g b
      = volume.withDensity fun x => ((Real.toNNReal (scaleDensity G.g b x) : NNReal) : ℝ≥0∞) :=
    rfl
  rw [hrw, integral_withDensity_eq_integral_smul hmeas]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (Real.toNNReal (scaleDensity G.g b x)) • f x = scaleDensity G.g b x * f x
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (scaleDensity_nonneg G hb x)]

/-- The conditional resampling kernel of the remark, as a total map into
probability measures.  Off the eligible region (`b ≤ 0`) it is set to a point
mass; only `b > 0` is ever used. -/
noncomputable def scaleKernel (G : ScaleGen) (b : ℝ) : ProbabilityMeasure ℝ :=
  if h : 0 < b then ⟨scaleMeasure G.g b, isProbabilityMeasure_scaleMeasure G h⟩
  else ⟨Measure.dirac 0, Measure.dirac.isProbabilityMeasure⟩

theorem scaleKernel_coe (G : ScaleGen) {b : ℝ} (hb : 0 < b) :
    (scaleKernel G b : Measure ℝ) = scaleMeasure G.g b := by
  simp [scaleKernel, hb]

/-! ## Half the `L¹` distance between densities

Mathlib's `MeasureTheory.Measure.totalVariation` is the Jordan variation of a
*signed* measure and does not come with the density identification, so the
distance used below is defined by hand as half the `L¹` distance of the two
densities.  `halfL1_eq_measure_diff` identifies it with the usual probability
total-variation distance `sup_A |P A - Q A|` for the measures at hand, and
`abs_integral_sub_le_halfL1` is the dual (bounded-test-function) form that
`TVLipschitzKernel` asks for. -/

/-- Half the `L¹` distance between two densities. -/
noncomputable def halfL1 (p q : ℝ → ℝ) : ℝ := (∫ x, |p x - q x|) / 2

theorem halfL1_nonneg (p q : ℝ → ℝ) : 0 ≤ halfL1 p q :=
  div_nonneg (integral_nonneg fun _ => abs_nonneg _) (by norm_num)

/-- Dual form: any payoff with values in `[0, w]` separates two densities by at
most `w` times half their `L¹` distance. -/
theorem abs_integral_sub_le_halfL1
    {p q : ℝ → ℝ} (hp : Integrable p) (hq : Integrable q)
    (hp1 : ∫ x, p x = 1) (hq1 : ∫ x, q x = 1)
    {f : ℝ → ℝ} (hf : Measurable f) {w : ℝ}
    (hfr : ∀ x, f x ∈ Icc (0 : ℝ) w) :
    |(∫ x, f x * p x) - ∫ x, f x * q x| ≤ w * halfL1 p q := by
  have hw : 0 ≤ w := le_trans (hfr 0).1 (hfr 0).2
  have hfsm : AEStronglyMeasurable f volume := hf.aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ, ‖f x‖ ≤ w := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hfr x).1]
    exact (hfr x).2
  have hfp : Integrable fun x => f x * p x := hp.bdd_mul hfsm hbound
  have hfq : Integrable fun x => f x * q x := hq.bdd_mul hfsm hbound
  have hshift : AEStronglyMeasurable (fun x => f x - w / 2) volume :=
    (hf.sub measurable_const).aestronglyMeasurable
  have hshiftAbs : ∀ x : ℝ, |f x - w / 2| ≤ w / 2 := by
    intro x
    rw [abs_le]
    constructor <;> [linarith [(hfr x).1]; linarith [(hfr x).2]]
  have hshiftBound : ∀ᵐ x : ℝ, ‖f x - w / 2‖ ≤ w / 2 := by
    filter_upwards with x
    simpa [Real.norm_eq_abs] using hshiftAbs x
  have hprod : Integrable fun x => (f x - w / 2) * (p x - q x) :=
    (hp.sub hq).bdd_mul hshift hshiftBound
  have hkey : ∫ x, (f x - w / 2) * (p x - q x)
      = (∫ x, f x * p x) - ∫ x, f x * q x := by
    have hfun : (fun x => (f x - w / 2) * (p x - q x))
        = fun x => (f x * p x - f x * q x) - ((w / 2) * p x - (w / 2) * q x) := by
      funext x; ring
    have hA : Integrable (fun x => f x * p x - f x * q x) volume := hfp.sub hfq
    have hpc : Integrable (fun x => (w / 2) * p x) volume := hp.const_mul _
    have hqc : Integrable (fun x => (w / 2) * q x) volume := hq.const_mul _
    have hB : Integrable (fun x => (w / 2) * p x - (w / 2) * q x) volume := hpc.sub hqc
    rw [hfun, integral_sub hA hB, integral_sub hfp hfq, integral_sub hpc hqc,
      integral_const_mul, integral_const_mul, hp1, hq1]
    ring
  rw [← hkey]
  calc |∫ x, (f x - w / 2) * (p x - q x)|
      ≤ ∫ x, |(f x - w / 2) * (p x - q x)| := abs_integral_le_integral_abs
    _ ≤ ∫ x, (w / 2) * |p x - q x| := by
        refine integral_mono hprod.abs ((hp.sub hq).abs.const_mul _) fun x => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hshiftAbs x) (abs_nonneg _)
    _ = w * halfL1 p q := by
        rw [integral_const_mul, halfL1]; ring

/-! ## Exact decomposition of the `L¹` distance -/

/-- The remark's change of variables `x = b' u`, carried out exactly.  For
`0 < b ≤ b'` the `L¹` distance of the two scale densities splits into an
"overlap" term on `[0, b/b')` and a pure boundary term on `[b/b', 1)`. -/
theorem l1_scaleDensity_decomposition (G : ScaleGen) {b b' : ℝ}
    (hb : 0 < b) (hbb' : b ≤ b') :
    ∫ x, |scaleDensity G.g b x - scaleDensity G.g b' x|
      = (∫ u in (0 : ℝ)..(b / b'), |(b' / b) * G.g ((b' / b) * u) - G.g u|)
        + ∫ u in (b / b')..1, G.g u := by
  have hb' : 0 < b' := lt_of_lt_of_le hb hbb'
  have hb0 : b ≠ 0 := ne_of_gt hb
  have hb'0 : b' ≠ 0 := ne_of_gt hb'
  set D : ℝ → ℝ := fun x => |scaleDensity G.g b x - scaleDensity G.g b' x| with hD
  have hDint : Integrable D volume :=
    ((integrable_scaleDensity G.continuous_g b).sub
      (integrable_scaleDensity G.continuous_g b')).abs
  have hsupp : ∀ x, x ∉ Ico (0 : ℝ) b' → D x = 0 := by
    intro x hx
    have h1 : x ∉ Ico (0 : ℝ) b := fun h => hx ⟨h.1, lt_of_lt_of_le h.2 hbb'⟩
    simp only [hD, scaleDensity_of_notMem h1, scaleDensity_of_notMem hx, sub_self, abs_zero]
  have hstep1 : ∫ x, D x = ∫ x in Ico (0 : ℝ) b', D x := by
    rw [← integral_indicator measurableSet_Ico]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Ico (0 : ℝ) b'
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hsupp x hx]
  have hdisj : Disjoint (Ico (0 : ℝ) b) (Ico b b') := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hxb⟩ ⟨hbx, -⟩
    exact absurd hbx (not_le.2 hxb)
  have hstep2 : ∫ x in Ico (0 : ℝ) b', D x
      = (∫ x in Ico (0 : ℝ) b, D x) + ∫ x in Ico b b', D x := by
    rw [← Set.Ico_union_Ico_eq_Ico hb.le hbb',
      setIntegral_union hdisj measurableSet_Ico hDint.integrableOn hDint.integrableOn]
  have hpiece1 : ∫ x in Ico (0 : ℝ) b, D x
      = ∫ u in (0 : ℝ)..(b / b'), |(b' / b) * G.g ((b' / b) * u) - G.g u| := by
    have hcongr : EqOn D (fun x => |G.g (x / b) / b - G.g (x / b') / b'|) (Ico (0 : ℝ) b) := by
      intro x hx
      have hx' : x ∈ Ico (0 : ℝ) b' := ⟨hx.1, lt_of_lt_of_le hx.2 hbb'⟩
      simp only [hD, scaleDensity_of_mem hx, scaleDensity_of_mem hx']
    rw [setIntegral_congr_fun measurableSet_Ico hcongr, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hb.le]
    have hform : (fun x : ℝ => |G.g (x / b) / b - G.g (x / b') / b'|)
        = fun x : ℝ => (fun u : ℝ => |G.g ((b' / b) * u) / b - G.g u / b'|) (x / b') := by
      funext x
      have hxx : (b' / b) * (x / b') = x / b := by field_simp
      simp only [hxx]
    rw [hform, intervalIntegral.integral_comp_div
        (fun u : ℝ => |G.g ((b' / b) * u) / b - G.g u / b'|) hb'0,
      zero_div, smul_eq_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have hbb : b' * (G.g ((b' / b) * u) / b - G.g u / b')
        = (b' / b) * G.g ((b' / b) * u) - G.g u := by field_simp
    rw [← hbb, abs_mul, abs_of_pos hb']
  have hpiece2 : ∫ x in Ico b b', D x = ∫ u in (b / b')..1, G.g u := by
    have hcongr : EqOn D (fun x => G.g (x / b') / b') (Ico b b') := by
      intro x hx
      have h1 : x ∉ Ico (0 : ℝ) b := fun h => absurd hx.1 (not_le.2 h.2)
      have hx' : x ∈ Ico (0 : ℝ) b' := ⟨le_trans hb.le hx.1, hx.2⟩
      have hnn : 0 ≤ G.g (x / b') / b' :=
        div_nonneg (G.nonneg' _ ⟨div_nonneg hx'.1 hb'.le, (div_le_one hb').2 hx'.2.le⟩) hb'.le
      simp only [hD, scaleDensity_of_notMem h1, scaleDensity_of_mem hx', zero_sub, abs_neg,
        abs_of_nonneg hnn]
    rw [setIntegral_congr_fun measurableSet_Ico hcongr, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hbb']
    have hform : (fun x : ℝ => G.g (x / b') / b')
        = fun x : ℝ => (fun u : ℝ => G.g u / b') (x / b') := rfl
    rw [hform, intervalIntegral.integral_comp_div (fun u : ℝ => G.g u / b') hb'0,
      div_self hb'0, smul_eq_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    field_simp
  rw [hstep1, hstep2, hpiece1, hpiece2]


/-! ## The density-variation integral

The remark's constant is built from the derivative of `v ↦ v g v`.  Nothing in
this section mentions the scale parameter. -/

namespace ScaleGen

variable (G : ScaleGen)

/-- Integrand of the paper's density-variation integral: `g v + v g'(v)`, the
derivative of `v ↦ v g v`. -/
noncomputable def hvar (v : ℝ) : ℝ := G.g v + v * G.g' v

theorem continuous_hvar : Continuous G.hvar := by
  show Continuous fun v => G.g v + v * G.g' v
  exact G.continuous_g.add (continuous_id.mul G.continuous_g')

theorem hasDerivAt_mul_g (v : ℝ) : HasDerivAt (fun x => x * G.g x) (G.hvar v) v := by
  simpa [hvar] using (hasDerivAt_id v).mul (G.hasDerivAt' v)

theorem intervalIntegrable_abs_hvar (a b : ℝ) :
    IntervalIntegrable (fun v => |G.hvar v|) volume a b :=
  G.continuous_hvar.abs.intervalIntegrable a b

/-- Variation of `v ↦ v g v` accumulated from `0`. -/
noncomputable def Phi (x : ℝ) : ℝ := ∫ v in (0 : ℝ)..x, |G.hvar v|

theorem continuous_Phi : Continuous G.Phi :=
  intervalIntegral.continuous_primitive (fun a b => G.intervalIntegrable_abs_hvar a b) 0

@[simp] theorem Phi_zero : G.Phi 0 = 0 := by simp [Phi]

theorem Phi_sub (x y : ℝ) : G.Phi y - G.Phi x = ∫ v in x..y, |G.hvar v| := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (G.intervalIntegrable_abs_hvar 0 x) (G.intervalIntegrable_abs_hvar x y)
  simp only [Phi]
  linarith

theorem Phi_mono : Monotone G.Phi := by
  intro x y hxy
  have h0 : (0 : ℝ) ≤ ∫ v in x..y, |G.hvar v| :=
    intervalIntegral.integral_nonneg hxy fun u _ => abs_nonneg _
  linarith [G.Phi_sub x y]

theorem Phi_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ G.Phi x := by
  simpa using G.Phi_mono hx

/-- The paper's density-variation integral `A = ∫₀¹ |g u + u g'(u)| du`. -/
noncomputable def varA : ℝ := ∫ u in (0 : ℝ)..1, |G.g u + u * G.g' u|

theorem varA_eq_Phi_one : G.varA = G.Phi 1 := rfl

theorem varA_nonneg : 0 ≤ G.varA :=
  intervalIntegral.integral_nonneg zero_le_one fun _ _ => abs_nonneg _

theorem Phi_le_varA {x : ℝ} (hx : x ≤ 1) : G.Phi x ≤ G.varA := by
  rw [varA_eq_Phi_one]; exact G.Phi_mono hx

/-- The endpoint value `g(1⁻)`.  A `ScaleGen` is differentiable, hence
continuous, so the left limit at `1` is the value at `1`. -/
noncomputable def endpoint : ℝ := G.g 1

theorem tendsto_endpoint :
    Filter.Tendsto G.g (nhdsWithin 1 (Iio 1)) (nhds G.endpoint) :=
  (G.continuous_g.tendsto 1).mono_left nhdsWithin_le_nhds

theorem endpoint_nonneg : 0 ≤ G.endpoint := G.nonneg' 1 (by norm_num)

/-- The remark's constant `c_g = (A + g(1⁻))/2`. -/
noncomputable def cg : ℝ := (1 / 2) * (G.varA + G.endpoint)

theorem cg_nonneg : 0 ≤ G.cg := by
  have h1 := G.varA_nonneg
  have h2 := G.endpoint_nonneg
  simp only [cg]
  linarith

theorem exists_bound_hvar : ∃ C : ℝ, 0 ≤ C ∧ ∀ v ∈ Icc (0 : ℝ) 1, |G.hvar v| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := G.hvar) (s := Icc (0 : ℝ) 1) G.continuous_hvar.continuousOn
  have h0 : |G.hvar 0| ≤ C := by simpa [Real.norm_eq_abs] using hC 0 (by norm_num)
  exact ⟨C, le_trans (abs_nonneg _) h0, fun v hv => by simpa [Real.norm_eq_abs] using hC v hv⟩

theorem Phi_le_const_mul {C : ℝ} (hC : ∀ v ∈ Icc (0 : ℝ) 1, |G.hvar v| ≤ C)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : G.Phi t ≤ C * t := by
  have hbound : ∀ x ∈ Set.uIoc (0 : ℝ) t, ‖|G.hvar x|‖ ≤ C := by
    intro x hx
    rw [Set.uIoc_of_le ht0] at hx
    exact by simpa [Real.norm_eq_abs] using hC x ⟨hx.1.le, le_trans hx.2 ht1⟩
  have hmain := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hPhi : ‖G.Phi t‖ ≤ C * |t - 0| := hmain
  rw [Real.norm_eq_abs, abs_of_nonneg (G.Phi_nonneg ht0), sub_zero,
    abs_of_nonneg ht0] at hPhi
  exact hPhi

theorem abs_Phi_div_le {C : ℝ} (hC : ∀ v ∈ Icc (0 : ℝ) 1, |G.hvar v| ≤ C)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) : |G.Phi t / t| ≤ C := by
  rw [abs_div, abs_of_pos ht0, abs_of_nonneg (G.Phi_nonneg ht0.le), div_le_iff₀ ht0]
  exact G.Phi_le_const_mul hC ht0.le ht1

theorem intervalIntegrable_Phi_ratio {k x : ℝ} (hk : 0 < k) (hx : 0 ≤ x) (hkx : k * x ≤ 1) :
    IntervalIntegrable (fun u => G.Phi (k * u) / (k * u)) volume 0 x := by
  obtain ⟨C, -, hC⟩ := G.exists_bound_hvar
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
  refine Measure.integrableOn_of_bounded (M := C) measure_Ioc_lt_top.ne ?_ ?_
  · exact ((G.continuous_Phi.measurable.comp (measurable_id.const_mul k)).div
      (measurable_id.const_mul k)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have h1 : 0 < k * u := mul_pos hk hu.1
    have h2 : k * u ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hu.2 hk.le) hkx
    rw [Real.norm_eq_abs]
    exact G.abs_Phi_div_le hC h1 h2

theorem intervalIntegrable_Phi_div {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    IntervalIntegrable (fun t => G.Phi t / t) volume 0 x := by
  simpa using G.intervalIntegrable_Phi_ratio one_pos hx (by simpa using hx1)

end ScaleGen

/-! ## The overlap term -/

/-- **First term of the decomposition.**  With `λ = b'/b ≥ 1`, the overlap
piece of the `L¹` distance is at most `A log λ`, where `A` is the
density-variation integral.  The proof is the paper's, rearranged so that no
two-dimensional Fubini step is needed: writing `Φ x = ∫₀ˣ |g + v g'|` and using
`λ g(λu) - g(u) = (Φ(λu) - Φ(u))/u` pointwise, the substitution `t = λu`
telescopes the two primitives into `∫_{1/λ}^1 Φ(t)/t dt ≤ A log λ`. -/
theorem overlap_le_varA_mul_log (G : ScaleGen) {lam : ℝ} (hlam : 1 ≤ lam) :
    (∫ u in (0 : ℝ)..(1 / lam), |lam * G.g (lam * u) - G.g u|) ≤ G.varA * Real.log lam := by
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le zero_lt_one hlam
  have hlamne : lam ≠ 0 := ne_of_gt hlam0
  set d : ℝ := 1 / lam with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hd1 : d ≤ 1 := by rw [hd, div_le_one hlam0]; exact hlam
  have hlamd : lam * d = 1 := by rw [hd]; field_simp
  have hpt : ∀ u ∈ Ioo (0 : ℝ) d,
      |lam * G.g (lam * u) - G.g u|
        ≤ lam * (G.Phi (lam * u) / (lam * u)) - G.Phi u / u := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hune : u ≠ 0 := ne_of_gt hu0
    have hlu : u ≤ lam * u := le_mul_of_one_le_left hu0.le hlam
    have hFTC : (∫ v in u..(lam * u), G.hvar v)
        = (lam * u) * G.g (lam * u) - u * G.g u :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => G.hasDerivAt_mul_g v)
        (G.continuous_hvar.intervalIntegrable u (lam * u))
    have habs : |(lam * u) * G.g (lam * u) - u * G.g u| ≤ G.Phi (lam * u) - G.Phi u := by
      rw [← hFTC, G.Phi_sub u (lam * u)]
      exact intervalIntegral.abs_integral_le_integral_abs hlu
    have hkey : lam * G.g (lam * u) - G.g u
        = ((lam * u) * G.g (lam * u) - u * G.g u) / u := by
      field_simp
    have hrhs : lam * (G.Phi (lam * u) / (lam * u)) - G.Phi u / u
        = (G.Phi (lam * u) - G.Phi u) / u := by
      field_simp
    rw [hkey, hrhs, abs_div, abs_of_pos hu0]
    gcongr
  have hint_lhs : IntervalIntegrable (fun u => |lam * G.g (lam * u) - G.g u|) volume 0 d :=
    (((continuous_const.mul
      (G.continuous_g.comp (continuous_const.mul continuous_id))).sub
        G.continuous_g).abs).intervalIntegrable 0 d
  have hint_ratio : IntervalIntegrable (fun u => G.Phi (lam * u) / (lam * u)) volume 0 d :=
    G.intervalIntegrable_Phi_ratio hlam0 hd0.le (le_of_eq hlamd)
  have hint_div : IntervalIntegrable (fun t => G.Phi t / t) volume 0 d :=
    G.intervalIntegrable_Phi_div hd0.le hd1
  have hstep : (∫ u in (0 : ℝ)..d, |lam * G.g (lam * u) - G.g u|)
      ≤ ∫ u in (0 : ℝ)..d, (lam * (G.Phi (lam * u) / (lam * u)) - G.Phi u / u) :=
    intervalIntegral.integral_mono_on_of_le_Ioo hd0.le hint_lhs
      ((hint_ratio.const_mul lam).sub hint_div) hpt
  have hint_d1 : IntervalIntegrable (fun t => G.Phi t / t) volume d 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hd1]
    exact G.continuous_Phi.continuousOn.div continuousOn_id
      fun t ht => ne_of_gt (lt_of_lt_of_le hd0 ht.1)
  have hsubst : (∫ u in (0 : ℝ)..d, G.Phi (lam * u) / (lam * u))
      = lam⁻¹ * ∫ t in (0 : ℝ)..1, G.Phi t / t := by
    have h := intervalIntegral.integral_comp_mul_left (a := (0 : ℝ)) (b := d) (c := lam)
      (f := fun t => G.Phi t / t) hlamne
    rw [mul_zero, hlamd] at h
    simpa [smul_eq_mul] using h
  have hadj := intervalIntegral.integral_add_adjacent_intervals hint_div hint_d1
  have hrhs_eq : (∫ u in (0 : ℝ)..d, (lam * (G.Phi (lam * u) / (lam * u)) - G.Phi u / u))
      = ∫ t in d..1, G.Phi t / t := by
    rw [intervalIntegral.integral_sub ((hint_ratio.const_mul lam)) hint_div,
      intervalIntegral.integral_const_mul, hsubst, ← hadj]
    field_simp
    ring
  have hint_const : IntervalIntegrable (fun t => G.varA / t) volume d 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hd1]
    exact continuousOn_const.div continuousOn_id
      fun t ht => ne_of_gt (lt_of_lt_of_le hd0 ht.1)
  have hfinal : (∫ t in d..1, G.Phi t / t) ≤ G.varA * Real.log lam := by
    have hmono : ∀ t ∈ Icc d 1, G.Phi t / t ≤ G.varA / t := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hd0 ht.1
      have := G.Phi_le_varA ht.2
      gcongr
    calc (∫ t in d..1, G.Phi t / t)
        ≤ ∫ t in d..1, G.varA / t :=
          intervalIntegral.integral_mono_on hd1 hint_d1 hint_const hmono
      _ = G.varA * Real.log lam := by
          have hfun : (fun t : ℝ => G.varA / t) = fun t : ℝ => G.varA * (1 / t) := by
            funext t; ring
          rw [hfun, intervalIntegral.integral_const_mul,
            integral_one_div_of_pos hd0 zero_lt_one, hd, one_div_one_div]
  calc (∫ u in (0 : ℝ)..d, |lam * G.g (lam * u) - G.g u|)
      ≤ ∫ u in (0 : ℝ)..d, (lam * (G.Phi (lam * u) / (lam * u)) - G.Phi u / u) := hstep
    _ = ∫ t in d..1, G.Phi t / t := hrhs_eq
    _ ≤ G.varA * Real.log lam := hfinal

/-! ## The boundary term -/

/-- **Second term of the decomposition, exactly.**  The substitution `u = 1/s`
rewrites the boundary mass as an integral over the scale ratio. -/
theorem boundary_eq_inv_integral (G : ScaleGen) {lam : ℝ} (hlam : 1 ≤ lam) :
    (∫ u in (1 / lam)..1, G.g u) = ∫ s in (1 : ℝ)..lam, G.g (1 / s) / s ^ 2 := by
  have huIcc : uIcc (1 : ℝ) lam = Icc 1 lam := Set.uIcc_of_le hlam
  have hpos : ∀ s ∈ uIcc (1 : ℝ) lam, (0 : ℝ) < s := by
    intro s hs
    rw [huIcc] at hs
    exact lt_of_lt_of_le zero_lt_one hs.1
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (f := fun x : ℝ => x⁻¹) (f' := fun s : ℝ => -(s ^ 2)⁻¹) (g := G.g)
    (a := (1 : ℝ)) (b := lam)
    (fun s hs => hasDerivAt_inv (ne_of_gt (hpos s hs)))
    (by
      refine ContinuousOn.neg (ContinuousOn.inv₀ (continuous_pow 2).continuousOn ?_)
      intro s hs
      exact pow_ne_zero 2 (ne_of_gt (hpos s hs)))
    G.continuous_g
  have hL : (∫ s in (1 : ℝ)..lam, (-(s ^ 2)⁻¹) • (G.g ∘ fun x : ℝ => x⁻¹) s)
      = -∫ s in (1 : ℝ)..lam, G.g (1 / s) / s ^ 2 := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [Function.comp_apply, smul_eq_mul, one_div]
    ring
  have hR : (∫ x in (1 : ℝ)⁻¹..lam⁻¹, G.g x) = -∫ u in (1 / lam)..1, G.g u := by
    rw [inv_one, one_div, intervalIntegral.integral_symm]
  rw [hL, hR] at hsub
  linarith

/-- **Second term of the decomposition, bounded.**  Any bound `M` for `g` on
`[a, 1)` bounds the boundary mass. -/
theorem boundary_le (G : ScaleGen) {a M : ℝ} (ha1 : a ≤ 1)
    (hM : ∀ u ∈ Ico a 1, G.g u ≤ M) :
    (∫ u in a..1, G.g u) ≤ M * (1 - a) := by
  have h := intervalIntegral.integral_mono_on_of_le_Ioo (f := G.g) (g := fun _ => M) ha1
    (G.continuous_g.intervalIntegrable a 1) intervalIntegrable_const (μ := volume)
    (fun u hu => hM u ⟨hu.1.le, hu.2⟩)
  simpa [mul_comm] using h

/-! ## The finite bound on the eligible region -/

theorem halfL1_comm (p q : ℝ → ℝ) : halfL1 p q = halfL1 q p := by
  simp only [halfL1]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => abs_sub_comm _ _)

/-- **The honest finite bound.**  For `0 < b ≤ b'` and any bound `M` for `g` on
`[b/b', 1)`, half the `L¹` distance between the two resampling densities is at
most `(A + M)/2` times the relative scale change `(b' - b)/b`.  The two pieces
are `A log(b'/b) ≤ A (b'-b)/b` and `M (1 - b/b') ≤ M (b'-b)/b`. -/
theorem halfL1_scaleDensity_le (G : ScaleGen) {b b' M : ℝ} (hb : 0 < b) (hbb' : b ≤ b')
    (hM : ∀ u ∈ Ico (b / b') 1, G.g u ≤ M) :
    halfL1 (scaleDensity G.g b) (scaleDensity G.g b')
      ≤ (1 / 2) * (G.varA + M) * (b' - b) / b := by
  rcases eq_or_lt_of_le hbb' with heq | hlt
  · subst heq
    simp [halfL1]
  · have hb' : 0 < b' := lt_trans hb hlt
    have hlam : 1 ≤ b' / b := (one_le_div hb).2 hbb'
    have hlt1 : b / b' < 1 := (div_lt_one hb').2 hlt
    have hinv : b / b' = 1 / (b' / b) := by field_simp
    have hM0 : 0 ≤ M :=
      le_trans (G.nonneg' (b / b') ⟨by positivity, hlt1.le⟩) (hM _ ⟨le_refl _, hlt1⟩)
    have h1 : (∫ u in (0 : ℝ)..(b / b'), |(b' / b) * G.g ((b' / b) * u) - G.g u|)
        ≤ G.varA * Real.log (b' / b) := by
      rw [hinv]
      exact overlap_le_varA_mul_log G hlam
    have h2 : (∫ u in (b / b')..1, G.g u) ≤ M * (1 - b / b') := boundary_le G hlt1.le hM
    have hlog : Real.log (b' / b) ≤ b' / b - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hquot : b' / b - 1 = (b' - b) / b := by field_simp
    have hAX : G.varA * Real.log (b' / b) ≤ G.varA * ((b' - b) / b) := by
      rw [← hquot]
      exact mul_le_mul_of_nonneg_left hlog G.varA_nonneg
    have hsecond : 1 - b / b' ≤ (b' - b) / b := by
      have hrw : 1 - b / b' = (b' - b) / b' := by field_simp
      rw [hrw]
      exact div_le_div_of_nonneg_left (by linarith) hb hbb'
    have hMX : M * (1 - b / b') ≤ M * ((b' - b) / b) := mul_le_mul_of_nonneg_left hsecond hM0
    have hexp : (1 / 2) * (G.varA + M) * (b' - b) / b
        = (G.varA * ((b' - b) / b) + M * ((b' - b) / b)) / 2 := by ring
    rw [halfL1, l1_scaleDensity_decomposition G hb hbb', hexp]
    linarith

/-- The same bound on the eligible region `[r, ∞)`, symmetric in the two bids
and with the uniform denominator `r`.  `M` now bounds `g` on all of `[0,1)`. -/
theorem halfL1_scaleDensity_le_reserve (G : ScaleGen) {r b b' M : ℝ} (hr : 0 < r)
    (hb : r ≤ b) (hb' : r ≤ b') (hM : ∀ u ∈ Ico (0 : ℝ) 1, G.g u ≤ M) :
    halfL1 (scaleDensity G.g b) (scaleDensity G.g b')
      ≤ (1 / 2) * (G.varA + M) * |b - b'| / r := by
  have hM0 : 0 ≤ M := le_trans (G.nonneg' 0 ⟨le_refl _, zero_le_one⟩) (hM 0 ⟨le_refl _, one_pos⟩)
  have key : ∀ x y : ℝ, r ≤ x → x ≤ y →
      halfL1 (scaleDensity G.g x) (scaleDensity G.g y)
        ≤ (1 / 2) * (G.varA + M) * (y - x) / r := by
    intro x y hx hxy
    have hx0 : 0 < x := lt_of_lt_of_le hr hx
    have hy0 : 0 < y := lt_of_lt_of_le hx0 hxy
    have hstep := halfL1_scaleDensity_le G hx0 hxy
      (M := M) fun u hu => hM u ⟨le_trans (by positivity) hu.1, hu.2⟩
    refine le_trans hstep (div_le_div_of_nonneg_left ?_ hr hx)
    have : 0 ≤ y - x := by linarith
    have hAM : 0 ≤ G.varA + M := by linarith [G.varA_nonneg]
    positivity
  rcases le_total b b' with h | h
  · have habs : |b - b'| = b' - b := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [habs]
    exact key b b' hb h
  · have habs : |b - b'| = b - b' := abs_of_nonneg (by linarith)
    rw [habs, halfL1_comm]
    exact key b' b hb' h

/-! ## The displayed bound, with no side condition

`halfL1_scaleDensity_le` pays for the moving support with the supremum of `g`
near the endpoint rather than with `g(1⁻)`, which is not what the remark
prints.  The remark's own route is different and gives the printed constant:
it computes the *local* rate `c_g/b` and integrates it along reports.  That
route is reconstructed here.  Half the `L¹` distance is a metric, so it is
subadditive along a chain of intermediate scales; on a geometric chain of `n`
steps between `b` and `b'` every step compares the same ratio, and as the mesh
refines the bound on `g` over the shrinking sliver falls back to `g(1⁻)` by
continuity while `n(λ^{1/n} - 1)` falls to `log λ`.  The limit is
`c_g log(b'/b)`, and `log λ ≤ λ - 1` delivers the printed `c_g (b'-b)/r`. -/

@[simp] theorem halfL1_self (p : ℝ → ℝ) : halfL1 p p = 0 := by
  simp [halfL1]

/-- Half the `L¹` distance obeys the triangle inequality on scale densities. -/
theorem halfL1_scaleDensity_triangle (G : ScaleGen) (b c d : ℝ) :
    halfL1 (scaleDensity G.g b) (scaleDensity G.g d)
      ≤ halfL1 (scaleDensity G.g b) (scaleDensity G.g c)
        + halfL1 (scaleDensity G.g c) (scaleDensity G.g d) := by
  have hb := integrable_scaleDensity G.continuous_g b
  have hc := integrable_scaleDensity G.continuous_g c
  have hd := integrable_scaleDensity G.continuous_g d
  have h1 : Integrable (fun x => |scaleDensity G.g b x - scaleDensity G.g c x|) :=
    (hb.sub hc).abs
  have h2 : Integrable (fun x => |scaleDensity G.g c x - scaleDensity G.g d x|) :=
    (hc.sub hd).abs
  have hmono : (∫ x, |scaleDensity G.g b x - scaleDensity G.g d x|)
      ≤ ∫ x, (|scaleDensity G.g b x - scaleDensity G.g c x|
          + |scaleDensity G.g c x - scaleDensity G.g d x|) := by
    refine integral_mono ((hb.sub hd).abs) (h1.add h2) (fun x => ?_)
    exact abs_sub_le _ _ _
  rw [integral_add h1 h2] at hmono
  simp only [halfL1]
  linarith

/-- **The chain bound.**  On a geometric grid of `n` steps with ratio `rho`,
every step compares two scales in the same ratio, so one bound `M` for `g` on
the common sliver `[1/rho, 1)` serves all of them. -/
theorem halfL1_geom_chain (G : ScaleGen) {b rho M : ℝ} (hb : 0 < b) (hrho : 1 ≤ rho)
    (hM : ∀ u ∈ Ico (1 / rho) 1, G.g u ≤ M) :
    ∀ n : ℕ, halfL1 (scaleDensity G.g b) (scaleDensity G.g (b * rho ^ n))
      ≤ (n : ℝ) * ((1 / 2) * (G.varA + M) * (rho - 1)) := by
  have hrho0 : (0 : ℝ) < rho := lt_of_lt_of_le zero_lt_one hrho
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hbn : 0 < b * rho ^ n := by positivity
    have hpown : (0 : ℝ) < rho ^ n := pow_pos hrho0 n
    have hstepmono : b * rho ^ n ≤ b * rho ^ (n + 1) := by
      rw [pow_succ]
      nlinarith
    have hratio : (b * rho ^ n) / (b * rho ^ (n + 1)) = 1 / rho := by
      rw [pow_succ]
      field_simp
    have hM' : ∀ u ∈ Ico ((b * rho ^ n) / (b * rho ^ (n + 1))) 1, G.g u ≤ M := by
      rw [hratio]; exact hM
    have hstep := halfL1_scaleDensity_le G hbn hstepmono hM'
    have hval : (1 / 2) * (G.varA + M) * (b * rho ^ (n + 1) - b * rho ^ n) / (b * rho ^ n)
        = (1 / 2) * (G.varA + M) * (rho - 1) := by
      rw [pow_succ]
      field_simp
    rw [hval] at hstep
    have htri := halfL1_scaleDensity_triangle G b (b * rho ^ n) (b * rho ^ (n + 1))
    push_cast
    linarith

/-- `n (e^{L/n} - 1) → L`: refining the geometric grid recovers the logarithm. -/
theorem tendsto_nat_mul_exp_sub_one {L : ℝ} (hL : L ≠ 0) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * (Real.exp (L / n) - 1)) Filter.atTop (nhds L) := by
  have hslope : Filter.Tendsto (fun y : ℝ => (Real.exp y - 1) / y)
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) (nhds 1) := by
    have h := Real.hasDerivAt_exp 0
    rw [Real.exp_zero, hasDerivAt_iff_tendsto_slope] at h
    refine Filter.Tendsto.congr (fun y => ?_) h
    simp [slope, Real.exp_zero, div_eq_inv_mul]
  have hzero : Filter.Tendsto (fun n : ℕ => L / n) Filter.atTop
      (nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (tendsto_const_div_atTop_nhds_zero_nat L) ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact div_ne_zero hL (ne_of_gt hn0)
  have hmul := (hslope.comp hzero).const_mul L
  rw [mul_one] at hmul
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp_apply]
  field_simp

/-- **The remark's bound in logarithmic form**, with no hypothesis beyond the
ones the remark already carries. -/
theorem halfL1_scaleDensity_le_log (G : ScaleGen) {b b' : ℝ} (hb : 0 < b) (hbb' : b ≤ b') :
    halfL1 (scaleDensity G.g b) (scaleDensity G.g b') ≤ G.cg * Real.log (b' / b) := by
  rcases eq_or_lt_of_le hbb' with heq | hlt
  · subst heq; simp
  have hb' : 0 < b' := lt_trans hb hlt
  set L : ℝ := Real.log (b' / b) with hLdef
  have hratio1 : 1 < b' / b := (one_lt_div hb).2 hlt
  have hL : 0 < L := Real.log_pos hratio1
  refine le_of_forall_pos_le_add (fun eps heps => ?_)
  set eta : ℝ := eps / L with hetadef
  have heta : 0 < eta := div_pos heps hL
  obtain ⟨delta, hdelta0, hdelta⟩ :=
    Metric.continuousAt_iff.mp (G.continuous_g.continuousAt (x := (1 : ℝ))) eta heta
  set M : ℝ := G.endpoint + eta with hMdef
  set rho : ℕ → ℝ := fun n => Real.exp (L / n) with hrhodef
  have hrho1 : ∀ n : ℕ, 1 ≤ rho n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hrhodef, hn]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      exact Real.one_le_exp (by positivity)
  have hinvto : Filter.Tendsto (fun n : ℕ => 1 / rho n) Filter.atTop (nhds 1) := by
    have h0 : Filter.Tendsto (fun n : ℕ => L / n) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat L
    have hexp : Filter.Tendsto (fun n : ℕ => rho n) Filter.atTop (nhds 1) := by
      have := Real.continuous_exp.continuousAt.tendsto.comp h0
      simpa [hrhodef, Function.comp_def] using this
    simpa using hexp.inv₀ (by norm_num)
  have hsliver : ∀ᶠ n : ℕ in Filter.atTop, ∀ u ∈ Ico (1 / rho n) 1, G.g u ≤ M := by
    have hev := hinvto.eventually_const_lt (show 1 - delta < 1 by linarith)
    filter_upwards [hev] with n hn u hu
    have hdist : dist u 1 < delta := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hu.2] : (0:ℝ) ≤ 1 - u)]
      linarith [hu.1]
    have hgu := hdelta hdist
    rw [Real.dist_eq, abs_lt] at hgu
    simp only [hMdef, ScaleGen.endpoint]
    linarith [hgu.2]
  have hchain : ∀ᶠ n : ℕ in Filter.atTop,
      halfL1 (scaleDensity G.g b) (scaleDensity G.g b')
        ≤ (1 / 2) * (G.varA + M) * ((n : ℝ) * (rho n - 1)) := by
    filter_upwards [hsliver, Filter.eventually_gt_atTop 0] with n hM' hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hpow : b * rho n ^ n = b' := by
      have hexp : rho n ^ n = Real.exp L := by
        rw [hrhodef, ← Real.exp_nat_mul, mul_div_cancel₀ _ (ne_of_gt hn0)]
      rw [hexp, hLdef, Real.exp_log (by positivity)]
      field_simp
    have h := halfL1_geom_chain G hb (hrho1 n) hM' n
    rw [hpow] at h
    calc halfL1 (scaleDensity G.g b) (scaleDensity G.g b')
        ≤ (n : ℝ) * ((1 / 2) * (G.varA + M) * (rho n - 1)) := h
      _ = (1 / 2) * (G.varA + M) * ((n : ℝ) * (rho n - 1)) := by ring
  have hlim : Filter.Tendsto (fun n : ℕ => (1 / 2) * (G.varA + M) * ((n : ℝ) * (rho n - 1)))
      Filter.atTop (nhds ((1 / 2) * (G.varA + M) * L)) :=
    (tendsto_nat_mul_exp_sub_one (ne_of_gt hL)).const_mul _
  have hle : halfL1 (scaleDensity G.g b) (scaleDensity G.g b')
      ≤ (1 / 2) * (G.varA + M) * L := ge_of_tendsto hlim hchain
  have hexpand : (1 / 2) * (G.varA + M) * L = G.cg * L + (1 / 2) * eta * L := by
    simp only [hMdef, ScaleGen.cg]
    ring
  have hetaL : (1 / 2) * eta * L = eps / 2 := by
    rw [hetadef]
    field_simp
  rw [hexpand, hetaL] at hle
  linarith

/-- **The remark's displayed bound**, `c_g (b' - b)/r` on the eligible region,
with no hypothesis the printed remark does not state. -/
theorem halfL1_scaleDensity_le_cg (G : ScaleGen) {r b b' : ℝ} (hr : 0 < r)
    (hb : r ≤ b) (hbb' : b ≤ b') :
    halfL1 (scaleDensity G.g b) (scaleDensity G.g b') ≤ G.cg * (b' - b) / r := by
  have hb0 : 0 < b := lt_of_lt_of_le hr hb
  have hb'0 : 0 < b' := lt_of_lt_of_le hb0 hbb'
  have hlog := halfL1_scaleDensity_le_log G hb0 hbb'
  have hle1 : Real.log (b' / b) ≤ (b' - b) / b := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < b' / b by positivity)
    have heq : b' / b - 1 = (b' - b) / b := by field_simp
    linarith [h, heq.le, heq.ge]
  have hle2 : (b' - b) / b ≤ (b' - b) / r :=
    div_le_div_of_nonneg_left (by linarith) hr hb
  have hcg := G.cg_nonneg
  calc halfL1 (scaleDensity G.g b) (scaleDensity G.g b')
      ≤ G.cg * Real.log (b' / b) := hlog
    _ ≤ G.cg * ((b' - b) / r) :=
        mul_le_mul_of_nonneg_left (le_trans hle1 hle2) hcg
    _ = G.cg * (b' - b) / r := by ring

/-- The symmetric, reserve-normalized form the kernel certificate consumes. -/
theorem halfL1_scaleDensity_le_cg_reserve (G : ScaleGen) {r b b' : ℝ} (hr : 0 < r)
    (hb : r ≤ b) (hb' : r ≤ b') :
    halfL1 (scaleDensity G.g b) (scaleDensity G.g b') ≤ G.cg * |b - b'| / r := by
  rcases le_total b b' with hle | hle
  · rw [abs_of_nonpos (by linarith), neg_sub]
    exact halfL1_scaleDensity_le_cg G hr hb hle
  · rw [abs_of_nonneg (by linarith), halfL1_comm]
    exact halfL1_scaleDensity_le_cg G hr hb' hle

/-! ## The local rate -/

/-- **The remark's own phrasing, `c_g / b`.**  As `b' ↓ b` the difference
quotient of the resampling law is eventually below `c_g / b + ε`, for every
`ε > 0`.  Nothing beyond the generator's continuity at `1` is used: the
supremum of `g` over the shrinking window `[b/b', 1)` tends to `g(1⁻)`, so the
boundary term contributes exactly `g(1⁻)/2` in the limit. -/
theorem eventually_halfL1_le_local_rate (G : ScaleGen) {b : ℝ} (hb : 0 < b) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ b' in nhdsWithin b (Ioi b),
      halfL1 (scaleDensity G.g b) (scaleDensity G.g b') ≤ (G.cg / b + ε) * (b' - b) := by
  have hη0 : 0 < 2 * b * ε := by positivity
  obtain ⟨δ, hδ0, hδ⟩ :
      ∃ δ > 0, ∀ u : ℝ, |u - 1| < δ → G.g u ≤ G.endpoint + 2 * b * ε := by
    have hmet := Metric.tendsto_nhds.1 (G.continuous_g.tendsto 1) (2 * b * ε) hη0
    rw [Metric.eventually_nhds_iff] at hmet
    obtain ⟨δ, hδ0, hδ⟩ := hmet
    refine ⟨δ, hδ0, fun u hu => ?_⟩
    have hdist : dist (G.g u) (G.g 1) < 2 * b * ε := hδ (by rwa [Real.dist_eq])
    rw [Real.dist_eq, abs_lt] at hdist
    simp only [ScaleGen.endpoint]
    linarith [hdist.2]
  have hratio0 : Filter.Tendsto (fun x : ℝ => b / x) (nhds b) (nhds (b / b)) :=
    continuousAt_const.div continuousAt_id (ne_of_gt hb)
  rw [div_self (ne_of_gt hb)] at hratio0
  have hev : ∀ᶠ b' in nhdsWithin b (Ioi b), 1 - δ < b / b' :=
    (hratio0.mono_left nhdsWithin_le_nhds).eventually_const_lt (by linarith)
  filter_upwards [hev, self_mem_nhdsWithin] with b' hb'ratio hb'mem
  have hbb' : b < b' := hb'mem
  have hM : ∀ u ∈ Ico (b / b') 1, G.g u ≤ G.endpoint + 2 * b * ε := by
    intro u hu
    refine hδ u ?_
    rw [abs_lt]
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hstep := halfL1_scaleDensity_le G hb hbb'.le hM
  have hcalc : (1 / 2) * (G.varA + (G.endpoint + 2 * b * ε)) * (b' - b) / b
      = (G.cg / b + ε) * (b' - b) := by
    simp only [ScaleGen.cg]
    field_simp
    ring
  linarith [hstep, hcalc.le, hcalc.ge]

/-- The same statement as a difference quotient, which is the form the remark
prints: half the total-variation norm per unit of bid is `c_g / b` in the
limit. -/
theorem eventually_halfL1_div_le_local_rate (G : ScaleGen) {b : ℝ} (hb : 0 < b) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ b' in nhdsWithin b (Ioi b),
      halfL1 (scaleDensity G.g b) (scaleDensity G.g b') / (b' - b) ≤ G.cg / b + ε := by
  filter_upwards [eventually_halfL1_le_local_rate G hb hε, self_mem_nhdsWithin] with
    b' hb'bound hb'mem
  have hbb' : b < b' := hb'mem
  rw [div_le_iff₀ (by linarith : (0:ℝ) < b' - b)]
  exact hb'bound

/-! ## The uniform kernel, computed -/

/-- The uniform generator `g ≡ 1`: the resampling law is `Uniform[0, b)`. -/
def uniformGen : ScaleGen where
  g := fun _ => 1
  g' := fun _ => 0
  hasDerivAt' := fun x => by simpa using hasDerivAt_const x (1 : ℝ)
  continuous_g' := continuous_const
  nonneg' := fun _ _ => zero_le_one
  normalized := by simp

@[simp] theorem uniformGen_g (x : ℝ) : uniformGen.g x = 1 := rfl

@[simp] theorem uniformGen_g' (x : ℝ) : uniformGen.g' x = 0 := rfl

theorem uniformGen_varA : uniformGen.varA = 1 := by
  simp [ScaleGen.varA]

theorem uniformGen_endpoint : uniformGen.endpoint = 1 := rfl

theorem uniformGen_cg : uniformGen.cg = 1 := by
  rw [ScaleGen.cg, uniformGen_varA, uniformGen_endpoint]
  norm_num

/-- For the uniform kernel the `L¹` distance is exact.  Both terms of the
decomposition contribute `(b' - b)/b'`, so half the total variation is
`(b' - b)/b'`. -/
theorem halfL1_uniform {b b' : ℝ} (hb : 0 < b) (hbb' : b ≤ b') :
    halfL1 (scaleDensity uniformGen.g b) (scaleDensity uniformGen.g b') = (b' - b) / b' := by
  have hb' : 0 < b' := lt_of_lt_of_le hb hbb'
  have hone : (1 : ℝ) ≤ b' / b := (one_le_div hb).2 hbb'
  rw [halfL1, l1_scaleDensity_decomposition uniformGen hb hbb']
  simp only [uniformGen_g, mul_one]
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ b' / b - 1), intervalIntegral.integral_const,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  field_simp
  ring

/-- The paper's displayed bound holds for the uniform kernel with no extra
hypothesis: `g ≡ 1` is dominated by its own endpoint value. -/
theorem halfL1_uniform_le_cg {b b' : ℝ} (hb : 0 < b) (hbb' : b ≤ b') :
    halfL1 (scaleDensity uniformGen.g b) (scaleDensity uniformGen.g b')
      ≤ uniformGen.cg * (b' - b) / b := by
  rw [halfL1_uniform hb hbb', uniformGen_cg, one_mul]
  exact div_le_div_of_nonneg_left (by linarith) hb hbb'

/-- The remark's own warning, made precise.  Dropping the boundary term from
`c_g` would leave `A/2 = 1/2` for the uniform kernel, and that bound is false
already at `b = 1`, `b' = 3/2`, where half the total variation is `1/3 > 1/4`. -/
theorem uniform_not_le_varA_only :
    ¬ halfL1 (scaleDensity uniformGen.g 1) (scaleDensity uniformGen.g (3 / 2))
        ≤ (1 / 2) * uniformGen.varA * ((3 / 2) - 1) / 1 := by
  rw [halfL1_uniform one_pos (by norm_num), uniformGen_varA]
  norm_num

/-- For the uniform kernel the local rate is attained, so the constant `c_g`
in `eventually_halfL1_le_local_rate` cannot be lowered in general: the
difference quotient converges to `c_g / b = 1 / b`. -/
theorem tendsto_halfL1_uniform_div {b : ℝ} (hb : 0 < b) :
    Filter.Tendsto
      (fun b' => halfL1 (scaleDensity uniformGen.g b) (scaleDensity uniformGen.g b') / (b' - b))
      (nhdsWithin b (Ioi b)) (nhds (uniformGen.cg / b)) := by
  rw [uniformGen_cg]
  have hcongr : (fun b' : ℝ => 1 / b') =ᶠ[nhdsWithin b (Ioi b)]
      fun b' => halfL1 (scaleDensity uniformGen.g b) (scaleDensity uniformGen.g b') / (b' - b) := by
    filter_upwards [self_mem_nhdsWithin] with b' hb'
    have hlt : b < b' := hb'
    have hne : b' - b ≠ 0 := ne_of_gt (by linarith)
    have hb'0 : b' ≠ 0 := ne_of_gt (by linarith)
    rw [halfL1_uniform hb hlt.le]
    field_simp
  refine Filter.Tendsto.congr' hcongr ?_
  exact (continuousAt_const.div continuousAt_id (ne_of_gt hb)).mono_left nhdsWithin_le_nhds

/-! ## Feeding the wrapper certificate -/

/-- Integration against the scale kernel, in the shape the dual bound wants. -/
theorem integral_scaleKernel (G : ScaleGen) {b : ℝ} (hb : 0 < b) (f : ℝ → ℝ) :
    (∫ ω, f ω ∂(scaleKernel G b : Measure ℝ)) = ∫ y, f y * scaleDensity G.g b y := by
  rw [scaleKernel_coe G hb, integral_scaleMeasure G hb]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => mul_comm _ _)

/-- **The scale kernel is TV-Lipschitz on the eligible region**, with modulus
`(A + M)/(2r)` for any bound `M` of `g` on `[0,1)`.  This is the premise shape
`wrapper_certificate` consumes. -/
theorem tvLipschitzKernel_scaleKernel (G : ScaleGen) {r bidCap M : ℝ} (hr : 0 < r)
    (hM : ∀ u ∈ Ico (0 : ℝ) 1, G.g u ≤ M) :
    TVLipschitzKernel (scaleKernel G) r bidCap ((1 / 2) * (G.varA + M) / r) := by
  intro b hb b' hb' w f hw hfmeas hfrange
  have hb0 : 0 < b := lt_of_lt_of_le hr hb.1
  have hb'0 : 0 < b' := lt_of_lt_of_le hr hb'.1
  rw [integral_scaleKernel G hb0, integral_scaleKernel G hb'0]
  refine le_trans (abs_integral_sub_le_halfL1
    (integrable_scaleDensity G.continuous_g b) (integrable_scaleDensity G.continuous_g b')
    (integral_scaleDensity G hb0) (integral_scaleDensity G hb'0) hfmeas hfrange) ?_
  calc w * halfL1 (scaleDensity G.g b) (scaleDensity G.g b')
      ≤ w * ((1 / 2) * (G.varA + M) * |b - b'| / r) :=
        mul_le_mul_of_nonneg_left (halfL1_scaleDensity_le_reserve G hr hb.1 hb'.1 hM) hw
    _ = w * ((1 / 2) * (G.varA + M) / r) * |b - b'| := by ring

/-- The `c_g` form of the kernel certificate.  The boundary hypothesis is now
demanded on all of `[0,1)`, because the certificate quantifies over every pair
of eligible bids; `g` nondecreasing, or bounded by its endpoint value, is
enough.  The printed remark carries no such hypothesis. -/
theorem tvLipschitzKernel_scaleKernel_cg (G : ScaleGen) {r bidCap : ℝ} (hr : 0 < r) :
    TVLipschitzKernel (scaleKernel G) r bidCap (G.cg / r) := by
  intro b hb b' hb' w f hw hfmeas hfrange
  have hb0 : 0 < b := lt_of_lt_of_le hr hb.1
  have hb'0 : 0 < b' := lt_of_lt_of_le hr hb'.1
  rw [integral_scaleKernel G hb0, integral_scaleKernel G hb'0]
  refine le_trans (abs_integral_sub_le_halfL1
    (integrable_scaleDensity G.continuous_g b) (integrable_scaleDensity G.continuous_g b')
    (integral_scaleDensity G hb0) (integral_scaleDensity G hb'0) hfmeas hfrange) ?_
  calc w * halfL1 (scaleDensity G.g b) (scaleDensity G.g b')
      ≤ w * (G.cg * |b - b'| / r) :=
        mul_le_mul_of_nonneg_left (halfL1_scaleDensity_le_cg_reserve G hr hb.1 hb'.1) hw
    _ = w * (G.cg / r) * |b - b'| := by ring

/-- **The remark's punchline.**  Publishing the pair `(μ, g)` publishes the
deployed sensitivity certificate: the FIRM-L base curve contributes
`(1 - μ) w₁/(e τ)` and the scale-family resampling kernel contributes
`μ w₁ c_g / r`, uniformly over the eligible region `[r, bidCap]`. -/
theorem wrapper_certificate_scaleKernel {ι : Type*} [Fintype ι] (G : ScaleGen)
    (mu reserve bidCap tau weight : ℝ)
    (base : ℝ → ι → ℝ) (payoff : ι → ℝ → ℝ)
    (hMu : mu ∈ Icc (0 : ℝ) 1) (hReserve : 0 < reserve) (hTau : 0 < tau)
    (hWeight : 0 ≤ weight)
    (hBase : ∀ j, ∀ b ∈ Icc reserve bidCap, ∀ b' ∈ Icc reserve bidCap,
      |base b j - base b' j| ≤ firmLBaseSensitivity weight tau * |b - b'|)
    (hPayoffMeasurable : ∀ j, Measurable (payoff j))
    (hPayoffRange : ∀ j ω, payoff j ω ∈ Icc (0 : ℝ) weight)
    (b b' : ℝ) (hBid : b ∈ Icc reserve bidCap) (hBid' : b' ∈ Icc reserve bidCap) :
    ‖deployedKernelVector mu base (scaleKernel G) payoff b -
        deployedKernelVector mu base (scaleKernel G) payoff b'‖ ≤
      ((1 - mu) * firmLBaseSensitivity weight tau +
        mu * weight * (G.cg / reserve)) * |b - b'| :=
  wrapper_certificate mu reserve bidCap tau weight (G.cg / reserve) base (scaleKernel G) payoff
    hMu hTau hWeight (div_nonneg G.cg_nonneg hReserve.le) hBase
    (tvLipschitzKernel_scaleKernel_cg G hReserve)
    hPayoffMeasurable hPayoffRange b b' hBid hBid'

end SmoothingCliff.Wrapper
