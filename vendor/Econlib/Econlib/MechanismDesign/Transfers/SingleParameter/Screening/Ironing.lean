/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Concavification1D.ConvexEnvelope
public import Econlib.Math.Analysis.ConvexRightDeriv
public import Econlib.Math.MeasureTheory.ConvexIntegralRepr
public import Econlib.Math.MeasureTheory.StieltjesRegularization
public import Econlib.Math.MeasureTheory.TriangleFubini
public import Econlib.MechanismDesign.Transfers.SingleParameter.Screening.RevenueIdentity
public import Econlib.Probability.ContDist.Quantile
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Myerson ironing

When the virtual value `ψ` is not monotone (the environment is irregular), the "serve iff `ψ ≥ 0`"
rule is not implementable, because the implied interim allocation is not monotone. Myerson's
**ironing** (Myerson 1981) replaces `ψ` by the **ironed virtual value** `ψ̄`, the monotone function
whose primitive (in quantile space) is the **convex envelope** of the primitive of `ψ`. The
construction requires no regularity assumption.

## Main definitions

* `ScreeningEnv.vvQuantile` — the virtual value pulled back to quantile space, `h(q) = ψ(F⁻¹ q)`.
* `ScreeningEnv.vvPrimitive` — its primitive `H(q) = ∫₀^q h`.
* `ScreeningEnv.ironedPrimitive` — the convex envelope `Ĥ = convexEnvelope 0 1 H`.
* `ScreeningEnv.ironedVVQuantile` — the monotone right derivative `ĥ = Ĥ'₊` of the convex envelope.
* `ScreeningEnv.ironedVirtualValue` — the ironed virtual value `ψ̄(θ) = ĥ(F(θ))`, in type space.

## Main statements

* `ScreeningEnv.ironedVirtualValue_monotone` — `ψ̄` is monotone on the type interval, so the ironed
  allocation is implementable.
* `ScreeningEnv.expected_virtualSurplus_le_ironed` — for any monotone allocation, expected virtual
  surplus is weakly raised by ironing: `𝔼[ψ·x] ≤ 𝔼[ψ̄·x]`.
* `ScreeningEnv.expected_virtualSurplus_eq_ironed` — equality holds when the allocation is constant
  on every level set of `ψ̄`.

## Notes

With the revenue identity, `expected_virtualSurplus_le_ironed` bounds revenue by the ironed virtual
surplus; achievability — the ironed-optimal allocation attaining the bound — is a separate result.

## References

* Myerson, Roger B. 1981. “Optimal Auction Design.” *Mathematics of Operations Research* 6 (1):
  58–73. [https://doi.org/10.1287/moor.6.1.58](https://doi.org/10.1287/moor.6.1.58).

## Tags

ironing, virtual value, myerson, mechanism design, screening, convex envelope
-/

@[expose] public section

open Set MeasureTheory Function Filter
open scoped Topology

noncomputable section

namespace Econlib.MechanismDesign.Transfers.SingleParameter

namespace ScreeningEnv

variable (E : ScreeningEnv)

/-! ### The quantile pullback -/

/-- The quantile function `F⁻¹` of the type distribution. -/
def quantileInv (q : ℝ) : ℝ := Measure.quantile E.dist.toMeasure q

/-- For an interior quantile `q ∈ (0, 1)`, `F⁻¹ q` lands in the type interval `[θlo, θhi]`. -/
lemma quantileInv_mem {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) : E.quantileInv q ∈ E.types := by
  have hzero : ∀ t, t ∉ Icc E.θlo E.θhi → E.dist.density t = 0 := fun t ht =>
    E.density_eq_zero_of_notMem ht
  constructor
  · by_contra hlt
    push Not at hlt
    have hcdf0 : E.dist.cdf (E.quantileInv q) = 0 :=
      E.dist.cdf_eq_zero_of_supportsOn_Icc_left hzero hlt
    have hle : q ≤ E.dist.cdf (E.quantileInv q) := E.dist.le_cdf_quantile hq
    rw [hcdf0] at hle
    exact absurd hle (not_le.mpr hq.1)
  · have hcdf1 : E.dist.cdf E.θhi = 1 :=
      E.dist.cdf_eq_one_of_supportsOn_Icc_right hzero (le_refl _)
    have h := (E.dist.quantile_le_iff hq (x := E.θhi)).mpr (by rw [hcdf1]; exact hq.2.le)
    exact h

/-- `h(q) = ψ(F⁻¹ q)`: The virtual value pulled back to quantile space. -/
def vvQuantile (q : ℝ) : ℝ := E.virtualValue (E.quantileInv q)

@[simp] lemma vvQuantile_def (q : ℝ) :
    E.vvQuantile q = E.virtualValue (E.quantileInv q) := rfl

/-- The virtual value `ψ = θ − (1 − F θ)/(f θ)` is continuous on the type interval `[θlo, θhi]`. -/
lemma virtualValue_continuousOn : ContinuousOn E.virtualValue E.types := by
  have hF : ContinuousOn E.dist.cdf E.types := E.dist.cdf_continuous.continuousOn
  have hf : ContinuousOn E.dist.density E.types := E.density_cont
  have hf_ne : ∀ θ ∈ E.types, E.dist.density θ ≠ 0 := fun θ hθ => (E.density_pos θ hθ).ne'
  have hquot : ContinuousOn (fun θ => (1 - E.dist.cdf θ) / E.dist.density θ) E.types :=
    ((continuousOn_const.sub hF).div hf hf_ne)
  exact continuousOn_id.sub hquot

/-- `h = ψ ∘ F⁻¹` is bounded on `(0, 1)`: `ψ` is continuous on the compact type interval, and
`F⁻¹ q ∈ [θlo, θhi]` for interior quantiles `q ∈ (0, 1)`. -/
lemma exists_bound_vvQuantile : ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ Ioo (0 : ℝ) 1, |E.vvQuantile q| ≤ C := by
  have hcompact : IsCompact E.types := isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn E.virtualValue_continuousOn
  refine ⟨max C 0, le_max_right _ _, fun q hq => ?_⟩
  have hmem : E.quantileInv q ∈ E.types := E.quantileInv_mem hq
  exact (hC _ hmem).trans (le_max_left _ _)

/-- `H(q) = ∫₀^q ψ(F⁻¹ u) du`: The primitive of the pulled-back virtual value. -/
def vvPrimitive (q : ℝ) : ℝ := ∫ u in (0 : ℝ)..q, E.vvQuantile u

@[simp] lemma vvPrimitive_def (q : ℝ) :
    E.vvPrimitive q = ∫ u in (0 : ℝ)..q, E.vvQuantile u := rfl

/-- `Ĥ = convexEnvelope 0 1 H`: The convex hull of the virtual-value primitive on `[0, 1]`. -/
def ironedPrimitive (q : ℝ) : ℝ := convexEnvelope 0 1 E.vvPrimitive q

@[simp] lemma ironedPrimitive_def (q : ℝ) :
    E.ironedPrimitive q = convexEnvelope 0 1 E.vvPrimitive q := rfl

/-! ### Boundedness and continuity -/

/-- `h = ψ ∘ F⁻¹` is interval-integrable on `[0, 1]`. -/
lemma intervalIntegrable_vvQuantile : IntervalIntegrable E.vvQuantile volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
  obtain ⟨C, _, hC⟩ := E.exists_bound_vvQuantile
  haveI := E.dist.toMeasure_isProbability
  have hqae : AEMeasurable E.quantileInv (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have h := Measure.aemeasurable_quantile_restrict_Ioo (μ := E.dist.toMeasure)
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h
  have hψ : AEMeasurable E.virtualValue volume := E.virtualValue_measurable.aemeasurable
  have hmap : (volume.restrict (Ioc (0 : ℝ) 1)).map E.quantileInv = E.dist.toMeasure := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact Measure.map_quantile_volume_Ioo
  have hψmap : AEMeasurable E.virtualValue ((volume.restrict (Ioc (0:ℝ) 1)).map E.quantileInv) := by
    rw [hmap, E.dist.toMeasure_eq]; exact hψ.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmble : AEStronglyMeasurable E.vvQuantile (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (hψmap.comp_aemeasurable hqae).aestronglyMeasurable
  rw [IntegrableOn, ← Measure.restrict_univ (μ := (volume.restrict (Ioc (0:ℝ) 1)))]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hmble ?_
  rw [Measure.restrict_univ, Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
  refine (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun q hq => ?_)
  rw [Real.norm_eq_abs]; exact hC q hq

/-- `H` is continuous on `[0, 1]`. -/
lemma vvPrimitive_continuousOn : ContinuousOn E.vvPrimitive (Icc 0 1) := by
  have h := intervalIntegral.continuousOn_primitive_interval'
    E.intervalIntegrable_vvQuantile (a := 0) (by rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; simp)
  rwa [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h

/-- The convex hull of `H` is convex on `[0, 1]`. -/
lemma ironedPrimitive_convexOn : ConvexOn ℝ (Icc (0 : ℝ) 1) E.ironedPrimitive :=
  convexEnvelope_convexOn (by norm_num) E.vvPrimitive_continuousOn

/-- `H` is `C`-Lipschitz on `[0, 1]`, where `C` bounds `|h|` on `(0, 1)`. -/
lemma vvPrimitive_sub_le {C : ℝ} (hC : ∀ q ∈ Ioo (0 : ℝ) 1, |E.vvQuantile q| ≤ C)
    {q q' : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) (hq' : q' ∈ Icc (0 : ℝ) 1) :
    |E.vvPrimitive q - E.vvPrimitive q'| ≤ C * |q - q'| := by
  have hsub : ∀ r ∈ Icc (0 : ℝ) 1, IntervalIntegrable E.vvQuantile volume 0 r := fun r hr =>
    E.intervalIntegrable_vvQuantile.mono_set (by
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), uIcc_of_le hr.1]
      exact Icc_subset_Icc_right hr.2)
  have hdiff : E.vvPrimitive q - E.vvPrimitive q' = ∫ u in q'..q, E.vvQuantile u :=
    intervalIntegral.integral_interval_sub_left (hsub q hq) (hsub q' hq')
  rw [hdiff, ← Real.norm_eq_abs]
  refine intervalIntegral.norm_integral_le_of_norm_le_const_ae ?_
  have hnull : ∀ᵐ u ∂volume, u ∉ ({(0:ℝ), 1} : Set ℝ) := by
    rw [ae_iff]; simp only [not_not]
    have hset : {a : ℝ | a ∈ ({0, 1} : Set ℝ)} = {0, 1} := rfl
    rw [hset]
    exact measure_union_null (measure_singleton 0) (measure_singleton 1)
  filter_upwards [hnull] with u hu huIoc
  rw [Real.norm_eq_abs]
  have hu_mem : u ∈ Icc (0 : ℝ) 1 := by
    rw [uIoc_eq_union] at huIoc
    rcases huIoc with h | h
    · exact ⟨le_trans hq'.1 h.1.le, le_trans h.2 hq.2⟩
    · exact ⟨le_trans hq.1 h.1.le, le_trans h.2 hq'.2⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hu
  exact hC u ⟨lt_of_le_of_ne hu_mem.1 (Ne.symm hu.1), lt_of_le_of_ne hu_mem.2 hu.2⟩

/-- The right derivative of `Ĥ` on `(0, 1)` is bounded in absolute value by `C`, the bound on
`|h|`. -/
lemma ironedPrimitive_rightDeriv_abs_le {C : ℝ}
    (hC : ∀ q ∈ Ioo (0 : ℝ) 1, |E.vvQuantile q| ≤ C) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    |derivWithin E.ironedPrimitive (Ioi x) x| ≤ C := by
  have hconv : ConvexOn ℝ (Icc (0:ℝ) 1) E.ironedPrimitive := E.ironedPrimitive_convexOn
  have hcont : ContinuousOn E.vvPrimitive (Icc (0:ℝ) 1) := E.vvPrimitive_continuousOn
  have hxint : x ∈ interior (Icc (0:ℝ) 1) := by rw [interior_Icc]; exact hx
  have hx0 : (0:ℝ) < x := hx.1
  have hx1 : x < (1:ℝ) := hx.2
  have h0mem : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have h1mem : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨by norm_num, le_refl _⟩
  have hle : ∀ q ∈ Icc (0:ℝ) 1, E.ironedPrimitive q ≤ E.vvPrimitive q := fun q hq =>
    convexEnvelope_le_self (by norm_num) hcont hq
  have hmin1 : IsAffineMinorant 0 1 E.vvPrimitive C (E.vvPrimitive 1 - C) := by
    intro t ht
    have hlip := E.vvPrimitive_sub_le hC h1mem ht
    rw [abs_le, abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)] at hlip
    linarith [hlip.2]
  have hmin0 : IsAffineMinorant 0 1 E.vvPrimitive (-C) (E.vvPrimitive 0) := by
    intro t ht
    have hlip := E.vvPrimitive_sub_le hC ht h0mem
    rw [abs_le, abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - 0)] at hlip
    linarith [hlip.1]
  have hge1 : ∀ q ∈ Icc (0:ℝ) 1, C * q + (E.vvPrimitive 1 - C) ≤ E.ironedPrimitive q := fun q hq =>
    convexEnvelope_ge_affineMinorant hmin1 hq
  have hge0 : ∀ q ∈ Icc (0:ℝ) 1, (-C) * q + E.vvPrimitive 0 ≤ E.ironedPrimitive q := fun q hq =>
    convexEnvelope_ge_affineMinorant hmin0 hq
  have hupper : derivWithin E.ironedPrimitive (Ioi x) x ≤ C := by
    refine (hconv.rightDeriv_le_slope_of_mem_interior hxint h1mem hx1).trans ?_
    rw [slope_def_field, div_le_iff₀ (by linarith : (0:ℝ) < 1 - x)]
    have h1 : E.ironedPrimitive 1 ≤ E.vvPrimitive 1 := hle 1 h1mem
    have h2 : C * x + (E.vvPrimitive 1 - C) ≤ E.ironedPrimitive x := hge1 x ⟨hx0.le, hx1.le⟩
    nlinarith [h1, h2]
  have hlower : -C ≤ derivWithin E.ironedPrimitive (Ioi x) x := by
    have hsl : slope E.ironedPrimitive 0 x ≤ derivWithin E.ironedPrimitive (Iio x) x :=
      hconv.slope_le_leftDeriv_of_mem_interior h0mem hxint hx0
    have hlr : derivWithin E.ironedPrimitive (Iio x) x
        ≤ derivWithin E.ironedPrimitive (Ioi x) x :=
      hconv.leftDeriv_le_rightDeriv_of_mem_interior hxint
    refine le_trans ?_ (le_trans hsl hlr)
    rw [slope_def_field, sub_zero, le_div_iff₀ hx0]
    have h1 : E.ironedPrimitive 0 ≤ E.vvPrimitive 0 := hle 0 h0mem
    have h2 : (-C) * x + E.vvPrimitive 0 ≤ E.ironedPrimitive x := hge0 x ⟨hx0.le, hx1.le⟩
    nlinarith [h1, h2]
  rw [abs_le]; exact ⟨hlower, hupper⟩

/-- The right derivative of `Ĥ` is bounded below on `(0, 1)` (`Ĥ` is Lipschitz). -/
lemma ironedPrimitive_rightDeriv_bddBelow :
    BddBelow ((fun x => derivWithin E.ironedPrimitive (Ioi x) x) '' Ioo (0 : ℝ) 1) := by
  obtain ⟨C, _, hC⟩ := E.exists_bound_vvQuantile
  refine ⟨-C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (abs_le.mp (E.ironedPrimitive_rightDeriv_abs_le hC hx)).1

/-- The right derivative of `Ĥ` is bounded above on `(0, 1)` (`Ĥ` is Lipschitz). -/
lemma ironedPrimitive_rightDeriv_bddAbove :
    BddAbove ((fun x => derivWithin E.ironedPrimitive (Ioi x) x) '' Ioo (0 : ℝ) 1) := by
  obtain ⟨C, _, hC⟩ := E.exists_bound_vvQuantile
  refine ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (abs_le.mp (E.ironedPrimitive_rightDeriv_abs_le hC hx)).2

/-! ### The ironed virtual value -/

/-- `ĥ(q) = Ĥ'₊(q)`: The (monotone) right derivative of the convex hull, in quantile space. -/
def ironedVVQuantile (q : ℝ) : ℝ :=
  (E.ironedPrimitive_convexOn).rightDerivExtend (by norm_num) q

/-- `ψ̄(θ) = ĥ(F(θ))`: The **ironed virtual value**, monotone by construction. -/
def ironedVirtualValue (θ : ℝ) : ℝ := E.ironedVVQuantile (E.dist.cdf θ)

@[simp] lemma ironedVirtualValue_def (θ : ℝ) :
    E.ironedVirtualValue θ = E.ironedVVQuantile (E.dist.cdf θ) := rfl

/-- `ĥ` is globally monotone. -/
lemma ironedVVQuantile_monotone : Monotone E.ironedVVQuantile :=
  (E.ironedPrimitive_convexOn).rightDerivExtend_monotone (by norm_num)
    E.ironedPrimitive_rightDeriv_bddBelow E.ironedPrimitive_rightDeriv_bddAbove

/-- **The ironed virtual value is monotone on the type interval.** Ironing always produces a
regular virtual value, so the ironed allocation is implementable. -/
theorem ironedVirtualValue_monotone : MonotoneOn E.ironedVirtualValue E.types := by
  intro θ _ θ' _ hθθ'
  exact E.ironedVVQuantile_monotone (E.dist.cdf.mono hθθ')

/-- If the ironed primitive `Ĥ` equals the affine function `m·x + c` throughout
`Ioo p r ⊆ Ioo 0 1`, then its right derivative `ĥ` equals the slope `m` at every point of that
interval. -/
lemma ironedVVQuantile_eq_of_affineOn {p r m c : ℝ} (hpr : 0 ≤ p)
    (hr1 : r ≤ 1) (haffine : ∀ x ∈ Ioo p r, E.ironedPrimitive x = m * x + c)
    {t : ℝ} (ht : t ∈ Ioo p r) :
    E.ironedVVQuantile t = m := by
  have htoo : t ∈ Ioo (0:ℝ) 1 := ⟨lt_of_le_of_lt hpr ht.1, lt_of_lt_of_le ht.2 hr1⟩
  rw [ironedVVQuantile,
    (E.ironedPrimitive_convexOn).rightDerivExtend_eq_of_mem_Ioo (by norm_num) htoo]
  have haff : HasDerivWithinAt (fun x => m * x + c) m (Ioi t) t := by
    simpa using ((hasDerivWithinAt_id t (Ioi t)).const_mul m).add_const c
  have hmem_nhds : Ioo p r ∈ nhds t := Ioo_mem_nhds ht.1 ht.2
  have heq : E.ironedPrimitive =ᶠ[nhds t] fun x => m * x + c :=
    Filter.eventuallyEq_of_mem hmem_nhds haffine
  exact (haff.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds)
    (heq.eq_of_nhds)).derivWithin (uniqueDiffWithinAt_Ioi t)

/-! ### Integrability for the change of variables -/

/-- The quantile pullback `X = x ∘ F⁻¹` of a monotone allocation is monotone on `(0, 1)`. -/
lemma allocQuantile_monotoneOn (M : DirectMechanism E) (hmono : MonotoneAlloc M.alloc) :
    MonotoneOn (fun t => M.x (E.quantileInv t)) (Ioo (0 : ℝ) 1) := by
  haveI := E.dist.toMeasure_isProbability
  intro s hs t ht hst
  exact hmono (E.quantileInv_mem hs) (E.quantileInv_mem ht)
    (Measure.monotoneOn_quantile hs ht hst)

/-- The ironed virtual value `ψ̄ = ĥ ∘ F` is measurable. -/
lemma ironedVirtualValue_measurable : Measurable E.ironedVirtualValue :=
  E.ironedVVQuantile_monotone.measurable.comp E.dist.cdf_continuous.measurable

/-- The ironed virtual value satisfies `ĥ 0 ≤ ψ̄ θ ≤ ĥ 1` for all `θ`. -/
lemma ironedVirtualValue_bdd (θ : ℝ) :
    E.ironedVVQuantile 0 ≤ E.ironedVirtualValue θ ∧
      E.ironedVirtualValue θ ≤ E.ironedVVQuantile 1 := by
  refine ⟨E.ironedVVQuantile_monotone (E.dist.cdf_nonneg θ),
    E.ironedVVQuantile_monotone (E.dist.cdf_le_one θ)⟩

/-- A monotone allocation is AE-strongly-measurable against the type measure. -/
lemma alloc_aestronglyMeasurable_toMeasure (M : DirectMechanism E)
    (hmono : MonotoneAlloc M.alloc) :
    AEStronglyMeasurable M.x E.dist.toMeasure := by
  have hcompl : E.dist.toMeasure (Icc E.θlo E.θhi)ᶜ = 0 := by
    rw [E.dist.toMeasure_eq, withDensity_apply _ (measurableSet_Icc.compl)]
    rw [setLIntegral_congr_fun (measurableSet_Icc.compl)
      (fun θ hθ => by rw [E.density_eq_zero_of_notMem hθ, ENNReal.ofReal_zero])]
    simp
  have hae : ∀ᵐ θ ∂E.dist.toMeasure, θ ∈ Icc E.θlo E.θhi := by
    rw [Filter.Eventually, mem_ae_iff, setOf_mem_eq]; exact hcompl
  have hxmono : MonotoneOn M.x (Icc E.θlo E.θhi) := hmono
  have hxvol : AEMeasurable M.x (volume.restrict (Icc E.θlo E.θhi)) :=
    aemeasurable_restrict_of_monotoneOn measurableSet_Icc hxmono
  have hac : (E.dist.toMeasure.restrict (Icc E.θlo E.θhi)).AbsolutelyContinuous
      (volume.restrict (Icc E.θlo E.θhi)) := by
    rw [E.dist.toMeasure_eq]
    exact (withDensity_absolutelyContinuous _ _).restrict _
  have hxtoMrestrict : AEMeasurable M.x (E.dist.toMeasure.restrict (Icc E.θlo E.θhi)) :=
    hxvol.mono_ac hac
  have hxtoM : AEMeasurable M.x E.dist.toMeasure := by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]; exact hxtoMrestrict
  exact hxtoM.aestronglyMeasurable

/-- `ψ · x` is integrable against the type measure. -/
lemma integrable_virtualValue_mul_alloc (M : DirectMechanism E)
    (hmono : MonotoneAlloc M.alloc) :
    Integrable (fun θ => E.virtualValue θ * M.x θ) E.dist.toMeasure := by
  haveI := E.dist.toMeasure_isProbability
  obtain ⟨Cψ, hψ⟩ := (isCompact_Icc (a := E.θlo) (b := E.θhi)).exists_bound_of_continuousOn
    E.virtualValue_continuousOn
  have hψmble : AEStronglyMeasurable E.virtualValue E.dist.toMeasure := by
    rw [E.dist.toMeasure_eq]
    exact (E.virtualValue_measurable.aemeasurable.mono_ac
      (withDensity_absolutelyContinuous _ _)).aestronglyMeasurable
  have hxmble : AEStronglyMeasurable M.x E.dist.toMeasure :=
    E.alloc_aestronglyMeasurable_toMeasure M hmono
  have hbound : ∀ᵐ θ ∂E.dist.toMeasure, ‖E.virtualValue θ * M.x θ‖ ≤ Cψ := by
    have hae : ∀ᵐ θ ∂E.dist.toMeasure, θ ∈ Icc E.θlo E.θhi := by
      rw [Filter.Eventually, mem_ae_iff, setOf_mem_eq]
      rw [E.dist.toMeasure_eq, withDensity_apply _ (measurableSet_Icc.compl)]
      rw [setLIntegral_congr_fun (measurableSet_Icc.compl)
        (fun θ hθ => by rw [E.density_eq_zero_of_notMem hθ, ENNReal.ofReal_zero])]
      simp
    filter_upwards [hae] with θ hθ
    rw [Real.norm_eq_abs, abs_mul]
    have hxle : |M.x θ| ≤ 1 := abs_le.mpr ⟨by linarith [M.x_nonneg θ], M.x_le_one θ⟩
    have hψle : |E.virtualValue θ| ≤ Cψ := by simpa [Real.norm_eq_abs] using hψ θ hθ
    have hCψ : 0 ≤ Cψ := le_trans (abs_nonneg _) hψle
    calc |E.virtualValue θ| * |M.x θ| ≤ Cψ * 1 := by
            apply mul_le_mul hψle hxle (abs_nonneg _) hCψ
      _ = Cψ := by ring
  exact Integrable.mono' (integrable_const Cψ) (hψmble.mul hxmble) hbound

/-- `ψ̄ · x` is integrable against the type measure. -/
lemma integrable_ironedVirtualValue_mul_alloc (M : DirectMechanism E)
    (hmono : MonotoneAlloc M.alloc) :
    Integrable (fun θ => E.ironedVirtualValue θ * M.x θ) E.dist.toMeasure := by
  haveI := E.dist.toMeasure_isProbability
  have hψmble : AEStronglyMeasurable E.ironedVirtualValue E.dist.toMeasure :=
    E.ironedVirtualValue_measurable.aestronglyMeasurable
  have hxmble : AEStronglyMeasurable M.x E.dist.toMeasure :=
    E.alloc_aestronglyMeasurable_toMeasure M hmono
  set Cψ := max |E.ironedVVQuantile 0| |E.ironedVVQuantile 1| with hCψ_def
  have hbound : ∀ᵐ θ ∂E.dist.toMeasure, ‖E.ironedVirtualValue θ * M.x θ‖ ≤ Cψ := by
    refine ae_of_all _ fun θ => ?_
    rw [Real.norm_eq_abs, abs_mul]
    have hxle : |M.x θ| ≤ 1 := abs_le.mpr ⟨by linarith [M.x_nonneg θ], M.x_le_one θ⟩
    have hψle : |E.ironedVirtualValue θ| ≤ Cψ := by
      obtain ⟨h0, h1⟩ := E.ironedVirtualValue_bdd θ
      rw [abs_le]
      exact ⟨le_trans (neg_le_neg (le_max_left _ _) |>.trans (neg_abs_le _ |>.trans h0))
        (le_refl _), le_trans h1 (le_trans (le_abs_self _) (le_max_right _ _))⟩
    have hCψ : 0 ≤ Cψ := le_trans (abs_nonneg _) hψle
    calc |E.ironedVirtualValue θ| * |M.x θ| ≤ Cψ * 1 :=
            mul_le_mul hψle hxle (abs_nonneg _) hCψ
      _ = Cψ := by ring
  exact Integrable.mono' (integrable_const Cψ) (hψmble.mul hxmble) hbound

/-- The convex hull `Ĥ` is continuous on `[0, 1]`. -/
lemma ironedPrimitive_continuousOn : ContinuousOn E.ironedPrimitive (Icc (0 : ℝ) 1) := by
  have hcont := E.vvPrimitive_continuousOn
  obtain ⟨C, _, hC⟩ := E.exists_bound_vvQuantile
  have h0mem : (0:ℝ) ∈ Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr (by norm_num)
  have h1mem : (1:ℝ) ∈ Icc (0:ℝ) 1 := Set.right_mem_Icc.mpr (by norm_num)
  have hconv := E.ironedPrimitive_convexOn
  set L : ℝ → ℝ := fun t => max (-C * t + E.vvPrimitive 0) (C * t + (E.vvPrimitive 1 - C)) with hL
  have hmin0 : IsAffineMinorant 0 1 E.vvPrimitive (-C) (E.vvPrimitive 0) := by
    intro t ht
    have hlip := E.vvPrimitive_sub_le hC ht h0mem
    rw [abs_le, abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - 0)] at hlip
    linarith [hlip.1]
  have hmin1 : IsAffineMinorant 0 1 E.vvPrimitive C (E.vvPrimitive 1 - C) := by
    intro t ht
    have hlip := E.vvPrimitive_sub_le hC h1mem ht
    rw [abs_le, abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)] at hlip
    linarith [hlip.2]
  have hLcont : Continuous L := ((continuous_const.mul continuous_id).add continuous_const).max
    ((continuous_const.mul continuous_id).add continuous_const)
  have hLle : ∀ x ∈ Icc (0:ℝ) 1, L x ≤ E.ironedPrimitive x := fun x hx =>
    max_le (convexEnvelope_ge_affineMinorant hmin0 hx) (convexEnvelope_ge_affineMinorant hmin1 hx)
  have hleH : ∀ x ∈ Icc (0:ℝ) 1, E.ironedPrimitive x ≤ E.vvPrimitive x := fun x hx =>
    convexEnvelope_le_self (by norm_num) hcont hx
  have hCnn : (0:ℝ) ≤ C := by
    have := E.vvPrimitive_sub_le hC h1mem h0mem
    rw [abs_le] at this; nlinarith [this.1, this.2, abs_nonneg (E.vvPrimitive 1 - E.vvPrimitive 0)]
  have hL0 : L 0 = E.vvPrimitive 0 := by
    rw [hL]; simp only [mul_zero, zero_add]
    rw [max_eq_left]; have := E.vvPrimitive_sub_le hC h1mem h0mem
    rw [abs_le, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 - 0)] at this; linarith [this.2]
  have hL1 : L 1 = E.vvPrimitive 1 := by
    change max (-C * 1 + E.vvPrimitive 0) (C * 1 + (E.vvPrimitive 1 - C)) = E.vvPrimitive 1
    rw [max_eq_right]; · ring_nf
    have := E.vvPrimitive_sub_le hC h1mem h0mem
    rw [abs_le, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 - 0)] at this; nlinarith [this.1]
  have hsqueeze : ∀ p ∈ Icc (0:ℝ) 1, L p = E.vvPrimitive p →
      ContinuousWithinAt E.ironedPrimitive (Icc (0:ℝ) 1) p := by
    intro p hp hLp
    have hĤp : E.ironedPrimitive p = E.vvPrimitive p :=
      le_antisymm (hleH p hp) (hLp ▸ hLle p hp)
    have hgL : Filter.Tendsto L (𝓝[Icc (0:ℝ) 1] p) (𝓝 (E.ironedPrimitive p)) := by
      rw [hĤp, ← hLp]; exact hLcont.continuousWithinAt
    have hgH : Filter.Tendsto E.vvPrimitive (𝓝[Icc (0:ℝ) 1] p) (𝓝 (E.ironedPrimitive p)) := by
      rw [hĤp]; exact (hcont p hp)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hgL hgH
      (eventually_nhdsWithin_of_forall hLle) (eventually_nhdsWithin_of_forall hleH)
  intro x hx
  rcases eq_or_lt_of_le hx.1 with hx0 | hx0
  · subst hx0; exact hsqueeze 0 h0mem hL0
  rcases eq_or_lt_of_le hx.2 with hx1 | hx1
  · subst hx1; exact hsqueeze 1 h1mem hL1
  · exact ((hconv.continuousOn_Ioo (by norm_num)).continuousAt
      (Ioo_mem_nhds hx0 hx1)).continuousWithinAt

/-- **Cumulative identity:** `∫₀ˢ (ĥ − h) = Ĥ(s) − H(s)` for `s ∈ [0, 1]`. -/
lemma integral_ironedVVQuantile_sub_vvQuantile {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∫ t in (0:ℝ)..s, (E.ironedVVQuantile t - E.vvQuantile t)
      = E.ironedPrimitive s - E.vvPrimitive s := by
  have hconv := E.ironedPrimitive_convexOn
  have hcont := E.vvPrimitive_continuousOn
  obtain ⟨C, _, hC⟩ := E.exists_bound_vvQuantile
  have hĤ0 : E.ironedPrimitive 0 = E.vvPrimitive 0 := by
    refine convexEnvelope_eq_of_affineMinorant_contact (by norm_num) hcont
      (Set.left_mem_Icc.mpr (by norm_num)) (m := -C) (c := E.vvPrimitive 0) ?_ (by ring)
    intro t ht
    have hlip := E.vvPrimitive_sub_le hC ht (Set.left_mem_Icc.mpr (by norm_num))
    rw [abs_le, abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t - 0)] at hlip
    linarith [hlip.1]
  have h0mem : (0:ℝ) ∈ Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr (by norm_num)
  have hĥ_int : ∫ t in (0:ℝ)..s, E.ironedVVQuantile t
      = E.ironedPrimitive s - E.ironedPrimitive 0 := by
    rw [← hconv.ftc_rightDeriv (by norm_num) E.ironedPrimitive_continuousOn
      E.ironedPrimitive_rightDeriv_bddBelow
      E.ironedPrimitive_rightDeriv_bddAbove hs.1 hs.2]
    refine intervalIntegral.integral_congr_ae ?_
    have hone : ∀ᵐ t ∂volume, t ≠ (1:ℝ) := by
      rw [ae_iff]; simp only [not_not]; exact measure_singleton 1
    filter_upwards [hone] with t ht1 ht
    rw [uIoc_of_le hs.1] at ht
    have htoo : t ∈ Ioo (0:ℝ) 1 :=
      ⟨ht.1, lt_of_le_of_ne (le_trans ht.2 hs.2) ht1⟩
    exact hconv.rightDerivExtend_eq_of_mem_Ioo (by norm_num) htoo
  have hh_int : ∫ t in (0:ℝ)..s, E.vvQuantile t = E.vvPrimitive s := rfl
  have hsub : ∫ t in (0:ℝ)..s, (E.ironedVVQuantile t - E.vvQuantile t)
      = (∫ t in (0:ℝ)..s, E.ironedVVQuantile t) - ∫ t in (0:ℝ)..s, E.vvQuantile t := by
    refine intervalIntegral.integral_sub E.ironedVVQuantile_monotone.intervalIntegrable ?_
    exact E.intervalIntegrable_vvQuantile.mono_set (by
      rw [uIcc_of_le hs.1, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Icc_subset_Icc_right hs.2)
  have hH0 : E.vvPrimitive 0 = 0 := by rw [vvPrimitive, intervalIntegral.integral_same]
  rw [hsub, hĥ_int, hh_int, hĤ0, hH0]
  ring

/-! ### The ironing revenue bound -/

/-- **Ironing weakly raises virtual surplus.** For any monotone allocation, expected virtual
surplus under the ironed virtual value dominates that under the raw virtual value:
`𝔼[ψ·x] ≤ 𝔼[ψ̄·x]`. -/
theorem expected_virtualSurplus_le_ironed (M : DirectMechanism E)
    (hmono : MonotoneAlloc M.alloc) :
    E.dist.expect (fun θ => E.virtualValue θ * M.x θ)
      ≤ E.dist.expect (fun θ => E.ironedVirtualValue θ * M.x θ) := by
  haveI := E.dist.toMeasure_isProbability
  set X : ℝ → ℝ := fun t => M.x (E.quantileInv t) with hX_def
  have hlhs : E.dist.expect (fun θ => E.virtualValue θ * M.x θ)
      = ∫ t in Ioo (0:ℝ) 1, E.vvQuantile t * X t := by
    rw [E.dist.expect_eq_integral_quantile (E.integrable_virtualValue_mul_alloc M hmono)]
    rfl
  have hrhs : E.dist.expect (fun θ => E.ironedVirtualValue θ * M.x θ)
      = ∫ t in Ioo (0:ℝ) 1, E.ironedVVQuantile t * X t := by
    rw [E.dist.expect_eq_integral_quantile (E.integrable_ironedVirtualValue_mul_alloc M hmono)]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    change E.ironedVVQuantile (E.dist.cdf (E.quantileInv t)) * M.x (E.quantileInv t)
      = E.ironedVVQuantile t * X t
    rw [quantileInv, E.dist.cdf_quantile ht]
    rfl
  rw [hlhs, hrhs]
  have hmap : E.dist.toMeasure = (volume.restrict (Ioo (0:ℝ) 1)).map E.quantileInv :=
    Measure.map_quantile_volume_Ioo.symm
  have hqae : AEMeasurable E.quantileInv (volume.restrict (Ioo (0:ℝ) 1)) :=
    Measure.aemeasurable_quantile_restrict_Ioo
  have hint_lhs : IntegrableOn (fun t => E.vvQuantile t * X t) (Ioo (0:ℝ) 1) := by
    have hg := E.integrable_virtualValue_mul_alloc M hmono
    rw [hmap, integrable_map_measure (hmap ▸ hg.1) hqae] at hg
    exact hg
  have hint_rhs : IntegrableOn (fun t => E.ironedVVQuantile t * X t) (Ioo (0:ℝ) 1) := by
    have hg := E.integrable_ironedVirtualValue_mul_alloc M hmono
    rw [hmap, integrable_map_measure (hmap ▸ hg.1) hqae] at hg
    refine hg.congr ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun t ht => ?_))
    change E.ironedVirtualValue (E.quantileInv t) * M.x (E.quantileInv t)
      = E.ironedVVQuantile t * X t
    rw [ironedVirtualValue, quantileInv, E.dist.cdf_quantile ht]; rfl
  have hsplit : ∫ t in Ioo (0:ℝ) 1, (E.ironedVVQuantile t - E.vvQuantile t) * X t
      = (∫ t in Ioo (0:ℝ) 1, E.ironedVVQuantile t * X t)
        - ∫ t in Ioo (0:ℝ) 1, E.vvQuantile t * X t := by
    rw [← integral_sub hint_rhs hint_lhs]
    exact setIntegral_congr_fun measurableSet_Ioo (fun t _ => by ring)
  have hcore : 0 ≤ ∫ t in Ioo (0:ℝ) 1, (E.ironedVVQuantile t - E.vvQuantile t) * X t := by
    set g : ℝ → ℝ := fun t => E.ironedVVQuantile t - E.vvQuantile t with hg_def
    set G : ℝ → ℝ := fun t => E.ironedPrimitive t - E.vvPrimitive t with hG_def
    set Xe : ℝ → ℝ := fun t => if t ≤ 0 then (0:ℝ) else if 1 ≤ t then 1 else X t with hXe
    have hX0 : ∀ t, 0 ≤ X t := fun t => M.x_nonneg _
    have hX1 : ∀ t, X t ≤ 1 := fun t => M.x_le_one _
    have hXmono : ∀ u v, 0 < u → u ≤ v → v < 1 → X u ≤ X v := fun u v hu0 huv hv1 =>
      hmono (E.quantileInv_mem ⟨hu0, lt_of_le_of_lt huv hv1⟩)
        (E.quantileInv_mem ⟨lt_of_lt_of_le hu0 huv, hv1⟩)
        (Measure.monotoneOn_quantile ⟨hu0, lt_of_le_of_lt huv hv1⟩
          ⟨lt_of_lt_of_le hu0 huv, hv1⟩ huv)
    have hXe_mono : Monotone Xe := by
      intro u v huv
      simp only [hXe]
      by_cases hv0 : v ≤ 0
      · rw [if_pos (le_trans huv hv0), if_pos hv0]
      by_cases hu0 : u ≤ 0
      · rw [if_pos hu0]
        by_cases hv1 : 1 ≤ v
        · rw [if_neg hv0, if_pos hv1]; norm_num
        · rw [if_neg hv0, if_neg hv1]; exact hX0 v
      · rw [if_neg hu0]
        by_cases hu1 : 1 ≤ u
        · rw [if_pos hu1, if_neg hv0, if_pos (le_trans hu1 huv)]
        · rw [if_neg hu1]
          by_cases hv1 : 1 ≤ v
          · rw [if_neg hv0, if_pos hv1]; exact hX1 u
          · rw [if_neg hv0, if_neg hv1]
            exact hXmono u v (not_le.mp hu0) huv (not_le.mp hv1)
    have hXe_eq : ∀ t ∈ Ioo (0:ℝ) 1, Xe t = X t := by
      intro t ht; simp only [hXe, if_neg (not_le.mpr ht.1), if_neg (not_le.mpr ht.2)]
    have hg_ii : IntervalIntegrable g volume 0 1 :=
      E.ironedVVQuantile_monotone.intervalIntegrable.sub E.intervalIntegrable_vvQuantile
    have hcum : ∀ s ∈ Icc (0:ℝ) 1, ∫ t in (0:ℝ)..s, g t = G s :=
      fun s hs => E.integral_ironedVVQuantile_sub_vvQuantile hs
    obtain ⟨C, _, hC⟩ := E.exists_bound_vvQuantile
    have h1mem : (1:ℝ) ∈ Icc (0:ℝ) 1 := Set.right_mem_Icc.mpr (by norm_num)
    have hG1 : G 1 = 0 := by
      have hĤ1 : E.ironedPrimitive 1 = E.vvPrimitive 1 := by
        refine convexEnvelope_eq_of_affineMinorant_contact (by norm_num)
          E.vvPrimitive_continuousOn h1mem (m := C) (c := E.vvPrimitive 1 - C) ?_ (by ring)
        intro t ht
        have hlip := E.vvPrimitive_sub_le hC h1mem ht
        rw [abs_le, abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)] at hlip
        linarith [hlip.2]
      simp only [hG_def, hĤ1, sub_self]
    have hg01 : ∫ t in (0:ℝ)..1, g t = 0 := by rw [hcum 1 h1mem, hG1]
    have htail : ∀ s ∈ Ioc (0:ℝ) 1, ∫ t in s..1, g t = -G s := by
      intro s hs
      have hii0s : IntervalIntegrable g volume 0 s := hg_ii.mono_set (by
        rw [uIcc_of_le hs.1.le, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact Icc_subset_Icc_right hs.2)
      have hiis1 : IntervalIntegrable g volume s 1 := hg_ii.mono_set (by
        rw [uIcc_of_le hs.2, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
        exact Icc_subset_Icc_left hs.1.le)
      have hsplit_g : (∫ t in (0:ℝ)..s, g t) + ∫ t in s..(1:ℝ), g t = ∫ t in (0:ℝ)..1, g t :=
        intervalIntegral.integral_add_adjacent_intervals hii0s hiis1
      rw [hcum s ⟨hs.1.le, hs.2⟩, hg01] at hsplit_g
      linarith [hsplit_g]
    set Xsf := Monotone.stieltjes hXe_mono with hXsf
    set μX := Monotone.stieltjesMeasure hXe_mono with hμX
    have hX_eq_Xsf : (fun t => g t * X t) =ᵐ[volume.restrict (Ioo (0:ℝ) 1)]
        fun t => g t * Xsf t := by
      have hae : Xe =ᵐ[volume.restrict (Ioo (0:ℝ) 1)] Xsf :=
        (Filter.EventuallyEq.symm (stieltjes_eq_ae hXe_mono)).restrict
      have hXeqXe : X =ᵐ[volume.restrict (Ioo (0:ℝ) 1)] Xe :=
        (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun t ht => (hXe_eq t ht).symm)
      filter_upwards [hXeqXe, hae] with t h1 h2
      rw [h1, h2]
    have hg_oc : IntegrableOn g (Ioc (0:ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hg_ii
    have hXsf_bdd : ∀ᵐ t ∂(volume.restrict (Ioc (0:ℝ) 1)),
        ‖Xsf t‖ ≤ max |Xsf 0| |Xsf 1| := by
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_le]
      have hlo : Xsf 0 ≤ Xsf t := Xsf.mono ht.1.le
      have hhi : Xsf t ≤ Xsf 1 := Xsf.mono ht.2
      exact ⟨le_trans (neg_le_neg (le_max_left _ _)) (neg_abs_le _ |>.trans hlo),
        le_trans hhi (le_trans (le_abs_self _) (le_max_right _ _))⟩
    have hg_Xsf_oc : IntegrableOn (fun t => g t * Xsf t) (Ioc (0:ℝ) 1) volume := by
      rw [show (fun t => g t * Xsf t) = fun t => Xsf t * g t from funext fun t => mul_comm _ _]
      exact hg_oc.bdd_mul Xsf.mono.measurable.aestronglyMeasurable.restrict hXsf_bdd
    have hg_Xsf_ii : IntervalIntegrable (fun t => g t * Xsf t) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr hg_Xsf_oc
    have hstep1 : ∫ t in Ioo (0:ℝ) 1, g t * X t = ∫ t in Ioc (0:ℝ) 1, g t * Xsf t := by
      rw [setIntegral_congr_set Ioo_ae_eq_Ioc]
      refine setIntegral_congr_ae measurableSet_Ioc ?_
      have hX_eq_Xsf' : (fun t => g t * X t) =ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
          fun t => g t * Xsf t := by
        rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hX_eq_Xsf
      exact (ae_restrict_iff' measurableSet_Ioc).mp hX_eq_Xsf'
    have hstep2 : ∫ t in Ioc (0:ℝ) 1, g t * Xsf t
        = ∫ t in (0:ℝ)..1, g t * (Xsf t - Xsf 0) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      have hexpand : ∀ t, g t * (Xsf t - Xsf 0) = g t * Xsf t - Xsf 0 * g t := fun t => by ring
      simp_rw [hexpand]
      rw [integral_sub hg_Xsf_oc (hg_oc.const_mul (Xsf 0))]
      have : ∫ t in Ioc (0:ℝ) 1, Xsf 0 * g t = Xsf 0 * ∫ t in (0:ℝ)..1, g t := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_const_mul]
      rw [this, hg01, mul_zero, sub_zero]
    have hstep3 : ∫ t in (0:ℝ)..1, g t * (Xsf t - Xsf 0)
        = ∫ s in Ioc (0:ℝ) 1, (∫ t in s..1, g t) ∂μX :=
      integral_triangle_swap_stieltjes hXe_mono (by norm_num) hg_ii
    rw [hstep1, hstep2, hstep3]
    refine setIntegral_nonneg measurableSet_Ioc (fun s hs => ?_)
    rw [htail s hs, hG_def]
    simp only [neg_sub]
    exact sub_nonneg.mpr (convexEnvelope_le_self (by norm_num) E.vvPrimitive_continuousOn
      ⟨hs.1.le, hs.2⟩)
  linarith [hcore, hsplit]

/-- For a monotone allocation that is constant on every level set of the ironed virtual value, the
quantile-space gap integral `∫_{Ioo 0 1} (ĥ − h) X` equals zero. -/
theorem ironingGap_eq_zero_of_constOn_levelSet (M : DirectMechanism E)
    (hmono : MonotoneAlloc M.alloc)
    (hflat : ∀ {t t' : ℝ}, E.ironedVirtualValue t = E.ironedVirtualValue t' → M.x t = M.x t') :
    ∫ t in Ioo (0:ℝ) 1, (E.ironedVVQuantile t - E.vvQuantile t)
        * M.x (E.quantileInv t) = 0 := by
  haveI := E.dist.toMeasure_isProbability
  set X : ℝ → ℝ := fun t => M.x (E.quantileInv t) with hX_def
  set g : ℝ → ℝ := fun t => E.ironedVVQuantile t - E.vvQuantile t with hg_def
  set G : ℝ → ℝ := fun t => E.ironedPrimitive t - E.vvPrimitive t with hG_def
  set Xe : ℝ → ℝ := fun t => if t ≤ 0 then (0:ℝ) else if 1 ≤ t then 1 else X t with hXe
  have hX0 : ∀ t, 0 ≤ X t := fun t => M.x_nonneg _
  have hX1 : ∀ t, X t ≤ 1 := fun t => M.x_le_one _
  have hXmono : ∀ u v, 0 < u → u ≤ v → v < 1 → X u ≤ X v := fun u v hu0 huv hv1 =>
    hmono (E.quantileInv_mem ⟨hu0, lt_of_le_of_lt huv hv1⟩)
      (E.quantileInv_mem ⟨lt_of_lt_of_le hu0 huv, hv1⟩)
      (Measure.monotoneOn_quantile ⟨hu0, lt_of_le_of_lt huv hv1⟩
        ⟨lt_of_lt_of_le hu0 huv, hv1⟩ huv)
  have hXe_mono : Monotone Xe := by
    intro u v huv
    simp only [hXe]
    by_cases hv0 : v ≤ 0
    · rw [if_pos (le_trans huv hv0), if_pos hv0]
    by_cases hu0 : u ≤ 0
    · rw [if_pos hu0]
      by_cases hv1 : 1 ≤ v
      · rw [if_neg hv0, if_pos hv1]; norm_num
      · rw [if_neg hv0, if_neg hv1]; exact hX0 v
    · rw [if_neg hu0]
      by_cases hu1 : 1 ≤ u
      · rw [if_pos hu1, if_neg hv0, if_pos (le_trans hu1 huv)]
      · rw [if_neg hu1]
        by_cases hv1 : 1 ≤ v
        · rw [if_neg hv0, if_pos hv1]; exact hX1 u
        · rw [if_neg hv0, if_neg hv1]
          exact hXmono u v (not_le.mp hu0) huv (not_le.mp hv1)
  have hXe_eq : ∀ t ∈ Ioo (0:ℝ) 1, Xe t = X t := by
    intro t ht; simp only [hXe, if_neg (not_le.mpr ht.1), if_neg (not_le.mpr ht.2)]
  have hg_ii : IntervalIntegrable g volume 0 1 :=
    E.ironedVVQuantile_monotone.intervalIntegrable.sub E.intervalIntegrable_vvQuantile
  have hcum : ∀ s ∈ Icc (0:ℝ) 1, ∫ t in (0:ℝ)..s, g t = G s :=
    fun s hs => E.integral_ironedVVQuantile_sub_vvQuantile hs
  obtain ⟨C, _, hC⟩ := E.exists_bound_vvQuantile
  have h1mem : (1:ℝ) ∈ Icc (0:ℝ) 1 := Set.right_mem_Icc.mpr (by norm_num)
  have hG1 : G 1 = 0 := by
    have hĤ1 : E.ironedPrimitive 1 = E.vvPrimitive 1 := by
      refine convexEnvelope_eq_of_affineMinorant_contact (by norm_num)
        E.vvPrimitive_continuousOn h1mem (m := C) (c := E.vvPrimitive 1 - C) ?_ (by ring)
      intro t ht
      have hlip := E.vvPrimitive_sub_le hC h1mem ht
      rw [abs_le, abs_of_nonneg (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)] at hlip
      linarith [hlip.2]
    simp only [hG_def, hĤ1, sub_self]
  have hg01 : ∫ t in (0:ℝ)..1, g t = 0 := by rw [hcum 1 h1mem, hG1]
  have htail : ∀ s ∈ Ioc (0:ℝ) 1, ∫ t in s..1, g t = -G s := by
    intro s hs
    have hii0s : IntervalIntegrable g volume 0 s := hg_ii.mono_set (by
      rw [uIcc_of_le hs.1.le, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Icc_subset_Icc_right hs.2)
    have hiis1 : IntervalIntegrable g volume s 1 := hg_ii.mono_set (by
      rw [uIcc_of_le hs.2, uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Icc_subset_Icc_left hs.1.le)
    have hsplit_g : (∫ t in (0:ℝ)..s, g t) + ∫ t in s..(1:ℝ), g t = ∫ t in (0:ℝ)..1, g t :=
      intervalIntegral.integral_add_adjacent_intervals hii0s hiis1
    rw [hcum s ⟨hs.1.le, hs.2⟩, hg01] at hsplit_g
    linarith [hsplit_g]
  set Xsf := Monotone.stieltjes hXe_mono with hXsf
  set μX := Monotone.stieltjesMeasure hXe_mono with hμX
  have hX_eq_Xsf : (fun t => g t * X t) =ᵐ[volume.restrict (Ioo (0:ℝ) 1)]
      fun t => g t * Xsf t := by
    have hae : Xe =ᵐ[volume.restrict (Ioo (0:ℝ) 1)] Xsf :=
      (Filter.EventuallyEq.symm (stieltjes_eq_ae hXe_mono)).restrict
    have hXeqXe : X =ᵐ[volume.restrict (Ioo (0:ℝ) 1)] Xe :=
      (ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun t ht => (hXe_eq t ht).symm)
    filter_upwards [hXeqXe, hae] with t h1 h2
    rw [h1, h2]
  have hg_oc : IntegrableOn g (Ioc (0:ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hg_ii
  have hXsf_bdd : ∀ᵐ t ∂(volume.restrict (Ioc (0:ℝ) 1)),
      ‖Xsf t‖ ≤ max |Xsf 0| |Xsf 1| := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t ht => ?_)
    rw [Real.norm_eq_abs, abs_le]
    have hlo : Xsf 0 ≤ Xsf t := Xsf.mono ht.1.le
    have hhi : Xsf t ≤ Xsf 1 := Xsf.mono ht.2
    exact ⟨le_trans (neg_le_neg (le_max_left _ _)) (neg_abs_le _ |>.trans hlo),
      le_trans hhi (le_trans (le_abs_self _) (le_max_right _ _))⟩
  have hg_Xsf_oc : IntegrableOn (fun t => g t * Xsf t) (Ioc (0:ℝ) 1) volume := by
    rw [show (fun t => g t * Xsf t) = fun t => Xsf t * g t from funext fun t => mul_comm _ _]
    exact hg_oc.bdd_mul Xsf.mono.measurable.aestronglyMeasurable.restrict hXsf_bdd
  have hstep1 : ∫ t in Ioo (0:ℝ) 1, g t * X t = ∫ t in Ioc (0:ℝ) 1, g t * Xsf t := by
    rw [setIntegral_congr_set Ioo_ae_eq_Ioc]
    refine setIntegral_congr_ae measurableSet_Ioc ?_
    have hX_eq_Xsf' : (fun t => g t * X t) =ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
        fun t => g t * Xsf t := by
      rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hX_eq_Xsf
    exact (ae_restrict_iff' measurableSet_Ioc).mp hX_eq_Xsf'
  have hstep2 : ∫ t in Ioc (0:ℝ) 1, g t * Xsf t
      = ∫ t in (0:ℝ)..1, g t * (Xsf t - Xsf 0) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have hexpand : ∀ t, g t * (Xsf t - Xsf 0) = g t * Xsf t - Xsf 0 * g t := fun t => by ring
    simp_rw [hexpand]
    rw [integral_sub hg_Xsf_oc (hg_oc.const_mul (Xsf 0))]
    have : ∫ t in Ioc (0:ℝ) 1, Xsf 0 * g t = Xsf 0 * ∫ t in (0:ℝ)..1, g t := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1), integral_const_mul]
    rw [this, hg01, mul_zero, sub_zero]
  have hstep3 : ∫ t in (0:ℝ)..1, g t * (Xsf t - Xsf 0)
      = ∫ s in Ioc (0:ℝ) 1, (∫ t in s..1, g t) ∂μX :=
    integral_triangle_swap_stieltjes hXe_mono (by norm_num) hg_ii
  rw [hstep1, hstep2, hstep3]
  refine setIntegral_eq_zero_of_ae_eq_zero ?_
  have hnull : μX {s | s ∈ Ioc (0:ℝ) 1 ∧ E.ironedPrimitive s < E.vvPrimitive s} = 0 := by
    refine measure_null_of_locally_null _ (fun s hs => ?_)
    obtain ⟨hs_oc, hlt⟩ := hs
    have hs_oo : s ∈ Ioo (0:ℝ) 1 := by
      refine ⟨hs_oc.1, lt_of_le_of_ne hs_oc.2 (fun h1 => ?_)⟩
      have : E.ironedPrimitive 1 = E.vvPrimitive 1 := by
        have := hG1; simp only [hG_def, sub_eq_zero] at this; exact this
      rw [h1, this] at hlt; exact lt_irrefl _ hlt
    obtain ⟨p, r, m, c, _, _, hps, hsr, haffine⟩ :=
      convexEnvelope_affineOn_of_lt (by norm_num : (0:ℝ) ≤ 1) E.vvPrimitive_continuousOn hs_oo hlt
    have haffine' : ∀ x ∈ Ioo p r, E.ironedPrimitive x = m * x + c := fun x hx =>
      haffine x ⟨hx.1.le, hx.2.le⟩
    set p' := max p 0 with hp'_def
    set r' := min r 1 with hr'_def
    have hp'lt : p' < s := max_lt hps hs_oo.1
    have hsr' : s < r' := lt_min hsr hs_oo.2
    have hsub : Ioo p' r' ⊆ Ioo p r := fun x hx =>
      ⟨lt_of_le_of_lt (le_max_left _ _) hx.1, lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
    have hsub01 : Ioo p' r' ⊆ Ioo (0:ℝ) 1 := fun x hx =>
      ⟨lt_of_le_of_lt (le_max_right _ _) hx.1, lt_of_lt_of_le hx.2 (min_le_right _ _)⟩
    have haffine'' : ∀ x ∈ Ioo p' r', E.ironedPrimitive x = m * x + c :=
      fun x hx => haffine' x (hsub hx)
    have hXe_const : ∀ x ∈ Ioo p' r', Xe x = X s := by
      intro x hx
      have hx01 : x ∈ Ioo (0:ℝ) 1 := hsub01 hx
      have hs01 : s ∈ Ioo (0:ℝ) 1 := hs_oo
      have hĥx : E.ironedVVQuantile x = m :=
        E.ironedVVQuantile_eq_of_affineOn (le_max_right _ _) (min_le_right _ _) haffine'' hx
      have hĥs : E.ironedVVQuantile s = m :=
        E.ironedVVQuantile_eq_of_affineOn (le_max_right _ _) (min_le_right _ _) haffine''
          ⟨hp'lt, hsr'⟩
      have hivvx : E.ironedVirtualValue (E.quantileInv x)
          = E.ironedVirtualValue (E.quantileInv s) := by
        rw [ironedVirtualValue, ironedVirtualValue, quantileInv, quantileInv,
          E.dist.cdf_quantile hx01, E.dist.cdf_quantile hs01, hĥx, hĥs]
      rw [hXe_eq x hx01]
      exact hflat hivvx
    have hμ_zero : μX (Ioo p' r') = 0 :=
      Monotone.stieltjesMeasure_Ioo_eq_zero_of_constantOn hXe_mono (lt_trans hp'lt hsr') hXe_const
    refine ⟨Ioo p' r', ?_, hμ_zero⟩
    exact mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hp'lt hsr')
  rw [ae_iff]
  refine measure_mono_null (fun s hs => ?_) hnull
  simp only [mem_setOf_eq, Classical.not_imp] at hs
  obtain ⟨hs_oc, hne⟩ := hs
  refine ⟨hs_oc, ?_⟩
  rw [htail s hs_oc, hG_def] at hne
  have hle : E.ironedPrimitive s ≤ E.vvPrimitive s :=
    convexEnvelope_le_self (by norm_num) E.vvPrimitive_continuousOn ⟨hs_oc.1.le, hs_oc.2⟩
  by_contra hge
  push Not at hge
  exact hne (by simp only [neg_sub]; linarith [hle, hge])

/-- **Ironing is exact for allocations flat on the ironed intervals.** If a monotone allocation
`M.x` is constant on every level set of the ironed virtual value `ψ̄`, then expected virtual
surplus is unchanged by ironing: `𝔼[ψ·x] = 𝔼[ψ̄·x]`. -/
theorem expected_virtualSurplus_eq_ironed (M : DirectMechanism E)
    (hmono : MonotoneAlloc M.alloc)
    (hflat : ∀ {t t' : ℝ}, E.ironedVirtualValue t = E.ironedVirtualValue t' → M.x t = M.x t') :
    E.dist.expect (fun θ => E.virtualValue θ * M.x θ)
      = E.dist.expect (fun θ => E.ironedVirtualValue θ * M.x θ) := by
  haveI := E.dist.toMeasure_isProbability
  refine le_antisymm (E.expected_virtualSurplus_le_ironed M hmono) ?_
  set X : ℝ → ℝ := fun t => M.x (E.quantileInv t) with hX_def
  have hlhs : E.dist.expect (fun θ => E.virtualValue θ * M.x θ)
      = ∫ t in Ioo (0:ℝ) 1, E.vvQuantile t * X t := by
    rw [E.dist.expect_eq_integral_quantile (E.integrable_virtualValue_mul_alloc M hmono)]; rfl
  have hrhs : E.dist.expect (fun θ => E.ironedVirtualValue θ * M.x θ)
      = ∫ t in Ioo (0:ℝ) 1, E.ironedVVQuantile t * X t := by
    rw [E.dist.expect_eq_integral_quantile (E.integrable_ironedVirtualValue_mul_alloc M hmono)]
    refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
    change E.ironedVVQuantile (E.dist.cdf (E.quantileInv t)) * M.x (E.quantileInv t)
      = E.ironedVVQuantile t * X t
    rw [quantileInv, E.dist.cdf_quantile ht]; rfl
  rw [hlhs, hrhs]
  have hmap : E.dist.toMeasure = (volume.restrict (Ioo (0:ℝ) 1)).map E.quantileInv :=
    Measure.map_quantile_volume_Ioo.symm
  have hqae : AEMeasurable E.quantileInv (volume.restrict (Ioo (0:ℝ) 1)) :=
    Measure.aemeasurable_quantile_restrict_Ioo
  have hint_lhs : IntegrableOn (fun t => E.vvQuantile t * X t) (Ioo (0:ℝ) 1) := by
    have hg := E.integrable_virtualValue_mul_alloc M hmono
    rw [hmap, integrable_map_measure (hmap ▸ hg.1) hqae] at hg; exact hg
  have hint_rhs : IntegrableOn (fun t => E.ironedVVQuantile t * X t) (Ioo (0:ℝ) 1) := by
    have hg := E.integrable_ironedVirtualValue_mul_alloc M hmono
    rw [hmap, integrable_map_measure (hmap ▸ hg.1) hqae] at hg
    refine hg.congr ((ae_restrict_iff' measurableSet_Ioo).mpr (ae_of_all _ fun t ht => ?_))
    change E.ironedVirtualValue (E.quantileInv t) * M.x (E.quantileInv t)
      = E.ironedVVQuantile t * X t
    rw [ironedVirtualValue, quantileInv, E.dist.cdf_quantile ht]; rfl
  have hsplit : ∫ t in Ioo (0:ℝ) 1, (E.ironedVVQuantile t - E.vvQuantile t) * X t
      = (∫ t in Ioo (0:ℝ) 1, E.ironedVVQuantile t * X t)
        - ∫ t in Ioo (0:ℝ) 1, E.vvQuantile t * X t := by
    rw [← integral_sub hint_rhs hint_lhs]
    exact setIntegral_congr_fun measurableSet_Ioo (fun t _ => by ring)
  have hgap_zero : ∫ t in Ioo (0:ℝ) 1, (E.ironedVVQuantile t - E.vvQuantile t) * X t = 0 :=
    E.ironingGap_eq_zero_of_constOn_levelSet M hmono hflat
  linarith [hsplit, hgap_zero]

/-! ### Regularity makes ironing a no-op

Under Myerson regularity (`E.Regular`, i.e. `ψ` monotone on the type interval), the convex
envelope of the virtual-value primitive coincides with the primitive itself, so the ironed virtual
value equals the raw virtual value on the interior of the type interval. -/

/-- The CDF vanishes at the lowest type: `F(θlo) = 0`. The density is supported on `[θlo, θhi]`, so
`F = 0` strictly below `θlo`; continuity of `F` carries this to `θlo`. -/
lemma cdf_zero_left : E.dist.cdf E.θlo = 0 := by
  have hzero_lt : ∀ x, x < E.θlo → E.dist.cdf x = 0 := fun x hx =>
    E.dist.cdf_eq_zero_of_supportsOn_Icc_left
      (fun t ht => E.density_eq_zero_of_notMem ht) hx
  have htend : Filter.Tendsto E.dist.cdf (𝓝[<] E.θlo) (𝓝 (E.dist.cdf E.θlo)) :=
    E.dist.cdf_continuous.continuousAt.continuousWithinAt.tendsto
  have htend0 : Filter.Tendsto E.dist.cdf (𝓝[<] E.θlo) (𝓝 0) :=
    tendsto_const_nhds.congr'
      (by filter_upwards [self_mem_nhdsWithin] with x hx using (hzero_lt x hx).symm)
  exact tendsto_nhds_unique htend htend0

/-- The CDF saturates at the highest type: `F(θhi) = 1`. The density vanishes above `θhi`. -/
lemma cdf_one_right : E.dist.cdf E.θhi = 1 :=
  E.dist.cdf_eq_one_of_supportsOn_Icc_right
    (fun _t ht => E.density_eq_zero_of_notMem ht) le_rfl

/-- The CDF is strictly increasing on the type interval, since the density is positive there. -/
lemma cdf_strictMonoOn_types : StrictMonoOn E.dist.cdf E.types := by
  intro a ha b hb hab
  exact E.dist.cdf_strictMono hab
    (fun x hx => E.density_pos x ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩)
    (E.density_cont.mono (fun x hx => ⟨le_trans ha.1 hx.1, le_trans hx.2 hb.2⟩))

/-- On the open type interval the CDF is interior: `F(θ) ∈ (0, 1)` for `θ ∈ (θlo, θhi)`. -/
lemma cdf_mem_Ioo {θ : ℝ} (hθ : θ ∈ Ioo E.θlo E.θhi) : E.dist.cdf θ ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨E.dist.cdf_pos_of_mem_Ioo_support hθ
      (fun y hy => E.density_pos y ⟨hy.1.le, hy.2.le⟩) E.density_cont, ?_⟩
  have h1 : E.dist.cdf θ < E.dist.cdf E.θhi :=
    E.cdf_strictMonoOn_types ⟨hθ.1.le, hθ.2.le⟩ E.θhi_mem_types hθ.2
  rwa [E.cdf_one_right] at h1

/-- **Left inverse of the CDF on the interior.** For `θ ∈ (θlo, θhi)`, `F⁻¹(F θ) = θ`: The quantile
of `F θ` recovers `θ`. The `≤` direction is the Galois identity; the `≥` direction uses strict
monotonicity of `F` (a strictly smaller quantile would have strictly smaller CDF, contradicting
`F θ ≤ F(F⁻¹(F θ))`). -/
lemma quantileInv_cdf {θ : ℝ} (hθ : θ ∈ Ioo E.θlo E.θhi) :
    E.quantileInv (E.dist.cdf θ) = θ := by
  haveI := E.dist.toMeasure_isProbability
  have hmem : E.dist.cdf θ ∈ Ioo (0:ℝ) 1 := E.cdf_mem_Ioo hθ
  refine le_antisymm ((E.dist.quantile_le_iff hmem).mpr le_rfl) ?_
  by_contra hlt
  push Not at hlt
  have hq'_mem : E.quantileInv (E.dist.cdf θ) ∈ E.types := E.quantileInv_mem hmem
  have hstrict : E.dist.cdf (E.quantileInv (E.dist.cdf θ)) < E.dist.cdf θ :=
    E.cdf_strictMonoOn_types hq'_mem ⟨hθ.1.le, hθ.2.le⟩ hlt
  have hge : E.dist.cdf θ ≤ E.dist.cdf (E.quantileInv (E.dist.cdf θ)) :=
    E.dist.le_cdf_quantile hmem
  linarith

/-- For an interior quantile `q ∈ (0, 1)`, `F⁻¹ q` lands strictly inside the type interval. -/
lemma quantileInv_mem_Ioo {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    E.quantileInv q ∈ Ioo E.θlo E.θhi := by
  haveI := E.dist.toMeasure_isProbability
  have hcdfq : E.dist.cdf (E.quantileInv q) = q := E.dist.cdf_quantile hq
  have hmem : E.quantileInv q ∈ E.types := E.quantileInv_mem hq
  refine ⟨lt_of_le_of_ne hmem.1 ?_, lt_of_le_of_ne hmem.2 ?_⟩
  · intro h
    rw [← h, E.cdf_zero_left] at hcdfq
    exact (ne_of_lt hq.1) hcdfq
  · intro h
    rw [h, E.cdf_one_right] at hcdfq
    exact (ne_of_lt hq.2) hcdfq.symm

/-- The quantile `F⁻¹` is continuous at every interior point `q ∈ (0, 1)`. The quantile is monotone
and its image on `(0, 1)` contains the open interval `(θlo, θhi)` — an open neighborhood of `F⁻¹ q`
— because `F⁻¹(F x) = x` realizes each interior type as a quantile value. A monotone map whose
image is a neighborhood of its value is continuous there. -/
lemma quantileInv_continuousAt {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt E.quantileInv q := by
  haveI := E.dist.toMeasure_isProbability
  have hq_oo : E.quantileInv q ∈ Ioo E.θlo E.θhi := E.quantileInv_mem_Ioo hq
  have himage : E.quantileInv '' Ioo (0:ℝ) 1 ∈ 𝓝 (E.quantileInv q) := by
    refine mem_of_superset (Ioo_mem_nhds hq_oo.1 hq_oo.2) ?_
    intro x hx
    exact ⟨E.dist.cdf x, E.cdf_mem_Ioo hx, E.quantileInv_cdf hx⟩
  exact continuousAt_of_monotoneOn_of_image_mem_nhds
    (Measure.monotoneOn_quantile (μ := E.dist.toMeasure)) (Ioo_mem_nhds hq.1 hq.2) himage

/-- `h = ψ ∘ F⁻¹` is continuous at every interior quantile `q ∈ (0, 1)`: `ψ` is continuous on the
type interval, `F⁻¹ q` lands in its interior, and `F⁻¹` is continuous at `q`. -/
lemma vvQuantile_continuousAt {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    ContinuousAt E.vvQuantile q := by
  have hq_oo : E.quantileInv q ∈ Ioo E.θlo E.θhi := E.quantileInv_mem_Ioo hq
  have hcont_vv : ContinuousAt E.virtualValue (E.quantileInv q) :=
    E.virtualValue_continuousOn.continuousAt
      (mem_of_superset (Ioo_mem_nhds hq_oo.1 hq_oo.2) Ioo_subset_Icc_self)
  exact hcont_vv.comp (E.quantileInv_continuousAt hq)

/-- Under regularity, `h = ψ ∘ F⁻¹` is monotone on `(0, 1)`: `F⁻¹` is monotone into the type
interval and `ψ` is monotone there. -/
lemma vvQuantile_monotoneOn_of_regular (hreg : E.Regular) :
    MonotoneOn E.vvQuantile (Ioo (0 : ℝ) 1) := by
  haveI := E.dist.toMeasure_isProbability
  have hreg' : MonotoneOn E.virtualValue E.types := hreg
  intro s hs t ht hst
  exact hreg' (E.quantileInv_mem hs) (E.quantileInv_mem ht)
    (Measure.monotoneOn_quantile (μ := E.dist.toMeasure) hs ht hst)

/-- **Regularity ⇒ no ironing (quantile space).** When `h = ψ ∘ F⁻¹` is monotone, its primitive `H`
is convex, so the convex envelope `Ĥ` equals `H` on `(0, 1)`; hence the ironed virtual value
`ĥ = Ĥ'₊` equals `h` there. The proof builds, at each interior `x`, the supporting line of slope
`h(x)` through `(x, H(x))` (a minorant by monotonicity of `h`), giving `Ĥ = H`; the right
derivative then transfers from `Ĥ` to `H`, and the FTC identifies `H'₊(q) = h(q)` using continuity
of `h`. -/
lemma ironedVVQuantile_eq_vvQuantile_of_regular (hreg : E.Regular)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    E.ironedVVQuantile q = E.vvQuantile q := by
  haveI := E.dist.toMeasure_isProbability
  have hmono_vv : MonotoneOn E.vvQuantile (Ioo (0 : ℝ) 1) :=
    E.vvQuantile_monotoneOn_of_regular hreg
  -- Step B: the convex envelope agrees with `H` on `(0, 1)`, via supporting lines.
  have hEqOn : ∀ x ∈ Ioo (0:ℝ) 1, E.ironedPrimitive x = E.vvPrimitive x := by
    intro x hx
    -- The line of slope `h(x)` through `(x, H(x))` is a minorant of `H` with contact at `x`.
    have hminor : IsAffineMinorant 0 1 E.vvPrimitive (E.vvQuantile x)
        (E.vvPrimitive x - E.vvQuantile x * x) := by
      intro t ht
      have hII_t : IntervalIntegrable E.vvQuantile volume 0 t :=
        E.intervalIntegrable_vvQuantile.mono_set (by
          rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), uIcc_of_le ht.1]
          exact Icc_subset_Icc_right ht.2)
      have hII_x : IntervalIntegrable E.vvQuantile volume 0 x :=
        E.intervalIntegrable_vvQuantile.mono_set (by
          rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), uIcc_of_le hx.1.le]
          exact Icc_subset_Icc_right hx.2.le)
      have hdiff : E.vvPrimitive t - E.vvPrimitive x = ∫ u in x..t, E.vvQuantile u :=
        intervalIntegral.integral_interval_sub_left hII_t hII_x
      -- `h(x)·(t − x) ≤ ∫ₓᵗ h`, by comparing `h` to the constant `h(x)` (monotonicity on `(0,1)`).
      have hkey : E.vvQuantile x * (t - x) ≤ ∫ u in x..t, E.vvQuantile u := by
        rcases le_total x t with hxt | htx
        · have hII_xt : IntervalIntegrable E.vvQuantile volume x t :=
            E.intervalIntegrable_vvQuantile.mono_set (by
              rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), uIcc_of_le hxt]
              exact Icc_subset_Icc hx.1.le ht.2)
          have hbound : ∀ u ∈ Ioo x t, E.vvQuantile x ≤ E.vvQuantile u := fun u hu =>
            hmono_vv hx ⟨lt_trans hx.1 hu.1, lt_of_lt_of_le hu.2 ht.2⟩ hu.1.le
          have hconst : E.vvQuantile x * (t - x) = ∫ u in x..t, E.vvQuantile x := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
          have h : (∫ u in x..t, E.vvQuantile x) ≤ ∫ u in x..t, E.vvQuantile u :=
            intervalIntegral.integral_mono_on_of_le_Ioo hxt intervalIntegrable_const hII_xt hbound
          rw [hconst]; exact h
        · have hII_tx : IntervalIntegrable E.vvQuantile volume t x :=
            E.intervalIntegrable_vvQuantile.mono_set (by
              rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), uIcc_of_le htx]
              exact Icc_subset_Icc ht.1 hx.2.le)
          have hbound : ∀ u ∈ Ioo t x, E.vvQuantile u ≤ E.vvQuantile x := fun u hu =>
            hmono_vv ⟨lt_of_le_of_lt ht.1 hu.1, lt_trans hu.2 hx.2⟩ hx hu.2.le
          have hconst : E.vvQuantile x * (x - t) = ∫ u in t..x, E.vvQuantile x := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
          have h : (∫ u in t..x, E.vvQuantile u) ≤ ∫ u in t..x, E.vvQuantile x :=
            intervalIntegral.integral_mono_on_of_le_Ioo htx hII_tx intervalIntegrable_const hbound
          have hsymm : (∫ u in x..t, E.vvQuantile u) = -(∫ u in t..x, E.vvQuantile u) :=
            intervalIntegral.integral_symm t x
          rw [hsymm]
          rw [← hconst] at h
          nlinarith [h]
      nlinarith [hkey, hdiff]
    have hcontact_env := convexEnvelope_eq_of_affineMinorant_contact (by norm_num : (0:ℝ) ≤ 1)
      E.vvPrimitive_continuousOn (show x ∈ Icc (0:ℝ) 1 from ⟨hx.1.le, hx.2.le⟩) hminor (by ring)
    rw [ironedPrimitive_def]; exact hcontact_env
  -- Step C: transfer the right derivative from `Ĥ` to `H` (they agree near `q`).
  have hev : E.ironedPrimitive =ᶠ[𝓝[Ioi q] q] E.vvPrimitive :=
    Filter.eventuallyEq_of_mem (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hq.1 hq.2)) hEqOn
  have hC : E.ironedVVQuantile q = derivWithin E.vvPrimitive (Ioi q) q := by
    rw [ironedVVQuantile,
      (E.ironedPrimitive_convexOn).rightDerivExtend_eq_of_mem_Ioo (by norm_num) hq]
    exact hev.derivWithin_eq (hEqOn q hq)
  -- Step D: the FTC identifies `H'₊(q) = h(q)` using continuity of `h` at `q`.
  have hII_q : IntervalIntegrable E.vvQuantile volume 0 q :=
    E.intervalIntegrable_vvQuantile.mono_set (by
      rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), uIcc_of_le hq.1.le]
      exact Icc_subset_Icc_right hq.2.le)
  have hmeas : StronglyMeasurableAtFilter E.vvQuantile (𝓝 q) := by
    refine ⟨Ioo (0:ℝ) 1, Ioo_mem_nhds hq.1 hq.2, ?_⟩
    have hint : IntegrableOn E.vvQuantile (Ioc (0:ℝ) 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp
        E.intervalIntegrable_vvQuantile
    exact hint.1.mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
  have hderiv : HasDerivAt E.vvPrimitive (E.vvQuantile q) q :=
    intervalIntegral.integral_hasDerivAt_right hII_q hmeas (E.vvQuantile_continuousAt hq)
  have hD : derivWithin E.vvPrimitive (Ioi q) q = E.vvQuantile q :=
    hderiv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi q)
  rw [hC, hD]

/-- **Myerson regularity makes ironing a no-op.** Under `E.Regular` (the virtual value `ψ` is
monotone on the type interval), the ironed virtual value `ψ̄` equals the raw virtual value `ψ` on
the interior of the type interval. Ironing only changes `ψ` where it is non-monotone; regularity
leaves nothing to iron. -/
theorem ironedVirtualValue_eq_virtualValue_of_regular (hreg : E.Regular)
    {θ : ℝ} (hθ : θ ∈ Ioo E.θlo E.θhi) :
    E.ironedVirtualValue θ = E.virtualValue θ := by
  have hmem : E.dist.cdf θ ∈ Ioo (0:ℝ) 1 := E.cdf_mem_Ioo hθ
  rw [ironedVirtualValue_def, E.ironedVVQuantile_eq_vvQuantile_of_regular hreg hmem,
    vvQuantile_def, E.quantileInv_cdf hθ]

end ScreeningEnv

end Econlib.MechanismDesign.Transfers.SingleParameter
