/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ConvexRightDeriv
public import Econlib.Math.MeasureTheory.TriangleFubini
public import Econlib.Probability.Order.SOSD.DoubleIBP

/-!
# SOSD for monotone concave utilities on a compact support

This file proves the second-order stochastic dominance (SOSD) forward direction for monotone
concave utilities without any global linear-growth bound, under the hypothesis that the
distributions are supported on a compact interval `[a, b]`. The utility `u` is required to be
concave, monotone, and continuous only on `[a, b]`; it need not be defined or concave on all of
`ℝ`. In particular, the canonical risk-averse utilities `Real.log` and CRRA fall under this theorem
directly, without the tangent-line extension used by `Order/SOSD/PositiveSupport.lean`.

## Main statements

* `CDF.SOSD.expect_concave_compactSupport` — SOSD forward direction for monotone concave utilities
  on a compact support, with no linear-growth hypothesis.
* `CDF.SOSD.expect_concave_compactSupport_of_hasDerivAt` — the same result when `u` is
  differentiable on the interior, replacing right-derivative boundedness with bounds on `u'`.

## Tags

second-order stochastic dominance, concave order, compact support, integration by parts, stieltjes
-/

@[expose] public section

open MeasureTheory Set Filter Function intervalIntegral ConvexOn
open scoped Topology ENNReal

namespace Econlib.Probability

variable {dF dG : ContDist}

/-! ### Compact-support CDF identities -/

/-- On a compact support `[a, b]`, the CDF below `a` vanishes: `F(t) = 0` for `t ≤ a`. -/
lemma contDist_cdf_eq_zero_of_le (d : ContDist) {a b t : ℝ}
    (h_supp : ∀ x ∉ Icc a b, d.density x = 0) (ht : t ≤ a) : d.cdf t = 0 := by
  rw [ContDist.cdf_eq_integral]
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic]
  have hae : ∀ᵐ s ∂volume, s ≠ a := by simp [ae_iff]
  filter_upwards [hae] with s hs hst
  refine h_supp s (fun hmem => hs (le_antisymm (le_trans hst ht) hmem.1))

/-- On a compact support `[a, b]`, the CDF is the running interval integral of the density from
`a`: `F(t) = ∫_a^t density` for every `t`. -/
lemma contDist_cdf_eq_intervalIntegral (d : ContDist) {a b : ℝ}
    (h_supp : ∀ x ∉ Icc a b, d.density x = 0) (t : ℝ) :
    d.cdf t = ∫ s in a..t, d.density s := by
  rcases le_or_gt a t with hat | hta
  · rw [ContDist.cdf_eq_integral, intervalIntegral.integral_of_le hat]
    have hsplit : ∫ s in Iic t, d.density s
        = (∫ s in Iic a, d.density s) + ∫ s in Ioc a t, d.density s := by
      rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        d.integrable.integrableOn d.integrable.integrableOn, Iic_union_Ioc_eq_Iic hat]
    rw [hsplit]
    have hFa : ∫ s in Iic a, d.density s = 0 := by
      have := contDist_cdf_eq_zero_of_le d h_supp (le_refl a)
      rwa [ContDist.cdf_eq_integral] at this
    rw [hFa, zero_add]
  · rw [contDist_cdf_eq_zero_of_le d h_supp hta.le, intervalIntegral.integral_of_ge hta.le]
    have hzero : ∫ s in Ioc t a, d.density s = 0 := by
      apply integral_eq_zero_of_ae
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      have hae : ∀ᵐ s ∂volume, s ≠ a := by simp [ae_iff]
      filter_upwards [hae] with s hs hsmem
      exact h_supp s (fun hmem => hs (le_antisymm hsmem.2 hmem.1))
    rw [hzero, neg_zero]

/-- On a compact support `[a, b]` the total mass on `a..b` is `1`. -/
lemma contDist_mass_intervalIntegral (d : ContDist) {a b : ℝ}
    (h_supp : ∀ x ∉ Icc a b, d.density x = 0) :
    ∫ s in a..b, d.density s = 1 := by
  rw [← contDist_cdf_eq_intervalIntegral d h_supp b, ContDist.cdf_eq_integral]
  have hIoi : ∫ s in Ioi b, d.density s = 0 := by
    apply integral_eq_zero_of_ae
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with s hs
    exact h_supp s (fun hmem => absurd hmem.2 (not_le.mpr hs))
  have hunion : (∫ s in Iic b, d.density s) + ∫ s in Ioi b, d.density s = 1 := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      d.integrable.integrableOn d.integrable.integrableOn, Iic_union_Ioi, setIntegral_univ]
    exact d.integral_one
  rw [hIoi, add_zero] at hunion
  exact hunion

/-- On a compact support `[a, b]`, the expectation collapses to an interval integral over `a..b`. -/
lemma contDist_expect_eq_intervalIntegral (d : ContDist) (u : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (h_supp : ∀ x ∉ Icc a b, d.density x = 0) :
    d.expect u = ∫ s in a..b, d.density s * u s := by
  rw [ContDist.expect, intervalIntegral.integral_of_le hab]
  rw [← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [h_supp x hx, zero_mul])).symm

/-- On compact supports, the integrated CDF difference is the running interval integral of the CDF
difference from `a`: `H(s) = ∫_a^s (F - G)`. -/
lemma integratedCDFDiff_eq_intervalIntegral {a b : ℝ} (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (h_suppF : ∀ x ∉ Icc a b, dF.density x = 0)
    (h_suppG : ∀ x ∉ Icc a b, dG.density x = 0) (s : ℝ) :
    integratedCDFDiff dF dG s = ∫ t in a..s, (dF.cdf t - dG.cdf t) := by
  have hFG_zero : ∀ t ≤ a, dF.cdf t - dG.cdf t = 0 := fun t ht => by
    rw [contDist_cdf_eq_zero_of_le dF h_suppF ht, contDist_cdf_eq_zero_of_le dG h_suppG ht,
      sub_zero]
  have hFG_int : ∀ x : ℝ, IntegrableOn (fun t => dF.cdf t - dG.cdf t) (Iic x) :=
    fun x => (h_sosd.tails_left x).sub (h_sosd.tails_right x)
  simp only [integratedCDFDiff]
  rcases le_or_gt a s with has | hsa
  · rw [intervalIntegral.integral_of_le has]
    have hsplit : ∫ t in Iic s, (dF.cdf t - dG.cdf t)
        = (∫ t in Iic a, (dF.cdf t - dG.cdf t)) + ∫ t in Ioc a s, (dF.cdf t - dG.cdf t) := by
      rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        ((hFG_int s).mono_set (Iic_subset_Iic.mpr has))
        ((hFG_int s).mono_set Ioc_subset_Iic_self), Iic_union_Ioc_eq_Iic has]
    have hIica : ∫ t in Iic a, (dF.cdf t - dG.cdf t) = 0 := by
      apply integral_eq_zero_of_ae
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic]
      filter_upwards with t ht using hFG_zero t ht
    rw [hsplit, hIica, zero_add]
  · rw [intervalIntegral.integral_of_ge hsa.le]
    have hIics : ∫ t in Iic s, (dF.cdf t - dG.cdf t) = 0 := by
      apply integral_eq_zero_of_ae
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Iic]
      filter_upwards with t ht using hFG_zero t (le_trans ht hsa.le)
    have hIocsa : ∫ t in Ioc s a, (dF.cdf t - dG.cdf t) = 0 := by
      apply integral_eq_zero_of_ae
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      filter_upwards with t ht using hFG_zero t ht.2
    rw [hIics, hIocsa, neg_zero]

/-! ### The compact-support concave SOSD step -/

/-- SOSD forward direction for monotone concave utilities on a compact support. If `dF`
second-order stochastically dominates `dG`, both densities are supported on `[a, b]`, and `u` is
concave, monotone, and continuous on `[a, b]` (with right-derivative boundedness on the interior),
then `E_G[u] ≤ E_F[u]`. No global linear-growth bound is required, and `u` need not be defined or
concave outside `[a, b]`. -/
theorem CDF.SOSD.expect_concave_compactSupport (dF dG : ContDist) (u : ℝ → ℝ) {a b : ℝ}
    (hab : a < b)
    (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (h_suppF : ∀ x ∉ Icc a b, dF.density x = 0)
    (h_suppG : ∀ x ∉ Icc a b, dG.density x = 0)
    (hu_conc : ConcaveOn ℝ (Icc a b) u)
    (hu_mono : MonotoneOn u (Icc a b))
    (hu_cont : ContinuousOn u (Icc a b))
    (h_bddBelow : BddBelow ((fun x => derivWithin (fun y => -u y) (Ioi x) x) '' Ioo a b))
    (h_bddAbove : BddAbove ((fun x => derivWithin (fun y => -u y) (Ioi x) x) '' Ioo a b))
    (h_intF : Integrable (fun x => dF.density x * u x))
    (h_intG : Integrable (fun x => dG.density x * u x)) :
    dG.expect u ≤ dF.expect u := by
  set φ : ℝ → ℝ := fun y => -u y with hφ_def
  have hφ_conv : ConvexOn ℝ (Icc a b) φ := hu_conc.neg
  have hφ_cont : ContinuousOn φ (Icc a b) := hu_cont.neg
  set gd : ℝ → ℝ := fun x => derivWithin φ (Ioi x) x with hgd_def
  set g : ℝ → ℝ := hφ_conv.rightDerivExtend hab with hg_def
  have hg_mono : Monotone g := hφ_conv.rightDerivExtend_monotone hab h_bddBelow h_bddAbove
  set g_sf : StieltjesFunction ℝ := Monotone.stieltjes hg_mono with hg_sf_def
  set μ_g : Measure ℝ := Monotone.stieltjesMeasure hg_mono with hμ_g_def
  set H : ℝ → ℝ := integratedCDFDiff dF dG with hH_def
  -- `g ≤ 0`: the right-derivative of the convex `-u` is bounded above by the slope from `p` to
  -- `b`, which is nonpositive because `u` is monotone nondecreasing.
  have hg_nonpos : ∀ x, g x ≤ 0 := by
    have hgd_nonpos : ∀ p ∈ Ioo a b, gd p ≤ 0 := by
      intro p hp
      have hp_int : p ∈ interior (Icc a b) := by rw [interior_Icc]; exact hp
      have hb_mem : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
      have hslope := hφ_conv.rightDeriv_le_slope_of_mem_interior hp_int hb_mem hp.2
      rw [slope_def_field, hφ_def] at hslope
      have hp_mem : p ∈ Icc a b := ⟨hp.1.le, hp.2.le⟩
      have hupub : u p ≤ u b := hu_mono hp_mem hb_mem hp.2.le
      refine le_trans hslope (div_nonpos_of_nonpos_of_nonneg ?_ (by linarith [hp.2]))
      simp only; linarith
    intro x
    have hne : ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b).Nonempty :=
      Set.Nonempty.image _ (nonempty_Ioo.mpr hab)
    obtain ⟨p, hp⟩ := nonempty_Ioo.mpr hab
    by_cases hxa : x ≤ a
    · rw [hg_def, hφ_conv.rightDerivExtend_of_le_left hab hxa]
      exact csInf_le_of_le h_bddBelow (mem_image_of_mem _ hp) (hgd_nonpos p hp)
    · push Not at hxa
      by_cases hxb : b ≤ x
      · rw [hg_def, hφ_conv.rightDerivExtend_of_right_le hab hxb]
        refine csSup_le hne ?_
        rintro v ⟨q, hq, rfl⟩
        exact hgd_nonpos q hq
      · push Not at hxb
        rw [hg_def, hφ_conv.rightDerivExtend_eq_of_mem_Ioo hab ⟨hxa, hxb⟩]
        exact hgd_nonpos x ⟨hxa, hxb⟩
  have hg_sf_nonpos : ∀ x, g_sf x ≤ 0 := by
    intro x
    have hrl : (g_sf : ℝ → ℝ) x = Function.rightLim g x := hg_mono.stieltjesFunction_eq x
    rw [hg_sf_def] at hrl ⊢
    rw [hrl]
    exact le_trans (hg_mono.rightLim_le (lt_add_one x)) (hg_nonpos (x + 1))
  have hftc : ∀ t ∈ Icc a b, (∫ s in a..t, gd s) = u a - u t := by
    intro t ht
    have hraw := hφ_conv.ftc_rightDeriv hab hφ_cont h_bddBelow h_bddAbove ht.1 ht.2
    rw [show gd = fun s => derivWithin φ (Ioi s) s from hgd_def, hraw, hφ_def]
    ring
  have hgd_int : IntervalIntegrable gd volume a b :=
    hφ_conv.intervalIntegrable_rightDeriv hab h_bddBelow h_bddAbove hab.le le_rfl
  have h_gd_ae : (fun s => (dF.cdf s - dG.cdf s) * gd s)
      =ᵐ[volume.restrict (Ioc a b)] fun s => (dF.cdf s - dG.cdf s) * g_sf s := by
    have hgd_eq : gd =ᵐ[volume.restrict (Ioc a b)] (fun s => (g_sf : ℝ → ℝ) s) := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      -- `gd = g_sf` a.e.: both equal `g` off the null set `{b}` and the countable
      -- discontinuity set of the monotone function `g`.
      have hb_null : ∀ᵐ x ∂volume, x ≠ b := by
        rw [ae_iff]; simp
      have hcont_null : ∀ᵐ x ∂volume, ContinuousAt g x := by
        rw [ae_iff]
        exact (hg_mono.countable_not_continuousAt).measure_zero volume
      filter_upwards [hb_null, hcont_null] with x hxb hxcont hx_mem
      have hx_oo : x ∈ Ioo a b := ⟨hx_mem.1, lt_of_le_of_ne hx_mem.2 hxb⟩
      have h1 : gd x = g x := by
        rw [hgd_def, hg_def]; exact (hφ_conv.rightDerivExtend_eq_of_mem_Ioo hab hx_oo).symm
      have h2 : (g_sf : ℝ → ℝ) x = g x := by
        rw [hg_sf_def]
        rw [hg_mono.stieltjesFunction_eq x]
        exact hxcont.continuousWithinAt.rightLim_eq
      rw [h1, h2]
    filter_upwards [hgd_eq] with s hs
    rw [hs]
  have hstep1 : dF.expect u - dG.expect u
      = ∫ s in a..b, gd s * (dF.cdf s - dG.cdf s) := by
    have hsurv : ∀ (d : ContDist), (∀ x ∉ Icc a b, d.density x = 0) →
        Integrable (fun x => d.density x * u x) →
        u a - d.expect u = ∫ s in a..b, gd s * (1 - d.cdf s) := by
      intro d hd hd_du
      have hd_int : IntervalIntegrable d.density volume a b := d.integrable.intervalIntegrable
      have hF : ∀ t, d.cdf t = ∫ s in a..t, d.density s :=
        fun t => contDist_cdf_eq_intervalIntegral d hd t
      have hmass : (∫ θ in a..b, d.density θ) = 1 := contDist_mass_intervalIntegral d hd
      have hswap := integral_triangle_swap_survival hab.le hgd_int hd_int hF hmass
      have hlhs : (∫ θ in a..b, (∫ s in a..θ, gd s) * d.density θ)
          = ∫ θ in a..b, (u a - u θ) * d.density θ := by
        rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le]
        refine setIntegral_congr_fun measurableSet_Ioc (fun θ hθ => ?_)
        rw [hftc θ ⟨hθ.1.le, hθ.2⟩]
      have hexp : (∫ θ in a..b, (u a - u θ) * d.density θ) = u a - d.expect u := by
        have hsplit : (fun θ => (u a - u θ) * d.density θ)
            = fun θ => u a * d.density θ - d.density θ * u θ := by
          funext θ; ring
        rw [hsplit,
            intervalIntegral.integral_sub (hd_int.const_mul (u a)) hd_du.intervalIntegrable,
            intervalIntegral.integral_const_mul, hmass,
            ← contDist_expect_eq_intervalIntegral d u hab.le hd]
        ring
      rw [← hexp, ← hlhs, hswap]
    have hsF := hsurv dF h_suppF h_intF
    have hsG := hsurv dG h_suppG h_intG
    have hcontF : ContinuousOn (fun s => (1 : ℝ) - dF.cdf s) (uIcc a b) :=
      (continuous_const.sub (contdist_cdf_continuous dF)).continuousOn
    have hcontG : ContinuousOn (fun s => (1 : ℝ) - dG.cdf s) (uIcc a b) :=
      (continuous_const.sub (contdist_cdf_continuous dG)).continuousOn
    have hint_F : IntervalIntegrable (fun s => gd s * (1 - dF.cdf s)) volume a b :=
      hgd_int.mul_continuousOn hcontF
    have hint_G : IntervalIntegrable (fun s => gd s * (1 - dG.cdf s)) volume a b :=
      hgd_int.mul_continuousOn hcontG
    have hdiff : dF.expect u - dG.expect u
        = (∫ s in a..b, gd s * (1 - dG.cdf s)) - ∫ s in a..b, gd s * (1 - dF.cdf s) := by
      rw [← hsF, ← hsG]; ring
    rw [hdiff, ← intervalIntegral.integral_sub hint_G hint_F]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    ring
  -- Bridge gd → g_sf in the Lebesgue integral.
  have hbridge : (∫ s in a..b, gd s * (dF.cdf s - dG.cdf s))
      = ∫ s in a..b, g_sf s * (dF.cdf s - dG.cdf s) := by
    rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le]
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [h_gd_ae] with s hs
    rw [mul_comm (gd s), hs, mul_comm]
  have hstep2 : (∫ s in a..b, g_sf s * (dF.cdf s - dG.cdf s))
      = H b * g_sf b - ∫ t in Ioc a b, H t ∂μ_g := by
    set w : ℝ → ℝ := fun t => dF.cdf t - dG.cdf t with hw_def
    have hw_cont : Continuous w := (contdist_cdf_continuous dF).sub (contdist_cdf_continuous dG)
    have hw_int : IntervalIntegrable w volume a b := hw_cont.intervalIntegrable a b
    have TS := integral_triangle_swap_stieltjes hg_mono hab hw_int
    rw [← hg_sf_def, ← hμ_g_def] at TS
    have hHb : (∫ t in a..b, w t) = H b := by
      rw [hH_def]; exact (integratedCDFDiff_eq_intervalIntegral h_sosd h_suppF h_suppG b).symm
    have hInner : ∀ s ∈ Ioc a b, (∫ t in s..b, w t) = H b - H s := by
      intro s _
      have hsb_int : IntervalIntegrable w volume a s := hw_cont.intervalIntegrable a s
      have hHs : (∫ t in a..s, w t) = H s := by
        rw [hH_def]; exact (integratedCDFDiff_eq_intervalIntegral h_sosd h_suppF h_suppG s).symm
      rw [← hHb, ← hHs]
      exact (intervalIntegral.integral_interval_sub_left hw_int hsb_int).symm
    have hμ_eq : μ_g (Ioc a b) = ENNReal.ofReal ((g_sf : ℝ → ℝ) b - g_sf a) := by
      rw [hμ_g_def]; exact g_sf.measure_Ioc a b
    have hμ_real : (μ_g (Ioc a b)).toReal = (g_sf : ℝ → ℝ) b - g_sf a := by
      rw [hμ_eq, ENNReal.toReal_ofReal (sub_nonneg.mpr (g_sf.mono (le_of_lt hab)))]
    haveI hμ_loc : IsLocallyFiniteMeasure μ_g := by rw [hμ_g_def]; infer_instance
    have hcdf_intF : ∀ y, IntegrableOn dF.cdf (Iic y) := fun y => h_sosd.tails_left y
    have hcdf_intG : ∀ y, IntegrableOn dG.cdf (Iic y) := fun y => h_sosd.tails_right y
    have hH_diff : Differentiable ℝ H := by
      rw [hH_def]
      exact fun x => (integratedCDFDiff_hasDerivAt dF dG x hcdf_intF hcdf_intG).differentiableAt
    have hH_cont : Continuous H := hH_diff.continuous
    have hH_intOn : IntegrableOn H (Ioc a b) μ_g := hH_cont.integrableOn_Ioc
    have hHb_intOn : IntegrableOn (fun _ : ℝ => H b) (Ioc a b) μ_g :=
      integrableOn_const (by rw [hμ_eq]; exact ENNReal.ofReal_ne_top)
    have hRHS : (∫ s in Ioc a b, (∫ t in s..b, w t) ∂μ_g)
        = H b * ((g_sf : ℝ → ℝ) b - g_sf a) - ∫ t in Ioc a b, H t ∂μ_g := by
      rw [setIntegral_congr_fun measurableSet_Ioc (fun s hs => hInner s hs),
          MeasureTheory.integral_sub hHb_intOn hH_intOn,
          setIntegral_const, measureReal_def, hμ_real, smul_eq_mul]
      ring
    have hg_sf_ii : IntervalIntegrable (fun t => (g_sf : ℝ → ℝ) t) volume a b :=
      g_sf.mono.intervalIntegrable
    have hwg_ii : IntervalIntegrable (fun t => w t * (g_sf : ℝ → ℝ) t) volume a b :=
      hg_sf_ii.continuousOn_mul (hw_cont.continuousOn)
    have hLHS : (∫ t in a..b, w t * ((g_sf : ℝ → ℝ) t - g_sf a))
        = (∫ t in a..b, (g_sf : ℝ → ℝ) t * w t) - g_sf a * H b := by
      have hdistr : (fun t => w t * ((g_sf : ℝ → ℝ) t - g_sf a))
          = fun t => w t * (g_sf : ℝ → ℝ) t - g_sf a * w t := by funext t; ring
      rw [hdistr, intervalIntegral.integral_sub hwg_ii (hw_int.const_mul (g_sf a)),
          intervalIntegral.integral_const_mul, hHb]
      congr 1
      exact intervalIntegral.integral_congr (fun t _ => by rw [mul_comm])
    rw [TS, hRHS] at hLHS
    change (∫ s in a..b, (g_sf : ℝ → ℝ) s * w s) = H b * g_sf b - ∫ t in Ioc a b, H t ∂μ_g
    linarith [hLHS]
  have hHb_nonpos : H b ≤ 0 := integratedCDFDiff_nonpos h_sosd b
  have hHs_nonpos : ∀ s, H s ≤ 0 := fun s => integratedCDFDiff_nonpos h_sosd s
  have h_boundary_nonneg : 0 ≤ H b * g_sf b :=
    mul_nonneg_of_nonpos_of_nonpos hHb_nonpos (hg_sf_nonpos b)
  have h_int_nonpos : (∫ t in Ioc a b, H t ∂μ_g) ≤ 0 :=
    setIntegral_nonpos measurableSet_Ioc (fun s _ => hHs_nonpos s)
  have h_final : dF.expect u - dG.expect u = H b * g_sf b - ∫ t in Ioc a b, H t ∂μ_g := by
    rw [hstep1, hbridge, hstep2]
  linarith [h_final, h_boundary_nonneg, h_int_nonpos]

/-- Variant of `CDF.SOSD.expect_concave_compactSupport` for utilities differentiable on the
interior `(a, b)` with derivative `u'`. The right-derivative boundedness hypotheses reduce to
`BddBelow` and `BddAbove` of `u'` on `(a, b)`. -/
theorem CDF.SOSD.expect_concave_compactSupport_of_hasDerivAt (dF dG : ContDist) (u u' : ℝ → ℝ)
    {a b : ℝ} (hab : a < b)
    (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (h_suppF : ∀ x ∉ Icc a b, dF.density x = 0)
    (h_suppG : ∀ x ∉ Icc a b, dG.density x = 0)
    (hu_conc : ConcaveOn ℝ (Icc a b) u)
    (hu_mono : MonotoneOn u (Icc a b))
    (hu_cont : ContinuousOn u (Icc a b))
    (hu_deriv : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x)
    (hu'_bddBelow : BddBelow (u' '' Ioo a b))
    (hu'_bddAbove : BddAbove (u' '' Ioo a b))
    (h_intF : Integrable (fun x => dF.density x * u x))
    (h_intG : Integrable (fun x => dG.density x * u x)) :
    dG.expect u ≤ dF.expect u := by
  have heq : ∀ x ∈ Ioo a b, derivWithin (fun y => -u y) (Ioi x) x = -(u' x) := by
    intro x hx
    have hd : HasDerivAt (fun y => -u y) (-(u' x)) x := (hu_deriv x hx).neg
    exact hd.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)
  refine CDF.SOSD.expect_concave_compactSupport dF dG u hab h_sosd h_suppF h_suppG
    hu_conc hu_mono hu_cont ?_ ?_ h_intF h_intG
  · obtain ⟨M, hM⟩ := hu'_bddAbove
    refine ⟨-M, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    change -M ≤ derivWithin (fun y => -u y) (Ioi x) x
    rw [heq x hx]
    exact neg_le_neg (hM ⟨x, hx, rfl⟩)
  · obtain ⟨m, hm⟩ := hu'_bddBelow
    refine ⟨-m, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    change derivWithin (fun y => -u y) (Ioi x) x ≤ -m
    rw [heq x hx]
    exact neg_le_neg (hm ⟨x, hx, rfl⟩)

end Econlib.Probability
