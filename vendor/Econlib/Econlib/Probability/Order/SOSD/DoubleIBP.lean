/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.IntegralAsymp
public import Econlib.Math.MeasureTheory.StieltjesAbsCont
public import Econlib.Math.MeasureTheory.StieltjesIBP
public import Econlib.Probability.ContDist.CDFStieltjes
public import Econlib.Probability.Order.SOSD.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Double integration by parts for SOSD

This file provides the analytical core of the second-order stochastic dominance forward direction
for smooth utilities: Given `SOSD F G`, monotone `u` (`u' ≥ 0`), and concave `u` (`u'' ≤ 0`, so
`u ∈ C²`), the expectation ordering `E_G[u] ≤ E_F[u]` holds. The argument integrates by parts
twice: Once to rewrite `E_F[u] - E_G[u]` as an integral of the CDF difference, and once more to
expose the integrated CDF difference `H(x) = ∫_{Iic x} (F - G)`, whose sign (from dominance) and
that of `u''` (from concavity) deliver the inequality.

## Main definitions

* `integratedCDFDiff` — the integrated CDF difference `H(x) = ∫_{Iic x} (F(t) - G(t)) dt`.

## Main statements

* `first_ibp` — `E_F[u] - E_G[u] = ∫ (G - F) dμ_u`.
* `stieltjes_to_lebesgue` — `∫ h dμ_u = ∫ h · u' dx` for `C¹` monotone `u`.
* `second_ibp` — `∫ (F - G) · u' = L - ∫ H · u''`, with the boundary limit `L`.
* `integratedCDFDiff_nonpos` — `H ≤ 0` under SOSD.
* `sosd_expect_concave_mono_smooth_assembled` — the assembled `C²` forward direction.
-/

@[expose] public section

open MeasureTheory Set Filter Function
open scoped Topology ENNReal Real

namespace Econlib.Probability

open Monotone

variable {dF dG : ContDist} {u u' u'' : ℝ → ℝ}

-- First IBP: `E_F[u] - E_G[u] = ∫ (G - F) dμ_u`.

/-- First IBP on a bounded interval. -/
lemma first_ibp_local (dF dG : ContDist) (u : ℝ → ℝ) (hu : Monotone u)
    (a b : ℝ) (hab : a < b) :
    let F_sf := stieltjes dF.cdf.mono
    let G_sf := stieltjes dG.cdf.mono
    let u_sf := stieltjes hu
    let μ_u := stieltjesMeasure hu
    (∫ y in Ioc a b, G_sf y - F_sf y ∂μ_u) +
    ((∫ x in Ioc a b, dG.density x * u x) - (∫ x in Ioc a b, dF.density x * u x)) =
    (G_sf b - F_sf b) * u_sf b - (G_sf a - F_sf a) * u_sf a := by
  simp only
  set F_sf := stieltjes dF.cdf.mono
  set G_sf := stieltjes dG.cdf.mono
  set u_sf := stieltjes hu
  set μ_u := stieltjesMeasure hu
  have hF_ibp := stieltjes_ibp_local dF.cdf.mono hu a b hab
  have hG_ibp := stieltjes_ibp_local dG.cdf.mono hu a b hab
  dsimp only at hF_ibp hG_ibp
  rw [contdist_ibp_bridge_set dF u hu measurableSet_Ioc] at hF_ibp
  rw [contdist_ibp_bridge_set dG u hu measurableSet_Ioc] at hG_ibp
  -- hF_ibp : ∫ y in Ioc a b, F_sf y ∂μ_u + ∫ x in Ioc a b, dF.density x * u x
  --        = F_sf b * u_sf b - F_sf a * u_sf a
  -- hG_ibp : ∫ y in Ioc a b, G_sf y ∂μ_u + ∫ x in Ioc a b, dG.density x * u x
  --        = G_sf b * u_sf b - G_sf a * u_sf a
  -- Need integrability of F_sf and G_sf on Ioc a b w.r.t. μ_u to apply integral_sub
  have h_fin : μ_u (Ioc a b) ≠ ⊤ := by
    simp [μ_u, stieltjesMeasure, StieltjesFunction.measure_Ioc, ENNReal.ofReal_ne_top]
  have h_intF : IntegrableOn (⇑F_sf) (Ioc a b) μ_u :=
    stieltjes_integrableOn_Ioc F_sf a b h_fin
  have h_intG : IntegrableOn (⇑G_sf) (Ioc a b) μ_u :=
    stieltjes_integrableOn_Ioc G_sf a b h_fin
  -- Instead of rw, derive the split as a hypothesis for linarith
  have h_split : ∫ y in Ioc a b, G_sf y - F_sf y ∂μ_u =
      ∫ y in Ioc a b, G_sf y ∂μ_u - ∫ y in Ioc a b, F_sf y ∂μ_u :=
    MeasureTheory.integral_sub h_intG h_intF
  linarith

/-- Global first IBP: `E_F[u] - E_G[u] = ∫ (G - F) dμ_u`. All boundary limits are over ℝ (not ℕ) to
avoid casting overhead. -/
lemma first_ibp (dF dG : ContDist) (u : ℝ → ℝ) (hu : Monotone u)
    (h_intF : Integrable (fun x => dF.density x * u x))
    (h_intG : Integrable (fun x => dG.density x * u x))
    (h_stieltjes_int : Integrable
      (fun y => (stieltjes dG.cdf.mono) y - (stieltjes dF.cdf.mono) y)
      (stieltjesMeasure hu))
    -- Boundary decay over ℝ (avoids 0×∞; proved via tail-integral bounds)
    (h_bdy_top : Tendsto (fun x : ℝ =>
      ((stieltjes dG.cdf.mono) x - (stieltjes dF.cdf.mono) x) * (stieltjes hu) x) atTop (𝓝 0))
    (h_bdy_bot : Tendsto (fun x : ℝ =>
      ((stieltjes dG.cdf.mono) x - (stieltjes dF.cdf.mono) x) * (stieltjes hu) x) atBot (𝓝 0)) :
    dF.expect u - dG.expect u =
    ∫ y, (stieltjes dG.cdf.mono) y - (stieltjes dF.cdf.mono) y ∂(stieltjesMeasure hu) := by
  set F_sf := stieltjes dF.cdf.mono
  set G_sf := stieltjes dG.cdf.mono
  set u_sf := stieltjes hu
  set μ_u := stieltjesMeasure hu
  -- Approximate ℝ by expanding intervals Ioc(-n, n)
  set s := fun n : ℕ => Ioc (-(↑n : ℝ)) (↑n : ℝ)
  -- `d.expect u = ∫ x, d.density x * u x` (the global Lebesgue integral)
  have h_expect_eq : ∀ (d : ContDist), d.expect u = ∫ x, d.density x * u x := fun _ => rfl
  -- Local identity (for n ≥ 1)
  have h_local : ∀ᶠ n in atTop,
      (∫ y in s n, G_sf y - F_sf y ∂μ_u) +
      ((∫ x in s n, dG.density x * u x) - (∫ x in s n, dF.density x * u x)) =
      (G_sf ↑n - F_sf ↑n) * u_sf ↑n -
      (G_sf (-(↑n : ℝ)) - F_sf (-(↑n : ℝ))) * u_sf (-(↑n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact first_ibp_local dF dG u hu (-(↑n : ℝ)) ↑n
      (by have : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.one_le_iff_ne_zero.mp hn |>.bot_lt)
          linarith)
  -- Set integrals converge to global integrals
  have h_GF_lim : Tendsto (fun n => ∫ y in s n, G_sf y - F_sf y ∂μ_u) atTop
      (𝓝 (∫ y, G_sf y - F_sf y ∂μ_u)) :=
    tendsto_setIntegral_Ioc_neg h_stieltjes_int
  have h_expect_F : Tendsto (fun n => ∫ x in s n, dF.density x * u x) atTop
      (𝓝 (dF.expect u)) :=
    (h_expect_eq dF) ▸ tendsto_setIntegral_Ioc_neg h_intF
  have h_expect_G : Tendsto (fun n => ∫ x in s n, dG.density x * u x) atTop
      (𝓝 (dG.expect u)) :=
    (h_expect_eq dG) ▸ tendsto_setIntegral_Ioc_neg h_intG
  -- Boundary terms → 0
  have h_bdy : Tendsto (fun n : ℕ =>
      (G_sf ↑n - F_sf ↑n) * u_sf ↑n -
      (G_sf (-(↑n : ℝ)) - F_sf (-(↑n : ℝ))) * u_sf (-(↑n : ℝ))) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = 0 - 0 from (sub_self 0).symm]
    exact (h_bdy_top.comp tendsto_natCast_atTop_atTop).sub
      (h_bdy_bot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
  -- The LHS of the local identity tends to (∫ G_sf-F_sf dμ_u) + (E_G[u] - E_F[u])
  have h_lhs_lim : Tendsto (fun n =>
      (∫ y in s n, G_sf y - F_sf y ∂μ_u) +
      ((∫ x in s n, dG.density x * u x) - (∫ x in s n, dF.density x * u x))) atTop
      (𝓝 ((∫ y, G_sf y - F_sf y ∂μ_u) + (dG.expect u - dF.expect u))) :=
    h_GF_lim.add (h_expect_G.sub h_expect_F)
  -- By the local identity, this also tends to 0 (boundary terms)
  have h_eq_zero : (∫ y, G_sf y - F_sf y ∂μ_u) + (dG.expect u - dF.expect u) = 0 :=
    tendsto_nhds_unique h_lhs_lim ((tendsto_congr' h_local).mpr h_bdy)
  linarith

-- Stieltjes-to-Lebesgue conversion: `∫ h dμ_u = ∫ h · u' dx`.

/-- For C¹ monotone u with continuous u' ≥ 0: `∫ h dμ_u = ∫ h · u' dx`. -/
lemma stieltjes_to_lebesgue (hu : Monotone u)
    (h_deriv : ∀ x, HasDerivAt u (u' x) x) (hu_nn : ∀ x, 0 ≤ u' x)
    (hu_cont : Continuous u')
    (h : ℝ → ℝ) :
    ∫ y, h y ∂(stieltjesMeasure hu) = ∫ y, h y * u' y :=
  Monotone.stieltjes_integral_eq_lebesgue hu h_deriv hu_nn hu_cont h

-- Second IBP: `∫ (F - G) · u' = L - ∫ H · u''`.

/-- The integrated CDF difference: `H(x) = ∫_{Iic x} (F(t) - G(t)) dt`. Defined as a single
integral of the difference — NOT as `(∫ F) - (∫ G)`, which silently degenerates to 0 when
individual CDFs aren't integrable on Iic x (Bochner integral returns 0 for non-integrable
functions). -/
noncomputable def integratedCDFDiff (dF dG : ContDist) (x : ℝ) : ℝ :=
  ∫ t in Iic x, dF.cdf t - dG.cdf t

/-- H(x) ≤ 0 from SOSD. The per-cutoff CDF integrability comes from the tail witnesses bundled in
`h_sosd`. -/
lemma integratedCDFDiff_nonpos (h_sosd : CDF.SOSD dF.cdf dG.cdf) (x : ℝ) :
    integratedCDFDiff dF dG x ≤ 0 := by
  simp only [integratedCDFDiff]
  rw [integral_sub (h_sosd.tails_left x) (h_sosd.tails_right x)]
  exact sub_nonpos.mpr (h_sosd.dominance x)

/-- `integratedCDFDiff` is differentiable with derivative the pointwise CDF difference
`F(x) - G(x)`, given per-cutoff integrability of each CDF. -/
lemma integratedCDFDiff_hasDerivAt (dF dG : ContDist) (x : ℝ)
    (h_intF : ∀ y, IntegrableOn dF.cdf (Iic y))
    (h_intG : ∀ y, IntegrableOn dG.cdf (Iic y)) :
    HasDerivAt (integratedCDFDiff dF dG) (dF.cdf x - dG.cdf x) x := by
  -- h(t) = F(t) - G(t) is continuous
  set h := fun t => dF.cdf t - dG.cdf t with h_def
  have hh_cont : Continuous h := (contdist_cdf_continuous dF).sub (contdist_cdf_continuous dG)
  -- H(x) = C + ∫_0^x h where C = ∫ Iic 0 h
  set H := integratedCDFDiff dF dG with H_def
  set C := ∫ t in Iic (0 : ℝ), h t with C_def
  -- Key identity: H(y) = C + ∫_0^y h for all y
  -- Uses integral_Iic_sub_Iic which needs IntegrableOn h on both Iic 0 and Iic y.
  -- h = F - G is continuous and bounded (each CDF ∈ [0,1]), so integrable on bounded sets.
  -- On Iic y (semi-infinite): h is integrable iff the CDFs are individually integrable,
  -- which needs finite first moment. For the HasDerivAt proof, we only need the shift
  -- identity on a neighborhood of x, so we can work with bounded intervals.
  -- Alternative: use the fact that H is defined as an Iic integral, and write
  -- H(y) - H(0) as a difference of Iic integrals = interval integral by definition.
  have h_shift : ∀ y, H y = C + ∫ t in (0 : ℝ)..y, h t := by
    intro y; simp only [H_def, integratedCDFDiff, C_def, h_def]
    have h_int_y : IntegrableOn (fun t => dF.cdf t - dG.cdf t) (Iic y) :=
      (h_intF y).sub (h_intG y)
    have h_int_0 : IntegrableOn (fun t => dF.cdf t - dG.cdf t) (Iic 0) :=
      (h_intF 0).sub (h_intG 0)
    linarith [intervalIntegral.integral_Iic_sub_Iic (a := (0 : ℝ)) (b := y) h_int_0 h_int_y]
  -- FTC: d/dx (∫_0^x h) = h(x) when h is continuous at x
  have h_ftc : HasDerivAt (fun y => ∫ t in (0 : ℝ)..y, h t) (h x) x :=
    intervalIntegral.integral_hasDerivAt_right
      (hh_cont.intervalIntegrable 0 x)
      (hh_cont.stronglyMeasurableAtFilter volume (𝓝 x))
      hh_cont.continuousAt
  -- H = C + interval_integral, so H' = 0 + h(x) = h(x) = F(x) - G(x)
  have h_eq : H = fun y => C + ∫ t in (0 : ℝ)..y, h t := funext h_shift
  rw [show (dF.cdf x - dG.cdf x) = 0 + h x from by simp [h_def]]
  rw [h_eq]
  exact (hasDerivAt_const x C).add h_ftc

/-- Second IBP on [a, b]: `∫_a^b H' · u' = [H · u']_a^b - ∫_a^b H · u''`. -/
lemma second_ibp_local (dF dG : ContDist) (u' u'' : ℝ → ℝ)
    (h_deriv_u' : ∀ x, HasDerivAt u' (u'' x) x)
    (hu'_cont : Continuous u') (hu''_cont : Continuous u'')
    (h_cdf_intF : ∀ y, IntegrableOn dF.cdf (Iic y))
    (h_cdf_intG : ∀ y, IntegrableOn dG.cdf (Iic y))
    (a b : ℝ) :
    ∫ x in a..b, (dF.cdf x - dG.cdf x) * u' x =
    integratedCDFDiff dF dG b * u' b - integratedCDFDiff dF dG a * u' a -
    ∫ x in a..b, integratedCDFDiff dF dG x * u'' x := by
  -- CDF continuity for ContDist
  have hF_cont : Continuous dF.cdf := contdist_cdf_continuous dF
  have hG_cont : Continuous dG.cdf := contdist_cdf_continuous dG
  -- H is continuous: it has a derivative everywhere, hence is differentiable, hence continuous.
  have hH_diff : Differentiable ℝ (integratedCDFDiff dF dG) :=
    fun x => (integratedCDFDiff_hasDerivAt dF dG x h_cdf_intF h_cdf_intG).differentiableAt
  have hH_cont : Continuous (integratedCDFDiff dF dG) := hH_diff.continuous
  -- Each summand is continuous, hence interval-integrable
  have h_int1 : IntervalIntegrable (fun x => (dF.cdf x - dG.cdf x) * u' x) volume a b :=
    ((hF_cont.sub hG_cont).mul hu'_cont).intervalIntegrable a b
  have h_int2 : IntervalIntegrable (fun x => integratedCDFDiff dF dG x * u'' x) volume a b :=
    (hH_cont.mul hu''_cont).intervalIntegrable a b
  have h_prod_deriv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun x => integratedCDFDiff dF dG x * u' x)
        ((dF.cdf x - dG.cdf x) * u' x + integratedCDFDiff dF dG x * u'' x) x :=
    fun x _ => (integratedCDFDiff_hasDerivAt dF dG x h_cdf_intF h_cdf_intG).mul (h_deriv_u' x)
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt h_prod_deriv (h_int1.add h_int2)
  linarith [intervalIntegral.integral_add h_int1 h_int2]

/-- Global second IBP with algebraic limit existence. The boundary limit
`L = lim_{x→+∞} H(x)·u'(x)` exists because `H·u'` differs from a pair of convergent integrals by a
constant; it need not be monotone, since `H` may oscillate. -/
lemma second_ibp (dF dG : ContDist) (u' u'' : ℝ → ℝ)
    (h_deriv_u' : ∀ x, HasDerivAt u' (u'' x) x)
    (hu'_cont : Continuous u') (hu''_cont : Continuous u'')
    (h_cdf_intF : ∀ y, IntegrableOn dF.cdf (Iic y))
    (h_cdf_intG : ∀ y, IntegrableOn dG.cdf (Iic y))
    (h_bdy_left : Tendsto (fun x : ℝ => u' x * integratedCDFDiff dF dG x) atBot (𝓝 0))
    (h_int_prod : Integrable (fun x => (dF.cdf x - dG.cdf x) * u' x))
    (h_int_Hu : Integrable (fun x => integratedCDFDiff dF dG x * u'' x)) :
    -- The limit L exists and the global identity holds simultaneously
    ∃ L : ℝ,
      Tendsto (fun x : ℝ => integratedCDFDiff dF dG x * u' x) atTop (𝓝 L) ∧
      ∫ x, (dF.cdf x - dG.cdf x) * u' x = L - ∫ x, integratedCDFDiff dF dG x * u'' x := by
  -- Abbreviations
  set H := integratedCDFDiff dF dG
  set f := fun x => (dF.cdf x - dG.cdf x) * u' x  -- = H' * u'
  set g := fun x => H x * u'' x                              -- = H * u''
  -- Define L as the limit value ∫ f + ∫ g
  set L := (∫ x, f x) + (∫ x, g x) with L_def
  -- The identity ∫ f = L - ∫ g is immediate from L = ∫ f + ∫ g
  have h_identity : ∫ x, f x = L - ∫ x, g x :=
    L_def ▸ (add_sub_cancel_right (∫ x, f x) (∫ x, g x)).symm
  -- For the ℝ-indexed Tendsto: H·u' is continuous (product of differentiable functions)
  -- and H(n)·u'(n) → L. Extension from ℕ to ℝ for continuous functions with
  -- ℕ-indexed limits: use the local identity H(x)·u'(x) = H(0)·u'(0) + ∫_0^x f + ∫_0^x g
  -- and ℝ-indexed convergence of set integrals of integrable functions.
  have h_real_lim : Tendsto (fun x : ℝ => H x * u' x) atTop (𝓝 L) := by
    -- From local IBP on [0, x]: H(x)·u'(x) = H(0)·u'(0) + ∫_0^x f + ∫_0^x g
    -- Both ∫_0^x f and ∫_0^x g converge over ℝ (from integrability).
    -- H(x)·u'(x) is the sum of a constant and two convergent integrals.
    have h_from_real : ∀ x : ℝ, 0 ≤ x →
        H x * u' x = (H (-x) * u' (-x) + ∫ t in (-x)..x, f t) + ∫ t in (-x)..x, g t := by
      intro x hx
      have h_ibp :=
        second_ibp_local dF dG u' u'' h_deriv_u' hu'_cont hu''_cont h_cdf_intF h_cdf_intG (-x) x
      linarith
    -- ∫_0^x f → ∫_{Ioi 0} f and ∫_0^x g → ∫_{Ioi 0} g as x → +∞ (from integrability)
    -- H(x)·u'(x) = const + converging + converging → limit exists
    have h_bdy_real : Tendsto (fun x : ℝ => H (-x) * u' (-x)) atTop (𝓝 0) := by
      have := h_bdy_left.comp tendsto_neg_atTop_atBot
      exact this.congr' (Filter.Eventually.of_forall (fun x => mul_comm _ _))
    have h_f_tendsto : Tendsto (fun x : ℝ => ∫ t in (-x)..x, f t) atTop (𝓝 (∫ t, f t)) :=
      MeasureTheory.intervalIntegral_tendsto_integral h_int_prod
        tendsto_neg_atTop_atBot tendsto_id
    have h_g_tendsto : Tendsto (fun x : ℝ => ∫ t in (-x)..x, g t) atTop (𝓝 (∫ t, g t)) :=
      MeasureTheory.intervalIntegral_tendsto_integral h_int_Hu
        tendsto_neg_atTop_atBot tendsto_id
    have h_sum : Tendsto
        (fun x : ℝ => (H (-x) * u' (-x) + ∫ t in (-x)..x, f t) + ∫ t in (-x)..x, g t)
        atTop (𝓝 L) := by
      have := (h_bdy_real.add h_f_tendsto).add h_g_tendsto
      simp only [zero_add, ← L_def] at this
      exact this
    refine h_sum.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact (h_from_real x hx).symm
  exact ⟨L, h_real_lim, h_identity⟩

-- Sign analysis: `∫ H · u'' ≥ 0` and `-L ≥ 0`.

/-- ∫ H · u'' ≥ 0 because H ≤ 0 (SOSD) and u'' ≤ 0 (concavity). -/
lemma integral_H_u''_nonneg (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (hu_concave : ∀ x, u'' x ≤ 0) :
    0 ≤ ∫ x, integratedCDFDiff dF dG x * u'' x := by
  apply integral_nonneg
  intro x
  exact mul_nonneg_of_nonpos_of_nonpos
    (integratedCDFDiff_nonpos h_sosd x) (hu_concave x)

/-- L ≤ 0 (hence -L ≥ 0) because each H(x)·u'(x) ≤ 0 (H ≤ 0, u' ≥ 0). -/
lemma boundary_nonneg (h_sosd : CDF.SOSD dF.cdf dG.cdf) (hu_mono : ∀ x, 0 ≤ u' x)
    (L : ℝ) (hL : Tendsto (fun x : ℝ => integratedCDFDiff dF dG x * u' x) atTop (𝓝 L)) :
    0 ≤ -L := by
  have h_nonpos : ∀ x : ℝ, integratedCDFDiff dF dG x * u' x ≤ 0 :=
    fun x => mul_nonpos_of_nonpos_of_nonneg
      (integratedCDFDiff_nonpos h_sosd x) (hu_mono x)
  have : L ≤ 0 := le_of_tendsto hL (Eventually.of_forall h_nonpos)
  linarith

-- Assembly.

/-- The fully assembled SOSD forward direction for C² functions. -/
theorem sosd_expect_concave_mono_smooth_assembled
    (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (hu_mono_fn : Monotone u) (hu_mono : ∀ x, 0 ≤ u' x) (hu_concave : ∀ x, u'' x ≤ 0)
    (h_deriv_u : ∀ x, HasDerivAt u (u' x) x) (h_deriv_u' : ∀ x, HasDerivAt u' (u'' x) x)
    (hu'_cont : Continuous u') (hu''_cont : Continuous u'')
    (h_intF : Integrable (fun x => dF.density x * u x))
    (h_intG : Integrable (fun x => dG.density x * u x))
    -- Boundary decay over ℝ (avoid 0×∞)
    (h_bdy_left : Tendsto (fun x : ℝ => u' x * integratedCDFDiff dF dG x) atBot (𝓝 0))
    (h_bdy_top_ibp1 : Tendsto (fun x : ℝ =>
      ((stieltjes dG.cdf.mono) x - (stieltjes dF.cdf.mono) x) * (stieltjes hu_mono_fn) x)
      atTop (𝓝 0))
    (h_bdy_bot_ibp1 : Tendsto (fun x : ℝ =>
      ((stieltjes dG.cdf.mono) x - (stieltjes dF.cdf.mono) x) * (stieltjes hu_mono_fn) x)
      atBot (𝓝 0))
    -- Global integrability of intermediate products
    (h_int_GF_u' : Integrable (fun x => (dF.cdf x - dG.cdf x) * u' x))
    (h_int_H_u'' : Integrable (fun x => integratedCDFDiff dF dG x * u'' x))
    (h_stieltjes_int : Integrable
      (fun y => (stieltjes dG.cdf.mono) y - (stieltjes dF.cdf.mono) y)
      (stieltjesMeasure hu_mono_fn)) :
    dG.expect u ≤ dF.expect u := by
  -- The per-cutoff CDF integrability comes from the tail witnesses bundled in `h_sosd`.
  have h_cdf_int : ∀ x, IntegrableOn dF.cdf (Iic x) ∧ IntegrableOn dG.cdf (Iic x) :=
    fun x => ⟨h_sosd.tails_left x, h_sosd.tails_right x⟩
  -- Step 1: E_F[u] - E_G[u] = ∫ (G - F) dμ_u
  have h1 := first_ibp dF dG u hu_mono_fn h_intF h_intG
    h_stieltjes_int h_bdy_top_ibp1 h_bdy_bot_ibp1
  -- Step 2: ∫ (G - F) dμ_u = ∫ (G - F) · u' dx
  have h2 := stieltjes_to_lebesgue hu_mono_fn h_deriv_u hu_mono hu'_cont
    (fun y => (stieltjes dG.cdf.mono) y - (stieltjes dF.cdf.mono) y)
  -- Step 3: ∃ L, ∫ (F-G)·u' = L - ∫ H·u'' (with algebraic limit existence)
  obtain ⟨L, hL_tendsto, h3⟩ := second_ibp dF dG u' u'' h_deriv_u' hu'_cont hu''_cont
    (fun y => (h_cdf_int y).1) (fun y => (h_cdf_int y).2)
    h_bdy_left h_int_GF_u' h_int_H_u''
  -- Step 4: Sign analysis
  have h4 := integral_H_u''_nonneg h_sosd hu_concave
  have h5 := boundary_nonneg h_sosd hu_mono L hL_tendsto
  -- Chain: E_F - E_G = ∫ (G-F) dμ_u          [h1]
  --                   = ∫ (G-F) · u' dx        [h2]
  --                   = -(∫ (F-G) · u')         [negation]
  --                   = -(L - ∫ H·u'')          [h3]
  --                   = -L + ∫ H·u''            [algebra]
  -- Since -L ≥ 0 [h5] and ∫ H·u'' ≥ 0 [h4]:
  --   E_F - E_G ≥ 0, i.e., E_G ≤ E_F.
  -- Bridge: stieltjes(CDF.mono) = CDF.cdf for right-continuous CDFs
  have h_sf_eq : ∀ (d : ContDist) (y : ℝ), (stieltjes d.cdf.mono) y = d.cdf y := by
    intro d y
    change d.cdf.mono.stieltjesFunction y = d.cdf y
    rw [Monotone.stieltjesFunction_eq]
    exact rightLim_eq_of_tendsto (nhdsWithin_Ioi_neBot le_rfl).ne
      ((d.cdf.right_continuous y).mono_left (nhdsWithin_mono y Ioi_subset_Ici_self))
  -- h2 converts from Stieltjes integral to Lebesgue integral:
  --   ∫ (G_sf - F_sf) dμ_u = ∫ (G_sf - F_sf) · u'
  -- Using G_sf = G.cdf and F_sf = F.cdf:
  --   ∫ (G.cdf - F.cdf) dμ_u = ∫ (G.cdf - F.cdf) · u'
  -- h3 gives: ∫ (F.cdf - G.cdf) · u' = L - ∫ H·u''
  -- So: ∫ (G.cdf - F.cdf) · u' = -(L - ∫ H·u'') = -L + ∫ H·u''
  -- h1 gives: E_F - E_G = ∫ (G_sf - F_sf) dμ_u = ∫ (G.cdf - F.cdf) dμ_u
  -- Combining: E_F - E_G = -L + ∫ H·u'' ≥ 0
  -- Rewrite h2 using the CDF identity
  have h2' : ∫ y, ((stieltjes dG.cdf.mono) y - (stieltjes dF.cdf.mono) y) * u' y =
      ∫ y, (dG.cdf y - dF.cdf y) * u' y := by
    congr 1; ext y; rw [h_sf_eq dG y, h_sf_eq dF y]
  -- The negation identity: ∫ (G-F)·u' = -(∫ (F-G)·u')
  have h_neg : ∫ y, (dG.cdf y - dF.cdf y) * u' y =
      -(∫ y, (dF.cdf y - dG.cdf y) * u' y) := by
    rw [← integral_neg]; congr 1; ext y; ring
  -- Chain the equalities
  have h_chain : dF.expect u - dG.expect u = -L + ∫ x, integratedCDFDiff dF dG x * u'' x := by
    linarith [h1, h2, h2', h_neg, h3]
  linarith

end Econlib.Probability
