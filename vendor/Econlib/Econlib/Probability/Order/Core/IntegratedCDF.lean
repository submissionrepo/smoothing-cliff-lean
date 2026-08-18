/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.CDFTails
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Level-one integrated CDF identities

This file proves level-one integrated CDF identities for any continuous distribution with a finite
first moment. The central identity rewrites `∫_{Iic x} F(s) ds` in terms of `x · F(x)` and the
truncated first moment, giving the integration-by-parts form for stochastic-order arguments.

## Main statements

* `ibp_cdf_id_local` — integration by parts on a bounded interval: `∫ F + ∫ density·t = F·x - F·a`.
* `integral_cdf_Iic_eq` — the global identity `∫_{Iic x} F = x·F(x) - ∫_{Iic x} density·t`.
* `cdf_integrableOn_Iic` — integrability of the CDF on `Iic x` from a finite first moment.

## Tags

integrated cdf, integration by parts, continuous distribution
-/

@[expose] public section

open MeasureTheory Set BigOperators Function Filter
open scoped Topology ENNReal Real

namespace Econlib.Probability

open Monotone

/-- Integration by parts on `(a, x]`:
`∫_{(a,x]} F(s) ds + ∫_{(a,x]} density(t) * t dt = F(x)*x - F(a)*a`. -/
lemma ibp_cdf_id_local (d : ContDist) (a x : ℝ) (hax : a < x) :
    (∫ t in Ioc a x, d.cdf t) +
    ∫ t in Ioc a x, d.density t * t =
    d.cdf x * x - d.cdf a * a := by
  have h_ibp := stieltjes_ibp_local d.cdf.mono monotone_id a x hax
  have hF_eq : ∀ y, (stieltjes d.cdf.mono) y = d.cdf y :=
    stieltjes_eq_of_rightCts d.cdf.mono d.cdf.right_continuous
  have hid_eq : ⇑(stieltjes monotone_id) = id := stieltjes_id_eq
  have h_mu_id : stieltjesMeasure monotone_id = volume := stieltjesMeasure_id_eq_volume
  have h1 : ∫ y in Ioc a x, (stieltjes d.cdf.mono) y ∂(stieltjesMeasure monotone_id) =
      ∫ s in Ioc a x, d.cdf s := by
    rw [h_mu_id]; exact setIntegral_congr_fun measurableSet_Ioc (fun s _ => hF_eq s)
  have h2 : ∫ x_1 in Ioc a x, leftLim (⇑(stieltjes monotone_id)) x_1
      ∂(stieltjesMeasure d.cdf.mono) = ∫ t in Ioc a x, d.density t * t :=
    contdist_ibp_bridge_set d id monotone_id measurableSet_Ioc
  have h3 : (stieltjes d.cdf.mono) x * (stieltjes monotone_id) x -
      (stieltjes d.cdf.mono) a * (stieltjes monotone_id) a =
      d.cdf x * x - d.cdf a * a := by
    rw [hF_eq, hF_eq, show (stieltjes monotone_id) x = x from congr_fun hid_eq x,
        show (stieltjes monotone_id) a = a from congr_fun hid_eq a]
  linarith

/-- Shared `AECover` scaffolding for the integrated-CDF limit. With `s n := (-n, x]` covering
`Iic x`, this packages the three ingredients both `integral_cdf_Iic_eq` and `cdf_integrableOn_Iic`
feed to their `AECover` finishers: The cover itself, per-`n` integrability of the (continuous,
hence bounded) CDF restricted to `Iic x`, and convergence of the partial integrals to
`x·F(x) − ∫_{Iic x} density·t` (obtained from `ibp_cdf_id_local` plus
`cdf_times_a_tendsto_zero_left` for the boundary decay). -/
private lemma cdf_Iic_aecover_scaffold (d : ContDist) (x : ℝ)
    (h_mean : Integrable (fun t => d.density t * t)) :
    let s : ℕ → Set ℝ := fun n => Ioc (-(↑n : ℝ)) x
    AECover (volume.restrict (Iic x)) atTop s ∧
    (∀ n, IntegrableOn d.cdf (s n) (volume.restrict (Iic x))) ∧
    Tendsto (fun n => ∫ t in s n, d.cdf t ∂(volume.restrict (Iic x))) atTop
      (𝓝 (x * d.cdf x - ∫ t in Iic x, d.density t * t)) := by
  intro s
  have hs_union : ⋃ n : ℕ, s n = Iic x := by
    ext t; simp only [s, mem_iUnion, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨n, _, htx⟩; exact htx
    · intro htx; obtain ⟨n, hn⟩ := exists_nat_gt (-t)
      exact ⟨n, by linarith, htx⟩
  have hs_mono : Monotone s :=
    fun _ _ h => Ioc_subset_Ioc (neg_le_neg (Nat.cast_le.mpr h)) le_rfl
  have hF_cont : Continuous d.cdf := contdist_cdf_continuous d
  -- `s n ∩ Iic x = s n`, so restricting the volume measure to `Iic x` is harmless on each `s n`.
  have hs_inter : ∀ n, s n ∩ Iic x = s n :=
    fun n => by ext t; simp only [s, mem_inter_iff, mem_Ioc, mem_Iic]; tauto
  have h_ae_cover : AECover (volume.restrict (Iic x)) atTop s := by
    refine ⟨?_, fun n => measurableSet_Ioc⟩
    exact (ae_restrict_mem measurableSet_Iic).mono fun t (ht : t ≤ x) => by
      obtain ⟨N, hN⟩ := exists_nat_gt (-t)
      exact eventually_atTop.mpr ⟨N, fun n hn => by
        simp only [s, mem_Ioc]
        exact ⟨by linarith [show (↑N : ℝ) ≤ (↑n : ℝ) from Nat.cast_le.mpr hn], ht⟩⟩
  have h_intOn_restr : ∀ n, IntegrableOn d.cdf (s n) (volume.restrict (Iic x)) := by
    intro n
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioc, hs_inter n]
    exact hF_cont.integrableOn_Ioc
  have h_restrict_eq : ∀ n, ∫ t in s n, d.cdf t ∂(volume.restrict (Iic x)) =
      ∫ t in s n, d.cdf t :=
    fun n => by rw [Measure.restrict_restrict measurableSet_Ioc, hs_inter n]
  have h_dt_lim : Tendsto (fun n => ∫ t in s n, d.density t * t) atTop
      (𝓝 (∫ t in Iic x, d.density t * t)) := by
    rw [← hs_union]
    exact tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioc) hs_mono
      (hs_union ▸ h_mean.integrableOn)
  -- IBP on each `(-n, x]`, valid once `-n < x`, gives `∫ F = F(x)·x - F(-n)·(-n) - ∫ density·t`.
  have h_ibp_n : ∀ᶠ n : ℕ in atTop,
      ∫ t in s n, d.cdf t =
      d.cdf x * x - d.cdf (-(↑n : ℝ)) * (-(↑n : ℝ)) -
      ∫ t in s n, d.density t * t := by
    obtain ⟨N, hN⟩ := exists_nat_gt (-x)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hax : -(↑n : ℝ) < x := by
      have : (↑N : ℝ) ≤ (↑n : ℝ) := Nat.cast_le.mpr hn; linarith
    have := ibp_cdf_id_local d (-(↑n : ℝ)) x hax; linarith
  have h_bdy := cdf_times_a_tendsto_zero_left d h_mean
  have h_cdf_lim : Tendsto (fun n => ∫ t in s n, d.cdf t) atTop
      (𝓝 (x * d.cdf x - ∫ t in Iic x, d.density t * t)) := by
    rw [show x * d.cdf x - ∫ t in Iic x, d.density t * t =
        d.cdf x * x - 0 - ∫ t in Iic x, d.density t * t from by ring]
    exact (tendsto_congr' h_ibp_n).mpr ((tendsto_const_nhds.sub h_bdy).sub h_dt_lim)
  have h_cdf_lim_restr : Tendsto (fun n => ∫ t in s n, d.cdf t ∂(volume.restrict (Iic x)))
      atTop (𝓝 (x * d.cdf x - ∫ t in Iic x, d.density t * t)) := by
    simp_rw [h_restrict_eq]; exact h_cdf_lim
  exact ⟨h_ae_cover, h_intOn_restr, h_cdf_lim_restr⟩

/-- The integrated CDF in closed form:
`∫_{Iic x} F(s) ds = x * F(x) - ∫_{Iic x} density(t) * t dt`, valid for any continuous distribution
with a finite first moment. -/
lemma integral_cdf_Iic_eq (d : ContDist) (x : ℝ)
    (h_mean : Integrable (fun t => d.density t * t)) :
    ∫ s in Iic x, d.cdf s =
    x * d.cdf x - ∫ t in Iic x, d.density t * t := by
  obtain ⟨h_ae_cover, h_cdf_intOn_restr, h_cdf_lim_restr⟩ :=
    cdf_Iic_aecover_scaffold d x h_mean
  exact h_ae_cover.integral_eq_of_tendsto_of_nonneg_ae
    (x * d.cdf x - ∫ t in Iic x, d.density t * t)
    (ae_of_all _ (fun t => d.cdf_nonneg t)) h_cdf_intOn_restr h_cdf_lim_restr

/-- The CDF is integrable on `Iic x` when the density has a finite first moment. -/
lemma cdf_integrableOn_Iic (d : ContDist) (x : ℝ)
    (h_mean : Integrable (fun t => d.density t * t)) :
    IntegrableOn d.cdf (Iic x) := by
  obtain ⟨h_ae_cover, h_intOn_restr, h_cdf_lim_restr⟩ :=
    cdf_Iic_aecover_scaffold d x h_mean
  exact h_ae_cover.integrable_of_integral_tendsto_of_nonneg_ae
    (x * d.cdf x - ∫ t in Iic x, d.density t * t)
    h_intOn_restr (ae_of_all _ d.cdf_nonneg) h_cdf_lim_restr

end Econlib.Probability
