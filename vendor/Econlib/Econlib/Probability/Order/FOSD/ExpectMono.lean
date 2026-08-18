/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.StieltjesIBP
public import Econlib.Probability.ContDist.CDFTails
public import Econlib.Probability.Order.FOSD.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Order.CompletePartialOrder

/-!
# FOSD and the monotone-expectation characterization

For continuous distributions, first-order stochastic dominance of `dF` over `dG` is equivalent to
`dF` raising the expectation of every monotone payoff: If `u` is monotone with `density · u`
integrable against both distributions, then `E_G[u] ≤ E_F[u]`. This is the every-increasing-utility
characterization of first-order dominance (Hadar and Russell 1969; Hanoch and Levy 1969).

## Main statements

* `FOSD.expect_mono` — first-order dominance raises monotone expectations.
* `FOSD.expect_strict_mono` — strict dominance and a strictly monotone payoff give a strict
  inequality.
* `FOSD.iff_expect_mono` — first-order dominance holds iff every monotone payoff is weakly
  preferred.

## References

* Hadar, Josef, and William R. Russell. 1969. “Rules for Ordering Uncertain Prospects.” *The
  American Economic Review* 59 (1): 25–34.
* Hanoch, G., and H. Levy. 1969. “The Efficiency Analysis of Choices Involving Risk.” *The Review
  of Economic Studies* 36 (3): 335–46. [https://doi.org/10.2307/2296431](https://doi.org/10.2307/2296431).

## Tags

first-order stochastic dominance, fosd, monotone, expectation, increasing utility
-/

@[expose] public section

open MeasureTheory Set BigOperators Function Filter
open scoped Topology ENNReal Real

namespace Econlib.Probability

open Monotone

/-- FOSD ordering is preserved by Stieltjes regularization. CDFs are right-continuous, so
`stieltjes(CDF.mono) = CDF.cdf` and FOSD transfers. -/
lemma stieltjes_fosd {F G : CDF} (h : IntegratedCDFTower 1 F G) (x : ℝ) :
    (stieltjes F.mono) x ≤ (stieltjes G.mono) x := by
  rw [show stieltjes F.mono = F.mono.stieltjesFunction from rfl,
      show stieltjes G.mono = G.mono.stieltjesFunction from rfl,
      stieltjes_eq_of_rightCts F.mono F.right_continuous,
      stieltjes_eq_of_rightCts G.mono G.right_continuous]
  exact h x

/-- CDFs live in `[0,1]`, so their Stieltjes regularization is integrable on any bounded `Ioc`
against the finite measure `μ_u`. Shared by the expanding-interval arguments below. -/
private lemma cdf_integrableOn_Ioc (d : ContDist) {u : ℝ → ℝ} (hu : Monotone u) (a b : ℝ) :
    IntegrableOn (⇑(stieltjes d.cdf.mono)) (Ioc a b) (stieltjesMeasure hu) := by
  have h_fin : stieltjesMeasure hu (Ioc a b) ≠ ⊤ := by
    simp [stieltjesMeasure, StieltjesFunction.measure_Ioc, ENNReal.ofReal_ne_top]
  exact Measure.integrableOn_of_bounded h_fin
    (stieltjes d.cdf.mono).mono.measurable.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun y _ => by
      rw [Real.norm_eq_abs, abs_le, stieltjes_eq_of_rightCts d.cdf.mono d.cdf.right_continuous]
      exact ⟨by linarith [d.cdf_nonneg y], d.cdf_le_one y⟩))

/-- The expanding-interval CDF integral difference converges to `E_F[u] - E_G[u]`. This packages
the local IBP identity (`stieltjes_ibp_local` + `contdist_ibp_bridge_set`), the density-expectation
convergence (`tendsto_setIntegral_of_monotone`), and the boundary decay
(`cdf_boundary_diff_tendsto_zero`) used by both `expect_mono` and `expect_strict_mono`. -/
private lemma cdf_integral_diff_tendsto (dF dG : ContDist) {u : ℝ → ℝ} (hu : Monotone u)
    (h_intF : Integrable (fun x => dF.density x * u x))
    (h_intG : Integrable (fun x => dG.density x * u x)) :
    Tendsto (fun n : ℕ =>
      ∫ y in Ioc (-(↑n : ℝ)) ↑n, stieltjes dG.cdf.mono y ∂(stieltjesMeasure hu) -
      ∫ y in Ioc (-(↑n : ℝ)) ↑n, stieltjes dF.cdf.mono y ∂(stieltjesMeasure hu)) atTop
      (𝓝 (dF.expect u - dG.expect u)) := by
  set F_sf := stieltjes dF.cdf.mono
  set G_sf := stieltjes dG.cdf.mono
  set u_sf := stieltjes hu
  set μ_u := stieltjesMeasure hu
  set s := fun n : ℕ => Ioc (-(↑n : ℝ)) (↑n : ℝ) with hs_def
  have hs_meas : ∀ n, MeasurableSet (s n) := fun _ => measurableSet_Ioc
  have hs_mono : Monotone s :=
    fun _ _ h => Ioc_subset_Ioc (neg_le_neg (Nat.cast_le.mpr h)) (Nat.cast_le.mpr h)
  have hs_union : ⋃ n, s n = univ := by
    ext x; simp only [s, mem_iUnion, mem_Ioc, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨n, neg_lt_of_abs_lt hn, le_of_lt (abs_lt.mp hn).2⟩
  -- Local IBP identity (n ≥ 1): CDF_diff + expect_diff = boundary
  have h_local : ∀ᶠ n in atTop,
      (∫ y in s n, G_sf y ∂μ_u - ∫ y in s n, F_sf y ∂μ_u) +
      (∫ x in s n, dG.density x * u x) - (∫ x in s n, dF.density x * u x) =
      (G_sf ↑n - F_sf ↑n) * u_sf ↑n -
      (G_sf (-(↑n : ℝ)) - F_sf (-(↑n : ℝ))) * u_sf (-(↑n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hab : (-(↑n : ℝ)) < ↑n := by
      have : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.one_le_iff_ne_zero.mp hn |>.bot_lt)
      linarith
    have hF : ∫ y in Ioc (-(↑n : ℝ)) ↑n, F_sf y ∂μ_u +
        ∫ x in Ioc (-(↑n : ℝ)) ↑n, leftLim (⇑u_sf) x ∂(stieltjesMeasure dF.cdf.mono) =
        F_sf ↑n * u_sf ↑n - F_sf (-(↑n : ℝ)) * u_sf (-(↑n : ℝ)) :=
      stieltjes_ibp_local dF.cdf.mono hu (-(↑n : ℝ)) ↑n hab
    have hG : ∫ y in Ioc (-(↑n : ℝ)) ↑n, G_sf y ∂μ_u +
        ∫ x in Ioc (-(↑n : ℝ)) ↑n, leftLim (⇑u_sf) x ∂(stieltjesMeasure dG.cdf.mono) =
        G_sf ↑n * u_sf ↑n - G_sf (-(↑n : ℝ)) * u_sf (-(↑n : ℝ)) :=
      stieltjes_ibp_local dG.cdf.mono hu (-(↑n : ℝ)) ↑n hab
    rw [contdist_ibp_bridge_set dF u hu measurableSet_Ioc] at hF
    rw [contdist_ibp_bridge_set dG u hu measurableSet_Ioc] at hG
    simp only [s]; linarith
  -- Density expectations converge on expanding intervals
  have h_expect_eq : ∀ (d : ContDist), d.expect u = ∫ x in ⋃ n, s n, d.density x * u x := by
    intro d; rw [hs_union, setIntegral_univ]; rfl
  have h_expect_G : Tendsto (fun n => ∫ x in s n, dG.density x * u x) atTop
      (𝓝 (dG.expect u)) := by
    rw [h_expect_eq]; exact tendsto_setIntegral_of_monotone hs_meas hs_mono
      (hs_union ▸ h_intG.integrableOn)
  have h_expect_F : Tendsto (fun n => ∫ x in s n, dF.density x * u x) atTop
      (𝓝 (dF.expect u)) := by
    rw [h_expect_eq]; exact tendsto_setIntegral_of_monotone hs_meas hs_mono
      (hs_union ▸ h_intF.integrableOn)
  -- Boundary terms → 0; combine into the CDF-difference limit via h_local
  have h_bdy := cdf_boundary_diff_tendsto_zero dF dG u hu h_intF h_intG
  have h_lim : Tendsto (fun (n : ℕ) =>
      (G_sf ↑n - F_sf ↑n) * u_sf ↑n -
      (G_sf (-(↑n : ℝ)) - F_sf (-(↑n : ℝ))) * u_sf (-(↑n : ℝ)) -
      ((∫ x in s n, dG.density x * u x) - (∫ x in s n, dF.density x * u x))) atTop
      (𝓝 (dF.expect u - dG.expect u)) := by
    rw [show dF.expect u - dG.expect u = 0 - (dG.expect u - dF.expect u) from by ring]
    exact h_bdy.sub (h_expect_G.sub h_expect_F)
  exact (Filter.tendsto_congr' (h_local.mono fun n h => by rw [hs_def]; linarith)).mp h_lim

namespace FOSD

/-- **First-order dominance raises monotone expectations.** If `dF` first-order stochastically
dominates `dG` and `u` is monotone with `density · u` integrable against both distributions, then
`E_G[u] ≤ E_F[u]` (Hadar and Russell 1969). -/
lemma expect_mono (dF dG : ContDist) (u : ℝ → ℝ) (hu : Monotone u)
    (h_fosd : IntegratedCDFTower 1 dF.cdf dG.cdf)
    (h_intF : Integrable (fun x => dF.density x * u x))
    (h_intG : Integrable (fun x => dG.density x * u x)) :
    dG.expect u ≤ dF.expect u := by
  -- Strategy: the expanding-interval CDF integral difference ∫_{s n}(G_sf - F_sf) dμ_u converges
  -- to E_F - E_G (cdf_integral_diff_tendsto) and is eventually ≥ 0 (FOSD + local integrability), so
  -- the limit E_F - E_G ≥ 0.
  set F_sf := stieltjes dF.cdf.mono
  set G_sf := stieltjes dG.cdf.mono
  set μ_u := stieltjesMeasure hu
  suffices h : 0 ≤ dF.expect u - dG.expect u by linarith
  have h_lim := cdf_integral_diff_tendsto dF dG hu h_intF h_intG
  -- Local CDF difference ≥ 0 (FOSD + integrability of bounded CDFs on bounded sets)
  have h_local_nonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ ∫ y in Ioc (-(↑n : ℝ)) ↑n, G_sf y ∂μ_u - ∫ y in Ioc (-(↑n : ℝ)) ↑n, F_sf y ∂μ_u := by
    filter_upwards with n
    rw [← integral_sub (cdf_integrableOn_Ioc dG hu _ _) (cdf_integrableOn_Ioc dF hu _ _)]
    exact setIntegral_nonneg measurableSet_Ioc
      (fun y _ => sub_nonneg.mpr (stieltjes_fosd h_fosd y))
  exact ge_of_tendsto h_lim h_local_nonneg

/-- **Strict FOSD implies a strict expectation gap for strictly monotone payoffs.** If `dF`
first-order stochastically dominates `dG` with strict CDF inequality `dF.cdf x₀ < dG.cdf x₀` at
some point, and `u` is strictly monotone with `density · u` integrable against both distributions,
then `E_G[u] < E_F[u]`. -/
lemma expect_strict_mono (dF dG : ContDist) (u : ℝ → ℝ) (hu : StrictMono u)
    (h_fosd : IntegratedCDFTower 1 dF.cdf dG.cdf)
    (h_strict : ∃ x₀, dF.cdf x₀ < dG.cdf x₀)
    (h_intF : Integrable (fun x => dF.density x * u x))
    (h_intG : Integrable (fun x => dG.density x * u x)) :
    dG.expect u < dF.expect u := by
  -- Weak inequality from FOSD.expect_mono
  have h_weak := expect_mono dF dG u hu.monotone h_fosd h_intF h_intG
  -- Strict: show E_F[u] - E_G[u] > 0 via the local IBP argument
  -- Reuse the IBP setup from expect_mono
  set F_sf := stieltjes dF.cdf.mono
  set G_sf := stieltjes dG.cdf.mono
  set u_sf := stieltjes hu.monotone
  set μ_u := stieltjesMeasure hu.monotone
  -- The local CDF integral is eventually strictly positive
  obtain ⟨x₀, hx₀⟩ := h_strict
  -- CDF gap: G_sf(x₀) > F_sf(x₀)
  have h_gap : F_sf x₀ < G_sf x₀ := by
    rwa [stieltjes_eq_of_rightCts dF.cdf.mono dF.cdf.right_continuous,
         stieltjes_eq_of_rightCts dG.cdf.mono dG.cdf.right_continuous]
  -- μ_u charges Ioc x₀ (x₀+1): since u is strictly monotone,
  -- u_sf(x₀+1) > u_sf(x₀), so μ_u(Ioc x₀ (x₀+1)) > 0
  have h_mu_pos : 0 < μ_u (Ioc x₀ (x₀ + 1)) := by
    rw [show μ_u = u_sf.measure from rfl, StieltjesFunction.measure_Ioc]
    apply ENNReal.ofReal_pos.mpr
    have : u_sf x₀ < u_sf (x₀ + 1) := by
      -- u_sf = stieltjesFunction = rightLim. For c < d with c = x₀, d = x₀+1:
      -- rightLim u x₀ ≤ u(x₀+½) < u(x₀+1) ≤ rightLim u (x₀+1)
      have h_mid := hu (show x₀ + 1 / 2 < x₀ + 1 by linarith)
      calc u_sf x₀ = hu.monotone.stieltjesFunction x₀ := rfl
        _ ≤ u (x₀ + 1 / 2) := Monotone.rightLim_le hu.monotone (by linarith)
        _ < u (x₀ + 1) := h_mid
        _ ≤ hu.monotone.stieltjesFunction (x₀ + 1) := Monotone.le_rightLim hu.monotone le_rfl
        _ = u_sf (x₀ + 1) := rfl
    linarith
  -- The CDF difference is ≥ 0 and strictly positive near x₀.
  -- ∫_{Ioc x₀ (x₀+1)} (G_sf - F_sf) dμ_u > 0
  have h_local_pos : 0 < ∫ y in Ioc x₀ (x₀ + 1), G_sf y - F_sf y ∂μ_u := by
    have h_nn : ∀ y, 0 ≤ G_sf y - F_sf y :=
      fun y => sub_nonneg.mpr (stieltjes_fosd h_fosd y)
    have h_cdf_intOn : ∀ (d : ContDist),
        IntegrableOn (⇑(stieltjes d.cdf.mono)) (Ioc x₀ (x₀ + 1)) μ_u :=
      fun d => cdf_integrableOn_Ioc d hu.monotone _ _
    -- Right-continuity of G_sf - F_sf at x₀ gives positivity on (x₀, x₀+ε)
    have hrc : ContinuousWithinAt (fun y => G_sf y - F_sf y) (Ici x₀) x₀ :=
      (G_sf.right_continuous x₀).sub (F_sf.right_continuous x₀)
    rw [Metric.continuousWithinAt_iff] at hrc
    obtain ⟨δ, hδ_pos, hδ⟩ := hrc _ (sub_pos.mpr h_gap)
    set ε := min (δ / 2) (1 / 2) with hε_def
    have hε_pos : 0 < ε := lt_min (by linarith) (by linarith)
    -- Positivity on the sub-interval
    have h_pos_on : ∀ y ∈ Ioc x₀ (x₀ + ε), 0 < G_sf y - F_sf y := by
      intro y hy
      have hy_mem : y ∈ Ici x₀ := le_of_lt hy.1
      have hy_dist : dist y x₀ < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hy.1])]
        calc y - x₀ ≤ ε := by linarith [hy.2]
          _ ≤ δ / 2 := min_le_left _ _
          _ < δ := by linarith
      have h_close := hδ hy_mem hy_dist
      rw [Real.dist_eq] at h_close
      linarith [(abs_lt.mp h_close).1]
    -- μ_u(Ioc x₀ (x₀+ε)) > 0
    have h_mu_ε : 0 < μ_u (Ioc x₀ (x₀ + ε)) := by
      rw [show μ_u = u_sf.measure from rfl, StieltjesFunction.measure_Ioc]
      exact ENNReal.ofReal_pos.mpr (by
        have : u_sf x₀ < u_sf (x₀ + ε) :=
          calc u_sf x₀ ≤ u (x₀ + ε / 2) :=
                Monotone.rightLim_le hu.monotone (by linarith)
            _ < u (x₀ + ε) := hu (by linarith)
            _ ≤ u_sf (x₀ + ε) := Monotone.le_rightLim hu.monotone le_rfl
        linarith)
    refine (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ h_nn) ((h_cdf_intOn dG).sub (h_cdf_intOn dF))).mpr ?_
    calc (0 : ℝ≥0∞) < μ_u (Ioc x₀ (x₀ + ε)) := h_mu_ε
      _ ≤ μ_u (Function.support (fun y => G_sf y - F_sf y) ∩ Ioc x₀ (x₀ + 1)) :=
          measure_mono (fun y hy =>
            ⟨ne_of_gt (h_pos_on y hy),
             Ioc_subset_Ioc_right (by linarith [min_le_right (δ/2) (1/2 : ℝ)]) hy⟩)
  -- Contradiction: the expanding-interval CDF integral → E_F - E_G = 0 (if equality held), yet it
  -- is eventually ≥ the strictly positive local piece on Ioc x₀ (x₀+1).
  exact lt_of_le_of_ne h_weak (fun h_eq => by
    have h_cdf_lim : Tendsto (fun n : ℕ =>
        ∫ y in Ioc (-(↑n : ℝ)) ↑n, G_sf y ∂μ_u -
        ∫ y in Ioc (-(↑n : ℝ)) ↑n, F_sf y ∂μ_u) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = dF.expect u - dG.expect u from by rw [h_eq]; ring]
      exact cdf_integral_diff_tendsto dF dG hu.monotone h_intF h_intG
    -- For large n, Ioc x₀ (x₀+1) ⊆ Ioc (-n) n, so the CDF integral dominates the local piece
    have h_ev_ge : ∀ᶠ n : ℕ in atTop,
        (∫ y in Ioc x₀ (x₀ + 1), G_sf y - F_sf y ∂μ_u) ≤
        (∫ y in Ioc (-(↑n : ℝ)) ↑n, G_sf y ∂μ_u - ∫ y in Ioc (-(↑n : ℝ)) ↑n, F_sf y ∂μ_u) := by
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, Ioc x₀ (x₀ + 1) ⊆ Ioc (-(↑n : ℝ)) ↑n := by
        obtain ⟨N, hN⟩ := exists_nat_gt (max (|x₀|) (|x₀ + 1|))
        exact ⟨N, fun n hn y hy => ⟨by
          calc -(↑n : ℝ) ≤ -(↑N : ℝ) := neg_le_neg (Nat.cast_le.mpr hn)
            _ < -|x₀| := by linarith [le_max_left (|x₀|) (|x₀ + 1|)]
            _ ≤ x₀ := neg_abs_le x₀
            _ < y := hy.1,
          le_of_lt (calc y ≤ x₀ + 1 := hy.2
            _ ≤ |x₀ + 1| := le_abs_self _
            _ < ↑N := by linarith [le_max_right (|x₀|) (|x₀ + 1|)]
            _ ≤ ↑n := Nat.cast_le.mpr hn)⟩⟩
      filter_upwards [eventually_ge_atTop N] with n hn
      rw [← integral_sub (cdf_integrableOn_Ioc dG hu.monotone _ _)
        (cdf_integrableOn_Ioc dF hu.monotone _ _)]
      exact setIntegral_mono_set
        ((cdf_integrableOn_Ioc dG hu.monotone _ _).sub (cdf_integrableOn_Ioc dF hu.monotone _ _))
        (ae_of_all _ (fun y => sub_nonneg.mpr (stieltjes_fosd h_fosd y)))
        (ae_of_all _ (fun y hy => hN n hn hy))
    linarith [ge_of_tendsto h_cdf_lim h_ev_ge])

/-- **First-order dominance characterized by monotone expectations.** First-order stochastic
dominance of `dF` over `dG` holds exactly when every monotone payoff with `density · u` integrable
against both distributions is weakly preferred, `E_G[u] ≤ E_F[u]`. The reverse direction recovers
CDF dominance from the upper-tail indicators `1_{(x,∞)}` (Hadar and Russell 1969). -/
lemma iff_expect_mono (dF dG : ContDist) :
    IntegratedCDFTower 1 dF.cdf dG.cdf ↔
    (∀ u : ℝ → ℝ, Monotone u →
     Integrable (fun x => dF.density x * u x) →
     Integrable (fun x => dG.density x * u x) →
     dG.expect u ≤ dF.expect u) := by
  constructor
  · -- Forward: FOSD → monotone expectations ordered. Already proved.
    exact fun h u hu hintF hintG => expect_mono dF dG u hu h hintF hintG
  · -- Reverse: instantiate with u = 1_{(x,∞)} to recover FOSD pointwise.
    intro h x
    -- `density * 1_{Ioi x} = 1_{Ioi x} ∘ density`, shared by expectation and integrability
    have h_dens_eq : ∀ (d : ContDist),
        (fun t => d.density t * Set.indicator (Ioi x) (fun _ => (1 : ℝ)) t) =
          Set.indicator (Ioi x) d.density :=
      fun d => funext fun t => by simp [Set.indicator_apply]
    -- E_d[1_{Ioi x}] = 1 - d.cdf x for any ContDist d
    have expect_indicator : ∀ (d : ContDist),
        d.expect (Set.indicator (Ioi x) (fun _ => (1 : ℝ))) = 1 - d.cdf x := by
      intro d; simp only [ContDist.expect]
      rw [h_dens_eq, integral_indicator measurableSet_Ioi]
      have h_compl := integral_add_compl (s := Iic x) measurableSet_Iic d.integrable
      rw [compl_Iic] at h_compl
      linarith [d.integral_one, ContDist.cdf_eq_integral d x]
    -- The indicator is monotone (0 below x, 1 above x)
    have hu : Monotone (Set.indicator (Ioi x) (fun _ => (1 : ℝ))) := by
      intro t₁ t₂ ht; simp only [Set.indicator_apply, mem_Ioi]; split_ifs <;> linarith
    -- The indicator times density is integrable (bounded by density)
    have hint : ∀ (d : ContDist),
        Integrable (fun t => d.density t * Set.indicator (Ioi x) (fun _ => (1 : ℝ)) t) := by
      intro d
      rw [h_dens_eq]; exact d.integrable.integrableOn.integrable_indicator measurableSet_Ioi
    -- E_G[u] ≤ E_F[u] gives 1 - G(x) ≤ 1 - F(x), hence F(x) ≤ G(x)
    have h_cdf : dF.cdf x ≤ dG.cdf x := by
      have h_expect := h _ hu (hint dF) (hint dG)
      rw [expect_indicator dG, expect_indicator dF] at h_expect
      linarith
    simpa using h_cdf

end FOSD

end Econlib.Probability
