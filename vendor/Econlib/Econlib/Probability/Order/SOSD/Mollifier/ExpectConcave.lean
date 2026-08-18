/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Order.SOSD.Mollifier.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Mollifier bridge for the SOSD expectation ordering

Second-order stochastic dominance of `dF` over `dG`, together with a monotone concave test function
`u` of linear growth, forces the expectation ordering `E_G[u] ≤ E_F[u]`. The merely continuous test
function is regularized by convolving against a `ContDiffBump` sequence, the smooth case
`sosd_smooth_step` is applied to each mollified function, and the dominated convergence theorem
passes the inequality to the limit.

## Main statements

* `sosd_expect_concave_mono_general` — second-order stochastic dominance implies `E_G[u] ≤ E_F[u]`
  for any monotone concave `u` of linear growth.

## Notes

The linear-growth hypothesis `∀ x, |u x| ≤ C·(1 + |x|)` is not automatic for monotone concave
functions on `ℝ` (e.g. `x ↦ -x²/4` for `x ≤ 0`, `0` for `x ≥ 0` is monotone concave but quadratic),
and it supplies the dominating function `density·C(1 + |x|)` for the limit passage. It covers
bounded, affine, and sublinear concave utilities, but excludes `Real.log` and CRRA, which are
superlinear in `|·|` as `x ↓ 0` and not real-valued on all of `ℝ`. Those utilities are recovered
under a positive bounded support hypothesis in `Order/SOSD/PositiveSupport.lean`.

## Tags

second-order stochastic dominance, concave, expectation ordering, mollifier, dominated convergence
-/

@[expose] public section

open MeasureTheory Set Filter Function
open scoped Topology ENNReal Real Convolution

namespace Econlib.Probability

variable {dF dG : ContDist}

/-- The mollifier bridge: If `dF` second-order stochastically dominates `dG` and `u` is a monotone
concave test function of linear growth, then `dG.expect u ≤ dF.expect u`. -/
theorem sosd_expect_concave_mono_general
    (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (u : ℝ → ℝ) (hu_conc : ConcaveOn ℝ univ u) (hu_mono : Monotone u)
    (h_linear : ∃ C : ℝ, 0 < C ∧ ∀ x, |u x| ≤ C * (1 + |x|))
    (_h_intF : Integrable (fun x => dF.density x * u x))
    (_h_intG : Integrable (fun x => dG.density x * u x))
    (h_meanF : Integrable (fun x => dF.density x * |x|))
    (h_meanG : Integrable (fun x => dG.density x * |x|)) :
    dG.expect u ≤ dF.expect u := by
  -- Step 1: u is continuous (concave on ℝ ⟹ locally Lipschitz ⟹ continuous)
  have hu_cont : Continuous u := hu_conc.locallyLipschitz.continuous
  have hu_loc : LocallyIntegrable u := hu_cont.locallyIntegrable
  obtain ⟨Cb, hCb, h_bound⟩ := h_linear
  -- Step 2: Construct mollifier sequence φ_n with rOut = 1/(n+2) → 0
  let φ : ℕ → ContDiffBump (0 : ℝ) := fun n => {
    rIn := 1 / (2 * (↑n + 2))
    rOut := 1 / (↑n + 2)
    rIn_pos := by positivity
    rIn_lt_rOut := by
      have hpos : (0 : ℝ) < ↑n + 2 := by positivity
      rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (↑n + 2)) hpos]
      nlinarith
  }
  let ψ : ℕ → ℝ → ℝ := fun n => (φ n).normed volume
  let u_n : ℕ → ℝ → ℝ := fun n =>
    ψ n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u
  -- Step 3: rOut → 0
  have h_rOut_tendsto : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    -- (φ n).rOut = 1/(n+2) → 0 as n → ∞
    simpa using tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
  -- Step 4: Pointwise convergence u_n(x) → u(x)
  have h_ptwise : ∀ (x : ℝ), Tendsto (fun n => u_n n x) atTop (𝓝 (u x)) := by
    intro x
    exact ContDiffBump.convolution_tendsto_right_of_continuous h_rOut_tendsto hu_cont x
  -- Step 5: Properties of each u_n
  -- Each u_n is C^∞ in the ℕ∞ sense (ContDiff ℝ (↑(⊤ : ℕ∞))), hence continuous
  have h_un_cont : ∀ (n : ℕ), Continuous (u_n n) := by
    intro n
    have h_cs := (φ n).hasCompactSupport_normed (μ := volume)
    have h_cd := (φ n).contDiff_normed (μ := volume) (n := ⊤)
    exact (HasCompactSupport.contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) h_cs h_cd hu_loc).continuous
  have h_un_mono : ∀ (n : ℕ), Monotone (u_n n) := by
    intro n
    exact convolution_monotone ((φ n).nonneg_normed) hu_mono
      ((φ n).hasCompactSupport_normed) ((φ n).contDiff_normed (n := 0).continuous) hu_cont
  have h_un_conc : ∀ (n : ℕ), ConcaveOn ℝ univ (u_n n) := by
    intro n
    exact convolution_concaveOn ((φ n).nonneg_normed) hu_conc
      ((φ n).hasCompactSupport_normed) ((φ n).contDiff_normed (n := 0).continuous) hu_cont
  -- Step 6: Uniform bound |u_n(x)| ≤ 2*Cb*(1+|x|) via mollify_uniform_bound
  have h_un_bound : ∀ (n : ℕ) (x : ℝ), |u_n n x| ≤ 2 * Cb * (1 + |x|) := by
    intro n
    apply mollify_uniform_bound u Cb hCb h_bound (ψ n) ((φ n).nonneg_normed) ((φ n).integral_normed)
    -- support (ψ n) ⊆ closedBall 0 1; support = ball 0 rOut, rOut = 1/(n+2) ≤ 1
    intro x hx
    rw [ContDiffBump.support_normed_eq] at hx
    -- hx : x ∈ ball 0 (1/(n+2)), need x ∈ closedBall 0 1
    have h_rOut_le : (φ n).rOut ≤ 1 := by
      simpa using div_le_one_of_le₀
        (by linarith [show (0 : ℝ) ≤ ↑n from Nat.cast_nonneg n])
        (by positivity)
    exact Metric.closedBall_subset_closedBall h_rOut_le (Metric.ball_subset_closedBall hx)
  -- Step 7/8 shared infrastructure: dominator integrability and dominator bounds
  -- (defined here so h_step can use them for each u_n, and DCT uses them globally)
  have h_dom_intG : Integrable (fun x => 2 * Cb * (dG.density x * (1 + |x|))) := by
    have h12 : Integrable (fun x => dG.density x * (1 + |x|)) := by
      simpa [mul_add, mul_one] using dG.integrable.add h_meanG
    exact h12.const_mul _
  have h_dom_intF : Integrable (fun x => 2 * Cb * (dF.density x * (1 + |x|))) := by
    have h12 : Integrable (fun x => dF.density x * (1 + |x|)) := by
      simpa [mul_add, mul_one] using dF.integrable.add h_meanF
    exact h12.const_mul _
  have h_meas_G : ∀ (n : ℕ),
      AEStronglyMeasurable (fun x => dG.density x * u_n n x) volume := by
    intro n
    exact dG.integrable.aestronglyMeasurable.mul
      (h_un_cont n).aestronglyMeasurable
  have h_meas_F : ∀ (n : ℕ),
      AEStronglyMeasurable (fun x => dF.density x * u_n n x) volume := by
    intro n
    exact dF.integrable.aestronglyMeasurable.mul
      (h_un_cont n).aestronglyMeasurable
  have h_dom_G : ∀ (n : ℕ), ∀ᵐ x ∂volume,
      ‖dG.density x * u_n n x‖ ≤ 2 * Cb * (dG.density x * (1 + |x|)) := by
    intro n; apply ae_of_all; intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dG.nonneg x)]
    calc dG.density x * |u_n n x|
        ≤ dG.density x * (2 * Cb * (1 + |x|)) :=
          mul_le_mul_of_nonneg_left (h_un_bound n x) (dG.nonneg x)
      _ = 2 * Cb * (dG.density x * (1 + |x|)) := by ring
  have h_dom_F : ∀ (n : ℕ), ∀ᵐ x ∂volume,
      ‖dF.density x * u_n n x‖ ≤ 2 * Cb * (dF.density x * (1 + |x|)) := by
    intro n; apply ae_of_all; intro x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (dF.nonneg x)]
    calc dF.density x * |u_n n x|
        ≤ dF.density x * (2 * Cb * (1 + |x|)) :=
          mul_le_mul_of_nonneg_left (h_un_bound n x) (dF.nonneg x)
      _ = 2 * Cb * (dF.density x * (1 + |x|)) := by ring
  -- Step 7: The C² theorem applied to each u_n
  -- Each u_n is C^∞ hence C², monotone, concave, with linear growth → E_G[u_n] ≤ E_F[u_n]
  -- This requires extracting derivatives from ContDiff, verifying all IBP hypotheses
  -- (boundary decay, Stieltjes integrability, CDF integrability on Iic x, etc.)
  have h_step : ∀ (n : ℕ), dG.expect (u_n n) ≤ dF.expect (u_n n) := by
    intro n
    -- u_n n is C^∞ (hence C²), monotone, concave, with linear growth
    have h_cd2 : ContDiff ℝ 2 (u_n n) :=
      (HasCompactSupport.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
        ((φ n).hasCompactSupport_normed) ((φ n).contDiff_normed (n := 2)) hu_loc)
    -- Integrability of density * u_n (dominated by 2Cb * density * (1+|x|))
    have h_intF_n : Integrable (fun x => dF.density x * u_n n x) :=
      Integrable.mono' h_dom_intF (h_meas_F n) (h_dom_F n)
    have h_intG_n : Integrable (fun x => dG.density x * u_n n x) :=
      Integrable.mono' h_dom_intG (h_meas_G n) (h_dom_G n)
    exact sosd_smooth_step h_sosd (u_n n) h_cd2 (h_un_mono n) (h_un_conc n)
      (2 * Cb) (by positivity) (h_un_bound n) h_intF_n h_intG_n h_meanF h_meanG
  -- Step 8: DCT to pass from u_n to u
  -- E_d[u_n] = ∫ d.density * u_n → ∫ d.density * u = E_d[u]
  -- Dominator: 2 * Cb * density(x) * (1 + |x|), integrable from density + density * |x|
  change ∫ x, dG.density x * u x ≤ ∫ x, dF.density x * u x
  have h_lim_G : ∀ᵐ x ∂volume,
      Tendsto (fun n => dG.density x * u_n n x) atTop (𝓝 (dG.density x * u x)) :=
    ae_of_all _ (fun x => tendsto_const_nhds.mul (h_ptwise x))
  have h_lim_F : ∀ᵐ x ∂volume,
      Tendsto (fun n => dF.density x * u_n n x) atTop (𝓝 (dF.density x * u x)) :=
    ae_of_all _ (fun x => tendsto_const_nhds.mul (h_ptwise x))
  -- DCT: ∫ density * u_n → ∫ density * u
  have h_tendsto_G := tendsto_integral_of_dominated_convergence
    (fun x => 2 * Cb * (dG.density x * (1 + |x|)))
    h_meas_G h_dom_intG h_dom_G h_lim_G
  have h_tendsto_F := tendsto_integral_of_dominated_convergence
    (fun x => 2 * Cb * (dF.density x * (1 + |x|)))
    h_meas_F h_dom_intF h_dom_F h_lim_F
  -- Step 9: Pass inequality to limit
  -- h_step gives ∫ dG.density * u_n n ≤ ∫ dF.density * u_n n (after unfolding expect)
  -- DCT gives convergence; le_of_tendsto_of_tendsto' closes it
  exact le_of_tendsto_of_tendsto' h_tendsto_G h_tendsto_F
    (fun n => h_step n)

end Econlib.Probability
