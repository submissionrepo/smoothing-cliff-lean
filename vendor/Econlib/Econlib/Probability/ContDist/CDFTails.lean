/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.IntegralTails
public import Econlib.Probability.ContDist.CDFStieltjes

/-!
# CDF-typed tail decay lemmas

CDF-typed corollaries of the generic integrable-function tail decay
(`Econlib.Math.MeasureTheory.IntegralTails`), specialized to a `ContDist`'s CDF and the boundary
products that appear in integration-by-parts arguments at `±∞`.

## Main statements

* `cdf_times_a_tendsto_zero_left` — `F(-n)·(-n) → 0` from a finite first moment.
* `one_sub_cdf_times_u_tendsto_zero`, `cdf_times_u_tendsto_zero_left` — per-CDF boundary products
  `(1-F(n))·u(n)`, `F(-n)·u(-n)` vanish under monotone integrable `u`.
* `cdf_boundary_diff_tendsto_zero` — the `(G-F)·u` boundary terms used in the integration-by-parts
  step vanish.

## Tags

continuous distribution, CDF, tail decay, integration by parts boundary
-/

@[expose] public section

open MeasureTheory Set BigOperators Function Filter
open scoped Topology ENNReal Real

namespace Econlib.Probability

open Monotone

/-- `F(-n) * (-n) → 0` as `n → ∞` from a finite first moment. -/
lemma cdf_times_a_tendsto_zero_left (d : ContDist)
    (h_mean : Integrable (fun t => d.density t * t)) :
    Tendsto (fun n : ℕ => d.cdf (-(↑n : ℝ)) * (-(↑n : ℝ))) atTop (𝓝 0) := by
  have h_nF_tendsto : Tendsto (fun n : ℕ => (↑n : ℝ) * d.cdf (-(↑n : ℝ))) atTop (𝓝 0) := by
    set g := fun n : ℕ => ∫ x in Iic (-(↑n : ℝ)), d.density x * |x|
    apply squeeze_zero (g := g)
    · intro n; exact mul_nonneg (Nat.cast_nonneg n) (d.cdf_nonneg _)
    · intro n
      rw [ContDist.cdf_eq_integral]
      have h_intOn_ndens : IntegrableOn (fun t => d.density t * (↑n : ℝ)) (Iic (-(↑n : ℝ))) :=
        (d.integrable.mul_const _).integrableOn
      have h_intOn_dabs : IntegrableOn (fun t => d.density t * |t|) (Iic (-(↑n : ℝ))) :=
        (h_mean.norm.congr (ae_of_all _ fun t => by
          simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (d.nonneg t)])).integrableOn
      calc (↑n : ℝ) * ∫ t in Iic (-(↑n : ℝ)), d.density t
            = ∫ t in Iic (-(↑n : ℝ)), d.density t * (↑n : ℝ) := by
              rw [mul_comm, integral_mul_const]
        _ ≤ ∫ t in Iic (-(↑n : ℝ)), d.density t * |t| := by
              apply setIntegral_mono_on h_intOn_ndens h_intOn_dabs measurableSet_Iic
              intro t (ht : t ≤ -(↑n : ℝ))
              apply mul_le_mul_of_nonneg_left _ (d.nonneg t)
              rw [abs_of_nonpos (by linarith : t ≤ 0)]; linarith
    · show Tendsto g atTop (𝓝 0)
      have h_eq : g = fun n : ℕ => ∫ x in Iic (-(↑n : ℝ)), ‖d.density x * x‖ := by
        ext n; exact setIntegral_congr_fun measurableSet_Iic fun t _ => by
          simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (d.nonneg t)]
      rw [h_eq]
      exact tail_Iic_tendsto_zero _ h_mean.norm
  have h_eq : (fun n : ℕ => d.cdf (-(↑n : ℝ)) * (-(↑n : ℝ))) =
      (fun n : ℕ => -((↑n : ℝ) * d.cdf (-(↑n : ℝ)))) := by
    ext n; ring
  rw [h_eq, show (0 : ℝ) = -0 from neg_zero.symm]
  exact h_nF_tendsto.neg

/-- Per-CDF tail product at `+∞`: `(1 - F(n)) * u_sf(n) → 0` for monotone `u` with `∫ density * u`
integrable. -/
lemma one_sub_cdf_times_u_tendsto_zero
    (d : ContDist) (u : ℝ → ℝ) (hu : Monotone u)
    (h_int : Integrable (fun x => d.density x * u x)) :
    Tendsto (fun n : ℕ => (1 - (stieltjes d.cdf.mono) ↑n) * (stieltjes hu) ↑n) atTop (𝓝 0) := by
  set F_sf := stieltjes d.cdf.mono
  set u_sf := stieltjes hu
  have hF_eq : ∀ x, F_sf x = d.cdf x :=
    stieltjes_eq_of_rightCts d.cdf.mono d.cdf.right_continuous
  have h_one_sub_cdf : ∀ n : ℕ, 1 - F_sf ↑n = ∫ x in Ioi (↑n : ℝ), d.density x := by
    intro n; rw [hF_eq, ContDist.cdf_eq_integral]
    have := integral_add_compl (s := Iic (↑n : ℝ)) measurableSet_Iic d.integrable
    rw [compl_Iic, d.integral_one] at this; linarith
  have h_one_sub_nonneg : ∀ n : ℕ, 0 ≤ 1 - F_sf ↑n := by
    intro n; rw [hF_eq]; linarith [d.cdf_le_one ↑n]
  have h_one_sub : Tendsto (fun n : ℕ => 1 - F_sf ↑n) atTop (𝓝 0) := by
    rw [show (0 : ℝ) = 1 - 1 from (sub_self 1).symm]
    exact tendsto_const_nhds.sub
      ((d.cdf.tendsto_top.comp tendsto_natCast_atTop_atTop).congr (fun n => (hF_eq _).symm))
  have h_usf_le_u : ∀ x y : ℝ, x < y → u_sf x ≤ u y := by
    intro x y hxy; change hu.stieltjesFunction x ≤ u y
    rw [Monotone.stieltjesFunction_eq]; exact hu.rightLim_le hxy
  by_cases h_bdd : BddAbove (range u)
  · obtain ⟨M, hM⟩ := h_bdd
    have h_usf_bdd : ∀ x, u_sf x ≤ M := by
      intro x; obtain ⟨y, hy⟩ := exists_gt x
      exact le_trans (h_usf_le_u x y hy) (hM (mem_range_self y))
    have h_u_conv := tendsto_atTop_ciSup
      (show Monotone (fun n : ℕ => u_sf (↑n : ℝ)) from fun _ _ h => u_sf.mono (Nat.cast_le.mpr h))
      ⟨M, fun _ ⟨n, hn⟩ => hn ▸ h_usf_bdd _⟩
    rw [show (0 : ℝ) = 0 * ⨆ n : ℕ, u_sf (↑n : ℝ) from (zero_mul _).symm]
    exact h_one_sub.mul h_u_conv
  · have h_unbdd : ∀ M : ℝ, ∃ x, M < u x := by
      intro M; by_contra h; push Not at h
      exact h_bdd ⟨M, fun _ ⟨y, hy⟩ => hy ▸ h y⟩
    have h_usf_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ u_sf ↑n := by
      obtain ⟨x, hx⟩ := h_unbdd 0
      obtain ⟨N, hN⟩ := exists_nat_gt x
      filter_upwards [eventually_ge_atTop N] with n hn
      calc (0 : ℝ) ≤ u x := le_of_lt hx
        _ ≤ u_sf x := by change u x ≤ hu.stieltjesFunction x
                         rw [Monotone.stieltjesFunction_eq]; exact hu.le_rightLim le_rfl
        _ ≤ u_sf ↑n := u_sf.mono (by exact_mod_cast le_trans (le_of_lt hN) (Nat.cast_le.mpr hn))
    have h_markov : ∀ n : ℕ,
        (1 - F_sf ↑n) * u_sf ↑n ≤ ∫ x in Ioi (↑n : ℝ), d.density x * u x := by
      intro n; rw [h_one_sub_cdf]
      rw [(integral_mul_const (u_sf ↑n) _).symm]
      exact setIntegral_mono_on (d.integrable.mul_const _).integrableOn
        h_int.integrableOn measurableSet_Ioi fun t (ht : (↑n : ℝ) < t) =>
        mul_le_mul_of_nonneg_left (h_usf_le_u ↑n t ht) (d.nonneg t)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tail_Ioi_tendsto_zero _ h_int)
      (h_usf_nonneg.mono fun n h_nn => mul_nonneg (h_one_sub_nonneg n) h_nn)
      (Eventually.of_forall h_markov)

/-- Per-CDF tail product at `-∞`: `F(-n) * u_sf(-n) → 0` for monotone `u` with `∫ density * u`
integrable. -/
lemma cdf_times_u_tendsto_zero_left
    (d : ContDist) (u : ℝ → ℝ) (hu : Monotone u)
    (h_int : Integrable (fun x => d.density x * u x)) :
    Tendsto (fun n : ℕ => (stieltjes d.cdf.mono) (-(↑n : ℝ)) * (stieltjes hu) (-(↑n : ℝ)))
      atTop (𝓝 0) := by
  set F_sf := stieltjes d.cdf.mono
  set u_sf := stieltjes hu
  have hF_eq : ∀ x, F_sf x = d.cdf x :=
    stieltjes_eq_of_rightCts d.cdf.mono d.cdf.right_continuous
  have h_cdf_eq : ∀ n : ℕ, F_sf (-(↑n : ℝ)) = ∫ x in Iic (-(↑n : ℝ)), d.density x := by
    intro n; rw [hF_eq, ContDist.cdf_eq_integral]
  have h_cdf_nonneg : ∀ n : ℕ, 0 ≤ F_sf (-(↑n : ℝ)) := by
    intro n; rw [hF_eq]; exact d.cdf_nonneg _
  have h_F_zero : Tendsto (fun n : ℕ => F_sf (-(↑n : ℝ))) atTop (𝓝 0) :=
    (d.cdf.tendsto_bot.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)).congr
      (fun n => (hF_eq _).symm)
  have h_u_le_usf : ∀ x, u x ≤ u_sf x := by
    intro x; change u x ≤ hu.stieltjesFunction x
    rw [Monotone.stieltjesFunction_eq]; exact hu.le_rightLim le_rfl
  have h_usf_le_u : ∀ x y : ℝ, x < y → u_sf x ≤ u y := by
    intro x y hxy; change hu.stieltjesFunction x ≤ u y
    rw [Monotone.stieltjesFunction_eq]; exact hu.rightLim_le hxy
  by_cases h_bdd : BddBelow (range u)
  · obtain ⟨m, hm⟩ := h_bdd
    have h_usf_lo : ∀ x, m ≤ u_sf x :=
      fun x => le_trans (hm (mem_range_self x)) (h_u_le_usf x)
    have h_u_conv := tendsto_atTop_ciInf
      (show Antitone (fun n : ℕ => u_sf (-(↑n : ℝ))) from
        fun _ _ h => u_sf.mono (neg_le_neg (Nat.cast_le.mpr h)))
      ⟨m, fun _ ⟨n, hn⟩ => hn ▸ h_usf_lo _⟩
    rw [show (0 : ℝ) = 0 * ⨅ n : ℕ, u_sf (-(↑n : ℝ)) from (zero_mul _).symm]
    exact h_F_zero.mul h_u_conv
  · have h_unbdd : ∀ m : ℝ, ∃ x, u x < m := by
      intro m; by_contra h; push Not at h
      exact h_bdd ⟨m, fun _ ⟨y, hy⟩ => hy ▸ h y⟩
    have h_usf_nonpos : ∀ᶠ n : ℕ in atTop, u_sf (-(↑n : ℝ)) ≤ 0 := by
      obtain ⟨x₀, hx₀⟩ := h_unbdd 0
      obtain ⟨N, hN⟩ := exists_nat_gt (-x₀)
      filter_upwards [eventually_ge_atTop N] with n hn
      calc u_sf (-(↑n : ℝ)) ≤ u x₀ :=
            h_usf_le_u _ _ (by linarith [show (↑N : ℝ) ≤ ↑n from Nat.cast_le.mpr hn])
        _ ≤ 0 := le_of_lt hx₀
    have h_markov : ∀ n : ℕ,
        ∫ x in Iic (-(↑n : ℝ)), d.density x * u x ≤ F_sf (-(↑n : ℝ)) * u_sf (-(↑n : ℝ)) := by
      intro n; rw [h_cdf_eq]
      calc ∫ x in Iic (-(↑n : ℝ)), d.density x * u x
            ≤ ∫ x in Iic (-(↑n : ℝ)), d.density x * u_sf (-(↑n : ℝ)) :=
              setIntegral_mono_on h_int.integrableOn
                (d.integrable.mul_const _).integrableOn measurableSet_Iic
                fun t (ht : t ≤ -(↑n : ℝ)) => mul_le_mul_of_nonneg_left
                  (le_trans (h_u_le_usf t) (u_sf.mono ht)) (d.nonneg t)
          _ = (∫ x in Iic (-(↑n : ℝ)), d.density x) * u_sf (-(↑n : ℝ)) :=
              integral_mul_const (u_sf (-(↑n : ℝ))) _
    have h_upper : ∀ᶠ n : ℕ in atTop, F_sf (-(↑n : ℝ)) * u_sf (-(↑n : ℝ)) ≤ 0 :=
      h_usf_nonpos.mono fun n hn => mul_nonpos_of_nonneg_of_nonpos (h_cdf_nonneg n) hn
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tail_Iic_tendsto_zero _ h_int) tendsto_const_nhds
      (Eventually.of_forall h_markov) h_upper

/-- **Tail estimate**: The boundary terms `(G(n)-F(n))*u(n)` vanish as `n → ∞`. -/
lemma cdf_boundary_diff_tendsto_zero
    (dF dG : ContDist) (u : ℝ → ℝ) (hu : Monotone u)
    (h_intF : Integrable (fun x => dF.density x * u x))
    (h_intG : Integrable (fun x => dG.density x * u x)) :
    Tendsto (fun n : ℕ =>
      ((stieltjes dG.cdf.mono) ↑n - (stieltjes dF.cdf.mono) ↑n) * (stieltjes hu) ↑n -
      ((stieltjes dG.cdf.mono) (-(↑n : ℝ)) - (stieltjes dF.cdf.mono) (-(↑n : ℝ))) *
        (stieltjes hu) (-(↑n : ℝ))) atTop (𝓝 0) := by
  set F_sf := stieltjes dF.cdf.mono
  set G_sf := stieltjes dG.cdf.mono
  set u_sf := stieltjes hu
  have h_rearrange : ∀ n : ℕ,
      (G_sf ↑n - F_sf ↑n) * u_sf ↑n -
      (G_sf (-(↑n : ℝ)) - F_sf (-(↑n : ℝ))) * u_sf (-(↑n : ℝ)) =
      ((1 - F_sf ↑n) * u_sf ↑n - (1 - G_sf ↑n) * u_sf ↑n) -
      (G_sf (-(↑n : ℝ)) * u_sf (-(↑n : ℝ)) - F_sf (-(↑n : ℝ)) * u_sf (-(↑n : ℝ))) := by
    intro n; ring
  simp_rw [h_rearrange]
  rw [show (0 : ℝ) = (0 - 0) - (0 - 0) from by ring]
  exact ((one_sub_cdf_times_u_tendsto_zero dF u hu h_intF).sub
    (one_sub_cdf_times_u_tendsto_zero dG u hu h_intG)).sub
    ((cdf_times_u_tendsto_zero_left dG u hu h_intG).sub
     (cdf_times_u_tendsto_zero_left dF u hu h_intF))

end Econlib.Probability
