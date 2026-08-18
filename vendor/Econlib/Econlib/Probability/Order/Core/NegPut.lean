/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Order.Core.IntegratedCDF

/-!
# The negative put-option test function

The negative put payoff `negPut x t = min(0, t - x)` is the reverse-direction test function for
SOSD-style characterizations: `E_d[negPut x]` equals `-∫_{Iic x} F(s) ds`, giving a direct bridge
between expectation monotonicity and integrated-CDF dominance without Stieltjes measures. The
contents are order-agnostic — the same test function probes any second-order characterization.

## Main definitions

* `negPut` — the negative put-option payoff `t ↦ min(0, t - x)`.

## Main statements

* `negPut_monotone`, `negPut_concave` — shape lemmas for the payoff.
* `integrable_negPut` — integrability against a density with a finite first moment.
* `expect_negPut_eq_neg_integral_cdf` — the reduction `E_d[negPut x] = -∫_{Iic x} F`.

## Tags

negative put, test function, integrated cdf, second-order stochastic dominance
-/

@[expose] public section

open MeasureTheory Set BigOperators Function Filter
open scoped Topology ENNReal Real

namespace Econlib.Probability

open Econlib

/-- The negative put-option test function. -/
noncomputable def negPut (x : ℝ) : ℝ → ℝ := fun t => min 0 (t - x)

/-- The negative put payoff is concave: It is the infimum of `0` and the affine `t - x`. -/
lemma negPut_concave (x : ℝ) : ConcaveOn ℝ univ (negPut x) := by
  have h0 : ConcaveOn ℝ univ (fun _ : ℝ => (0 : ℝ)) := concaveOn_const 0 convex_univ
  -- `t - x` is affine, hence concave: difference of the identity and a constant
  have h1 : ConcaveOn ℝ univ (fun t : ℝ => t - x) :=
    (concaveOn_id convex_univ).sub (convexOn_const x convex_univ)
  have h_inf := h0.inf h1
  exact h_inf.congr (fun t _ => by simp [negPut, Pi.inf_apply, min_comm])

/-- The negative put payoff is monotone. -/
lemma negPut_monotone (x : ℝ) : Monotone (negPut x) := by
  intro t₁ t₂ ht
  simp only [negPut]
  exact min_le_min le_rfl (sub_le_sub_right ht x)

/-- Finite first moments guarantee the put payoff is integrable against any density. -/
lemma integrable_negPut (d : ContDist) (x : ℝ)
    (h_mean : Integrable (fun t => d.density t * t)) :
    Integrable (fun t => d.density t * negPut x t) := by
  have h_dom : Integrable (fun t => d.density t * (t - x)) := by
    have h_eq : (fun t => d.density t * (t - x)) =
        (fun t => d.density t * t) - (fun t => d.density t * x) := by
      ext t; simp [mul_sub]
    rw [h_eq]; exact h_mean.sub (d.integrable.mul_const x)
  apply h_dom.mono
  · exact d.integrable.aestronglyMeasurable.mul
      ((continuous_const.min (continuous_id.sub continuous_const)).aestronglyMeasurable)
  · apply ae_of_all; intro t
    simp only [Real.norm_eq_abs, abs_mul, negPut]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    -- `|min 0 (t-x)| ≤ max |0| |t-x| = |t-x|`
    exact abs_min_le_max_abs_abs.trans (by simp)

/-- Auxiliary: On `Iic x`, `negPut x t = t - x`. -/
lemma negPut_of_le {x t : ℝ} (ht : t ≤ x) : negPut x t = t - x := by
  simp only [negPut, min_eq_right (sub_nonpos.mpr ht)]

/-- Auxiliary: On `Ioi x`, `negPut x t = 0`. -/
lemma negPut_of_gt {x t : ℝ} (ht : x < t) : negPut x t = 0 := by
  simp only [negPut, min_eq_left (le_of_lt (sub_pos.mpr ht))]

/-- Tonelli reduction: `E[min(0, t - x)] = -∫_{s ≤ x} F(s) ds`. Proved via splitting the integral
and applying the IBP identity for the integrated CDF. -/
lemma expect_negPut_eq_neg_integral_cdf (d : ContDist) (x : ℝ)
    (h_mean : Integrable (fun t => d.density t * t)) :
    d.expect (negPut x) = - ∫ s in Iic x, d.cdf s := by
  have h_int_negPut := integrable_negPut d x h_mean
  have h_Ioi_zero : ∫ t in Ioi x, d.density t * negPut x t = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun t ht =>
      by rw [negPut_of_gt (mem_Ioi.mp ht), mul_zero]
  have h_Iic : ∫ t in Iic x, d.density t * negPut x t =
      ∫ t in Iic x, d.density t * (t - x) :=
    setIntegral_congr_fun measurableSet_Iic fun t ht =>
      by rw [negPut_of_le ht]
  have h_split_lin : ∫ t in Iic x, d.density t * (t - x) =
      (∫ t in Iic x, d.density t * t) - x * d.cdf x := by
    simp_rw [mul_sub]
    rw [integral_sub h_mean.integrableOn (d.integrable.mul_const x).integrableOn]
    have h_const : ∫ t in Iic x, d.density t * x = x * d.cdf x := by
      rw [integral_mul_const, ContDist.cdf_eq_integral, mul_comm]
    linarith
  have h_ibp := integral_cdf_Iic_eq d x h_mean
  have h1 : d.expect (negPut x) =
      (∫ t in Iic x, d.density t * negPut x t) +
      ∫ t in Ioi x, d.density t * negPut x t := by
    change ∫ t, d.density t * negPut x t =
      (∫ t in Iic x, d.density t * negPut x t) + ∫ t in Ioi x, d.density t * negPut x t
    rw [← compl_Iic]
    exact (integral_add_compl measurableSet_Iic h_int_negPut).symm
  simp only [h1, h_Ioi_zero, add_zero, h_Iic, h_split_lin, h_ibp]; ring

end Econlib.Probability
