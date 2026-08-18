/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrability of a derivative on a left-infinite ray from a limit at `-∞`

If a real function `g` has a nonnegative derivative `g'` on `(-∞, a)` and converges to a finite
limit at `-∞`, then `g'` is integrable on `(-∞, a]`. The total variation of `g` over the ray is the
finite quantity `g a - l`, giving an improper fundamental-theorem-of-calculus integrability
criterion.

## Main statements

* `MeasureTheory.integrableOn_Iic_deriv_of_nonneg` — integrability of `g'` on `(-∞, a]` assuming
  differentiability on `(-∞, a)` and continuity at `a⁻`.
* `MeasureTheory.integrableOn_Iic_deriv_of_nonneg'` — the same, assuming differentiability on the
  closed ray `(-∞, a]`.

## Tags

fundamental theorem of calculus, improper integral, integrability, derivative
-/

open MeasureTheory Filter Set Topology

namespace MeasureTheory

variable {E : Type*} {f f' : ℝ → E} {g g' : ℝ → ℝ} {a l : ℝ} {m : E} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- When a function has a limit at minus infinity, and its derivative is nonnegative, then the
derivative is automatically integrable on `(-∞, a)`. Version assuming differentiability on
`(-∞, a)` and continuity at `a⁻`. -/
public theorem integrableOn_Iic_deriv_of_nonneg (hcont : ContinuousWithinAt g (Iic a) a)
    (hderiv : ∀ x ∈ Iio a, HasDerivAt g (g' x) x) (g'pos : ∀ x ∈ Iio a, 0 ≤ g' x)
    (hg : Tendsto g atBot (𝓝 l)) : IntegrableOn g' (Iic a) := by
  have hcont : ContinuousOn g (Iic a) := by
    intro x hx
    rcases hx.out.eq_or_lt with rfl | hx
    · exact hcont
    · exact (hderiv x hx).continuousAt.continuousWithinAt
  -- `g'` is integrable on every `Ioc x a`: continuity + nonneg derivative on the interval.
  have h_intgr : ∀ x : ℝ, IntegrableOn g' (Ioc x a) volume := fun x =>
    intervalIntegral.integrableOn_deriv_of_nonneg (hcont.mono Icc_subset_Iic_self)
      (fun y hy => hderiv y hy.2) fun y hy => g'pos y hy.2
  refine integrableOn_Iic_of_intervalIntegral_norm_tendsto (g a - l) a h_intgr tendsto_id ?_
  apply Tendsto.congr' _ (tendsto_const_nhds.sub hg)
  filter_upwards [Iic_mem_atBot a] with x hx
  have h'x : id x ≤ a := hx
  calc
    g a - g x = ∫ y in id x..a, g' y := by
      symm
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h'x
        (hcont.mono Icc_subset_Iic_self) fun y hy => hderiv y hy.2
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le h'x]
      exact h_intgr (id x)
    _ = ∫ y in id x..a, ‖g' y‖ := by
      simp_rw [intervalIntegral.integral_of_le h'x]
      -- Unlike the `Ioi` case, `Ioc x a` gives `y ≤ a`, but `g'pos` needs `y < a`
      rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
      dsimp only [Real.norm_eq_abs]
      rw [abs_of_nonneg]
      exact g'pos _ hy.2

/-- When a function has a limit at minus infinity, and its derivative is nonnegative, then the
derivative is automatically integrable on `(-∞, a]`. Version assuming differentiability on
`(-∞, a]`. -/
public theorem integrableOn_Iic_deriv_of_nonneg' (hderiv : ∀ x ∈ Iic a, HasDerivAt g (g' x) x)
    (g'pos : ∀ x ∈ Iio a, 0 ≤ g' x) (hg : Tendsto g atBot (𝓝 l)) : IntegrableOn g' (Iic a) := by
  refine integrableOn_Iic_deriv_of_nonneg ?_ (fun x hx => hderiv x hx.out.le) g'pos hg
  exact (hderiv a self_mem_Iic).continuousAt.continuousWithinAt

end MeasureTheory
