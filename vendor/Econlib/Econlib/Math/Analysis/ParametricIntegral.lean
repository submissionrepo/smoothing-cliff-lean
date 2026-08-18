/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory Topology

/-!
# Parametric integrals with moving bounds

Differentiation of an interval integral whose lower bound varies with the parameter. For a
continuous, locally integrable integrand `h`, the **Leibniz rule** gives
`d/dx ∫_{a(x)}^{b} h(t) dt = -h(a(x)) · a'(x)`, obtained by composing
`intervalIntegral.integral_hasDerivAt_left` with the chain rule. Specializations to the shift
`a(x) = x + c` and to `a(x) = x` are also provided.

The auxiliary `HasDerivAt.comp_real` is a form of `HasDerivAt.comp` for `ℝ → ℝ` functions whose
derivative is stated as the product `g' * f'` and whose composite is `fun x => g (f x)`, avoiding
the `smul`/`Function.comp` rewriting that the general lemma requires.

## Main statements

* `HasDerivAt.comp_real` — chain rule for `ℝ → ℝ` composition stated with `g' * f'`.
* `hasDerivAt_parametric_lower` — Leibniz rule for a moving lower bound.
* `hasDerivAt_parametric_lower_shift`, `hasDerivAt_parametric_lower_id` — the shift and identity
  specializations.

## Tags

leibniz rule, parametric integral, interval integral, chain rule
-/

@[expose] public section

variable {f g : ℝ → ℝ} {f' g' a b x₀ : ℝ}

/-! ## HasDerivAt.comp for ℝ → ℝ without smul -/

/-- Chain rule for `ℝ → ℝ` composition, with derivative stated as `g' * f'` rather than `g' • f'`
and composite stated as `fun x => g (f x)` rather than `g ∘ f`. -/
theorem HasDerivAt.comp_real (x : ℝ) (hg : HasDerivAt g g' (f x)) (hf : HasDerivAt f f' x) :
    HasDerivAt (fun x => g (f x)) (g' * f') x :=
  hg.comp x hf

/-! ## Parametric integrals with moving lower bound -/

/-- **Leibniz rule** for a moving lower bound: `d/dx ∫_{a(x)}^{b} h(t) dt = -h(a(x)) · a'(x)` when
`a` is differentiable at `x₀`, `h` is continuous at `a(x₀)`, integrable on `[a(x₀), b]`, and
strongly measurable near `a(x₀)`. -/
theorem hasDerivAt_parametric_lower {h : ℝ → ℝ} {a : ℝ → ℝ} {a' : ℝ} {b x₀ : ℝ}
    (ha : HasDerivAt a a' x₀)
    (hh_cont : ContinuousAt h (a x₀))
    (hh_int : IntervalIntegrable h volume (a x₀) b)
    (hh_meas : StronglyMeasurableAtFilter h (𝓝 (a x₀)) volume) :
    HasDerivAt (fun x => ∫ t in (a x)..b, h t) (-h (a x₀) * a') x₀ := by
  have hint := intervalIntegral.integral_hasDerivAt_left hh_int hh_meas hh_cont
  exact hint.comp_real x₀ ha

/-- Special case: `a(x) = x + c` (constant shift). The derivative simplifies to `-h(x₀ + c)` since
`a' = 1`. -/
theorem hasDerivAt_parametric_lower_shift {h : ℝ → ℝ} {c b x₀ : ℝ}
    (hh_cont : ContinuousAt h (x₀ + c))
    (hh_int : IntervalIntegrable h volume (x₀ + c) b)
    (hh_meas : StronglyMeasurableAtFilter h (𝓝 (x₀ + c)) volume) :
    HasDerivAt (fun x => ∫ t in (x + c)..b, h t) (-h (x₀ + c)) x₀ := by
  have ha : HasDerivAt (fun x => x + c) 1 x₀ := (hasDerivAt_id x₀).add_const c
  have := hasDerivAt_parametric_lower ha hh_cont hh_int hh_meas
  simpa [mul_one] using this

/-- Special case: `a(x) = x` (no shift). -/
theorem hasDerivAt_parametric_lower_id {h : ℝ → ℝ} {b x₀ : ℝ}
    (hh_cont : ContinuousAt h x₀)
    (hh_int : IntervalIntegrable h volume x₀ b)
    (hh_meas : StronglyMeasurableAtFilter h (𝓝 x₀) volume) :
    HasDerivAt (fun x => ∫ t in x..b, h t) (-h x₀) x₀ :=
  intervalIntegral.integral_hasDerivAt_left hh_int hh_meas hh_cont
