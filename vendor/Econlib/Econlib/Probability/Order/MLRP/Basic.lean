/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.Conditioning
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Monotone likelihood ratio property — definitions and basic monotonicity

This file defines the (strict) **monotone likelihood ratio property** (**MLRP**) for parameterized
families of density functions, establishes monotonicity of the likelihood ratio, the integrated
cross inequality, and the propagation of MLRP to posterior likelihood ratios.

## Main definitions

* `HasMonotoneLikelihoodRatio`, `HasStrictMonotoneLikelihoodRatio` — the (strict) MLRP predicates.

## Main statements

* `mlrp_integrated_cross` — the integrated cross-product inequality on separated sets.
* `HasMonotoneLikelihoodRatio.ratioMonotone` — the likelihood ratio is monotone.
* `HasMonotoneLikelihoodRatio.posteriorRatioMonotone` — posterior likelihood ratios are monotone in
  the observed signal.

## References

* Milgrom, Paul R. 1981. “Good News and Bad News: Representation Theorems and Applications.” *The
  Bell Journal of Economics* 12 (2): 380. [https://doi.org/10.2307/3003562](https://doi.org/10.2307/3003562).

## Tags

monotone likelihood ratio, mlrp, posterior
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.Probability

/-- The monotone likelihood ratio property for parameterized families of density functions. -/
def HasMonotoneLikelihoodRatio (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ θ₁ θ₂ x₁ x₂, θ₁ < θ₂ → x₁ ≤ x₂ →
    f x₁ θ₂ * f x₂ θ₁ ≤ f x₂ θ₂ * f x₁ θ₁

/-- Strict version of MLRP. -/
def HasStrictMonotoneLikelihoodRatio (f : ℝ → ℝ → ℝ) : Prop :=
  ∀ θ₁ θ₂ x₁ x₂, θ₁ < θ₂ → x₁ < x₂ →
    f x₁ θ₂ * f x₂ θ₁ < f x₂ θ₂ * f x₁ θ₁

namespace HasStrictMonotoneLikelihoodRatio

theorem hasMonotoneLikelihoodRatio
    {f : ℝ → ℝ → ℝ} (h : HasStrictMonotoneLikelihoodRatio f) :
    HasMonotoneLikelihoodRatio f := fun θ₁ θ₂ hθ x₁ x₂ hx => by
  rcases hx.lt_or_eq with hlt | heq
  · exact le_of_lt (h θ₁ θ₂ hθ x₁ x₂ hlt)
  · rw [heq]

end HasStrictMonotoneLikelihoodRatio

/-- **Pairwise integrated cross inequality.** For two integrable functions `g₁ g₂` whose pointwise
cross-products are ordered (`g₂ x₁ * g₁ x₂ ≤ g₂ x₂ * g₁ x₁` whenever `x₁ ≤ x₂`), the integrated
cross-product inequality holds on any pair of separated measurable sets `A ≤ B`. The parameterized
predicate `HasMonotoneLikelihoodRatio.integrated` is a corollary. -/
lemma mlrp_integrated_cross {g₁ g₂ : ℝ → ℝ}
    (hcross : ∀ x₁ x₂, x₁ ≤ x₂ → g₂ x₁ * g₁ x₂ ≤ g₂ x₂ * g₁ x₁)
    (hInt₁ : Integrable g₁) (hInt₂ : Integrable g₂)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hSep : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) :
    (∫ x in A, g₂ x) * (∫ x in B, g₁ x) ≤
    (∫ x in B, g₂ x) * (∫ x in A, g₁ x) := by
  have hProd₂₁ : IntegrableOn (fun z : ℝ × ℝ => g₂ z.1 * g₁ z.2) (A ×ˢ B) := by
    simpa [Measure.prod_restrict] using
      Integrable.mul_prod hInt₂.integrableOn hInt₁.integrableOn
  have hProd₁₂ : IntegrableOn (fun z : ℝ × ℝ => g₁ z.1 * g₂ z.2) (A ×ˢ B) := by
    simpa [Measure.prod_restrict] using
      Integrable.mul_prod hInt₁.integrableOn hInt₂.integrableOn
  rw [← setIntegral_prod_mul g₂ g₁ A B,
      mul_comm (∫ x in B, g₂ x) _,
      ← setIntegral_prod_mul g₁ g₂ A B]
  refine setIntegral_mono_on hProd₂₁ hProd₁₂ (hA.prod hB) ?_
  rintro ⟨a, b⟩ ⟨ha, hb⟩
  simpa [mul_comm] using hcross a b (hSep a ha b hb)

namespace HasMonotoneLikelihoodRatio

/-- Under MLRP, the likelihood ratio `f(·, θ₂) / f(·, θ₁)` is monotone when the lower-parameter
density is pointwise positive. -/
lemma ratioMonotone {f : ℝ → ℝ → ℝ}
    (hMlrp : HasMonotoneLikelihoodRatio f) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    (hPos : ∀ x, 0 < f x θ₁) :
    Monotone (fun x => f x θ₂ / f x θ₁) := by
  intro x₁ x₂ hx
  rw [div_le_div_iff₀ (hPos x₁) (hPos x₂)]
  exact hMlrp θ₁ θ₂ x₁ x₂ hθ hx

/-- Integrated MLRP: For separated sets `A ≤ B`, the cross-product integral inequality holds. -/
lemma integrated {f : ℝ → ℝ → ℝ}
    (hMlrp : HasMonotoneLikelihoodRatio f) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    (hInt₁ : Integrable (fun x => f x θ₁)) (hInt₂ : Integrable (fun x => f x θ₂))
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hSep : ∀ a ∈ A, ∀ b ∈ B, a ≤ b) :
    (∫ x in A, f x θ₂) * (∫ x in B, f x θ₁) ≤
    (∫ x in B, f x θ₂) * (∫ x in A, f x θ₁) :=
  mlrp_integrated_cross (fun x₁ x₂ hx => hMlrp θ₁ θ₂ x₁ x₂ hθ hx) hInt₁ hInt₂
    A B hA hB hSep

/-- If the likelihood family satisfies MLRP, then posterior likelihood ratios are monotone in the
observed signal. The normalizing constant from Bayes' rule cancels, so this reduces to monotonicity
of the primitive likelihood ratio. -/
lemma posteriorRatioMonotone
    {lk : ℝ → ℝ → ℝ} (hMlrp : HasMonotoneLikelihoodRatio lk)
    (prior : ContDist) {θ₁ θ₂ : ℝ} (hθ : θ₁ < θ₂)
    (hLkNonneg : ∀ x θ, 0 ≤ lk x θ)
    (hPos : ∀ x, 0 < lk x θ₁)
    (hPriorPos : 0 < prior.density θ₁)
    (hLkInt : ∀ x, Integrable (fun θ => prior.density θ * lk x θ))
    (hDenom : ∀ x, 0 < ∫ θ, prior.density θ * lk x θ) :
    Monotone (fun x =>
      (ContDist.posterior prior (fun θ s => lk s θ) x
        (fun θ => hLkNonneg x θ) (hLkInt x) (hDenom x)).density θ₂ /
      (ContDist.posterior prior (fun θ s => lk s θ) x
        (fun θ => hLkNonneg x θ) (hLkInt x) (hDenom x)).density θ₁) := by
  suffices hEq : ∀ x,
      (ContDist.posterior prior (fun θ s => lk s θ) x
        (fun θ => hLkNonneg x θ) (hLkInt x) (hDenom x)).density θ₂ /
      (ContDist.posterior prior (fun θ s => lk s θ) x
        (fun θ => hLkNonneg x θ) (hLkInt x) (hDenom x)).density θ₁ =
      (prior.density θ₂ / prior.density θ₁) * (lk x θ₂ / lk x θ₁) by
    intro x₁ x₂ hx
    -- Beta-reduce the `Monotone` lambda at both points, then replace each posterior ratio by the
    -- primitive likelihood ratio via `hEq` (explicit `rw`, since `simp` would unfold the
    -- `posterior` wrapper to `posteriorOrPrior` before `hEq` could fire).
    beta_reduce
    rw [hEq x₁, hEq x₂]
    exact mul_le_mul_of_nonneg_left (hMlrp.ratioMonotone hθ hPos hx)
      (div_nonneg (prior.nonneg θ₂) (prior.nonneg θ₁))
  intro x
  rw [ContDist.posterior_density prior _ x θ₂ _ (hLkInt x) (hDenom x),
      ContDist.posterior_density prior _ x θ₁ _ (hLkInt x) (hDenom x)]
  -- With positive prior mass at θ₁ the θ₁-posterior density is nonzero, so the Bayes normalizers
  -- cancel cleanly — no totalized `x / 0` branch.
  field_simp [ne_of_gt (hDenom x), hPriorPos.ne', ne_of_gt (hPos x)]

end HasMonotoneLikelihoodRatio

end Econlib.Probability
