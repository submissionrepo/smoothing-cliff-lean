/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Calculus.Rademacher

open MeasureTheory

/-!
# Rademacher under absolute continuity

Bridge from Mathlib's Rademacher theorem (Lipschitz functions on finite-dimensional inner-product
spaces are differentiable Haar-almost everywhere) to almost-everywhere differentiability under any
measure that is absolutely continuous with respect to a Haar measure.

## Main statements

* `ae_differentiableAt_of_lipschitz_absolutelyContinuous` — a Lipschitz function is differentiable
  `ν`-almost everywhere whenever `ν` is absolutely continuous with respect to a Haar measure.

## Tags

Rademacher, absolute continuity, almost everywhere differentiable, Lipschitz
-/

@[expose] public section

/-- **Rademacher transferred through absolute continuity.**

If `f : E → ℝ` is `C`-Lipschitz on a finite-dimensional inner-product space `E`, and `ν` is
absolutely continuous with respect to a Haar measure `μ` on `E`, then `f` is differentiable at
`ν`-almost every point. -/
theorem ae_differentiableAt_of_lipschitz_absolutelyContinuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {μ ν : Measure E} [μ.IsAddHaarMeasure] (hν : ν.AbsolutelyContinuous μ)
    {f : E → ℝ} {C : NNReal} (hf : LipschitzWith C f) :
    ∀ᵐ x ∂ν, DifferentiableAt ℝ f x :=
  hν.ae_le hf.ae_differentiableAt_of_real
