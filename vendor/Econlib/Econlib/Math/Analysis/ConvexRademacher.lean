/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Order.BourbakiWitt

open MeasureTheory Set Metric

/-!
# Almost-everywhere differentiability of convex functions

A convex function `f : E → ℝ` on a finite-dimensional inner product real space is differentiable
Lebesgue-almost everywhere. This is the convex specialization of Rademacher's theorem: A convex
function is locally Lipschitz, and a Lipschitz function is a.e. differentiable.

## Main statements

* `ConvexOn.ae_differentiableAt` — a convex function on a finite-dimensional inner product real
  space is differentiable at almost every point with respect to volume.

## Tags

convex function, rademacher, differentiable, almost everywhere, lipschitz
-/

@[expose] public section

namespace ConvexOn

/-- A convex function on a finite-dimensional normed space is Lipschitz on each open ball. -/
private lemma exists_lipschitzOnWith_ball'
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (R : ℝ) :
    ∃ K, LipschitzOnWith K f (Metric.ball (0 : E) R) := by
  by_cases hR : R ≤ 0
  · exact ⟨0, by rw [Metric.ball_eq_empty.mpr hR]; exact lipschitzOnWith_empty 0 f⟩
  have hR' : (0 : ℝ) < R := lt_of_not_ge hR
  -- f is continuous on E (convex on whole space is locally Lipschitz hence continuous).
  have hcont : Continuous f := hf.locallyLipschitz.continuous
  -- f is bounded on `closedBall 0 (R + 1)` (compact in finite-dim).
  have hcompact : IsCompact (Metric.closedBall (0 : E) (R + 1)) := isCompact_closedBall _ _
  have hBound_image : Bornology.IsBounded (f '' Metric.ball (0 : E) (R + 1)) :=
    (hcompact.image hcont).isBounded.subset (Set.image_mono Metric.ball_subset_closedBall)
  -- f is convex on ball 0 (R + 1).
  have hf_ball : ConvexOn ℝ (Metric.ball (0 : E) (R + 1)) f :=
    hf.subset (Set.subset_univ _) (convex_ball _ _)
  exact hf_ball.exists_lipschitzOnWith_of_isBounded (by linarith) hBound_image

/-- A convex function on a finite-dimensional inner product real space is a.e. differentiable. -/
theorem ae_differentiableAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    ∀ᵐ x ∂(volume : Measure E), DifferentiableAt ℝ f x := by
  -- For each n, f is Lipschitz on ball 0 n; a.e. x in ball 0 n is differentiable.
  have h_ball : ∀ n : ℕ, ∀ᵐ x ∂(volume : Measure E),
      x ∈ Metric.ball (0 : E) n → DifferentiableAt ℝ f x := by
    intro n
    obtain ⟨K, hK⟩ := ConvexOn.exists_lipschitzOnWith_ball' hf (n : ℝ)
    -- Rademacher within the ball gives a.e. DifferentiableWithinAt.
    have h_within : ∀ᵐ x ∂(volume : Measure E),
        x ∈ Metric.ball (0 : E) n → DifferentiableWithinAt ℝ f (Metric.ball (0 : E) n) x :=
      hK.ae_differentiableWithinAt_of_mem
    filter_upwards [h_within] with x hx hxball
    -- Open ball is a neighbourhood of any point in it; lift within → at.
    exact (hx hxball).differentiableAt (Metric.isOpen_ball.mem_nhds hxball)
  -- Cover E = ⋃ n, ball 0 n and take countable union of null sets.
  rw [MeasureTheory.ae_iff]
  -- {x | ¬ DiffAt f x} ⊆ ⋃ n, (ball 0 n ∩ {x | ¬ DiffAt f x})
  have h_subset :
      {x : E | ¬ DifferentiableAt ℝ f x} ⊆
        ⋃ n : ℕ, {x : E | x ∈ Metric.ball (0 : E) (n : ℝ) ∧ ¬ DifferentiableAt ℝ f x} := by
    intro x hx
    rw [Set.mem_iUnion]
    obtain ⟨n, hn⟩ := exists_nat_gt (dist x (0 : E))
    exact ⟨n, Metric.mem_ball.mpr hn, hx⟩
  refine measure_mono_null h_subset (measure_iUnion_null fun n => ?_)
  -- Each piece has measure zero.
  have hn := h_ball n
  rw [MeasureTheory.ae_iff] at hn
  refine measure_mono_null ?_ hn
  intro x ⟨hxball, hxnd⟩
  exact fun habs => hxnd (habs hxball)

end ConvexOn
