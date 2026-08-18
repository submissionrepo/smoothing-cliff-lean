/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.ContinuousOn

/-!
# Slater's condition

Domain-generic Slater predicates for convex inequality-constrained optimization.

`IsSlater X g` says: `X` is convex, each `g i` is convex on `X`, and there is a point `x ∈ X` where
every constraint is strictly satisfied (`g i x < 0`). This is the hypothesis that powers strong
duality and KKT necessity.

`IsParametricSlater X g p₀` strengthens this to uniform strict feasibility: A single witness
`x ∈ X` satisfies `g p i x < 0` for all `p` in a neighborhood of `p₀`. This is the form needed for
shadow-price duality, where the constraint depends on the dual variable.

## Main definitions

* `IsSlater`: Slater's condition for a convex program.
* `IsParametricSlater`: Uniform strict feasibility for a parametric family of constraints.

## Main statements

* `IsParametricSlater.toIsSlater`: A parametric Slater witness collapses to an ordinary Slater
  witness at the base parameter.

## References

* Slater, Morton. 1950. “Lagrange Multipliers Revisited.” *Cowles Commission Discussion Paper:
  Mathematics* 403.
* Boyd, Stephen P. 2006. *Convex Optimization*. Cambridge University Press. Section 5.2.3.

## Tags

slater, constraint qualification, convex optimization, strict feasibility
-/

@[expose] public section

open Topology

namespace Econlib.Optimization

/-- **Slater's condition** (Slater 1950) over an arbitrary real module. `X` is the ambient feasible
set; `g i x ≤ 0` encodes the `i`-th inequality constraint. Requires convexity of `X`, convexity of
each constraint on `X`, and a strictly feasible point `x ∈ X` with `g i x < 0` for every `i`. -/
structure IsSlater {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} (X : Set E) (g : ι → E → ℝ) : Prop where
  convex_X : Convex ℝ X
  convex_g : ∀ i, ConvexOn ℝ X (g i)
  strict_feasible : ∃ x ∈ X, ∀ i, g i x < 0

/-- Parametric Slater condition: Strict feasibility holds for a single `x ∈ X` uniformly as the
parameter `p` ranges over a neighborhood of `p₀`. Required for shadow-price duality, where the
constraint itself depends on the dual variable and we need strict feasibility to persist as we vary
that parameter (as in Kamenica–Gentzkow-type persuasion with a budget or participation
constraint). -/
structure IsParametricSlater {E P : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace P]
    {ι : Type*} (X : Set E) (g : P → ι → E → ℝ) (p₀ : P) : Prop where
  convex_X : Convex ℝ X
  convex_g : ∀ p i, ConvexOn ℝ X (g p i)
  strict_feasible_nearby : ∃ x ∈ X, ∀ᶠ p in 𝓝 p₀, ∀ i, g p i x < 0

/-- A parametric Slater witness collapses to an ordinary Slater witness at the base parameter. -/
lemma IsParametricSlater.toIsSlater {E P : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace P]
    {ι : Type*} {X : Set E} {g : P → ι → E → ℝ} {p₀ : P}
    (h : IsParametricSlater X g p₀) : IsSlater X (g p₀) where
  convex_X := h.convex_X
  convex_g := h.convex_g p₀
  strict_feasible := by
    obtain ⟨x, hx, hgs⟩ := h.strict_feasible_nearby
    exact ⟨x, hx, hgs.self_of_nhds⟩

end Econlib.Optimization
