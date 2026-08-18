/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Order.Supermodular
public import Econlib.Preferences.Basic
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Single crossing and increasing differences

This file develops the single-crossing property of Milgrom and Shannon (1994) at both the ordinal
relation level and the cardinal utility level, together with the stronger increasing-differences
conditions that imply it and a smooth cross-partial sufficient condition.

## Main definitions

* `SingleCrossingRel` — the relation-level Milgrom–Shannon condition, over ordered types, ordered
  actions, and a family of `PreferenceRel`s.
* `CardinalSingleCrossing` — the real-valued utility version, stated in terms of utility
  differences (Spence–Mirrlees condition).
* `WeakCardinalSingleCrossing` — the weak single-crossing property, the exact hypothesis of the
  monotone-comparative-statics theorem.
* `StrictIncreasingDifferences` — strictly increasing differences, strictly stronger than single
  crossing.

## Main statements

* `CardinalSingleCrossing.toSingleCrossingRel` — the cardinal condition induces the relation-level
  one through the utility representation.
* `StrictIncreasingDifferences.toCardinalSingleCrossing`, `CardinalSingleCrossing.toWeak`,
  `Supermodular.toWeakCardinalSingleCrossing` — implications among the conditions.
* `strict_increasing_differences_of_cross_partial_pos` — a strictly positive cross-partial
  `∂²u/∂θ∂x > 0` everywhere yields strictly increasing differences.

## Notes

The file keeps the one-dimensional action order explicit. Product-order and lattice comparative
statics should use the predicates in `Preferences.Geometry` and the optimization modules that
consume them.

## References

* Milgrom, Paul, and Chris Shannon. 1994. “Monotone Comparative Statics.” *Econometrica* 62 (1):
  157. [https://doi.org/10.2307/2951479](https://doi.org/10.2307/2951479).

## Tags

single crossing, increasing differences, spence-mirrlees, supermodularity, comparative statics
-/

@[expose] public section

namespace Econlib.Preferences

variable {Θ : Type*} {X : Type*} [LinearOrder Θ] [LinearOrder X]

/-- Relation-level **single-crossing** on ordered types and actions, the ordinal Milgrom–Shannon
condition (1994): If the lower type weakly prefers the higher action, then the higher type strictly
prefers the higher action. It does not require a real-valued utility, subtraction, or any cardinal
scale. -/
structure SingleCrossingRel (R : Θ → PreferenceRel X) where
  /-- If the lower type weakly prefers the higher action, then the higher type strictly prefers the
  higher action. -/
  weak_crossing : ∀ (θ₁ θ₂ : Θ) (x₁ x₂ : X),
    θ₁ < θ₂ → x₁ < x₂ →
    PreferenceRel.le (R θ₁) x₂ x₁ →
    PreferenceRel.lt (R θ₂) x₂ x₁

/-- A family of utility functions `u : Θ → X → ℝ` satisfies the **single-crossing property** (also
called the **Spence–Mirrlees condition**) if, for any two actions `x₁ < x₂` and two types
`θ₁ < θ₂`, `u θ₁ x₂ - u θ₁ x₁ ≥ 0  →  u θ₂ x₂ - u θ₂ x₁ > 0`.

If the lower type `θ₁` weakly prefers the higher action `x₂` to `x₁`, then the higher type `θ₂`
strictly prefers `x₂` to `x₁`. This is the cardinal form of the ordinal Milgrom–Shannon condition
(1994) recorded by `SingleCrossingRel.weak_crossing`. -/
structure CardinalSingleCrossing (u : Θ → X → ℝ) where
  /-- If the lower type weakly prefers the higher action, then the higher type strictly prefers the
  higher action. -/
  weak_crossing : ∀ (θ₁ θ₂ : Θ) (x₁ x₂ : X),
    θ₁ < θ₂ → x₁ < x₂ →
    u θ₁ x₂ - u θ₁ x₁ ≥ 0 →
    u θ₂ x₂ - u θ₂ x₁ > 0

/-- Cardinal single crossing induces relation-level single crossing through the real-valued utility
representation. -/
noncomputable def CardinalSingleCrossing.toSingleCrossingRel {u : Θ → X → ℝ}
    (h : CardinalSingleCrossing u) :
    SingleCrossingRel (fun θ => preferenceOfRealUtility (u θ)) where
  weak_crossing := by
    intro θ₁ θ₂ x₁ x₂ hθ hx hweak
    have hgt := h.weak_crossing θ₁ θ₂ x₁ x₂ hθ hx (sub_nonneg.mpr hweak)
    have hlt : u θ₂ x₁ < u θ₂ x₂ := sub_pos.mp hgt
    exact ⟨hlt.le, not_le.mpr hlt⟩

/-- A function `u : Θ → X → ℝ` has strictly increasing differences if the marginal return to
increasing the action is strictly increasing in the type: For `θ₁ < θ₂` and `x₁ < x₂`,
`u(θ₂, x₂) - u(θ₂, x₁) > u(θ₁, x₂) - u(θ₁, x₁)`

Strictly increasing differences implies single-crossing but is strictly stronger. In the
differentiable case, it is equivalent to `∂²u/∂θ∂x > 0` everywhere. -/
structure StrictIncreasingDifferences (u : Θ → X → ℝ) where
  strict_incr_diff : ∀ (θ₁ θ₂ : Θ) (x₁ x₂ : X),
    θ₁ < θ₂ → x₁ < x₂ →
    u θ₂ x₂ - u θ₂ x₁ > u θ₁ x₂ - u θ₁ x₁

/-- Strictly increasing differences implies cardinal single crossing: If `θ₂` gains strictly more
from raising the action than `θ₁` does, then weak preference by `θ₁` becomes strict preference by
`θ₂`. -/
lemma StrictIncreasingDifferences.toCardinalSingleCrossing {u : Θ → X → ℝ}
    (h : StrictIncreasingDifferences u) : CardinalSingleCrossing u where
  weak_crossing := fun θ₁ θ₂ x₁ x₂ hθ hx hge => by
    linarith [h.strict_incr_diff θ₁ θ₂ x₁ x₂ hθ hx]

/-- The **weak single-crossing property** of Milgrom and Shannon (1994): Weak preference for the
higher action crosses upward (once weakly preferred by a low type, weakly preferred by every higher
type), and so does strict preference. This is the hypothesis of the Milgrom–Shannon monotone-
comparative-statics theorem (argmax monotone in the strong set order) and is strictly weaker than
`CardinalSingleCrossing`. Objectives with flat tops, such as capacity-constrained payoffs
`min x θ`, satisfy the weak property but not the strict one. -/
structure WeakCardinalSingleCrossing (u : Θ → X → ℝ) : Prop where
  /-- Weak preference for the higher action crosses upward in the type. -/
  le_crossing : ∀ (θ₁ θ₂ : Θ) (x₁ x₂ : X),
    θ₁ < θ₂ → x₁ < x₂ →
    u θ₁ x₁ ≤ u θ₁ x₂ → u θ₂ x₁ ≤ u θ₂ x₂
  /-- Strict preference for the higher action crosses upward in the type. -/
  lt_crossing : ∀ (θ₁ θ₂ : Θ) (x₁ x₂ : X),
    θ₁ < θ₂ → x₁ < x₂ →
    u θ₁ x₁ < u θ₁ x₂ → u θ₂ x₁ < u θ₂ x₂

/-- Strict single crossing implies the weak Milgrom–Shannon property. -/
lemma CardinalSingleCrossing.toWeak {u : Θ → X → ℝ} (h : CardinalSingleCrossing u) :
    WeakCardinalSingleCrossing u where
  le_crossing := fun θ₁ θ₂ x₁ x₂ hθ hx hle =>
    (sub_pos.mp (h.weak_crossing θ₁ θ₂ x₁ x₂ hθ hx (sub_nonneg.mpr hle))).le
  lt_crossing := fun θ₁ θ₂ x₁ x₂ hθ hx hlt =>
    sub_pos.mp (h.weak_crossing θ₁ θ₂ x₁ x₂ hθ hx (sub_nonneg.mpr hlt.le))

/-- Supermodularity (weak increasing differences) implies the weak Milgrom–Shannon single-crossing
property: The marginal return to the higher action is nondecreasing in the type, so both weak and
strict preference for the higher action persist upward. -/
lemma Supermodular.toWeakCardinalSingleCrossing {u : Θ → X → ℝ} (h : Supermodular u) :
    WeakCardinalSingleCrossing u where
  le_crossing := fun θ₁ θ₂ x₁ x₂ hθ hx hle => by
    linarith [h θ₁ θ₂ x₁ x₂ hθ.le hx.le]
  lt_crossing := fun θ₁ θ₂ x₁ x₂ hθ hx hlt => by
    linarith [h θ₁ θ₂ x₁ x₂ hθ.le hx.le]

/-- If `u : ℝ → ℝ → ℝ` has cross-partial derivative `∂²u/∂θ∂x > 0` everywhere (supplied as
`HasDerivAt` hypotheses for the partial `u_θ` and the cross-partial `u_θx`), then `u` has strictly
increasing differences, and therefore satisfies single-crossing. -/
theorem strict_increasing_differences_of_cross_partial_pos
    (u : ℝ → ℝ → ℝ)
    -- Partial of u w.r.t. θ: for each x, θ ↦ u(θ, x) has derivative u_θ(θ, x)
    (u_θ : ℝ → ℝ → ℝ)
    (h_u_θ : ∀ θ x, HasDerivAt (fun θ' => u θ' x) (u_θ θ x) θ)
    -- Cross-partial: for each θ, x ↦ u_θ(θ, x) has derivative u_θx(θ, x)
    (u_θx : ℝ → ℝ → ℝ)
    (h_u_θx : ∀ θ x, HasDerivAt (u_θ θ) (u_θx θ x) x)
    -- The cross-partial is strictly positive everywhere
    (h_pos : ∀ θ x, 0 < u_θx θ x) :
    StrictIncreasingDifferences u where
  strict_incr_diff θ₁ θ₂ x₁ x₂ hθ hx := by
    have h_inner : ∀ θ, u_θ θ x₁ < u_θ θ x₂ :=
      fun θ => strictMono_of_hasDerivAt_pos (h_u_θx θ) (h_pos θ) hx
    exact strictMono_of_hasDerivAt_pos
      (show ∀ θ, HasDerivAt (fun θ' => u θ' x₂ - u θ' x₁) (u_θ θ x₂ - u_θ θ x₁) θ from
        fun θ => (h_u_θ θ x₂).sub (h_u_θ θ x₁))
      (fun θ => by linarith [h_inner θ]) hθ

end Econlib.Preferences
