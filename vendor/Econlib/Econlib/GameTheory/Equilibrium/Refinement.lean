/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Equilibrium.Problem

/-!
# Refined equilibrium

This file layers a candidate-validity predicate on top of `EquilibriumProblem`, yielding
`EquilibriumRefinement` and its predicate `IsRefinedEquilibrium`. The validity filter captures
well-formedness requirements that go beyond no-profitable-deviation, such as Bayes consistency,
Kreps–Wilson consistency, or tremble feasibility. `RefinedGameMorphism` extends `GameMorphism` with
validity preservation, and refined equilibria transport along it.

The refinement layer is opt-in: Equilibrium concepts that do not need a separate validity step
continue to use plain `EquilibriumProblem`.

## Main definitions

* `EquilibriumRefinement`: An equilibrium problem together with a validity predicate.
* `EquilibriumRefinement.IsRefinedEquilibrium`: Validity plus equilibrium.
* `RefinedGameMorphism`: A `GameMorphism` that also preserves validity.

## Main statements

* `RefinedGameMorphism.transport`: Refined equilibria transport along a `RefinedGameMorphism`.

## Tags

game theory, equilibrium, refinement, morphism
-/

@[expose] public section

namespace Econlib.GameTheory

universe u v

/-- An equilibrium problem refined by a candidate-validity predicate.

The underlying `EquilibriumProblem` carries the deviation data; `valid : S → Prop` is the
well-formedness filter on the candidate space (Bayes consistency, Kreps–Wilson consistency, tremble
feasibility). A refined equilibrium is a valid candidate that is also an `EquilibriumProblem`
equilibrium. This layer is opt-in: Equilibrium concepts that do not need a separate validity step
continue to use plain `EquilibriumProblem`. -/
structure EquilibriumRefinement extends EquilibriumProblem where
  /-- Validity / well-formedness of a candidate. -/
  valid : S → Prop

namespace EquilibriumRefinement

variable (R : EquilibriumRefinement)

/-- A profile is a refined equilibrium when it is valid and no deviator has a profitable unilateral
deviation. -/
structure IsRefinedEquilibrium (σ : R.S) : Prop where
  /-- The candidate is valid (well-formed). -/
  valid : R.valid σ
  /-- The candidate is an equilibrium of the underlying problem. -/
  isEquilibrium : R.toEquilibriumProblem.IsEquilibrium σ

end EquilibriumRefinement

/-- A morphism between refined equilibrium problems: A `GameMorphism` plus validity preservation
along the forward map. -/
structure RefinedGameMorphism (R Q : EquilibriumRefinement) extends
    GameMorphism R.toEquilibriumProblem Q.toEquilibriumProblem where
  /-- Validity is preserved under the forward map. -/
  valid_preserves : ∀ σ : R.S, R.valid σ → Q.valid (toFun σ)

namespace RefinedGameMorphism

variable {R Q : EquilibriumRefinement} (φ : RefinedGameMorphism R Q)

/-- Refined equilibria transport along a `RefinedGameMorphism`. -/
theorem transport {σ : R.S} (h : R.IsRefinedEquilibrium σ) :
    Q.IsRefinedEquilibrium (φ.toFun σ) :=
  ⟨φ.valid_preserves σ h.valid, φ.toGameMorphism.transport h.isEquilibrium⟩

end RefinedGameMorphism

end Econlib.GameTheory
