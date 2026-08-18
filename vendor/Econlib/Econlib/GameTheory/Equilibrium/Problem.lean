/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Real.Basic

/-!
# Abstract equilibrium API

This file defines the common record for Nash-style equilibrium predicates (Nash 1951). A bundled
`EquilibriumProblem` carries the data needed to phrase an equilibrium predicate: Strategy space,
deviator index, swap relation, and value functional. Its `IsEquilibrium` predicate says that no
allowed unilateral deviation improves the deviator's value.

`GameMorphism` packages a forward map between two equilibrium problems that preserves deviators,
swaps, and value, and `transport` carries equilibria across the map.

## Main definitions

* `EquilibriumProblem`: The strategy space, deviator index, swap relation, and value functional for
  an equilibrium predicate.
* `EquilibriumProblem.IsEquilibrium`: The no-profitable-deviation predicate associated to an
  equilibrium problem.
* `GameMorphism`: A forward map between equilibrium problems that transports equilibria.

## Main statements

* `GameMorphism.transport`: Equilibria transport along a `GameMorphism`.

## Notes

Concrete games expose named constructors returning `EquilibriumProblem` records, and their concrete
equilibrium predicates are defined as `(_).IsEquilibrium`. The `transport` lemma subsumes a number
of one-direction forwarding implications across the library (mixed to correlated, pure-BNE to
mixed-BNE, repeated to extensive).

## References

* Nash, John. 1951. “Non-Cooperative Games.” *The Annals of Mathematics* 54 (2): 286.
  [https://doi.org/10.2307/1969529](https://doi.org/10.2307/1969529).

## Tags

game theory, equilibrium, nash equilibrium, morphism
-/

@[expose] public section

namespace Econlib.GameTheory

universe u v

/-- Data needed to phrase a Nash-style equilibrium predicate.

`S` is the strategy / profile space. `I` is the deviator index — typically players, or player–type
pairs in Bayesian games, or player–history pairs in repeated/extensive games. `swap i σ σ'` records
which `σ'` count as permitted unilateral deviations of `σ` at deviator `i`. `value i σ` is the
deviator's evaluation of `σ`. -/
structure EquilibriumProblem where
  /-- Strategy / profile space. -/
  S : Type u
  /-- Deviator index. -/
  I : Type v
  /-- Permitted unilateral deviations: `swap i σ σ'` says `σ'` is a legal deviation of `σ` by
  deviator `i`. -/
  swap : I → S → S → Prop
  /-- The deviator's evaluation of a profile. -/
  value : I → S → ℝ

namespace EquilibriumProblem

variable (P : EquilibriumProblem)

/-- A profile `σ` is an equilibrium of `P` when no deviator has a profitable unilateral
deviation. -/
def IsEquilibrium (σ : P.S) : Prop :=
  ∀ i σ', P.swap i σ σ' → P.value i σ ≥ P.value i σ'

end EquilibriumProblem

/-- A morphism between equilibrium problems: A forward map of strategies that preserves deviator
structure in the direction needed to transport equilibria forward.

Concretely, `toFun : P.S → Q.S` carries `P`-strategies to `Q`-strategies, `deviatorMap` goes the
other way (every `Q`-deviator has a corresponding `P`-deviator), and the swap correspondence and
value equality are stated so that an equilibrium for `P` becomes one for `Q` after applying
`toFun`.

The asymmetry of `deviatorMap : Q.I → P.I` is intentional: When transporting an equilibrium
forward, every deviator on the target must be witnessed by one on the source, otherwise the target
could have unanswered deviation directions. -/
structure GameMorphism (P Q : EquilibriumProblem) where
  /-- Forward map of strategies. -/
  toFun : P.S → Q.S
  /-- Backward map of deviator indices. -/
  deviatorMap : Q.I → P.I
  /-- Every legal deviation on the target lifts to a legal deviation on the source. -/
  swap_lifts : ∀ (i : Q.I) (σ : P.S) (τ' : Q.S),
    Q.swap i (toFun σ) τ' → ∃ σ' : P.S, P.swap (deviatorMap i) σ σ' ∧ toFun σ' = τ'
  /-- Value is preserved under the forward map. -/
  value_eq : ∀ (i : Q.I) (σ : P.S),
    Q.value i (toFun σ) = P.value (deviatorMap i) σ

namespace GameMorphism

variable {P Q : EquilibriumProblem} (φ : GameMorphism P Q)

/-- Equilibria transport along a `GameMorphism`. -/
theorem transport {σ : P.S} (h : P.IsEquilibrium σ) :
    Q.IsEquilibrium (φ.toFun σ) := by
  intro i τ' hτ'
  obtain ⟨σ', hσ', rfl⟩ := φ.swap_lifts i σ τ' hτ'
  rw [φ.value_eq i σ, φ.value_eq i σ']
  exact h (φ.deviatorMap i) σ' hσ'

end GameMorphism

end Econlib.GameTheory
