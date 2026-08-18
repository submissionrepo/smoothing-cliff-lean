/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Equilibrium.Refinement
public import Econlib.GameTheory.Strategic.Basic

/-!
# Equilibrium Refinements

This file defines refinement predicates for finite strategic-form games. It models tremble lower
bounds, perturbed equilibria, trembling-hand perfection, and proper equilibrium using the common
`EquilibriumRefinement` API.

## Main definitions

* `FiniteStrategicGame.IsTotallyMixed`: Mixed profiles with full support.
* `FiniteStrategicGame.TrembleConstraint`: Lower-bound constraints for perturbed games.
* `FiniteStrategicGame.IsPerturbedEquilibrium`: Equilibrium under a tremble constraint.
* `FiniteStrategicGame.IsTremblingHandPerfect`: Trembling-hand perfect equilibrium.
* `FiniteStrategicGame.IsEpsilonProperEquilibrium`: ε-proper equilibrium.
* `FiniteStrategicGame.IsProperEquilibrium`: Proper equilibrium.

## Main statements

* `FiniteStrategicGame.MixedStrategy.isTotallyMixed_of_feasible`: Strictly positive trembles force
  total mixedness.
* `FiniteStrategicGame.IsPerturbedEquilibrium_iff`: Refinement characterization of perturbed
  equilibrium.
* `FiniteStrategicGame.IsTremblingHandPerfect_iff`: Refinement characterization of trembling-hand
  perfection.
* `FiniteStrategicGame.IsProperEquilibrium_iff`: Refinement characterization of proper equilibrium.

## References

* Selten, R. 1975. “Reexamination of the Perfectness Concept for Equilibrium Points in Extensive
  Games.” *International Journal of Game Theory* 4 (1): 25–55. [https://doi.org/10.1007/bf01766400](https://doi.org/10.1007/bf01766400).
* Myerson, R. B. 1978. “Refinements of the Nash Equilibrium Concept.” *International Journal of
  Game Theory* 7 (2): 73–80. [https://doi.org/10.1007/bf01753236](https://doi.org/10.1007/bf01753236).

## Tags

equilibrium refinements, trembling-hand perfection, proper equilibrium, strategic games
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

open Filter

namespace FiniteStrategicGame

variable (G : FiniteStrategicGame)

/-- A mixed strategy profile is totally mixed if every action of every player has strictly positive
probability. -/
def IsTotallyMixed (σ : G.MixedStrategy) : Prop :=
  ∀ i a, 0 < σ i a

/-- Lower-bound tremble constraints for a finite strategic-form game. A feasible mixed strategy
must put at least `lowerBound i a` on every action `a` of player `i`. -/
structure TrembleConstraint where
  lowerBound : (i : G.Player) → G.Action i → ℝ
  nonneg : ∀ i a, 0 ≤ lowerBound i a
  feasible : ∀ i, ∑ a : G.Action i, lowerBound i a ≤ 1

namespace TrembleConstraint

/-- A mixed action satisfies player `i`'s tremble lower bounds. -/
def FeasibleMixedAction (τ : G.TrembleConstraint) (i : G.Player)
    (y : stdSimplex ℝ (G.Action i)) : Prop :=
  ∀ a, τ.lowerBound i a ≤ y a

/-- A mixed-strategy profile satisfies every player's tremble lower bounds. -/
def FeasibleMixedStrategy (τ : G.TrembleConstraint) (σ : G.MixedStrategy) : Prop :=
  ∀ i, TrembleConstraint.FeasibleMixedAction (G := G) τ i (σ i)

/-- A sequence of tremble constraints vanishes action by action. -/
def TendsToZero (τseq : ℕ → G.TrembleConstraint) : Prop :=
  ∀ i a, Tendsto (fun n => (τseq n).lowerBound i a) atTop (nhds 0)

/-- A tremble constraint is strictly positive if every action of every player receives a positive
lower bound. Strict positivity forces every feasible mixed strategy to be totally mixed, which is
what makes the perturbed equilibria of Selten's THP construction interior. -/
def IsStrictlyPositive (τ : G.TrembleConstraint) : Prop :=
  ∀ i a, 0 < τ.lowerBound i a

end TrembleConstraint

/-- Any mixed strategy that is feasible under a strictly positive tremble constraint is totally
mixed. -/
theorem MixedStrategy.isTotallyMixed_of_feasible
    {τ : G.TrembleConstraint} {σ : G.MixedStrategy}
    (hpos : TrembleConstraint.IsStrictlyPositive G τ)
    (hfeas : TrembleConstraint.FeasibleMixedStrategy (G := G) τ σ) :
    G.IsTotallyMixed σ :=
  fun i a => lt_of_lt_of_le (hpos i a) (hfeas i a)

/-- The equilibrium problem associated with a perturbed game with tremble constraint `τ`. The
deviator index is the player; permitted deviations swap to mixed actions that still respect the
tremble lower bounds; the value is the expected payoff. -/
noncomputable def perturbedPred (τ : G.TrembleConstraint) : EquilibriumProblem where
  S := { σ : G.MixedStrategy // TrembleConstraint.FeasibleMixedStrategy (G := G) τ σ }
  I := G.Player
  swap i σ σ' := ∃ y : stdSimplex ℝ (G.Action i),
    TrembleConstraint.FeasibleMixedAction (G := G) τ i y ∧
      σ'.1 = Function.update σ.1 i y
  value i σ := G.expectedPayoff i σ.1

/-- Equilibrium of a perturbed game: The profile satisfies the tremble constraints and no player
can profitably deviate to another mixed action satisfying the same lower bounds. -/
def IsPerturbedEquilibrium (τ : G.TrembleConstraint) (σ : G.MixedStrategy) : Prop :=
  TrembleConstraint.FeasibleMixedStrategy (G := G) τ σ ∧
    ∀ i (y : stdSimplex ℝ (G.Action i)),
      TrembleConstraint.FeasibleMixedAction (G := G) τ i y →
        G.expectedPayoff i σ ≥ G.expectedPayoff i (Function.update σ i y)

@[simp] lemma perturbedPred_swap_iff (τ : G.TrembleConstraint) (i : G.Player)
    (σ σ' : { σ : G.MixedStrategy // TrembleConstraint.FeasibleMixedStrategy (G := G) τ σ }) :
    (G.perturbedPred τ).swap i σ σ' ↔
      ∃ y : stdSimplex ℝ (G.Action i),
        TrembleConstraint.FeasibleMixedAction (G := G) τ i y ∧
          σ'.1 = Function.update σ.1 i y := Iff.rfl

@[simp] lemma perturbedPred_value_eq (τ : G.TrembleConstraint) (i : G.Player)
    (σ : { σ : G.MixedStrategy // TrembleConstraint.FeasibleMixedStrategy (G := G) τ σ }) :
    (G.perturbedPred τ).value i σ = G.expectedPayoff i σ.1 := rfl

/-- The substrate-uniform form: A feasible profile is a perturbed equilibrium iff its underlying
subtype-bundled lift is an equilibrium of `perturbedPred τ`. -/
theorem IsPerturbedEquilibrium_iff (τ : G.TrembleConstraint) (σ : G.MixedStrategy) :
    G.IsPerturbedEquilibrium τ σ ↔
      ∃ hfeas : TrembleConstraint.FeasibleMixedStrategy (G := G) τ σ,
        (G.perturbedPred τ).IsEquilibrium (⟨σ, hfeas⟩ :
          { σ : G.MixedStrategy // TrembleConstraint.FeasibleMixedStrategy (G := G) τ σ }) := by
  unfold IsPerturbedEquilibrium
  dsimp only [perturbedPred, EquilibriumProblem.IsEquilibrium]
  constructor
  · rintro ⟨hfeas, h⟩
    refine ⟨hfeas, ?_⟩
    rintro i σ' ⟨y, hy_feas, hy_eq⟩
    rw [hy_eq]
    exact h i y hy_feas
  · rintro ⟨hfeas, h⟩
    refine ⟨hfeas, ?_⟩
    intro i y hy_feas
    have hupdate_feas : TrembleConstraint.FeasibleMixedStrategy (G := G) τ
        (Function.update σ i y) := by
      intro j
      by_cases hji : j = i
      · subst hji; intro a; rw [Function.update_self]; exact hy_feas a
      · intro a; rw [Function.update_of_ne hji]; exact hfeas j a
    exact h i ⟨Function.update σ i y, hupdate_feas⟩ ⟨y, hy_feas, rfl⟩

/-- Validity predicate for trembling-hand perfection: The profile is approximated by perturbed
equilibria with strictly positive, vanishing trembles. -/
def IsTHPValid (σ : G.MixedStrategy) : Prop :=
  ∃ (τseq : ℕ → G.TrembleConstraint) (σseq : ℕ → G.MixedStrategy),
    (∀ n, TrembleConstraint.IsStrictlyPositive G (τseq n)) ∧
    TrembleConstraint.TendsToZero G τseq ∧
    (∀ n, G.IsPerturbedEquilibrium (τseq n) (σseq n)) ∧
      ∀ i a, Tendsto (fun n => σseq n i a) atTop (nhds (σ i a))

/-- Substrate refinement object for trembling-hand perfection. The deviation skeleton is the
mixed-Nash one (`mixedNashPred`); the validity filter `valid` asks that the candidate is the
pointwise limit of perturbed equilibria with vanishing strictly positive trembles. -/
noncomputable def thpPred (G : FiniteStrategicGame) : EquilibriumRefinement :=
  { G.mixedNashPred with valid := fun σ => G.IsTHPValid σ }

/-- Trembling-hand perfection (Selten 1975): A mixed Nash equilibrium that is the pointwise limit
of equilibria of perturbed games whose strictly positive lower-bound trembles vanish to zero.
Strict positivity of `τseq n` forces each `σseq n` to be totally mixed
(`MixedStrategy.isTotallyMixed_of_feasible`). -/
structure IsTremblingHandPerfect (σ : G.MixedStrategy) : Prop where
  /-- A trembling-hand perfect equilibrium is a mixed Nash equilibrium. -/
  isMixedNash : G.IsMixedNash σ
  /-- The trembling-hand validity condition (limit of perturbed equilibria). -/
  thpValid : G.IsTHPValid σ

@[simp] lemma thpPred_swap_iff (i : G.Player) (σ σ' : G.MixedStrategy) :
    G.thpPred.swap i σ σ' ↔ ∃ y : stdSimplex ℝ (G.Action i), σ' = Function.update σ i y :=
  Iff.rfl

@[simp] lemma thpPred_value_eq (i : G.Player) (σ : G.MixedStrategy) :
    G.thpPred.value i σ = G.expectedPayoff i σ := rfl

@[simp] lemma thpPred_valid_iff (σ : G.MixedStrategy) :
    G.thpPred.valid σ ↔ G.IsTHPValid σ := Iff.rfl

/-- Substrate-uniform characterization: `IsTremblingHandPerfect` matches the refinement predicate
on `thpPred`. -/
theorem IsTremblingHandPerfect_iff (σ : G.MixedStrategy) :
    G.IsTremblingHandPerfect σ ↔ G.thpPred.IsRefinedEquilibrium σ := by
  constructor
  · rintro ⟨hne, hval⟩; exact ⟨hval, hne⟩
  · rintro ⟨hval, hne⟩; exact ⟨hne, hval⟩

/-- An **ε-proper equilibrium**: A totally mixed strategy in which any pure deviation that is
strictly worse than another pure deviation receives probability at most `ε` times the better
deviation's probability. The probability-ratio bound is the defining ingredient of proper
equilibrium. -/
def IsEpsilonProperEquilibrium (ε : ℝ) (σ : G.MixedStrategy) : Prop :=
  G.IsTotallyMixed σ ∧
    ∀ i (a b : G.Action i),
      G.expectedPayoff i (Function.update σ i (stdSimplex.vertex a)) <
        G.expectedPayoff i (Function.update σ i (stdSimplex.vertex b)) →
          σ i a ≤ ε * σ i b

/-- Validity predicate for proper equilibrium: The profile is approximated by ε-proper equilibria
with vanishing positive ε. -/
def IsProperValid (σ : G.MixedStrategy) : Prop :=
  ∃ (εseq : ℕ → ℝ) (σseq : ℕ → G.MixedStrategy),
    (∀ n, 0 < εseq n) ∧
    Tendsto εseq atTop (nhds 0) ∧
    (∀ n, G.IsEpsilonProperEquilibrium (εseq n) (σseq n)) ∧
      ∀ i a, Tendsto (fun n => σseq n i a) atTop (nhds (σ i a))

/-- Substrate refinement object for proper equilibrium. The deviation skeleton is the mixed-Nash
one (`mixedNashPred`); the validity filter asks that the candidate is the pointwise limit of
ε-proper equilibria with vanishing positive ε. -/
noncomputable def properPred (G : FiniteStrategicGame) : EquilibriumRefinement :=
  { G.mixedNashPred with valid := fun σ => G.IsProperValid σ }

/-- A **proper equilibrium** (Myerson 1978): A mixed Nash equilibrium that is the pointwise limit
of ε-proper equilibria with positive `ε` vanishing to zero. -/
structure IsProperEquilibrium (σ : G.MixedStrategy) : Prop where
  /-- A proper equilibrium is a mixed Nash equilibrium. -/
  isMixedNash : G.IsMixedNash σ
  /-- The proper validity condition (limit of ε-proper equilibria). -/
  properValid : G.IsProperValid σ

@[simp] lemma properPred_swap_iff (i : G.Player) (σ σ' : G.MixedStrategy) :
    G.properPred.swap i σ σ' ↔
      ∃ y : stdSimplex ℝ (G.Action i), σ' = Function.update σ i y :=
  Iff.rfl

@[simp] lemma properPred_value_eq (i : G.Player) (σ : G.MixedStrategy) :
    G.properPred.value i σ = G.expectedPayoff i σ := rfl

@[simp] lemma properPred_valid_iff (σ : G.MixedStrategy) :
    G.properPred.valid σ ↔ G.IsProperValid σ := Iff.rfl

/-- Substrate-uniform characterization: `IsProperEquilibrium` matches the refinement predicate on
`properPred`. -/
theorem IsProperEquilibrium_iff (σ : G.MixedStrategy) :
    G.IsProperEquilibrium σ ↔ G.properPred.IsRefinedEquilibrium σ := by
  constructor
  · rintro ⟨hne, hval⟩; exact ⟨hval, hne⟩
  · rintro ⟨hval, hne⟩; exact ⟨hne, hval⟩

namespace IsTremblingHandPerfect

/-- Every trembling-hand perfect equilibrium is a mixed Nash equilibrium. -/
theorem is_mixed_nash {σ : G.MixedStrategy}
    (hσ : G.IsTremblingHandPerfect σ) : G.IsMixedNash σ :=
  hσ.isMixedNash

end IsTremblingHandPerfect

/-- Every proper equilibrium is a mixed Nash equilibrium. -/
theorem IsProperEquilibrium.is_mixed_nash {σ : G.MixedStrategy}
    (hσ : G.IsProperEquilibrium σ) : G.IsMixedNash σ :=
  hσ.isMixedNash

end FiniteStrategicGame

end Econlib.GameTheory
