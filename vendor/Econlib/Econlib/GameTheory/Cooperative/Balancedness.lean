/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Cooperative.BalancedCore
public import Econlib.GameTheory.Cooperative.Core

/-!
# Balancedness and the Bondareva–Shapley theorem

A **balanced collection** of coalitional weights is a nonnegative weighting that sums to one on
every player; a TU game **satisfies balancedness** when, for every such collection, the weighted
sum of coalition values is dominated by the grand-coalition value. The Bondareva–Shapley theorem
(Bondareva 1963; Shapley 1967) states that this condition is equivalent to nonemptiness of the
core. The finite linear-programing engine is `coreFeasible_iff_satisfiesBalancedInequalities` in
`Econlib.GameTheory.Cooperative.BalancedCore`; this file packages it on `TUGameOn`.

## Main definitions

* `TUGameOn.IsBalanced`: Balanced coalitional weights.
* `TUGameOn.SatisfiesBalancedness`: The Bondareva–Shapley balancedness condition.

## Main statements

* `TUGameOn.core_nonempty_iff_balanced`: The Bondareva–Shapley theorem for `TUGameOn`.

## References

* Bondareva, Olga N. 1963. “Some Applications of Linear Programing Methods to the Theory of
  Cooperative Games.” *Problemy Kibernetiki* 10 : 119–39.
* Shapley, Lloyd S. 1967. “On Balanced Sets and Cores.” *Naval Research Logistics Quarterly* 14
  (4): 453–60. [https://doi.org/10.1002/nav.3800140404](https://doi.org/10.1002/nav.3800140404).

## Tags

cooperative game, balancedness, core
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

namespace TUGameOn

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- A **balanced collection** of coalition weights: Nonnegative, and summing to one over the
coalitions containing each fixed player. -/
@[mk_iff] structure IsBalanced (G : TUGameOn Player) (w : Finset Player → ℝ) : Prop where
  /-- The weights are nonnegative. -/
  nonneg : ∀ S, 0 ≤ w S
  /-- The weights sum to one over the coalitions containing each fixed player. -/
  sum_eq_one : ∀ i : Player, ∑ S ∈ Finset.univ.powerset.filter (fun S => i ∈ S), w S = 1

/-- The Bondareva–Shapley balancedness condition: For every balanced collection of weights, the
weighted sum of coalition values is at most the grand-coalition value. -/
def SatisfiesBalancedness (G : TUGameOn Player) : Prop :=
  ∀ w : Finset Player → ℝ, G.IsBalanced w →
    ∑ S ∈ Finset.univ.powerset, w S * G.value S ≤ G.value G.grandCoalition

/-- **Bondareva–Shapley theorem** (Bondareva 1963; Shapley 1967): The core is nonempty iff the game
satisfies balancedness. -/
theorem core_nonempty_iff_balanced (G : TUGameOn Player) :
    (∃ x : G.PayoffVector, G.IsCore x) ↔ G.SatisfiesBalancedness := by
  have hmain := coreFeasible_iff_satisfiesBalancedInequalities (α := Player) G.value
  have hcore : ∀ x, G.IsCore x ↔
      (G.IsEfficient x ∧ ∀ S : Finset Player, G.value S ≤ G.coalitionPayoff x S) :=
    fun x => ⟨fun h => ⟨h.efficient, h.coalitionRational⟩, fun h => ⟨h.1, h.2⟩⟩
  simpa [CoalitionCoreFeasible, SatisfiesBalancedInequalities, IsBalancedCollection, hcore,
    IsEfficient, coalitionPayoff, grandCoalition, SatisfiesBalancedness, isBalanced_iff] using hmain

end TUGameOn

end Econlib.GameTheory
