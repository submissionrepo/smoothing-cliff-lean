/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Equilibrium.Problem
public import Econlib.GameTheory.Strategic.Bayesian.Measurable.Game

/-!
# Bayesian Nash equilibrium for measure-theoretic Bayesian games

This file defines **Bayesian Nash equilibrium** (Harsanyi 1967–68) for `MeasBayesianGame` by
reusing the abstract `EquilibriumProblem` spine, as the finite stack does. The only
carrier-specific ingredient is the value functional, which here is the ex-ante integral
`exAntePayoff` rather than a finite sum.

## Main definitions

* `MeasBayesianGame.bnePred`: The equilibrium problem whose value is the ex-ante payoff.
* `MeasBayesianGame.IsBNE`: Bayesian Nash equilibrium.

## Main statements

* `MeasBayesianGame.isBNE_iff`: Unfolded best-response form of `IsBNE`.

## Notes

The `bnePred` deviator index is `Player`: A deviation rewrites a player's entire measurable
strategy function. A point-deviation at a single type is invisible to an integral over a non-atomic
prior, so deviating the whole strategy yields the ex-ante optimality condition, which is equivalent
to almost-everywhere interim best response (see `MeasBayesianGame.Interim`).

A deviation counts (lies in `swap`) only when its ex-ante payoff integrand is `Integrable`. A
non-integrable deviation has Bochner integral `0`, and admitting it would impose the spurious
constraint `exAntePayoff i s ≥ 0`; restricting to integrable deviations keeps the predicate sound.

## References

* Harsanyi, John C. 1968. “Games with Incomplete Information Played by 'Bayesian' Players, Parts
  I-Iii.” *Management Science* 14 : 159–82, 320–34, 486–502.

## Tags

bayesian games, continuous types, bayesian nash equilibrium, ex-ante payoff
-/

@[expose] public section

open MeasureTheory Function

noncomputable section
namespace Econlib.GameTheory

namespace MeasBayesianGame

variable (G : MeasBayesianGame)

/-- The equilibrium problem associated with (ex-ante) Bayesian Nash equilibrium. The deviator index
is a player; a legal deviation rewrites only that player's strategy function and keeps the payoff
integrand integrable; the value is the player's ex-ante expected payoff. -/
def bnePred (G : MeasBayesianGame) : EquilibriumProblem where
  S := G.Strategy
  I := G.Player
  swap := fun i s s' =>
    (∀ j, j ≠ i → s' j = s j) ∧
      Integrable (fun θ => G.payoff i (G.actionProfile s' θ) θ) G.prior
  value := fun i s => G.exAntePayoff i s

/-- **Bayesian Nash equilibrium** of a measure-theoretic Bayesian game: No player can raise its
ex-ante expected payoff by a unilateral (integrable) deviation of its measurable strategy, and the
incumbent profile's own payoff integrand is integrable for every player. -/
structure IsBNE (G : MeasBayesianGame) (s : G.Strategy) : Prop where
  /-- No player has a profitable unilateral integrable deviation. -/
  isEquilibrium : G.bnePred.IsEquilibrium s
  /-- The incumbent profile's payoff integrand is integrable for every player. -/
  integrable : ∀ i, Integrable (fun θ => G.payoff i (G.actionProfile s θ) θ) G.prior

@[simp] lemma bnePred_swap_iff (i : G.Player) (s s' : G.Strategy) :
    G.bnePred.swap i s s' ↔
      (∀ j, j ≠ i → s' j = s j) ∧
        Integrable (fun θ => G.payoff i (G.actionProfile s' θ) θ) G.prior := Iff.rfl

@[simp] lemma bnePred_value_eq (i : G.Player) (s : G.Strategy) :
    G.bnePred.value i s = G.exAntePayoff i s := rfl

/-- Unfolded characterization of `IsBNE`: For every player and every unilateral integrable
deviation, the equilibrium strategy yields at least as much ex-ante payoff (the best-response
condition), and the incumbent payoff integrand is integrable for every player. -/
theorem isBNE_iff (s : G.Strategy) :
    G.IsBNE s ↔
      (∀ (i : G.Player) (s' : G.Strategy), (∀ j, j ≠ i → s' j = s j) →
        Integrable (fun θ => G.payoff i (G.actionProfile s' θ) θ) G.prior →
          G.exAntePayoff i s ≥ G.exAntePayoff i s') ∧
      (∀ i, Integrable (fun θ => G.payoff i (G.actionProfile s θ) θ) G.prior) := by
  constructor
  · rintro ⟨h, hint⟩
    exact ⟨fun i s' hagree hintd => h i s' ⟨hagree, hintd⟩, hint⟩
  · rintro ⟨h, hint⟩
    exact ⟨fun i s' hs' => h i s' hs'.1 hs'.2, hint⟩

end MeasBayesianGame

end Econlib.GameTheory
end
