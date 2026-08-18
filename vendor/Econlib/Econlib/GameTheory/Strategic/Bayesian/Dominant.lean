/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Bayesian.PureBNE

/-!
# Dominant-strategy equilibrium

A pure strategy profile is a **weakly dominant-strategy equilibrium** if, for every player, every
realized type profile, and every profile of the opponents' actions, the prescribed action is a best
response. This is the ex-post, prior-free sibling of `IsBNE`: It compares payoffs at realized types
against arbitrary opponent actions, with no expectation over opponents' types. Under private values
it coincides with the ex-post equilibrium notion.

It is the canonical antecedent for dominant-strategy incentive compatibility in mechanism design —
quantifying over arbitrary opponent actions captures "truth is optimal even when others misreport."

## Main definitions

* `FinBayesianGame.IsDominantStrategy`: Weakly dominant-strategy equilibrium.

## Main statements

* `FinBayesianGame.IsDominantStrategy.isBNE`: A dominant strategy is a Bayes–Nash equilibrium.

## References

* Harsanyi, John C. 1968. “Games with Incomplete Information Played by 'Bayesian' Players, Parts
  I-Iii.” *Management Science* 14 : 159–82, 320–34, 486–502.

## Tags

bayesian games, dominant strategy, ex-post equilibrium
-/

@[expose] public section

open Function BigOperators

noncomputable section
namespace Econlib.GameTheory

namespace FinBayesianGame

variable (G : FinBayesianGame)

/-- A pure strategy profile is a **weakly dominant-strategy equilibrium**: For every player `i`,
every realized type profile `θ`, every profile of the opponents' actions `a`, and every alternative
action `a_i`, the prescribed action `s i (θ i)` does at least as well. Ex-post and prior-free —
there is no conditioning on type marginals (contrast `IsBNE`, an interim/expected best response).
Under private values this is exactly the ex-post equilibrium notion. -/
def IsDominantStrategy (s : G.PureStrategy) : Prop :=
  ∀ (i : G.Player) (θ : G.TypeProfile) (a : G.ActionProfile) (a_i : G.Action i),
    G.payoff i (Function.update a i a_i) θ
      ≤ G.payoff i (Function.update a i (s i (θ i))) θ

/-- A weakly dominant strategy is a Bayes–Nash equilibrium: The ex-post best-response inequality at
realized types implies the interim best-response condition under the prior conditional. -/
theorem IsDominantStrategy.isBNE {s : G.PureStrategy} (h : G.IsDominantStrategy s) : G.IsBNE s := by
  rw [IsBNE_iff]
  intro i θ_i _hpos a_i
  rw [ge_iff_le, interimPayoffAction, interimPayoffAction]
  refine Finset.sum_le_sum fun θ hθ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  refine mul_le_mul_of_nonneg_left ?_ (G.prior.condProbD_nonneg i θ_i θ)
  have hdom := h i θ (G.actionProfile s θ) a_i
  rwa [hθ] at hdom

end FinBayesianGame

end Econlib.GameTheory
end
