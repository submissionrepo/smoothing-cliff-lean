/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Rubinstein (1982) Alternating Offers — finite-horizon discretized variant

In Rubinstein's classical model two players bargain over a unit pie by alternating offers in
continuous time. With patient enough players and a continuum of feasible splits, backward induction
(the limiting argument on a finite horizon) selects a unique subgame-perfect equilibrium (SPE) in
which the *first proposer extracts a strictly greater share than half* — the famous **proposer
advantage** — and agreement is reached **immediately**, with no costly delay even though delay is
feasible.

This file gives a finite, fully formal worked example of the same two phenomena. Econlib does not
yet provide a continuous-action extensive-form, so we cannot encode Rubinstein's original continuum
of offers. Instead we exhibit a small *discretized* alternating-offers game and prove both
qualitative results — proposer advantage and immediate agreement — on it. Two things depart from the
textbook model: the discretized (binary) offer set, and the *collapsed* second round described below
(we fix the round-2 continuation rather than expand it into a full proposal stage). Everything
downstream (backward induction, SPE, continuation values) is the same machinery the full Econlib
game-theory library provides.

## The game

The pie is normalized to size `1`. The common discount factor is `δ = 1/3`. Two players alternate
offers over **two rounds**:

* **Round 1.** Player 0 picks one of two offers (its share for itself): The *fair* offer `s = 1/2`,
  or the *greedy* offer `s = 5/8`. Player 1 then **accepts** (terminal payoff `(s, 1 - s)`) or
  **rejects**, in which case we move to round 2.
* **Round 2 (collapsed).** Rather than introducing a second full proposal stage, we collapse round
  2 to a fixed continuation: If play reaches round 2, player 1 is allowed to take the entire pie
  (their take-it-or-leave-it offer is `0` to player 0). Because the round-2 payoff is realized *one
  period late*, both shares are discounted by `δ`. The round-2 terminal payoff is therefore
  `(0, δ) = (0, 1/3)`.

Compared to a fully-expanded second round with player-0 acceptance, this collapsing keeps the tree
shallow (three decision levels) without changing the qualitative analysis: In the expanded version
player 0 would accept any non-negative offer at round 2, so player 1 optimally demands the whole
pie, giving the same continuation `(0, δ)`. The cost is mild realism — we sidestep player 0's
round-2 acceptance choice — but it makes the backward-induction calculation a one-page proof by
`simp`.

## The discretization gap

Two facts depend on the discretization choice:

* The actual SPE share `5/8` and the strict gap `5/8 - 1/2 = 1/8` are artifacts of the binary offer
  set `{1/2, 5/8}`. With a finer grid, player 0's optimum would shift toward the largest feasible
  share that still leaves player 1 strictly above their reservation share `δ = 1/3` — i.e. toward
  `(1 - δ) - ε = 2/3 - ε` from below (any share strictly above `2/3` is rejected; at exactly `2/3`
  player 1 is indifferent and the prose assumes the standard "reject when indifferent" tie-break,
  leaving player 0 the round-2 continuation `0`). In the continuous Rubinstein model — where
  both rounds are
  full proposal stages, unlike this file's collapsed round 2 — the limit share is `1 / (1 + δ)`.
* The threshold offer `5/8 = 0.625` was chosen so that player 1's accept share `1 - 5/8 = 3/8`
  *strictly* exceeds the rejection value `δ · 0 + δ · 1 = 1/3`. With a different discretization
  player 1 might be exactly indifferent at the greedy offer; here we get a clean strict comparison
  and avoid relying on backward-induction tie-breaks.

## Main definitions and theorems

* `rubinstein2 : FinitePerfectInfoTree (Fin 2) (Fin 2)` — the three-level alternating-offers tree
  described above.
* `rubinstein_backwardInduction_is_SPE` — the backward-induction strategy is a subgame-perfect
  equilibrium of `rubinstein2.toExtensiveGame`.
* `rubinstein_SPE_proposer_advantage` — player 0's SPE payoff equals `5/8`, hence strictly exceeds
  `1/2`: The proposer extracts strictly more than half the pie.
* `rubinstein_SPE_player1_value` — player 1's SPE payoff equals `3/8`, the residual share.
* `rubinstein_no_delay` — agreement is reached in round 1: The sum of SPE payoffs is exactly the
  pie size `1`, ruling out the deadweight loss that any round-2 path `(0, δ) + 0` would entail
  (`1/3 < 1`).

## References

Rubinstein, Ariel. 1982. “Perfect Equilibrium in a Bargaining Model.” Econometrica 50 (1): 97.
https://doi.org/10.2307/1912531.
-/

noncomputable section

namespace EconlibExamples.GameTheory.Rubinstein

open Econlib.GameTheory

/-! ## The Bargaining Tree -/

/-- The common discount factor `δ = 1/3`. Chosen so that player 1's rejection value (the discounted
round-2 outcome `δ · 1 = 1/3`) is strictly below the *greedy* round-1 offer's share for player 1
(`1 - 5/8 = 3/8`), yielding a strict backward-induction comparison without tie-breaking. -/
abbrev δ : ℝ := 1 / 3

/-- The two **round-1 offers** by player 0, indexed by `Fin 2`:

* `0 = fair`  — player 0 keeps `1/2`, player 1 receives `1/2`,
* `1 = greedy` — player 0 keeps `5/8`, player 1 receives `3/8`.

The `proposerShare` function returns player 0's share `s` under each offer; player 1's share at
acceptance is then `1 - s`. -/
def proposerShare : Fin 2 → ℝ
  | 0 => 1 / 2
  | 1 => 5 / 8

/-- Player 1's two **round-1 responses**, indexed by `Fin 2`:

* `0 = accept` — terminal node, players split `(s, 1 - s)` immediately,
* `1 = reject` — move on to the (collapsed) round-2 continuation node. -/
abbrev accept : Fin 2 := 0

/-- The round-2 collapsed continuation as a terminal payoff. If round 1 ends in rejection, play
proceeds to round 2; here we collapse player 1's round-2 demand to "player 1 takes the whole pie".
Both payoffs are realized one period late and are therefore discounted by `δ`: Player 0 receives
`δ · 0 = 0` and player 1 receives `δ · 1 = δ = 1/3`. -/
def round2Payoff : Fin 2 → ℝ
  | 0 => 0
  | _ => δ

/-- The terminal payoffs under **acceptance** of round-1 offer `s` (indexed by `Fin 2`). Player 0
gets `proposerShare s` and player 1 gets the complementary share `1 - proposerShare s`. -/
def acceptPayoff (s : Fin 2) : Fin 2 → ℝ
  | 0 => proposerShare s
  | _ => 1 - proposerShare s

/-- **The bargaining game.** A three-level perfect-information tree. Player 0 picks one of two
offers; player 1 accepts (terminal with the chosen split) or rejects (terminal with the collapsed
round-2 continuation). Both decision nodes use the binary choice type `Fin 2` and emit themselves
as events via `Function.Embedding.refl _`. The response node's children are given positionally as
an `![accept-child, reject-child]` vector; the offer-level children stay a lambda because they
depend on the chosen offer. -/
def rubinstein2 : FinitePerfectInfoTree (Fin 2) (Fin 2) :=
  .decision 0 (Fin 2) (Function.Embedding.refl _) fun offer =>
    .decision 1 (Fin 2) (Function.Embedding.refl _)
      ![.terminal (acceptPayoff offer), .terminal round2Payoff]

/-! ## Subgame Perfection by Backward Induction -/

/-- **Subgame-perfect equilibrium.** The backward-induction behavioral strategy on `rubinstein2` is
a subgame-perfect equilibrium of the underlying extensive game. This is a direct instance of the
general theorem `FinitePerfectInfoTree.isSubgamePerfectEquilibrium_backwardInduction`. -/
theorem rubinstein_backwardInduction_is_SPE :
    rubinstein2.toExtensiveGame.IsSubgamePerfectEquilibrium
      rubinstein2.backwardInductionBehavioralStrategy :=
  rubinstein2.isSubgamePerfectEquilibrium_backwardInduction

/-! ## Backward-Induction Value: Proposer Advantage and Immediate Agreement -/

/-- **Backward-induction value at a round-1 response node**, parameterised by the round-1 offer.
Both players' continuation values are determined once we know player 1 strictly prefers accepting
(player-1 share `1 - s`) to rejecting (continuation `δ`).

This packages the level-2 backward-induction step into a single equation that the top-level proof
can `rw` with. We index by `i : Fin 2` and return `acceptPayoff offer i`. -/
private lemma value_at_response (offer : Fin 2) (i : Fin 2)
    (h_p1 : δ < 1 - proposerShare offer) :
    (FinitePerfectInfoTree.decision 1 (Fin 2) (Function.Embedding.refl _)
      ![.terminal (acceptPayoff offer),
        .terminal round2Payoff]).backwardInductionValue i
      = acceptPayoff offer i := by
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 0)
    (h := by bi_dominates)]
  rfl

/-- **Backward-induction value of the whole game**: The greedy offer, accepted. At the root player
0 compares the fair offer (accepted, share `1/2`) with the greedy offer (accepted, share `5/8`) and
strictly prefers greedy; both response nodes collapse by `value_at_response` since under either
offer player 1 strictly prefers accepting to the continuation `δ = 1/3` (fair: `1/3 < 1/2`; greedy:
`1/3 < 3/8`). -/
private lemma rubinstein2_backwardInductionValue (i : Fin 2) :
    rubinstein2.backwardInductionValue i = acceptPayoff 1 i := by
  unfold rubinstein2
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 1)]
  · -- The chosen child is the greedy-offer response node; collapse it at the readout `i`.
    exact value_at_response 1 i (by norm_num [proposerShare, δ])
  · -- Player 0's root comparison after collapsing both response nodes: `1/2 < 5/8`.
    intro c hc
    fin_cases c
    · change
        (FinitePerfectInfoTree.decision 1 (Fin 2) (Function.Embedding.refl _)
            ![.terminal (acceptPayoff 0), .terminal round2Payoff]).backwardInductionValue 0 <
          (FinitePerfectInfoTree.decision 1 (Fin 2) (Function.Embedding.refl _)
            ![.terminal (acceptPayoff 1), .terminal round2Payoff]).backwardInductionValue 0
      rw [value_at_response 0 0 (by norm_num [proposerShare, δ]),
        value_at_response 1 0 (by norm_num [proposerShare, δ])]
      norm_num [acceptPayoff, proposerShare]
    · exact absurd rfl hc

/-- **Proposer advantage.** Under the discretization `{1/2, 5/8}` and discount factor `δ = 1/3`,
the backward-induction value to player 0 (the round-1 proposer) is exactly `5/8`. In particular it
strictly exceeds `1/2`: The proposer captures a strictly greater share than half of the pie.

*Backward-induction calculation.* At the round-1 response node under the *greedy* offer `5/8`,
player 1 compares acceptance (share `3/8`) with rejection (continuation share `δ = 1/3`) and
chooses acceptance, since `3/8 > 1/3`. Under the *fair* offer `1/2`, player 1 also accepts, getting
`1/2`. Player 0 therefore compares `5/8` (greedy → accepted) with `1/2` (fair → accepted) and picks
the greedy offer, yielding final share `5/8`. -/
theorem rubinstein_SPE_proposer_advantage :
    rubinstein2.backwardInductionValue 0 = 5 / 8 := by
  rw [rubinstein2_backwardInductionValue]; rfl

/-- Player 0's SPE share strictly exceeds half. -/
theorem rubinstein_proposer_share_gt_half :
    rubinstein2.backwardInductionValue 0 > 1 / 2 := by
  rw [rubinstein_SPE_proposer_advantage]; norm_num

/-- **Player 1's SPE payoff.** Player 1 receives `3/8`, the residual share `1 - 5/8` from accepting
player 0's greedy offer in round 1. -/
theorem rubinstein_SPE_player1_value :
    rubinstein2.backwardInductionValue 1 = 3 / 8 := by
  rw [rubinstein2_backwardInductionValue]
  norm_num [acceptPayoff, proposerShare]

/-- **No delay.** Agreement is reached in round 1: The players' SPE payoffs sum to exactly the pie
size `1`, ruling out the deadweight loss that any round-2 outcome would entail. (If play reached
round 2, total surplus would be `0 + δ = 1/3 < 1`.) -/
theorem rubinstein_no_delay :
    rubinstein2.backwardInductionValue 0 + rubinstein2.backwardInductionValue 1 = 1 := by
  rw [rubinstein_SPE_proposer_advantage, rubinstein_SPE_player1_value]; norm_num

end EconlibExamples.GameTheory.Rubinstein

end
