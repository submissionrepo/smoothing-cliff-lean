/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Rosenthal's Centipede Game

Rosenthal (1981) introduced the *centipede game* as a finite, perfect-information game whose unique
subgame-perfect equilibrium (SPE) is spectacularly Pareto-dominated by joint cooperation. The
paradox is that the SPE stops at *every* node — on and off the equilibrium path, so the game
terminates immediately at the root — even though both players strictly prefer the cooperative
outcome reached by *nobody ever* stopping. The example is widely cited as a stress test on the
behavioral plausibility of iterated backward induction; the broader literature (McKelvey–Palfrey
1992, Aumann 1995, Reny 1992) revisits whether SPE actually captures what rational players do here.

## The game

Two players, `0` and `1`, alternate moves over four "rounds". At each round the mover chooses one
of two actions, encoded as named abbreviations for elements of `Fin 2`:

* `stop = 0` — *Stop*, which terminates the game with an immediate payoff vector,
* `continue_ = 1` — *Continue*, which passes the move to the opponent at the next round (named
  `continue_` with a trailing underscore because `continue` is a reserved keyword).

Payoffs at each terminal node are listed below, with player 0's coordinate first. This is the
canonical Rosenthal calibration: At *every* decision node, on or off the equilibrium path, the
mover strictly prefers to stop given the opponent's subsequent SPE play, so backward induction
unwinds the game all the way back to the root, where the mover stops immediately.

| node            | mover | Stop payoff | Continue payoff (if next mover stops) |
| --------------- | ----- | ----------- | ------------------------------------- |
| round 1 (root)  | 0     | `(1, 0)`    | `(0, 2)`                              |
| round 2         | 1     | `(0, 2)`    | `(3, 1)`                              |
| round 3         | 0     | `(3, 1)`    | `(2, 4)`                              |
| round 4 (final) | 1     | `(2, 4)`    | `(3, 3)`                              |

The unique terminal node reached by always continuing is `(3, 3)`.

## Backward induction

Solving from the leaves:

* **Round 4** (mover 1): `Stop` yields `4`, `Continue` yields `3`. Player 1 prefers to stop. The
  round-4 subgame's SPE value is `(2, 4)`.
* **Round 3** (mover 0): `Stop` yields `3`, `Continue` (anticipating player 1 stopping at round 4)
  yields `2`. Player 0 prefers to stop. SPE value here is `(3, 1)`.
* **Round 2** (mover 1): `Stop` yields `2`, `Continue` (anticipating player 0 stopping at round 3)
  yields `1`. Player 1 prefers to stop. SPE value is `(0, 2)`.
* **Round 1** (mover 0, the root): `Stop` yields `1`, `Continue` (anticipating player 1 stopping at
  round 2) yields `0`. Player 0 prefers to stop. **The SPE outcome is `(1, 0)`.**

So at the SPE both players get the immediate `Stop`-at-root payoffs `(1, 0)`, while if the game ran
its full length they would receive `(3, 3)`. Both coordinates of `(1, 0)` are strictly worse than
`(3, 3)`: The SPE is strictly Pareto-dominated.

## Lean construction

We build the centipede game as a `FinitePerfectInfoTree (Fin 2) (Fin 2)` — two players, two choices
at every decision node — using nested `.decision` constructors with `.terminal` leaves. From the
resulting tree we obtain for free, via Econlib's perfect-information API:

* `centipede4.backwardInductionBehavioralStrategy` — the SPE strategy,
* `centipede4.backwardInductionValue : Fin 2 → ℝ` — the SPE payoff vector,
* `centipede4.toExtensiveGame.IsSubgamePerfectEquilibrium …` — the equilibrium property,
* `IsPerfectBayesianEquilibrium … { strategy := …, beliefs := trivialBeliefs …}` — the PBE
  refinement under the canonical perfect-information singleton beliefs.

## Main definitions and theorems

* `centipede4 : FinitePerfectInfoTree (Fin 2) (Fin 2)` — the four-round Rosenthal centipede tree.
* `centipede_backwardInduction_is_SPE` — `centipede4.backwardInductionBehavioralStrategy` is a
  subgame-perfect equilibrium.
* `centipede_SPE_value_player0` and `centipede_SPE_value_player1` — the SPE payoffs are `(1, 0)`.
* `centipede_SPE_root_stops` — backward induction's root choice is `stop`, so on the equilibrium
  path the game terminates immediately at the root and player 1 never moves.
* `centipede_pareto_dominated_by_full_cooperation_player0` and
  `centipede_pareto_dominated_by_full_cooperation_player1` — strict Pareto domination by the
  always-continue outcome `(3, 3)`: At the SPE every player is strictly worse off than under full
  cooperation.
* `centipede_backwardInduction_is_PBE` — the same strategy together with the trivial
  perfect-information beliefs forms a perfect Bayesian equilibrium.
* `centipede4_isGeneric` and `centipede_SPE_unique` — every backward-induction comparison is
  strict, so the backward-induction strategy is the **unique** subgame-perfect local strategy: No
  other local behavioral strategy, pure or mixed, is subgame perfect. This formalizes the "unique
  SPE" claim above.

## References

Rosenthal, Robert W. 1981. “Games of Perfect Information, Predatory Pricing and the Chain-Store
Paradox.” Journal of Economic Theory 25 (1): 92–100. https://doi.org/10.1016/0022-0531(81)90018-1.
-/

noncomputable section

namespace EconlibExamples.GameTheory.Centipede

open Econlib.GameTheory

/-! ## The Tree -/

-- The full game is built bottom-up from named subtrees `round4Tree`,
-- `round3Tree`, `round2Tree`, each playing the role of the "continue at
-- round k" subgame. The tree has depth four. Children are given
-- positionally as a `![stop-child, pass-child]` vector over the node's
-- `Fin 2` choices, and terminal payoffs as `![player0, player1]` vectors.

/-- The *Stop* action: Terminate the game at the current node with its immediate payoffs. -/
abbrev stop : Fin 2 := 0
/-- The *Continue* action: Pass the move to the opponent at the next round. -/
abbrev continue_ : Fin 2 := 1

/-- Round-4 subgame: Player 1 chooses between `stop` (payoffs `(2, 4)`) and `continue_` (the
full-cooperation payoffs `(3, 3)`). -/
def round4Tree : FinitePerfectInfoTree (Fin 2) (Fin 2) :=
  .decision 1 (Fin 2) (Function.Embedding.refl _) ![.terminal ![2, 4], .terminal ![3, 3]]

/-- Round-3 subgame: Player 0 chooses between `stop` (payoffs `(3, 1)`) and `pass` (entering
`round4Tree`). -/
def round3Tree : FinitePerfectInfoTree (Fin 2) (Fin 2) :=
  .decision 0 (Fin 2) (Function.Embedding.refl _) ![.terminal ![3, 1], round4Tree]

/-- Round-2 subgame: Player 1 chooses between `stop` (payoffs `(0, 2)`) and `pass` (entering
`round3Tree`). -/
def round2Tree : FinitePerfectInfoTree (Fin 2) (Fin 2) :=
  .decision 1 (Fin 2) (Function.Embedding.refl _) ![.terminal ![0, 2], round3Tree]

/-- The full four-round Rosenthal centipede tree. Player 0 at the root chooses between `stop`
(payoffs `(1, 0)`) and `pass` (entering `round2Tree`). -/
def centipede4 : FinitePerfectInfoTree (Fin 2) (Fin 2) :=
  .decision 0 (Fin 2) (Function.Embedding.refl _) ![.terminal ![1, 0], round2Tree]

/-! ## The Backward-Induction SPE -/

/-- **Backward induction yields a subgame-perfect equilibrium of the centipede.** This is a direct
invocation of Econlib's general theorem
`FinitePerfectInfoTree.isSubgamePerfectEquilibrium_backwardInduction`, which states that the
behavioral strategy obtained by recursively choosing each mover's best continuation in every
subgame is an SPE of the induced `ExtensiveGame`. No game-specific work is needed beyond having
built the tree. -/
theorem centipede_backwardInduction_is_SPE :
    centipede4.toExtensiveGame.IsSubgamePerfectEquilibrium
      centipede4.backwardInductionBehavioralStrategy :=
  centipede4.isSubgamePerfectEquilibrium_backwardInduction

/-! ## The SPE Payoffs Are (1, 0): Bottom-Up Backward-Induction Computation -/

-- We compute the backward-induction value at every level of the centipede
-- tree as a separate `private` lemma. At each decision node the mover's
-- `stop`/`pass` continuation values differ strictly, so the mover stops.

/-- **Round-4 SPE value** `(2, 4)`. Player 1 prefers `stop` (own payoff `4`) to `pass` (own payoff
`3`); the resulting terminal is `(2, 4)`. -/
lemma round4_value (i : Fin 2) :
    round4Tree.backwardInductionValue i = ![2, 4] i := by
  unfold round4Tree
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 0)
    (h := by bi_dominates)]
  norm_num

/-- **Round-3 SPE value** `(3, 1)`. Player 0 prefers `stop` (own payoff `3`) to `pass` (own payoff
`2`, taken from the round-4 SPE `(2, 4)`). -/
lemma round3_value (i : Fin 2) :
    round3Tree.backwardInductionValue i = ![3, 1] i := by
  unfold round3Tree
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 0)
    (h := by bi_dominates [round4_value])]
  norm_num

/-- **Round-2 SPE value** `(0, 2)`. Player 1 prefers `stop` (own payoff `2`) to `pass` (own payoff
`1`, taken from the round-3 SPE `(3, 1)`). -/
lemma round2_value (i : Fin 2) :
    round2Tree.backwardInductionValue i = ![0, 2] i := by
  unfold round2Tree
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 0)
    (h := by bi_dominates [round3_value])]
  norm_num

/-- **Whole-game SPE value** `(1, 0)`. Player 0 at the root prefers `Stop` (own payoff `1`) to
`Continue` (own payoff `0`, from round-2 SPE `(0, 2)`). -/
lemma centipede4_backwardInductionValue (i : Fin 2) :
    centipede4.backwardInductionValue i = ![1, 0] i := by
  unfold centipede4
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 0)
    (h := by bi_dominates [round2_value])]
  norm_num

/-- **Player 0's SPE payoff is `1`.** The backward induction unwinds:

* at round 4, player 1 strictly prefers `stop` (`4 > 3`),
* at round 3, anticipating that, player 0 strictly prefers `stop` (`3 > 2`),
* at round 2, anticipating that, player 1 strictly prefers `stop` (`2 > 1`),
* at the root, anticipating that, player 0 strictly prefers `stop` (`1 > 0`).

The SPE prescribes `Stop` at the root, terminating the game with player 0 receiving `1`. -/
theorem centipede_SPE_value_player0 :
    centipede4.backwardInductionValue 0 = 1 := by rw [centipede4_backwardInductionValue]; rfl

/-- **Player 1's SPE payoff is `0`.** Player 1 never gets to move on the SPE path: Player 0 stops
at the root, so the game terminates at the round-1 `Stop` payoff `(1, 0)`. This is the heart of the
centipede paradox — player 1 would gladly continue if given the chance. -/
theorem centipede_SPE_value_player1 :
    centipede4.backwardInductionValue 1 = 0 := by simp [centipede4_backwardInductionValue]

/-- **The SPE stops at the root.** Backward induction's root choice for player 0 is `stop`: Player
0 strictly prefers stopping (own payoff `1`) to continuing into round 2 (own payoff `0`, the
round-2 SPE value). So on the equilibrium path the game terminates immediately at the root and
player 1 never gets to move — the formal content of the prose "player 1 never moves on the SPE
path". -/
theorem centipede_SPE_root_stops :
    centipede4.backwardInductionRootChoice = stop := by
  unfold centipede4 FinitePerfectInfoTree.backwardInductionRootChoice
  refine FinitePerfectInfoTree.bestChoice_eq_of_strictArgmax (Fin 2) _ 0 ?_
  bi_dominates [round2_value]

/-! ## The Full-Cooperation Outcome and Pareto Domination -/

/-- **Player 0 is strictly better off under full cooperation.** The "continue forever" terminal
node has player 0 payoff `3`, while the SPE delivers `1`. -/
theorem centipede_pareto_dominated_by_full_cooperation_player0 :
    centipede4.backwardInductionValue 0 < 3 := by rw [centipede_SPE_value_player0]; norm_num

/-- **Player 1 is strictly better off under full cooperation.** The "continue forever" terminal
node has player 1 payoff `3`, while the SPE delivers `0`. Player 1's gain from full cooperation
over the SPE is `3`, the more lopsided coordinate of the Pareto comparison. -/
theorem centipede_pareto_dominated_by_full_cooperation_player1 :
    centipede4.backwardInductionValue 1 < 3 := by rw [centipede_SPE_value_player1]; norm_num

/-- **The centipede paradox, stated once.** Both players are strictly worse off at the SPE than at
the full-cooperation terminal `(3, 3)`. This is the sense in which the unique SPE of the centipede
is *Pareto-dominated* by the non-equilibrium "trust the opponent" outcome, and the central reason
the game is held up as a tension between iterated rationality and welfare. -/
theorem centipede_SPE_pareto_dominated :
    centipede4.backwardInductionValue 0 < 3 ∧
      centipede4.backwardInductionValue 1 < 3 :=
  ⟨centipede_pareto_dominated_by_full_cooperation_player0,
    centipede_pareto_dominated_by_full_cooperation_player1⟩

/-! ## PBE Refinement Under Trivial Perfect-Information Beliefs -/

/-- **The backward-induction strategy is a perfect Bayesian equilibrium** under the canonical
perfect-information singleton beliefs. Because every information set in the centipede is a
singleton (perfect information), the Bayes-consistency condition is trivial, so this backward-
induction SPE strategy together with the trivial beliefs is also a PBE; the appropriate beliefs are
produced by `trivialBeliefs`. This is a direct invocation of Econlib's general PBE theorem
`FinitePerfectInfoTree.isPerfectBayesianEquilibrium_backwardInduction`. -/
theorem centipede_backwardInduction_is_PBE :
    IsPerfectBayesianEquilibrium
      centipede4.toExtensiveGame
      { strategy := centipede4.backwardInductionBehavioralStrategy
        beliefs := trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree } :=
  centipede4.isPerfectBayesianEquilibrium_backwardInduction

/-! ## Uniqueness of the SPE -/

/-- **Round 4 is generic.** Player 1's two continuation values are `4` (stop) and `3` (pass), which
differ; both arms are terminals. -/
private lemma round4Tree_isGeneric : round4Tree.IsGeneric := by
  unfold round4Tree
  bi_generic <;> exact FinitePerfectInfoTree.isGeneric_terminal _

/-- **Round 3 is generic.** Player 0's two continuation values are `3` (stop) and `2` (pass, the
round-4 SPE value), which differ; the pass child `round4Tree` is also generic. -/
private lemma round3Tree_isGeneric : round3Tree.IsGeneric := by
  unfold round3Tree
  bi_generic [round4_value]
  · exact FinitePerfectInfoTree.isGeneric_terminal _
  · exact round4Tree_isGeneric

/-- **Round 2 is generic.** Player 1's two continuation values are `2` (stop) and `1` (pass, the
round-3 SPE value), which differ; the pass child `round3Tree` is also generic. -/
private lemma round2Tree_isGeneric : round2Tree.IsGeneric := by
  unfold round2Tree
  bi_generic [round3_value]
  · exact FinitePerfectInfoTree.isGeneric_terminal _
  · exact round3Tree_isGeneric

/-- **The centipede is generic**: At each of the four decision nodes the mover's two
backward-induction continuation values differ (`4 ≠ 3`, `3 ≠ 2`, `2 ≠ 1`, `1 ≠ 0`), so no mover is
ever indifferent. This is the hypothesis under which backward induction yields the unique SPE. -/
theorem centipede4_isGeneric : centipede4.IsGeneric := by
  unfold centipede4
  bi_generic [round2_value]
  · exact FinitePerfectInfoTree.isGeneric_terminal _
  · exact round2Tree_isGeneric

/-- **The centipede's SPE is unique.** Every subgame-perfect local strategy — pure or mixed
(`LocalBehavioralStrategy` assigns a mixed action at every node) — equals the backward-induction
strategy. Every comparison in the backward induction is strict, so no SPE can mix or choose
differently at any node. -/
theorem centipede_SPE_unique (s : centipede4.LocalBehavioralStrategy)
    (hs : centipede4.IsSubgamePerfectStrategy s) :
    s = centipede4.backwardInductionStrategy :=
  hs.eq_backwardInductionStrategy centipede4_isGeneric

/-- Uniqueness in the flat extensive-game form: Any local strategy whose canonical embedding is an
SPE of `centipede4.toExtensiveGame` is the backward-induction strategy. -/
theorem centipede_SPE_unique_extensive (s : centipede4.LocalBehavioralStrategy)
    (hs : centipede4.toExtensiveGame.IsSubgamePerfectEquilibrium
      (FinitePerfectInfoTree.LocalBehavioralStrategy.toBehavioralStrategy centipede4 s)) :
    s = centipede4.backwardInductionStrategy :=
  FinitePerfectInfoTree.eq_backwardInductionStrategy_of_isSubgamePerfectEquilibrium
    centipede4_isGeneric hs

end EconlibExamples.GameTheory.Centipede

end
