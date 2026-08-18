/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Stackelberg Quantity Leadership — finite-grid discretized variant

In the Stackelberg (1934) duopoly model a *leader* firm commits to a quantity, a *follower*
observes it and best-responds, and the market price clears a linear inverse demand. The classic
results: The leader produces more than in the simultaneous (Cournot) benchmark, the follower
produces less, and the leader earns strictly higher profit — the **first-mover advantage**.

This file gives a finite, fully formal worked example of the first-mover advantage. As with the
`Rubinstein` example, Econlib does not yet provide continuous-action extensive forms, so the
quantity continuum is discretized to a small grid; everything downstream (backward induction,
subgame perfection, genericity, uniqueness) is the general Econlib machinery.

The example is deliberately the library's first **ternary** (`Fin 3`) perfect-information tree:
Every decision node offers three quantity choices, so none of the binary (`Fin 2`) evaluation sugar
applies and the proofs exercise the *general* lemmas
(`backwardInductionValue_decision_eq_of_strictArgmax`, `isGeneric_decision`) directly.

## The game

Inverse demand is `P = 12 − (q₁ + q₂)`; both firms produce at zero cost, so firm `i`'s profit is
`(12 − q₁ − q₂) · qᵢ`.

* **Stage 1.** The leader (player `0`) picks `q₁` from the grid `{2, 4, 7}`.
* **Stage 2.** The follower (player `1`) observes `q₁` and picks `q₂` from the grid `{2, 4, 5}`.

The follower's profits at each subgame, `(12 − q₁ − q₂) q₂` by column:

| `q₁` \ `q₂` | `2`  | `4`  | `5`  | best response |
| ----------- | ---- | ---- | ---- | ------------- |
| `2`         | `16` | `24` | `25` | `5`           |
| `4`         | `12` | `16` | `15` | `4`           |
| `7`         | `6`  | `4`  | `0`  | `2`           |

The follower's best response **slopes down** with the leader's quantity — `5, 4, 2` as `q₁` runs
`2, 4, 7` — so the grid captures the downward-sloping reaction function that makes
commitment bite. Anticipating it, the leader compares own profits `(12 − q₁ − q₂*(q₁)) q₁`: `10` at
`q₁ = 2` (against `q₂ = 5`), `16` at `q₁ = 4` (against `q₂ = 4`), `21` at `q₁ = 7` (against
`q₂ = 2`), and strictly prefers `q₁ = 7`. **The SPE outcome is `(q₁, q₂) = (7, 2)` with profits
`(21, 6)`.**

## First-mover advantage and the Cournot benchmark

To state the first-mover advantage precisely we formalize the *simultaneous* (Cournot) game on the
same grids as a `FiniteStrategicGame` (`cournotGame`) and prove — not merely assert — its
equilibrium. The leader's grid choice `q₁ = 4` is its **strictly dominant action** there
(`cournot_leader_strictly_dominant`): For each follower quantity the leader's static profit is
maximized at `q₁ = 4`. The follower's best response to `q₁ = 4` is `q₂ = 4`
(`cournot_follower_best_response`), so `(4, 4)` is the **unique** pure Nash profile
(`cournot_nashProfile_is_nash`, `cournot_nash_unique`) with profits `(16, 16)`
(`cournot_leader_nash_payoff`, `cournot_follower_nash_payoff`) — the Cournot benchmark.

Committing to `q₁ = 4` and letting the follower reply reproduces exactly this Cournot payoff `16`,
which is the backward-induction value of the `q₁ = 4` subtree
(`cournot_leader_payoff_eq_commitment` bridges the two). Moving first lets the leader instead
commit to `q₁ = 7`, dragging the follower down to `q₂ = 2`, and earn `21 > 16`
(`stackelberg_first_mover_advantage`). That strict gap is the first-mover advantage — the value
of commitment — and it has real bite here precisely because the follower's reaction is not flat.
The flip side: The follower earns `6 < 16` (`stackelberg_follower_accommodation`), strictly worse
than under simultaneous play, because it is forced to accommodate.

The classic Stackelberg signs hold in *quantities* too, read off the equilibrium root choices: The
leader expands (`q₁ = 7 > 4`, `stackelberg_leader_expands`) and the follower contracts
(`q₂ = 2 < 4`, `stackelberg_follower_contracts`) relative to the Cournot profile `(4, 4)`.

## The discretization gap

The exact numbers are grid artifacts. In the underlying *continuous* model — which this file does
not formalize, and which is stated here only to motivate the calibration — inverse demand
`P = 12 − Q` gives a Stackelberg SPE of `q₁ = 6, q₂ = 3` with profits `(18, 9)` and a Cournot
equilibrium of `q = 4` each with profit `16` each. Our grids bracket these: The leader grid
`{2, 4, 7}` straddles the continuous Stackelberg quantity `6`, and the follower grid `{2, 4, 5}` is
chosen so the follower's grid best response `(5, 4, 2)` — proved in `followerNode_value_2/4/7` —
tracks the continuous reaction `(12 − q₁)/2` evaluated at the leader's grid points (`5, 4, 2.5`).
The grids are deliberately *asymmetric*: A grid containing a pair symmetric about a profit vertex
would tie a mover's values and break genericity (uniqueness needs every comparison strict).

## Main definitions and theorems

* `stackelberg3 : FinitePerfectInfoTree (Fin 2) (Fin 3)` — the two-stage (sequential) quantity game.
* `stackelberg_backwardInduction_is_SPE` — backward induction is subgame perfect.
* `stackelberg_SPE_leader_profit` / `stackelberg_SPE_follower_profit` — SPE profits `(21, 6)`.
* `cournotGame : FiniteStrategicGame` — the *simultaneous* (Cournot) game on the same grids, with:
  `cournot_leader_strictly_dominant` (the leader's `q₁ = 4` strictly dominates),
  `cournot_follower_best_response` (the follower replies `q₂ = 4` to `q₁ = 4`),
  `cournot_nashProfile_is_nash` + `cournot_nash_unique` (`(4, 4)` is the unique pure Nash), and
  `cournot_leader_nash_payoff` / `cournot_follower_nash_payoff` (payoffs `(16, 16)`).
* `cournot_leader_payoff_eq_commitment` — the bridge: The leader's Cournot-Nash payoff equals the
  backward-induction value of committing to `q₁ = 4` in the tree.
* `stackelberg_first_mover_advantage` — the leader's SPE payoff strictly exceeds its simultaneous-
  game Nash payoff: The value of moving first.
* `stackelberg_follower_accommodation` — the mirror image: The follower's SPE payoff is strictly
  below its simultaneous-game Nash payoff, the cost of being forced to accommodate.
* `stackelberg_SPE_leader_choice` / `stackelberg_SPE_follower_choice` and
  `stackelberg_leader_expands` / `stackelberg_follower_contracts` — the equilibrium quantities
  (`q₁ = 7`, `q₂ = 2`) and the Stackelberg quantity signs (leader expands, follower contracts).
* `stackelberg3_isGeneric` and `stackelberg_SPE_unique` — every backward-induction comparison is
  strict, so the backward-induction strategy is the unique subgame-perfect local strategy.

## References

* Leontief, Wassily. 1936. “Stackelberg on Monopolistic Competition.” Journal of Political Economy
  44 (4): 554–59. https://doi.org/10.1086/254962.
* Stackelberg, Heinrich von. 1934. Marktform Und Gleichgewicht. Julius Springer.
-/

noncomputable section

namespace EconlibExamples.GameTheory.Stackelberg

open Econlib.GameTheory

/-! ## The Game Tree -/

/-- Market profits at quantity profile `(q₁, q₂)` under inverse demand `P = 12 − (q₁ + q₂)` and
zero costs: Firm `i` earns `P · qᵢ`. Player `0` is the leader, player `1` the follower. -/
def profits (q₁ q₂ : ℝ) : Fin 2 → ℝ :=
  ![(12 - q₁ - q₂) * q₁, (12 - q₁ - q₂) * q₂]

/-- The leader's quantity grid `{2, 4, 7}`, indexed by `Fin 3` (the same grid the extensive-form
tree commits to at stage 1). -/
def leaderQ : Fin 3 → ℝ := ![2, 4, 7]

/-- The follower's quantity grid `{2, 4, 5}`, indexed by `Fin 3` (the same grid the follower
replies from at every stage-2 subgame). -/
def followerQ : Fin 3 → ℝ := ![2, 4, 5]

/-- Stage-2 subgame after the leader commits to `q₁`: The follower picks `q₂` from the grid
`{2, 4, 5}` (choices `0, 1, 2`), each landing on the terminal profit vector. -/
def followerNode (q₁ : ℝ) : FinitePerfectInfoTree (Fin 2) (Fin 3) :=
  .decision 1 (Fin 3) (Function.Embedding.refl _)
    ![.terminal (profits q₁ 2), .terminal (profits q₁ 4), .terminal (profits q₁ 5)]

/-- **The Stackelberg game.** The leader picks `q₁` from the grid `{2, 4, 7}` (choices `0, 1, 2`);
the follower observes and replies from its own grid. -/
def stackelberg3 : FinitePerfectInfoTree (Fin 2) (Fin 3) :=
  .decision 0 (Fin 3) (Function.Embedding.refl _)
    ![followerNode 2, followerNode 4, followerNode 7]

/-! ## Subgame Perfection by Backward Induction -/

/-- **Subgame-perfect equilibrium.** The backward-induction behavioral strategy is an SPE of the
underlying extensive game — a direct instance of the general theorem, no game-specific work
needed. -/
theorem stackelberg_backwardInduction_is_SPE :
    stackelberg3.toExtensiveGame.IsSubgamePerfectEquilibrium
      stackelberg3.backwardInductionBehavioralStrategy :=
  stackelberg3.isSubgamePerfectEquilibrium_backwardInduction

/-! ## Backward-Induction Values

With three choices per node, the binary collapse lemmas do not apply; each node collapses via
the general `backwardInductionValue_decision_eq_of_strictArgmax`, whose side goal quantifies over
the non-argmax choices and is discharged by `fin_cases`.

The follower's best response now *varies* with the leader's quantity — `q₂ = 5, 4, 2` at
`q₁ = 2, 4, 7` — so unlike the Rubinstein-style constant-reply examples each stage-2 subgame
collapses to a *different* child. We record one value lemma per leader grid point. -/

/-- **Stage-2 value at `q₁ = 2`: The follower replies `q₂ = 5`.** Profits `16, 24, 25` on the
follower grid; choice `2` is the strict argmax. -/
private lemma followerNode_value_2 (i : Fin 2) :
    (followerNode 2).backwardInductionValue i = profits 2 5 i := by
  unfold followerNode
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 2)
    (h := by bi_dominates [profits])]
  rfl

/-- **Stage-2 value at `q₁ = 4`: The follower replies `q₂ = 4`.** Profits `12, 16, 15`; choice `1`
is the strict argmax. This is the Cournot subgame — `(4, 4)` is the simultaneous-game Nash. -/
private lemma followerNode_value_4 (i : Fin 2) :
    (followerNode 4).backwardInductionValue i = profits 4 4 i := by
  unfold followerNode
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 1)
    (h := by bi_dominates [profits])]
  rfl

/-- **Stage-2 value at `q₁ = 7`: The follower replies `q₂ = 2`.** Profits `6, 4, 0`; choice `0` is
the strict argmax — the follower accommodates the leader's large commitment. -/
private lemma followerNode_value_7 (i : Fin 2) :
    (followerNode 7).backwardInductionValue i = profits 7 2 i := by
  unfold followerNode
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 0)
    (h := by bi_dominates [profits])]
  rfl

/-- **Whole-game value: The SPE outcome is `(q₁, q₂) = (7, 2)`.** The leader's three continuation
profits are `10, 16, 21`; choice `2` (`q₁ = 7`) is the strict argmax. -/
private lemma stackelberg3_value (i : Fin 2) :
    stackelberg3.backwardInductionValue i = profits 7 2 i := by
  unfold stackelberg3
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 2)
    (h := by bi_dominates [followerNode_value_2, followerNode_value_4, followerNode_value_7,
      profits])]
  exact followerNode_value_7 i

/-- **The leader's SPE profit is `21`** — realized at the committed quantity `q₁ = 7` against the
follower's reply `q₂ = 2` (price `12 − 9 = 3`). -/
theorem stackelberg_SPE_leader_profit :
    stackelberg3.backwardInductionValue 0 = 21 := by
  rw [stackelberg3_value]; norm_num [profits]

/-- **The follower's SPE profit is `6`** — the follower sells `q₂ = 2` at the price `3` set by the
leader's commitment. -/
theorem stackelberg_SPE_follower_profit :
    stackelberg3.backwardInductionValue 1 = 6 := by
  rw [stackelberg3_value]; norm_num [profits]

/-- **The leader's Cournot benchmark profit is `16`** — committing to its dominant static quantity
`q₁ = 4` and letting the follower best-respond (`q₂ = 4`) reproduces the simultaneous-game Nash
`(4, 4)`. This is the backward-induction value of the `q₁ = 4` subtree. -/
theorem stackelberg_cournot_leader_profit :
    (followerNode 4).backwardInductionValue 0 = 16 := by
  rw [followerNode_value_4]; norm_num [profits]

/-- **The follower's Cournot benchmark profit is `16`** — its payoff at the simultaneous-game Nash
`(4, 4)`. -/
theorem stackelberg_cournot_follower_profit :
    (followerNode 4).backwardInductionValue 1 = 16 := by
  rw [followerNode_value_4]; norm_num [profits]

/-! ## The Simultaneous (Cournot) Benchmark

To make the first-mover advantage precise we formalize the *simultaneous* game on the same two
grids — the game the firms would play if the follower could not observe the leader's quantity. It
is a two-player `FiniteStrategicGame` whose payoffs reuse the same `profits` function. We prove the
leader has a strictly dominant action `q₁ = 4`, the unique pure Nash equilibrium is `(4, 4)` with
payoffs `(16, 16)`, and — the bridge — that this Cournot payoff equals the backward-induction value
of committing to `q₁ = 4` in the tree. The first-mover advantage is then the strict gap between the
SPE payoff and this simultaneous-game Nash payoff. -/

/-- **The simultaneous Cournot game.** Both firms pick a grid index in `Fin 3` *at the same time*;
player `0` (leader) reads off `leaderQ`, player `1` (follower) reads off `followerQ`, and payoffs
are the same `profits` as in the tree. Built with `mkFin` so the carriers reduce to `Fin 3`. -/
abbrev cournotGame : FiniteStrategicGame :=
  FiniteStrategicGame.mkFin 2 (fun _ => 3) fun i s =>
    profits (leaderQ (s 0)) (followerQ (s 1)) i

/-- The simultaneous-game profile `(q₁, q₂) = (4, 4)` (both players choose grid index `1`). -/
def cournotNashProfile : cournotGame.ActionProfile := fun _ => 1

/-- **The leader's static action `q₁ = 4` is strictly dominant.** For every alternative leader
index `a ≠ 1` and every follower action, committing to `q₁ = 4` strictly beats committing to
`q₁ ∈ {2, 7}` — so the leader's static best response is `4` regardless of the follower's quantity
(and hence, by linearity, regardless of any belief over it). The six numeric comparisons
(`a ∈ {0, 2}` against `q₂ ∈ {2, 4, 5}`) are discharged by `norm_num`. -/
theorem cournot_leader_strictly_dominant (a : Fin 3) (ha : a ≠ 1)
    (s : cournotGame.ActionProfile) :
    cournotGame.payoff 0 (Function.update s 0 a) <
      cournotGame.payoff 0 (Function.update s 0 1) := by
  simp only [cournotGame, Function.update_apply]
  -- The payoff depends on the leader's action and the follower's action `s 1`; case on both.
  generalize s 1 = b
  fin_cases a <;> fin_cases b <;>
    first | exact absurd rfl ha | norm_num [profits, leaderQ, followerQ]

/-- **The follower's best response to `q₁ = 4` is `q₂ = 4`.** Given the leader plays index `1`, any
other follower index is a strict loss. The two numeric comparisons (`b ∈ {0, 2}`) are by
`norm_num`. -/
theorem cournot_follower_best_response (b : Fin 3) (hb : b ≠ 1)
    (s : cournotGame.ActionProfile) (h0 : s 0 = 1) :
    cournotGame.payoff 1 (Function.update s 1 b) <
      cournotGame.payoff 1 (Function.update s 1 1) := by
  simp only [cournotGame, Function.update_apply, h0]
  fin_cases b <;>
    first | exact absurd rfl hb | norm_num [profits, leaderQ, followerQ]

/-- **`(4, 4)` is a pure Nash equilibrium of the simultaneous game.** No unilateral deviation pays:
The leader's index `1` is its dominant action and the follower's index `1` is its best response to
the leader's index `1`. The six `(player, deviation)` cases reduce to numeric `≤` by `norm_num`. -/
theorem cournot_nashProfile_is_nash : cournotGame.IsNash cournotNashProfile := by
  rw [StrategicGame.isNash_iff]
  intro i aᵢ
  fin_cases i <;> fin_cases aᵢ <;>
    simp only [cournotNashProfile, cournotGame, Function.update_apply] <;>
    norm_num [profits, leaderQ, followerQ]

/-- **The simultaneous-game Nash equilibrium is unique.** Every pure Nash equilibrium equals
`(4, 4)`. The leader's strictly dominant action forces its coordinate to `1`; given that, the
follower's strict best response forces its coordinate to `1` too. -/
theorem cournot_nash_unique (s : cournotGame.ActionProfile) (hs : cournotGame.IsNash s) :
    s = cournotNashProfile := by
  rw [StrategicGame.isNash_iff] at hs
  -- The leader's coordinate is `1`: any other value is beaten by deviating to `1`.
  have hL : s 0 = 1 := by
    by_contra ha
    have hdom := cournot_leader_strictly_dominant (s 0) ha s
    rw [Function.update_eq_self] at hdom
    have hnd := hs 0 1
    linarith
  -- Given the leader plays `1`, the follower's coordinate is `1` by its strict best response.
  have hF : s 1 = 1 := by
    by_contra hb
    have hbr := cournot_follower_best_response (s 1) hb s hL
    rw [Function.update_eq_self] at hbr
    have hnd := hs 1 1
    linarith
  funext j
  fin_cases j
  · exact hL
  · exact hF

/-- **The leader's Cournot-Nash payoff is `16`.** -/
theorem cournot_leader_nash_payoff : cournotGame.payoff 0 cournotNashProfile = 16 := by
  simp only [cournotNashProfile]
  norm_num [profits, leaderQ, followerQ]

/-- **The follower's Cournot-Nash payoff is `16`.** -/
theorem cournot_follower_nash_payoff : cournotGame.payoff 1 cournotNashProfile = 16 := by
  simp only [cournotNashProfile]
  norm_num [profits, leaderQ, followerQ]

/-- **The bridge.** The leader's payoff at the simultaneous-game Nash `(4, 4)` equals the
backward-induction value of *committing* to `q₁ = 4` in the tree (the `q₁ = 4` subtree value). This
is what licenses calling `(followerNode 4).value` the leader's "Cournot payoff": Committing to its
dominant static quantity and letting the follower reply reproduces the simultaneous outcome. -/
theorem cournot_leader_payoff_eq_commitment :
    cournotGame.payoff 0 cournotNashProfile = (followerNode 4).backwardInductionValue 0 := by
  rw [cournot_leader_nash_payoff, stackelberg_cournot_leader_profit]

/-- **First-mover advantage.** The leader's SPE payoff `21` strictly exceeds its payoff `16` at the
simultaneous-game Nash equilibrium `(4, 4)` — the value of moving first. Anticipated by
nothing in the static game, commitment to `q₁ = 7` lets the leader expand and force the follower to
accommodate. -/
theorem stackelberg_first_mover_advantage :
    cournotGame.payoff 0 cournotNashProfile < stackelberg3.backwardInductionValue 0 := by
  rw [cournot_leader_nash_payoff, stackelberg_SPE_leader_profit]; norm_num

/-- **The follower accommodates at a cost.** The mirror image: The follower's SPE payoff `6` is
strictly below its simultaneous-game Nash payoff `16`. Forced down from `q₂ = 4` to `q₂ = 2` by the
leader's commitment, the follower is strictly worse off than under simultaneous play. -/
theorem stackelberg_follower_accommodation :
    stackelberg3.backwardInductionValue 1 < cournotGame.payoff 1 cournotNashProfile := by
  rw [cournot_follower_nash_payoff, stackelberg_SPE_follower_profit]; norm_num

/-! ## Equilibrium Quantities

The first-mover advantage shows up in *quantities*, not just payoffs: Relative to the Cournot
benchmark the leader expands and the follower contracts. We read the equilibrium quantities off the
backward-induction root choices (`leaderQ`/`followerQ` of the selected indices) and compare them to
the Cournot profile. -/

/-- **The leader's SPE action is `q₁ = 7`** (grid index `2`) — the strict argmax of its three
continuation values `10, 16, 21`. -/
theorem stackelberg_SPE_leader_choice :
    stackelberg3.backwardInductionRootChoice = (2 : Fin 3) := by
  unfold stackelberg3 FinitePerfectInfoTree.backwardInductionRootChoice
  refine FinitePerfectInfoTree.bestChoice_eq_of_strictArgmax (Fin 3) _ 2 ?_
  bi_dominates [followerNode_value_2, followerNode_value_4, followerNode_value_7, profits]

/-- **The follower's SPE action in the realized subgame is `q₂ = 2`** (grid index `0`) — its strict
best response to the leader's commitment `q₁ = 7`. -/
theorem stackelberg_SPE_follower_choice :
    (followerNode 7).backwardInductionRootChoice = (0 : Fin 3) := by
  unfold followerNode FinitePerfectInfoTree.backwardInductionRootChoice
  refine FinitePerfectInfoTree.bestChoice_eq_of_strictArgmax (Fin 3) _ 0 ?_
  bi_dominates [profits]

/-- **The leader expands.** Its SPE quantity `q₁ = 7` strictly exceeds its Cournot quantity
`q₁ = 4`. -/
theorem stackelberg_leader_expands :
    leaderQ stackelberg3.backwardInductionRootChoice > leaderQ (cournotNashProfile 0) := by
  rw [stackelberg_SPE_leader_choice]; change (4 : ℝ) < 7; norm_num

/-- **The follower contracts.** Its SPE quantity `q₂ = 2` is strictly below its Cournot quantity
`q₂ = 4`. -/
theorem stackelberg_follower_contracts :
    followerQ (followerNode 7).backwardInductionRootChoice < followerQ (cournotNashProfile 1) := by
  rw [stackelberg_SPE_follower_choice]; change (2 : ℝ) < 4; norm_num

/-! ## Uniqueness of the SPE

The SPE is unique because every mover at every node has strictly distinct continuation values —
no mover is ever indifferent. Genericity (pairwise-distinct continuation values) is established
node by node: The root node by arithmetic on the three leader profits, and each stage-2 subgame by
arithmetic on the follower's grid profits at the corresponding leader quantity. -/

/-- **Stage-2 subgames are generic, parameterised by the leader's quantity.** The three hypotheses
are the pairwise distinctions among the follower's grid profits. -/
private lemma followerNode_isGeneric (q₁ : ℝ)
    (h24 : (12 - q₁ - 2) * 2 ≠ (12 - q₁ - 4) * 4)
    (h25 : (12 - q₁ - 2) * 2 ≠ (12 - q₁ - 5) * 5)
    (h45 : (12 - q₁ - 4) * 4 ≠ (12 - q₁ - 5) * 5) :
    (followerNode q₁).IsGeneric := by
  unfold followerNode
  bi_generic <;> exact FinitePerfectInfoTree.isGeneric_terminal _

/-- **The Stackelberg game is generic**: The follower's profits are pairwise distinct in every
stage-2 subgame, and the leader's three continuation profits `10, 16, 21` are pairwise distinct at
the root. -/
theorem stackelberg3_isGeneric : stackelberg3.IsGeneric := by
  -- Leader continuation values, pairwise distinct.
  have h24 : (followerNode 2).backwardInductionValue 0 ≠
      (followerNode 4).backwardInductionValue 0 := by
    rw [followerNode_value_2 0, followerNode_value_4 0]; norm_num [profits]
  have h27 : (followerNode 2).backwardInductionValue 0 ≠
      (followerNode 7).backwardInductionValue 0 := by
    rw [followerNode_value_2 0, followerNode_value_7 0]; norm_num [profits]
  have h47 : (followerNode 4).backwardInductionValue 0 ≠
      (followerNode 7).backwardInductionValue 0 := by
    rw [followerNode_value_4 0, followerNode_value_7 0]; norm_num [profits]
  unfold stackelberg3
  bi_generic
  · exact followerNode_isGeneric 2 (by norm_num) (by norm_num) (by norm_num)
  · exact followerNode_isGeneric 4 (by norm_num) (by norm_num) (by norm_num)
  · exact followerNode_isGeneric 7 (by norm_num) (by norm_num) (by norm_num)

/-- **The Stackelberg SPE is unique.** Every subgame-perfect local strategy — pure or mixed —
equals the backward-induction strategy: No mover is ever indifferent, so no node admits an
alternative choice or a mix. -/
theorem stackelberg_SPE_unique (s : stackelberg3.LocalBehavioralStrategy)
    (hs : stackelberg3.IsSubgamePerfectStrategy s) :
    s = stackelberg3.backwardInductionStrategy :=
  hs.eq_backwardInductionStrategy stackelberg3_isGeneric

end EconlibExamples.GameTheory.Stackelberg

end
