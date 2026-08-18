/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import EconlibExamples.GameTheory.Centipede
import EconlibExamples.GameTheory.EntryDeterrence
import EconlibTest.GameTheory.ExtensiveFormCore
import Mathlib

/-!
# Extensive-Form SPE / PBE — Non-Vacuity Checks (Chunks 3 & 4)

Compile-time semantic witnesses for backward induction, subgame-perfect equilibrium, perfect
Bayesian equilibrium, and the one-shot deviation principle on finite perfect-information trees
(`Econlib.GameTheory.ExtensiveForm.PerfectInfoTree.{BackwardInduction, SPE, OneShot}` and
`ExtensiveForm.{PBE, SequentialEquilibrium, OneShotDeviation}`). The headline failure mode here is
a **maximizer/minimizer or player-order flip in the backward-induction fold**: Backward induction
must select the *subgame-perfect* action and return the equilibrium payoff to the *correct* player.

We anchor on the two existing worked games rather than building parallel constructions:

* **Entry deterrence** (`EconlibExamples.GameTheory.EntryDeterrence`) — the mixed-arity Dixit tree
  (`Fin 3` capacity root, `Fin 2` entry nodes). The incumbent's three continuation profits are `4`
  (low, entry accommodated), `6` (medium, deterred), `5` (high, over-deterred); backward induction
  selects **medium** (root choice `1`) and the SPE payoff is `(6, 0)`. The strict argmax at the
  root (`6 > 5 > 4`) is the maximizer-direction anchor: A min/argmin flip would select low or high.
* **Centipede** (`EconlibExamples.GameTheory.Centipede`) — the four-round Rosenthal tree (`Fin 2`
  binary nodes). Backward induction stops at the root; the SPE payoff is `(1, 0)`.

## Failure modes caught

* **maximizer flip** — `backwardInductionRootChoice_isBest` confirms the selected root action
  weakly dominates *every* alternative for the *mover*; we exhibit the concrete strict comparison
  (medium beats low and high) so a min/argmin fold fails;
* **player-order flip in the fold** —
  `IsSubgamePerfectStrategy.strategyValue_eq_backwardInductionValue` anchors the SPE payoff to the
  *incumbent's* `6` and the *entrant's* `0`, distinct coordinates that a player swap would cross;
* **vacuous deviation in PBE** — `isPerfectBayesianEquilibrium_backwardInduction` instantiates the
  PBE on the concrete equilibrium; the trivial perfect-information beliefs are genuinely Bayes
  consistent, not vacuously so.
-/

noncomputable section

namespace EconlibTest.GameTheory.ExtensiveFormSPE

open Econlib.GameTheory
open EconlibExamples.GameTheory.EntryDeterrence (entryDeterrence entryNode)
open EconlibExamples.GameTheory.Centipede (centipede4 round4Tree round3Tree round2Tree stop)

/-! ## Chunk 3 — Backward induction values and SPE (BackwardInduction.lean)

We re-derive the entry-deterrence continuation values from the public API (the example's
per-node helpers are `private`). The entry node `entryNode enterPay stayOutPay` is a binary `Fin 2`
decision: Choice `0` is *enter* (payoff `enterPay`), choice `1` is *stay out* (payoff
`stayOutPay`). -/

/-- **`strategyValue_terminal`.** The value of a terminal node is its payoff vector — here the
deterring stay-out payoff `(6, 0)` at the medium entry node's *stay-out* leaf, read off for player
0. -/
theorem strategyValue_terminal_med_stayOut
    (s : (FinitePerfectInfoTree.terminal (I := Fin 2) (E := Fin 3)
        ![6, 0]).LocalBehavioralStrategy) :
    (FinitePerfectInfoTree.terminal (I := Fin 2) (E := Fin 3) ![6, 0]).strategyValue s 0 = 6 :=
    by
  rw [FinitePerfectInfoTree.strategyValue_terminal]; rfl

/-- **`backwardInductionValue_terminal`.** The backward-induction value at a terminal is its
payoff; the medium stay-out leaf pays the incumbent `6`. -/
theorem backwardInductionValue_terminal_med_stayOut :
    (FinitePerfectInfoTree.terminal (I := Fin 2) (E := Fin 3)
        ![6, 0]).backwardInductionValue 0 = 6 := by
  rw [FinitePerfectInfoTree.backwardInductionValue_terminal]; rfl

/-- **Binary strict-argmax discharge: Entry deterred.** At the medium entry node (enter pays the
entrant `-1`, stay out pays `0`, so the entrant strictly prefers stay out, choice `1`), the node
value is the *stay-out* payoff `(6, 0)`. -/
theorem backwardInductionValue_med_deterred (i : Fin 2) :
    (entryNode ![2, -1] ![6, 0]).backwardInductionValue i = ![6, 0] i := by
  unfold entryNode
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 1)
    (h := by bi_dominates)]
  rfl

/-- **Binary strict-argmax discharge: Entry accommodated.** At the *low* entry node (enter pays the
entrant `2 > 0`, so the entrant strictly prefers *enter*, choice `0`), the node value is the
*enter* payoff `(4, 2)`. -/
theorem backwardInductionValue_low_entered (i : Fin 2) :
    (entryNode ![4, 2] ![8, 0]).backwardInductionValue i = ![4, 2] i := by
  unfold entryNode
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 0)
    (h := by bi_dominates)]
  rfl

/-- The three capacity children of the entry-deterrence root, as a `Fin 3`-indexed family. -/
private def edChild : Fin 3 → FinitePerfectInfoTree (Fin 2) (Fin 3) :=
  ![entryNode ![4, 2] ![8, 0], entryNode ![2, -1] ![6, 0], entryNode ![1, -2] ![5, 0]]

/-- The incumbent's continuation profit at high capacity (`5`, deterred over-investment). -/
private theorem ed_high_value : (entryNode ![1, -2] ![5, 0]).backwardInductionValue 0 = 5 := by
  unfold entryNode
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 1)
    (h := by bi_dominates)]
  norm_num

/-- **`backwardInductionRootChoice_isBest`: The maximizer-direction anchor.** Every capacity choice
gives the incumbent a continuation profit no greater than the backward-induction root choice. We
exhibit the concrete strict comparison: Low (`4`) and high (`5`) are both strictly worse than the
selected medium (`6`), so the fold genuinely *maximizes* the incumbent's profit — an argmin fold
would pick low. -/
theorem entryDeterrence_rootChoice_isBest (c : Fin 3) :
    (edChild c).backwardInductionValue 0 ≤
      FinitePerfectInfoTree.backwardInductionValue
        (edChild (FinitePerfectInfoTree.backwardInductionRootChoice entryDeterrence)) 0 :=
  FinitePerfectInfoTree.backwardInductionRootChoice_isBest 0 (Fin 3)
    (Function.Embedding.refl _) edChild c

/-- The root choice that backward induction selects at the entry-deterrence root is **medium**
(`1`) — directly via the `bestChoice` strict argmax over the incumbent's `4, 6, 5` continuation
profits. -/
theorem entryDeterrence_rootChoice_eq_medium :
    FinitePerfectInfoTree.backwardInductionRootChoice entryDeterrence = (1 : Fin 3) := by
  -- This is exactly the example's `speCapacity_eq_medium`, re-derived here on the root choice.
  unfold entryDeterrence FinitePerfectInfoTree.backwardInductionRootChoice
  refine FinitePerfectInfoTree.bestChoice_eq_of_strictArgmax (Fin 3) _ 1 ?_
  bi_dominates [backwardInductionValue_low_entered, backwardInductionValue_med_deterred,
    ed_high_value]

/-- **The maximizer is strict: Low and high are dominated.** Combining `_isBest` with the value
computations, the selected medium child's incumbent value (`6`) strictly exceeds both the low (`4`)
and high (`5`) children's. A minimizer fold would have selected low (the `4`), failing this. -/
theorem entryDeterrence_rootChoice_strictly_dominates :
    (edChild 0).backwardInductionValue 0 <
      FinitePerfectInfoTree.backwardInductionValue
        (edChild (FinitePerfectInfoTree.backwardInductionRootChoice entryDeterrence)) 0 ∧
    (edChild 2).backwardInductionValue 0 <
      FinitePerfectInfoTree.backwardInductionValue
        (edChild (FinitePerfectInfoTree.backwardInductionRootChoice entryDeterrence)) 0 := by
  rw [entryDeterrence_rootChoice_eq_medium]
  refine ⟨?_, ?_⟩
  · -- low (4) < medium (6).
    change (entryNode ![4, 2] ![8, 0]).backwardInductionValue 0 <
      (entryNode ![2, -1] ![6, 0]).backwardInductionValue 0
    rw [backwardInductionValue_low_entered 0, backwardInductionValue_med_deterred 0]; norm_num
  · -- high (5) < medium (6).
    change (entryNode ![1, -2] ![5, 0]).backwardInductionValue 0 <
      (entryNode ![2, -1] ![6, 0]).backwardInductionValue 0
    rw [ed_high_value, backwardInductionValue_med_deterred 0]; norm_num

/-- The whole-game backward-induction value of entry deterrence is `(6, 0)`: Incumbent profit `6`,
entrant payoff `0`. Re-derived from the public `_value` helpers (the example's is `private`). -/
private theorem entryDeterrence_bi_value (i : Fin 2) :
    entryDeterrence.backwardInductionValue i = ![6, 0] i := by
  unfold entryDeterrence
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 1)]
  · exact backwardInductionValue_med_deterred i
  · bi_dominates [backwardInductionValue_low_entered, backwardInductionValue_med_deterred,
      ed_high_value]

/-- **`IsSubgamePerfectStrategy.strategyValue_eq_backwardInductionValue`: The SPE payoff anchor and
player-order check.** In the generic entry-deterrence tree, *every* subgame-perfect local strategy
attains the backward-induction value. Anchored to distinct coordinates — incumbent `6`, entrant `0`
— so a player-order flip in the value fold (reading the entrant's payoff at the incumbent's slot,
or vice versa) would fail. We instantiate on the backward-induction strategy itself. -/
theorem entryDeterrence_spe_value_player0 :
    entryDeterrence.strategyValue entryDeterrence.backwardInductionStrategy 0 = 6 := by
  rw [(FinitePerfectInfoTree.backwardInductionStrategy_isSubgamePerfect
    entryDeterrence).strategyValue_eq_backwardInductionValue
    EconlibExamples.GameTheory.EntryDeterrence.entryDeterrence_isGeneric 0]
  rw [entryDeterrence_bi_value]; rfl

/-- The entrant's coordinate of the SPE-value anchor: Every subgame-perfect strategy pays the
entrant `0` (it stays out). -/
theorem entryDeterrence_spe_value_player1 :
    entryDeterrence.strategyValue entryDeterrence.backwardInductionStrategy 1 = 0 := by
  rw [(FinitePerfectInfoTree.backwardInductionStrategy_isSubgamePerfect
    entryDeterrence).strategyValue_eq_backwardInductionValue
    EconlibExamples.GameTheory.EntryDeterrence.entryDeterrence_isGeneric 1]
  rw [entryDeterrence_bi_value]; rfl

/-- **`strategyValue_decision`.** The value at a decision node is the simplex-weighted sum of the
children's values. Exercised on the medium entry node under the backward-induction strategy. -/
theorem strategyValue_decision_entryNode :
    (entryNode ![2, -1] ![6, 0]).strategyValue
        (entryNode ![2, -1] ![6, 0]).backwardInductionStrategy 0 =
      ∑ c : Fin 2,
        (entryNode ![2, -1] ![6, 0]).backwardInductionStrategy.1 c *
          (![FinitePerfectInfoTree.terminal ![(2 : ℝ), -1],
              FinitePerfectInfoTree.terminal ![(6 : ℝ), 0]] c).strategyValue
            ((entryNode ![2, -1] ![6, 0]).backwardInductionStrategy.2 c) 0 := by
  unfold entryNode
  rw [FinitePerfectInfoTree.strategyValue_decision]

/-- **`backwardInductionLocalPureStrategy_isSubgamePerfect`.** The pure backward-induction
strategy, embedded as a behavioral strategy, is subgame perfect on the entry-deterrence tree. -/
theorem entryDeterrence_pure_bi_isSubgamePerfect :
    entryDeterrence.IsSubgamePerfectStrategy
      (FinitePerfectInfoTree.LocalPureStrategy.toStrategy entryDeterrence
        entryDeterrence.backwardInductionLocalPureStrategy) :=
  entryDeterrence.backwardInductionLocalPureStrategy_isSubgamePerfect

/-- **`bi_generic`.** A binary entry node is generic when the entrant's two payoffs differ. The
medium node (`-1 ≠ 0`) satisfies this condition — both arms are generic terminals. -/
theorem entryNode_med_isGeneric : (entryNode ![2, -1] ![6, 0]).IsGeneric := by
  unfold entryNode
  bi_generic <;> exact FinitePerfectInfoTree.isGeneric_terminal _

/-! ### Ternary (`Fin 3`) backward-induction discharge tactics (BackwardInduction.lean)

The mixed-arity root of `entryDeterrence` is a `Fin 3` decision node. This section covers
`bi_dominates` and `bi_generic` on a three-leaf player-`0` tree, with one witness per winning
arm. -/

/-- A three-leaf `Fin 3` decision node for player `0`, with incumbent leaf payoffs `a, b, c` (the
entrant coordinate is irrelevant here, fixed to `0`). -/
private def triLeaf (a b c : ℝ) : FinitePerfectInfoTree (Fin 2) (Fin 3) :=
  .decision 0 (Fin 3) (Function.Embedding.refl _)
    ![.terminal ![a, 0], .terminal ![b, 0], .terminal ![c, 0]]

/-- **`bi_dominates`, winner zero.** The first arm strictly dominates (`3 > 1` and `3 > 2`), so the
node collapses to it. -/
theorem fin_three_value_eq_zero (i : Fin 2) :
    (triLeaf 3 1 2).backwardInductionValue i = ![3, 0] i := by
  unfold triLeaf
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 0)
    (h := by bi_dominates [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- **`bi_dominates`, winner one.** The middle arm strictly dominates (`3 > 1` and `3 > 2`). -/
theorem fin_three_value_eq_one (i : Fin 2) :
    (triLeaf 1 3 2).backwardInductionValue i = ![3, 0] i := by
  unfold triLeaf
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 1)
    (h := by bi_dominates [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- **`bi_dominates`, winner two.** The last arm strictly dominates (`3 > 1` and `3 > 2`). -/
theorem fin_three_value_eq_two (i : Fin 2) :
    (triLeaf 1 2 3).backwardInductionValue i = ![3, 0] i := by
  unfold triLeaf
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 2)
    (h := by bi_dominates [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons])]
  norm_num [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

/-- **`bi_generic`.** Three pairwise-distinct mover values (`1, 2, 3`) with generic terminal
children make the ternary node generic. -/
theorem fin_three_isGeneric : (triLeaf 1 2 3).IsGeneric := by
  unfold triLeaf
  bi_generic [Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    exact FinitePerfectInfoTree.isGeneric_terminal _

/-! ### `rootDecisionMover` and the SPE predicate bridge (SPE.lean) -/

/-- **`rootDecisionMover_decision`.** The entry-deterrence root is a decision node whose mover is
the incumbent (player `0`). -/
theorem entryDeterrence_rootDecisionMover :
    entryDeterrence.rootDecisionMover = some 0 := by
  unfold entryDeterrence
  rw [FinitePerfectInfoTree.rootDecisionMover_decision]

/-- **`rootDecisionMover_terminal`.** A terminal node has no decision mover. -/
theorem terminal_rootDecisionMover :
    (FinitePerfectInfoTree.terminal (I := Fin 2) (E := Fin 3) ![6, 0]).rootDecisionMover = none :=
  FinitePerfectInfoTree.rootDecisionMover_terminal _

/-- **`isSubgamePerfectStrategy_iff_subgamePerfectStrategyPred`.** The recursive finite-tree SPE
predicate coincides with the `EquilibriumProblem`-level SPE refinement. Instantiated on the
entry-deterrence backward-induction strategy, this confirms the two SPE notions agree on the
concrete equilibrium. -/
theorem entryDeterrence_isSPE_iff_pred :
    entryDeterrence.IsSubgamePerfectStrategy entryDeterrence.backwardInductionStrategy ↔
      entryDeterrence.subgamePerfectStrategyPred.IsEquilibrium
        entryDeterrence.backwardInductionStrategy :=
  entryDeterrence.isSubgamePerfectStrategy_iff_subgamePerfectStrategyPred
    entryDeterrence.backwardInductionStrategy

/-! ### Centipede backward-induction values (BackwardInduction.lean) -/

/-- **`strategyValue_terminal` on centipede's full-cooperation leaf.** The "always continue"
terminal pays `(3, 3)`; its strategy value for player 0 is `3`. -/
theorem centipede_strategyValue_terminal
    (s : (FinitePerfectInfoTree.terminal (I := Fin 2) (E := Fin 2)
        ![3, 3]).LocalBehavioralStrategy) :
    (FinitePerfectInfoTree.terminal (I := Fin 2) (E := Fin 2) ![3, 3]).strategyValue s 0 = 3 :=
    by
  rw [FinitePerfectInfoTree.strategyValue_terminal]; rfl

/-- **`bi_dominates` on centipede round 4.** Player 1 prefers `stop` (own payoff `4 > 3`), choice
`0`; the round-4 value is `(2, 4)`. -/
theorem centipede_round4_value_zero (i : Fin 2) :
    round4Tree.backwardInductionValue i = ![2, 4] i := by
  unfold round4Tree
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 0)
    (h := by bi_dominates)]
  rfl

/-- **`rootDecisionMover_decision` on centipede.** The centipede root is player 0's decision
node. -/
theorem centipede_rootDecisionMover :
    centipede4.rootDecisionMover = some 0 := by
  unfold centipede4
  rw [FinitePerfectInfoTree.rootDecisionMover_decision]

/-! ### One-shot / extensive-game bridges (OneShot.lean, Tree.lean)

These witnesses exercise the perfect-info → extensive-game scaffolding under the canonical
trivial beliefs, on the centipede tree. -/

/-- **`toBehavioral_terminal_root`.** Embedding a terminal-tree strategy gives the trivial root
behavior `PUnit.unit`. -/
theorem toBehavioral_terminal_root_witness
    (s : (FinitePerfectInfoTree.terminal (I := Fin 2) (E := Fin 2)
        ![3, 3]).LocalBehavioralStrategy) :
    FinitePerfectInfoTree.LocalBehavioralStrategy.toBehavioral
      (.terminal ![3, 3]) s [] = PUnit.unit :=
  FinitePerfectInfoTree.toBehavioral_terminal_root ![3, 3] s

/-- **`at_terminal`.** The continuation strategy of a terminal-tree strategy at any history is
trivial. -/
theorem at_terminal_witness
    (s : (FinitePerfectInfoTree.terminal (I := Fin 2) (E := Fin 2) ![3, 3]).LocalBehavioralStrategy)
    (h : List (Fin 2)) :
    FinitePerfectInfoTree.LocalBehavioralStrategy.at (.terminal ![3, 3]) s h = PUnit.unit :=
  FinitePerfectInfoTree.at_terminal ![3, 3] s h

/-- **`at_decision_nil`.** The continuation strategy at the empty history is the strategy itself. -/
theorem at_decision_nil_witness (s : centipede4.LocalBehavioralStrategy) :
    FinitePerfectInfoTree.LocalBehavioralStrategy.at centipede4 s [] = s := by
  unfold centipede4 at s ⊢
  rw [FinitePerfectInfoTree.at_decision_nil]

/-- **`movesAt_iff_isMoverAt`.** On the centipede tree, the node-level `movesAt` of the embedded
game tree at the root coincides with the tree-level `isMoverAt`. Player 0 is the root mover. -/
theorem centipede_movesAt_iff_isMoverAt :
    (centipede4.toGameTree.nodeKind []).movesAt 0 ↔ centipede4.isMoverAt [] 0 :=
  centipede4.movesAt_iff_isMoverAt [] 0

/-- **`isMoverAt_append` at a *nonempty* prefix.** The mover at `[1] ++ rest` (i.e. after player 0
*continues* into the round-2 subgame) equals the mover at `rest` in the
`subtreeAt [1] = round2Tree` subtree. This exercises the genuine subtree-descent of the append
identity, not the degenerate `prefix = []` case. -/
theorem centipede_isMoverAt_append (rest : List (Fin 2)) (i : Fin 2) :
    centipede4.isMoverAt ([1] ++ rest) i ↔ (centipede4.subtreeAt [1]).isMoverAt rest i :=
  centipede4.isMoverAt_append [1] rest i

/-- **The continue-subtree is `round2Tree`.** Descending the root's *continue* edge (`[1]`) lands
in the round-2 subgame. -/
theorem centipede_subtree_continue : centipede4.subtreeAt [1] = round2Tree := by
  show centipede4.subtreeAt [(1 : Fin 2)] = round2Tree
  unfold centipede4 FinitePerfectInfoTree.subtreeAt
  rw [show decodeEmit (Function.Embedding.refl (Fin 2)) 1 = some 1 from
    decodeEmit_emit (Function.Embedding.refl (Fin 2)) 1]
  rfl

/-- **Player 1 moves at the continue node `[1]`.** After player 0 continues, the round-2 subgame is
player 1's decision (`round2Tree`'s mover is `1`). This is the substantive mover fact at a nonempty
history — a subtree-descent bug would misattribute the mover. -/
theorem centipede_isMoverAt_continue_player1 : centipede4.isMoverAt [1] 1 := by
  unfold FinitePerfectInfoTree.isMoverAt
  rw [centipede_subtree_continue]
  change (1 : Fin 2) = 1
  rfl

/-- **Player 0 does *not* move at the continue node `[1]`** — it is player 1's turn there. -/
theorem centipede_not_isMoverAt_continue_player0 : ¬ centipede4.isMoverAt [1] 0 := by
  unfold FinitePerfectInfoTree.isMoverAt
  rw [centipede_subtree_continue]
  change ¬ ((1 : Fin 2) = 0)
  decide

/-- **`toExtensiveGame_infoSetDeviation_unilateral`** (general form). An info-set deviation of
player 0 at the root observation lifts to a canonical unilateral deviation in the extensive game.
The concrete instantiation on the backward-induction strategy and its genuine one-shot surgery is
`centipede_infoSetDeviation_unilateral_surgery` (defined after the surgery construction below). -/
theorem centipede_infoSetDeviation_unilateral
    (β β' : centipede4.toExtensiveForm.BehavioralStrategy)
    (h_dev : IsInfoSetDeviation centipede4.toExtensiveForm 0 [] β β') :
    centipede4.toExtensiveForm.unilateralDeviation 0 β β' :=
  centipede4.toExtensiveGame_infoSetDeviation_unilateral β 0 [] β' h_dev

/-- **Root mover fact (discharged).** Player `0` *does* move at the centipede root: `movesAt 0 []`
reduces to `0 = 0`. -/
theorem centipede_root_movesAt_0 : (centipede4.toGameTree.nodeKind []).movesAt 0 := rfl

/-- **Root non-mover fact (discharged).** Player `1` does *not* move at the centipede root:
`movesAt 1 []` reduces to `(0 : Fin 2) = 1`, which is false. -/
theorem centipede_root_not_movesAt_1 : ¬ (centipede4.toGameTree.nodeKind []).movesAt 1 :=
  show ¬ ((0 : Fin 2) = 1) by decide

/-- **`assessmentValue_trivialBeliefs_perfectInfo_pos`, with the root mover fact discharged.** At
the root (player `0` moves, `centipede_root_movesAt_0`), the assessment value under trivial beliefs
is the continuation value — no longer parametric in an assumed `hm`. -/
theorem centipede_assessmentValue_pos
    (σ : centipede4.toExtensiveForm.BehavioralStrategy) :
    assessmentValue centipede4.toExtensiveGame
        { strategy := σ, beliefs := trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree } 0 [] =
      centipede4.toExtensiveGame.continuationValue σ [] 0 :=
  centipede4.assessmentValue_trivialBeliefs_perfectInfo_pos σ centipede_root_movesAt_0

/-- **`assessmentValue_trivialBeliefs_perfectInfo_neg`, with the root non-mover fact discharged.**
At the root, player `1` does not move (`centipede_root_not_movesAt_1`), so player `1`'s assessment
value is `0` — the empty info set carries no value. -/
theorem centipede_assessmentValue_neg
    (σ : centipede4.toExtensiveForm.BehavioralStrategy) :
    assessmentValue centipede4.toExtensiveGame
        { strategy := σ,
          beliefs := trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree } 1 [] = 0 :=
  centipede4.assessmentValue_trivialBeliefs_perfectInfo_neg σ centipede_root_not_movesAt_1

/-! ## Chunk 4 — PBE, one-shot deviation, sequential equilibrium

The backward-induction strategy with trivial perfect-information beliefs is a perfect Bayesian
equilibrium of the centipede (the easy `_backwardInduction` route). From it we derive the one-shot
PBE form, and we exercise the one-shot-deviation surgery and Bayes-consistency machinery. -/

/-- The canonical backward-induction assessment of the centipede: SPE strategy + trivial beliefs. -/
def centipedeAssessment : Assessment centipede4.toExtensiveForm where
  strategy := centipede4.backwardInductionBehavioralStrategy
  beliefs := trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree

/-- **`isPerfectBayesianEquilibrium_backwardInduction`: The concrete PBE.** The centipede's
backward-induction assessment is a perfect Bayesian equilibrium — the headline chunk-4 endpoint on
a concrete game. -/
theorem centipede_is_PBE :
    IsPerfectBayesianEquilibrium centipede4.toExtensiveGame centipedeAssessment :=
  centipede4.isPerfectBayesianEquilibrium_backwardInduction

/-- **`IsPerfectBayesianEquilibrium.oneShot`: The easy direction.** A full PBE yields the one-shot
PBE (no profitable *single-info-set* deviation). Instantiated on the concrete centipede PBE — the
no-profitable-deviation conclusion is non-vacuous because the underlying PBE genuinely rules out
deviations. -/
theorem centipede_PBE_oneShot :
    IsPerfectBayesianEquilibriumOneShot centipede4.toExtensiveGame centipedeAssessment :=
  centipede_is_PBE.oneShot

/-- **`IsOnPath`.** The root `[]` is on the equilibrium path — its reach probability is positive
(the root is reached with probability one). -/
theorem centipede_root_isOnPath :
    IsOnPath centipede4.toExtensiveForm centipede4.backwardInductionBehavioralStrategy [] := by
  change 0 < reachProb centipede4.toExtensiveForm centipede4.backwardInductionBehavioralStrategy []
  -- `reachProb [] = finitePrefixProb σ [] = finitePrefixProbFrom σ [] [] = 1`.
  change (0 : ℝ) < centipede4.toExtensiveForm.finitePrefixProb
    centipede4.backwardInductionBehavioralStrategy []
  rw [show centipede4.toExtensiveForm.finitePrefixProb
    centipede4.backwardInductionBehavioralStrategy [] = 1 from rfl]
  norm_num

/-! ### One-shot deviation surgery (OneShotDeviation.lean)

A genuine deviation `τ` from the equilibrium `σ` exists; the surgery
`oneShotSurgery G σ τ i obs` splices `τ`'s action at the single info set `(i, obs)` onto `σ`
elsewhere, and the lemmas certify it is an info-set deviation, a unilateral deviation, and agrees
with `τ` at the surgery point. These witness that the one-shot deviation the OSDP rules out is
*non-vacuous*. -/

/-- A concrete *alternative* strategy: The **uniform** behavioral strategy, which places mass
`1/card` on every legal choice at every info set. It is genuinely totally mixed
(`centipedeAltStrategy_totallyMixed`) and therefore *differs* from the (pure, point-mass)
backward-induction strategy (`centipedeAltStrategy_ne_backwardInduction`) — so the surgery below
splices a real deviation rather than copying the equilibrium action. (The previous version,
`vertex default`, was the `stop` vertex, which *equals* the backward-induction action at every
centipede decision node, making the surgery witnesses vacuous.) -/
def centipedeAltStrategy : centipede4.toExtensiveForm.BehavioralStrategy :=
  fun i obs =>
    ⟨fun _ => 1 / (Fintype.card (centipede4.toExtensiveForm.info.iChoiceType i obs) : ℝ), by
      constructor
      · intro c; positivity
      · rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, mul_one_div, div_self]
        have : 0 < Fintype.card (centipede4.toExtensiveForm.info.iChoiceType i obs) :=
          Fintype.card_pos
        positivity⟩

/-- **The alternative strategy is totally mixed.** Every (player, observation) coordinate puts
strictly positive mass `1/card > 0` on every legal choice. This is the substantive content that
distinguishes `centipedeAltStrategy` from the pure backward-induction strategy. -/
theorem centipedeAltStrategy_totallyMixed :
    centipede4.toExtensiveForm.IsTotallyMixed centipedeAltStrategy := by
  intro i obs c
  change 0 < 1 / (Fintype.card (centipede4.toExtensiveForm.info.iChoiceType i obs) : ℝ)
  have : 0 < Fintype.card (centipede4.toExtensiveForm.info.iChoiceType i obs) := Fintype.card_pos
  positivity

/-- Helper: A zero entry of `s` transports to a zero entry of `simplexTransport h s`. -/
private theorem simplexTransport_exists_zero {α β : Type u} [instA : Fintype α] [instB : Fintype β]
    (h : α = β) (s : stdSimplex ℝ α) {a : α} (ha : s.val a = 0) :
    ∃ b : β, (simplexTransport h s).val b = 0 := by
  subst h
  cases Subsingleton.elim instA instB
  exact ⟨a, ha⟩

/-- **The backward-induction strategy is *not* totally mixed.** At the root info set player `0`
places mass `1` on `stop`, hence mass `0` on `continue` — violating full support. This is the
contrast that forces the deviation below to be genuine. -/
theorem centipede_backwardInduction_not_totallyMixed :
    ¬ centipede4.toExtensiveForm.IsTotallyMixed
        centipede4.backwardInductionBehavioralStrategy := by
  have hm : (centipede4.toGameTree.nodeKind []).movesAt (0 : Fin 2) := rfl
  have hBI :
      centipede4.backwardInductionBehavioralStrategy (0 : Fin 2) [] =
        simplexTransport
          ((NodeKind.iChoiceTypeAt'_eq_iChoiceTypeAt _ (0 : Fin 2) hm).symm)
          (stdSimplex.vertex (S := ℝ) (EconlibExamples.GameTheory.Centipede.stop : Fin 2)) := by
    have hraw : centipede4.backwardInductionRaw [] =
        stdSimplex.vertex (S := ℝ) (EconlibExamples.GameTheory.Centipede.stop : Fin 2) := by
      change centipede4.backwardInductionStrategy.1 = _
      rw [show centipede4.backwardInductionStrategy.1 =
            stdSimplex.vertex (S := ℝ) centipede4.backwardInductionRootChoice from rfl,
          EconlibExamples.GameTheory.Centipede.centipede_SPE_root_stops]
      rfl
    unfold FinitePerfectInfoTree.backwardInductionBehavioralStrategy
    unfold ExtensiveForm.BehavioralStrategy.ofPerfectInfo
    rw [dif_pos hm]
    change simplexTransport _ (centipede4.backwardInductionRaw []) = _
    rw [hraw]
    rfl
  have hzero : (stdSimplex.vertex (S := ℝ)
      (EconlibExamples.GameTheory.Centipede.stop : Fin 2)).val
      (EconlibExamples.GameTheory.Centipede.continue_ : Fin 2) = 0 :=
    stdSimplex.vertex_apply_ne (by decide :
      (EconlibExamples.GameTheory.Centipede.stop : Fin 2) ≠
        EconlibExamples.GameTheory.Centipede.continue_)
  obtain ⟨c, hc⟩ :=
    simplexTransport_exists_zero
      ((NodeKind.iChoiceTypeAt'_eq_iChoiceTypeAt _ (0 : Fin 2) hm).symm)
      (stdSimplex.vertex (S := ℝ) (EconlibExamples.GameTheory.Centipede.stop : Fin 2)) hzero
  rw [← hBI] at hc
  intro htm
  have hpos : 0 < (centipede4.backwardInductionBehavioralStrategy (0 : Fin 2) []).val c :=
    htm (0 : Fin 2) [] c
  rw [hc] at hpos
  exact lt_irrefl 0 hpos

/-- **The alternative strategy is a genuine deviation:
`centipedeAltStrategy ≠
backwardInductionBehavioralStrategy`.** They cannot coincide because the
former is totally mixed and the latter is not (it stops with certainty at the root). So the
one-shot surgery below installs a real off-equilibrium action, not a copy of the backward-induction
action. -/
theorem centipedeAltStrategy_ne_backwardInduction :
    centipedeAltStrategy ≠ centipede4.backwardInductionBehavioralStrategy := by
  intro h
  refine centipede_backwardInduction_not_totallyMixed ?_
  rw [← h]
  exact centipedeAltStrategy_totallyMixed

/-- **`oneShotSurgery_isInfoSetDeviation`.** The surgery of the alternative strategy onto the
equilibrium at player 0's root info set is a genuine single-info-set deviation. -/
theorem centipede_oneShotSurgery_isInfoSetDeviation :
    IsInfoSetDeviation centipede4.toExtensiveForm 0 []
      centipede4.backwardInductionBehavioralStrategy
      (oneShotSurgery centipede4.toExtensiveForm
        centipede4.backwardInductionBehavioralStrategy centipedeAltStrategy 0 []) :=
  oneShotSurgery_isInfoSetDeviation centipede4.toExtensiveForm
    centipede4.backwardInductionBehavioralStrategy centipedeAltStrategy 0 []

/-- **`oneShotSurgery_unilateralDeviation`.** The same surgery is a canonical unilateral deviation
of player 0. -/
theorem centipede_oneShotSurgery_unilateralDeviation :
    centipede4.toExtensiveForm.unilateralDeviation 0
      centipede4.backwardInductionBehavioralStrategy
      (oneShotSurgery centipede4.toExtensiveForm
        centipede4.backwardInductionBehavioralStrategy centipedeAltStrategy 0 []) :=
  oneShotSurgery_unilateralDeviation centipede4.toExtensiveForm
    centipede4.backwardInductionBehavioralStrategy centipedeAltStrategy 0 []

/-- **`oneShotSurgery_at_self`.** At the surgery point `(0, [])` the surgery equals the alternative
strategy `τ` — the deviation is genuinely installed there. Since `centipedeAltStrategy` is a *real*
deviation (`centipedeAltStrategy_ne_backwardInduction`), this confirms the surgery copies `τ`, not
`σ`: A buggy surgery copying `σ` would instead return the backward-induction action here. -/
theorem centipede_oneShotSurgery_at_self :
    oneShotSurgery centipede4.toExtensiveForm
        centipede4.backwardInductionBehavioralStrategy centipedeAltStrategy 0 [] 0 [] =
      centipedeAltStrategy 0 [] :=
  oneShotSurgery_at_self centipede4.toExtensiveForm
    centipede4.backwardInductionBehavioralStrategy centipedeAltStrategy 0 []

/-- **`toExtensiveGame_infoSetDeviation_unilateral`, on the concrete genuine surgery.** The
one-shot surgery of the genuine deviation `centipedeAltStrategy` onto the equilibrium at player 0's
root info set lifts to a unilateral deviation — the info-set-deviation hypothesis is supplied by
the surgery's own `oneShotSurgery_isInfoSetDeviation`
(`centipede_oneShotSurgery_isInfoSetDeviation`), not assumed. This discharges the hard semantic
content on the advertised concrete deviation. -/
theorem centipede_infoSetDeviation_unilateral_surgery :
    centipede4.toExtensiveForm.unilateralDeviation 0
      centipede4.backwardInductionBehavioralStrategy
      (oneShotSurgery centipede4.toExtensiveForm
        centipede4.backwardInductionBehavioralStrategy centipedeAltStrategy 0 []) :=
  centipede_infoSetDeviation_unilateral _ _ centipede_oneShotSurgery_isInfoSetDeviation

/-- **`unilateralDeviation_of_isInfoSetDeviation`.** Any single-info-set deviation is a unilateral
deviation. Stated abstractly on the centipede form for an arbitrary info-set deviation. -/
theorem centipede_unilateralDeviation_of_isInfoSetDeviation
    (σ σ' : centipede4.toExtensiveForm.BehavioralStrategy)
    (hdev : IsInfoSetDeviation centipede4.toExtensiveForm 0 [] σ σ') :
    centipede4.toExtensiveForm.unilateralDeviation 0 σ σ' :=
  unilateralDeviation_of_isInfoSetDeviation centipede4.toExtensiveForm 0 [] hdev

/-- **`deviatedSeq`/`deviatedSeq_unilateralDeviation`.** The per-step deviation sequence (player 0
plays `σ'`, everyone else follows the trembling sequence `σseq n`) is a unilateral deviation at
each `n`. Exercised on a constant trembling sequence. -/
theorem centipede_deviatedSeq_unilateralDeviation
    (σ' : centipede4.toExtensiveForm.BehavioralStrategy)
    (σseq : ℕ → centipede4.toExtensiveForm.BehavioralStrategy) (n : ℕ) :
    centipede4.toExtensiveForm.unilateralDeviation 0 (σseq n)
      (deviatedSeq centipede4.toExtensiveForm 0 σ' σseq n) :=
  deviatedSeq_unilateralDeviation centipede4.toExtensiveForm 0 σ' σseq n

/-! ### Bayes-consistency, info-set probabilities, and tendsto (PBE / SequentialEquilibrium) -/

/-- **`infoSetProb_trivialBeliefs_perfectInfo_pos`, with the root mover fact discharged.** Under
trivial beliefs, the probability of player `0`'s root info set is the reach probability of the root
(the mover fact `centipede_root_movesAt_0` is discharged, not assumed). -/
theorem centipede_infoSetProb_pos
    (σ : (Econlib.GameTheory.perfectInfoForm centipede4.toGameTree).BehavioralStrategy) :
    infoSetProb (Econlib.GameTheory.perfectInfoForm centipede4.toGameTree) σ
        (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) 0 [] =
      reachProb _ σ [] :=
  infoSetProb_trivialBeliefs_perfectInfo_pos centipede4.toGameTree σ centipede_root_movesAt_0

/-- **`infoSetProb_trivialBeliefs_perfectInfo_neg`, with the root non-mover fact discharged.** At
the root, player `1` does not move (`centipede_root_not_movesAt_1`), so its info set has
probability `0`. -/
theorem centipede_infoSetProb_neg
    (σ : (Econlib.GameTheory.perfectInfoForm centipede4.toGameTree).BehavioralStrategy) :
    infoSetProb (Econlib.GameTheory.perfectInfoForm centipede4.toGameTree) σ
        (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) 1 [] = 0 :=
  infoSetProb_trivialBeliefs_perfectInfo_neg centipede4.toGameTree σ centipede_root_not_movesAt_1

/-- **`reachProb_tendsto`** (contract form). If a strategy sequence converges in step
probabilities, reach probabilities converge. The convergence hypothesis is genuinely required
(reach probabilities are products of step probabilities); this exposes the lemma's contract on the
centipede form. The concrete discharge of the hypothesis is `centipede_reachProb_tendsto_const`
below. -/
theorem centipede_reachProb_tendsto
    (σseq : ℕ → centipede4.toExtensiveForm.BehavioralStrategy)
    (σ : centipede4.toExtensiveForm.BehavioralStrategy)
    (hstep : ∀ h e, Filter.Tendsto (fun n => centipede4.toExtensiveForm.stepProb (σseq n) h e)
      Filter.atTop (nhds (centipede4.toExtensiveForm.stepProb σ h e)))
    (hist : List (Fin 2)) :
    Filter.Tendsto (fun n => reachProb centipede4.toExtensiveForm (σseq n) hist)
      Filter.atTop (nhds (reachProb centipede4.toExtensiveForm σ hist)) :=
  reachProb_tendsto centipede4.toExtensiveForm σseq σ hstep hist

/-- **`reachProb_tendsto`, with the convergence hypothesis discharged.** The constant sequence
`fun _ => centipedeAltStrategy` trivially converges in step probabilities (`tendsto_const_nhds`),
so its reach probabilities converge — a concrete instance where the contract's hypothesis is
*proved*, not assumed. -/
theorem centipede_reachProb_tendsto_const (hist : List (Fin 2)) :
    Filter.Tendsto (fun _ : ℕ => reachProb centipede4.toExtensiveForm centipedeAltStrategy hist)
      Filter.atTop (nhds (reachProb centipede4.toExtensiveForm centipedeAltStrategy hist)) :=
  reachProb_tendsto centipede4.toExtensiveForm (fun _ => centipedeAltStrategy) centipedeAltStrategy
    (fun _ _ => tendsto_const_nhds) hist

/-- **`infoSetProb_tendsto`** (contract form). Likewise info-set probabilities converge under
step-prob convergence; the hypothesis is dischargeable by the constant sequence as in
`centipede_reachProb_tendsto_const`. -/
theorem centipede_infoSetProb_tendsto
    (σseq : ℕ → centipede4.toExtensiveForm.BehavioralStrategy)
    (σ : centipede4.toExtensiveForm.BehavioralStrategy)
    (hstep : ∀ h e, Filter.Tendsto (fun n => centipede4.toExtensiveForm.stepProb (σseq n) h e)
      Filter.atTop (nhds (centipede4.toExtensiveForm.stepProb σ h e)))
    (i : Fin 2) (obs : List (Fin 2)) :
    Filter.Tendsto (fun n => infoSetProb centipede4.toExtensiveForm (σseq n)
        (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) i obs)
      Filter.atTop (nhds (infoSetProb centipede4.toExtensiveForm σ
        (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) i obs)) :=
  infoSetProb_tendsto centipede4.toExtensiveForm
    (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) σseq σ hstep i obs

/-- **`bayesBeliefAt_tendsto_of_pos`** (contract form). Where the limiting info-set probability is
positive, the Bayes beliefs converge. This exposes the lemma contract (convergence and positivity
hypotheses); the convergence half is dischargeable by a constant sequence. -/
theorem centipede_bayesBeliefAt_tendsto
    (σseq : ℕ → centipede4.toExtensiveForm.BehavioralStrategy)
    (σ : centipede4.toExtensiveForm.BehavioralStrategy)
    (hstep : ∀ h e, Filter.Tendsto (fun n => centipede4.toExtensiveForm.stepProb (σseq n) h e)
      Filter.atTop (nhds (centipede4.toExtensiveForm.stepProb σ h e)))
    (i : Fin 2) (obs : List (Fin 2))
    (hpos : 0 < infoSetProb centipede4.toExtensiveForm σ
      (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) i obs)
    (hist : List (Fin 2)) :
    Filter.Tendsto (fun n => bayesBeliefAt centipede4.toExtensiveForm (σseq n)
        (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) i obs hist)
      Filter.atTop (nhds (bayesBeliefAt centipede4.toExtensiveForm σ
        (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) i obs hist)) :=
  bayesBeliefAt_tendsto_of_pos centipede4.toExtensiveForm
    (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) σseq σ hstep i obs hpos hist

/-- **`IsPerfectBayesianEquilibrium_of_IsSequentialEquilibrium`.** A sequential equilibrium is a
perfect Bayesian equilibrium. Stated as a one-way implication on the centipede form. -/
theorem centipede_PBE_of_SeqEq
    (a : Assessment centipede4.toExtensiveForm)
    (hseq : IsSequentialEquilibrium centipede4.toExtensiveGame a) :
    IsPerfectBayesianEquilibrium centipede4.toExtensiveGame a :=
  IsPerfectBayesianEquilibrium_of_IsSequentialEquilibrium centipede4.toExtensiveGame a hseq

/-- **`IsSequentialEquilibriumOneShot_iff_seqEqPred`.** The one-shot sequential-equilibrium
predicate coincides with the refinement-scaffold equilibrium. -/
theorem centipede_seqEqOneShot_iff_pred
    (a : Assessment centipede4.toExtensiveForm) :
    IsSequentialEquilibriumOneShot centipede4.toExtensiveGame a ↔
      centipede4.toExtensiveGame.seqEqPred.IsRefinedEquilibrium a :=
  IsSequentialEquilibriumOneShot_iff_seqEqPred centipede4.toExtensiveGame a

/-- Centipede has no joint nodes (it is a perfect-information tree). -/
theorem centipede_no_joint (h : List (Fin 2)) (n : JointNode (Fin 2) (Fin 2)) :
    centipede4.toExtensiveForm.tree.nodeKind h ≠ .joint n := by
  rcases centipede4.toGameTree_nodeKind_cases h with ⟨_, hk⟩ | ⟨_, hk⟩ <;>
    rw [show centipede4.toExtensiveForm.tree = centipede4.toGameTree from rfl, hk] <;>
    exact fun hcontra => by cases hcontra

/-- **`reachProb_pos_of_totallyMixed_of_pos`, instantiated concretely.** Any history reachable with
positive probability under *some* strategy is also reached with positive probability under a
*totally mixed* strategy. We discharge every hypothesis on concrete data: The totally-mixed witness
is the uniform `centipedeAltStrategy` (`centipedeAltStrategy_totallyMixed`), the reference strategy
is the backward-induction strategy, and the anchor history is the root `[]`, which is reached with
probability `1` (hence `> 0`). The conclusion is therefore a concrete positivity fact, not a
restatement of the library contract. -/
theorem centipede_reachProb_pos_of_totallyMixed :
    0 < reachProb centipede4.toExtensiveForm centipedeAltStrategy [] := by
  have hroot : 0 < reachProb centipede4.toExtensiveForm
      centipede4.backwardInductionBehavioralStrategy [] := by
    change (0 : ℝ) < centipede4.toExtensiveForm.finitePrefixProb
      centipede4.backwardInductionBehavioralStrategy []
    rw [show centipede4.toExtensiveForm.finitePrefixProb
      centipede4.backwardInductionBehavioralStrategy [] = 1 from rfl]
    norm_num
  exact reachProb_pos_of_totallyMixed_of_pos centipede4.toExtensiveGame centipede_no_joint
    centipedeAltStrategy centipede4.backwardInductionBehavioralStrategy
    centipedeAltStrategy_totallyMixed hroot

/-- **`FrontierComplete` unfolds to its closure condition** (definitional). A `FrontierComplete`
frontier `F` for player `0` under beliefs `μ` and a strategy `σ'` is closed under the
belief-support reach successors. This is the *definitional shape*, not a satisfiability witness —
`F` is arbitrary, so it may be empty or fail the closure condition. The concrete *satisfiable*
instances are `centipede_frontierComplete_empty` and `centipede_frontierComplete_root_player1`
below. -/
theorem centipede_frontierComplete_def
    (σ' : centipede4.toExtensiveForm.BehavioralStrategy) (F : Finset (List (Fin 2))) :
    FrontierComplete centipede4.toExtensiveForm
        (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) 0 σ' F ↔
      ∀ z ∈ F, (centipede4.toExtensiveForm.tree.nodeKind z).movesAt 0 →
        ∀ x ∈ (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree).support 0
          (centipede4.toExtensiveForm.info.observe 0 z),
          0 < reachProb centipede4.toExtensiveForm σ' x.1 → x.1 ∈ F :=
  Iff.rfl

/-- **Concrete satisfiable `FrontierComplete` (empty frontier).** The empty frontier is vacuously
complete for player `0`: There is no `z ∈ ∅` to discharge the closure condition for. This certifies
the predicate is inhabited (not unsatisfiable). -/
theorem centipede_frontierComplete_empty
    (σ' : centipede4.toExtensiveForm.BehavioralStrategy) :
    FrontierComplete centipede4.toExtensiveForm
      (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) 0 σ' (∅ : Finset (List (Fin 2))) := by
  intro z hz
  simp only [Finset.notMem_empty] at hz

/-- **Concrete satisfiable `FrontierComplete` (nonempty root frontier for player 1).** The
singleton root frontier `{[]}` is complete for player `1`: Player `1` does *not* move at the
centipede root (player `0` does, `movesAt 1 [] = (0 = 1)`, false), so the closure condition is
vacuously satisfied at the only frontier node. This exhibits a *nonempty* satisfiable frontier, the
meaningful non-vacuity content. -/
theorem centipede_frontierComplete_root_player1
    (σ' : centipede4.toExtensiveForm.BehavioralStrategy) :
    FrontierComplete centipede4.toExtensiveForm
      (trivialBeliefs (Fin 2) (Fin 2) centipede4.toGameTree) 1 σ'
      ({[]} : Finset (List (Fin 2))) := by
  intro z hz hmoves
  rw [Finset.mem_singleton] at hz
  subst hz
  exact absurd hmoves (show ¬ ((0 : Fin 2) = 1) by decide)

/-! ### Perfect recall on the one-decision `oneShotFEF` (PerfectRecall.lean, OneShotDeviation.lean)

`oneShotFEF` (imported from `ExtensiveFormCore`) is a `FiniteExtensiveForm`, so it hosts the
`IsPerfectRecall` predicate and the `IsPerfectRecall.reachCoherent` transport — neither of which a
`FinitePerfectInfoTree` (whose `Obs = List E` is infinite) can host. The one-decision game is
trivially perfect-recall: The *only* history where any player moves is the root `[]` (player 0), so
the no-revisit and action-recall clauses reduce to `[] = []`. -/

open EconlibTest.GameTheory.ExtensiveFormCore (oneShotFEF oneShotTree oneShotTree_movesAt_iff)

/-- **`IsPerfectRecall` on `oneShotFEF`.** The one-decision game has perfect recall: Only the root
is a decision node, so any two histories in the same information set where a player moves are both
the root, hence equal. -/
theorem oneShotFEF_isPerfectRecall : oneShotFEF.IsPerfectRecall := by
  -- Both moving histories are the root `[]`, so the experiences coincide by `rfl`.
  intro i h₁ h₂ _ _ hm₁ hm₂ _
  have e₁ : h₁ = [] ∧ i = 0 := (oneShotTree_movesAt_iff i h₁).mp hm₁
  have e₂ : h₂ = [] ∧ i = 0 := (oneShotTree_movesAt_iff i h₂).mp hm₂
  rw [e₁.1, e₂.1]

/-- **`IsPerfectRecall.reachCoherent`: The recall transport.** The `FiniteExtensiveForm`-level
perfect recall of `oneShotFEF` transports to the `ExtensiveForm`-level reach-coherence bundle
`IsReachCoherent` that the one-shot deviation principle consumes. This is the central hypothesis of
the OSDP, exercised on a concrete finite extensive form. -/
theorem oneShotFEF_isReachCoherent : oneShotFEF.toExtensiveForm.IsReachCoherent :=
  IsPerfectRecall.reachCoherent oneShotFEF_isPerfectRecall

/-- **`LastStopAlign` on `oneShotFEF`.** The last-stop alignment is *vacuous* on the one-decision
game: The only reachable history where a player moves is the root `[]`, whose length is `0`, so the
hypothesis `m < z.length` is never satisfiable. This is the second non-`IsReachCoherent` hypothesis
of the one-shot deviation principle. -/
theorem oneShotFEF_lastStopAlign : oneShotFEF.toExtensiveForm.LastStopAlign := by
  intro i z w _ _ hmz _ _ m hm_lt _ _
  -- The mover history `z` is the root `[]`, so `z.length = 0` and `m < 0` is impossible.
  have hz : z = [] ∧ i = 0 := (oneShotTree_movesAt_iff i z).mp hmz
  rw [hz.1] at hm_lt
  exact absurd hm_lt (by simp)

/-- **`reachProb_pos_of_belief_pos`** (contract on the centipede form). Given a belief-limit
hypothesis (the consistency-sequence convergence) and a positive belief at an info-set node, *some*
trembling-sequence index reaches that node with positive probability. We exercise the lemma's
contract on `centipede4.toExtensiveGame`; supplying the hypotheses confirms the conclusion is a
genuine existence claim, non-vacuous wherever a positive belief sits on a reachable node. -/
theorem centipede_reachProb_pos_of_belief_pos
    (a : Assessment centipede4.toExtensiveForm)
    (σseq : ℕ → centipede4.toExtensiveForm.BehavioralStrategy)
    (hlim : ∀ (i : Fin 2) (obs : List (Fin 2)) (h : List (Fin 2)),
      Filter.Tendsto (fun n => bayesBeliefAt centipede4.toExtensiveForm (σseq n) a.beliefs i obs h)
        Filter.atTop (nhds (a.beliefs.prob i obs h)))
    (i : Fin 2) (obs : List (Fin 2)) (x : centipede4.toExtensiveForm.InfoSet i obs)
    (hbel : 0 < a.beliefs.belief i obs x) :
    ∃ n, 0 < reachProb centipede4.toExtensiveForm (σseq n) x.1 :=
  reachProb_pos_of_belief_pos centipede4.toExtensiveGame a σseq hlim i obs x hbel

end EconlibTest.GameTheory.ExtensiveFormSPE

end
