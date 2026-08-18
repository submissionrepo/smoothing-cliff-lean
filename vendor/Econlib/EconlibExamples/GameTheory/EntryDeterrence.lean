/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Entry Deterrence by Capacity Commitment (Dixit)

In the Dixit (1980) entry-deterrence model — building on Spence (1977) — an *incumbent* monopolist
commits to production capacity before a potential *entrant* decides whether to enter the market.
Capacity is a strategic instrument: A large enough commitment makes post-entry competition
unprofitable for the entrant, who then stays out. The classic insight is **strategic
overinvestment**: The incumbent installs *more* capacity than a protected monopolist would choose,
sacrificing monopoly profit to make the deterrence threat credible — yet stops at the cheapest
deterring level rather than over-deterring.

## The game

* **Stage 1.** The incumbent (player `0`) commits to capacity from `{low, medium, high}`.
* **Stage 2.** The entrant (player `1`) observes the capacity and chooses `enter` or `stay out`.

Payoffs `(incumbent, entrant)`:

| capacity | `enter`   | `stay out` | entrant's BR |
| -------- | --------- | ---------- | ------------ |
| low      | `(4, 2)`  | `(8, 0)`   | enter        |
| medium   | `(2, −1)` | `(6, 0)`   | stay out     |
| high     | `(1, −2)` | `(5, 0)`   | stay out     |

Low capacity leaves post-entry profits positive, inviting entry; medium and high capacity make
entry strictly unprofitable. Anticipating the entrant, the incumbent compares `4` (low, entry
accommodated), `6` (medium, deterred), `5` (high, deterred at wasteful extra capacity) and picks
**medium**: **the SPE outcome is `(medium, stay out)` with payoffs `(6, 0)`.**

Three economic features:

* **Deterrence beats accommodation:** the SPE profit `6` strictly exceeds the accommodation value
  `4` of low capacity (`entryDeterrence_deters`).
* **Strategic overinvestment (a *capacity* comparison):** absent the entry threat the incumbent
  would pick *low* (monopoly profits are `8 > 6 > 5` across the rows' stay-out column), but the SPE
  incumbent commits to *medium* — so the equilibrium capacity strictly exceeds the protected
  monopolist's optimal capacity in the order `0 < 1 < 2`
  (`entryDeterrence_strategic_overinvestment`, bundled in
  `entryDeterrence_overinvestment_verdict`). The mere threat of entry distorts *investment*
  strictly upward; the profit cap `6 < 8` (`entryDeterrence_overinvestment_cost`) is its price.
* **No over-deterrence:** medium beats high — capacity beyond the deterring level burns profit
  without buying anything.

## Lean construction: Mixed arity

This is the library's first **mixed-arity** perfect-information tree: A ternary root over `Fin 3`
capacities followed by binary entry nodes over `Fin 2`. The event alphabet must host the largest
arity, so `E = Fin 3` and the binary nodes embed their choices via `Fin.castLEEmb : Fin 2 ↪ Fin 3`
instead of `Function.Embedding.refl`. The `bi_dominates` and `bi_generic` tactics handle the binary
and ternary backward-induction goals over the underlying concrete `Fin n` choice types.

## Main definitions and theorems

* `entryDeterrence : FinitePerfectInfoTree (Fin 2) (Fin 3)` — the capacity-commitment game.
* `entryDeterrence_backwardInduction_is_SPE` — backward induction is subgame perfect.
* `entryDeterrence_SPE_incumbent_profit` / `entryDeterrence_SPE_entrant_profit` — SPE payoffs
  `(6, 0)`: Medium capacity, no entry.
* `entryDeterrence_deters` — deterrence beats accommodation: The SPE profit strictly exceeds the
  value of low capacity (which would be met by entry).
* `entryDeterrence_overinvestment_cost` — the entry threat is costly: The SPE profit falls strictly
  short of the protected-monopoly profit `8` at low capacity.
* `entryDeterrence_isGeneric` and `entryDeterrence_SPE_unique` — every comparison is strict, so the
  backward-induction strategy is the unique subgame-perfect local strategy.
* `monopolyProfit` / `monopolyCapacity` — the protected-monopoly benchmark: The stay-out payoff at
  each capacity (`![8, 6, 5]`) and the capacity (`low`) that maximizes it, with
  `monopolyCapacity_optimal` and `monopolyCapacity_unique_optimal` proving `low` is the (unique)
  monopoly optimum.
* `speCapacity` — the SPE capacity, *read off the backward-induction root choice*
  (`backwardInductionRootChoice`), with `speCapacity_eq_medium` proving it equals `medium`.
* `entryDeterrence_strategic_overinvestment` — the formal overinvestment claim, a *capacity*
  comparison: `monopolyCapacity < speCapacity` (`0 < 1`). The bundled
  `entryDeterrence_overinvestment_verdict` collects this with deterrence and no-over-deterrence.

## References

Dixit, Avinash. 1980. “The Role of Investment in Entry-Deterrence.” The Economic Journal 90 (357):
95. https://doi.org/10.2307/2231658. Spence, A. Michael. 1977. “Entry, Capacity, Investment and
Oligopolistic Pricing.” Bell Journal of Economics, no. 2: 534–44.
-/

noncomputable section

namespace EconlibExamples.GameTheory.EntryDeterrence

open Econlib.GameTheory

/-! ## The Game Tree -/

/-- Stage-2 entry decision: The entrant chooses `enter` (choice `0`, payoffs `enterPay`) or
`stay out` (choice `1`, payoffs `stayOutPay`). A binary node inside a `Fin 3`-event tree, so the
two choices embed via `Fin.castLEEmb` rather than the identity embedding. -/
def entryNode (enterPay stayOutPay : Fin 2 → ℝ) : FinitePerfectInfoTree (Fin 2) (Fin 3) :=
  .decision 1 (Fin 2) (Fin.castLEEmb (by norm_num : (2 : ℕ) ≤ 3))
    ![.terminal enterPay, .terminal stayOutPay]

/-- **The entry-deterrence game.** The incumbent commits to capacity `low`/`medium`/`high` (choices
`0, 1, 2`); the entrant observes and decides on entry. Payoff vectors are `![incumbent, entrant]`
per the table in the module docstring. -/
def entryDeterrence : FinitePerfectInfoTree (Fin 2) (Fin 3) :=
  .decision 0 (Fin 3) (Function.Embedding.refl _)
    ![entryNode ![4,  2] ![8, 0],
      entryNode ![2, -1] ![6, 0],
      entryNode ![1, -2] ![5, 0]]

/-! ## Subgame Perfection by Backward Induction -/

/-- **Subgame-perfect equilibrium.** The backward-induction behavioral strategy is an SPE of the
underlying extensive game — a direct instance of the general theorem. -/
theorem entryDeterrence_backwardInduction_is_SPE :
    entryDeterrence.toExtensiveGame.IsSubgamePerfectEquilibrium
      entryDeterrence.backwardInductionBehavioralStrategy :=
  entryDeterrence.isSubgamePerfectEquilibrium_backwardInduction

/-! ## Backward-Induction Values -/

/-- **Entry node value when entry is profitable**: If the entrant's post-entry payoff strictly
exceeds its outside payoff, the node's value is the post-entry payoff vector. -/
private lemma entryNode_value_enter (enterPay stayOutPay : Fin 2 → ℝ) (i : Fin 2)
    (h : stayOutPay 1 < enterPay 1) :
    (entryNode enterPay stayOutPay).backwardInductionValue i = enterPay i := by
  unfold entryNode
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 0)
    (h := by bi_dominates)]
  rfl

/-- **Entry node value when entry is deterred**: If the entrant's post-entry payoff is strictly
below its outside payoff, the node's value is the stay-out payoff vector. -/
private lemma entryNode_value_stayOut (enterPay stayOutPay : Fin 2 → ℝ) (i : Fin 2)
    (h : enterPay 1 < stayOutPay 1) :
    (entryNode enterPay stayOutPay).backwardInductionValue i = stayOutPay i := by
  unfold entryNode
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 1)
    (h := by bi_dominates)]
  rfl

/-! ### The incumbent's continuation profits, computed once

The three capacity nodes' incumbent values (`4`, `6`, `5`) and the strict comparisons among
them are the only quantitative content of the root analysis. We prove them once here and reuse them
in the node value, root choice, and genericity arguments below — there is no need to recompute them
per theorem. -/

/-- **Low capacity: Incumbent profit `4`** — entry is accommodated, so the node resolves to the
post-entry payoff `![4, 2]`. -/
private lemma incumbentValue_low :
    (entryNode ![4, 2] ![8, 0]).backwardInductionValue 0 = 4 := by
  rw [entryNode_value_enter _ _ 0 (by norm_num)]; norm_num

/-- **Medium capacity: Incumbent profit `6`** — entry is deterred, so the node resolves to the
stay-out payoff `![6, 0]`. -/
private lemma incumbentValue_medium :
    (entryNode ![2, -1] ![6, 0]).backwardInductionValue 0 = 6 := by
  rw [entryNode_value_stayOut _ _ 0 (by norm_num)]; norm_num

/-- **High capacity: Incumbent profit `5`** — entry is deterred at wasteful extra capacity, so the
node resolves to the stay-out payoff `![5, 0]`. -/
private lemma incumbentValue_high :
    (entryNode ![1, -2] ![5, 0]).backwardInductionValue 0 = 5 := by
  rw [entryNode_value_stayOut _ _ 0 (by norm_num)]; norm_num

/-- Medium strictly beats low (deterrence beats accommodation): `6 > 4`. -/
private lemma medium_beats_low :
    (entryNode ![4, 2] ![8, 0]).backwardInductionValue 0 <
      (entryNode ![2, -1] ![6, 0]).backwardInductionValue 0 := by
  rw [incumbentValue_low, incumbentValue_medium]; norm_num

/-- Medium strictly beats high (no over-deterrence): `6 > 5`. -/
private lemma medium_beats_high :
    (entryNode ![1, -2] ![5, 0]).backwardInductionValue 0 <
      (entryNode ![2, -1] ![6, 0]).backwardInductionValue 0 := by
  rw [incumbentValue_high, incumbentValue_medium]; norm_num

/-- Low and high give the incumbent distinct profits: `4 ≠ 5`. -/
private lemma low_ne_high :
    (entryNode ![4, 2] ![8, 0]).backwardInductionValue 0 ≠
      (entryNode ![1, -2] ![5, 0]).backwardInductionValue 0 := by
  rw [incumbentValue_low, incumbentValue_high]; norm_num

/-- **Whole-game value: Medium capacity, entry deterred.** The incumbent's three continuation
profits are `4` (low → entry), `6` (medium → deterred), `5` (high → deterred); choice `1` (medium)
is the strict argmax. -/
private lemma entryDeterrence_value (i : Fin 2) :
    entryDeterrence.backwardInductionValue i = ![6, 0] i := by
  unfold entryDeterrence
  rw [FinitePerfectInfoTree.backwardInductionValue_decision_eq_of_strictArgmax (c := 1)
    (h := by bi_dominates [incumbentValue_low, incumbentValue_medium, incumbentValue_high])]
  exact entryNode_value_stayOut _ _ i (by norm_num)

/-- **The incumbent's SPE profit is `6`** — medium capacity with entry deterred. -/
theorem entryDeterrence_SPE_incumbent_profit :
    entryDeterrence.backwardInductionValue 0 = 6 := by
  rw [entryDeterrence_value]; norm_num

/-- **The entrant's SPE payoff is `0`** — it stays out against medium capacity. -/
theorem entryDeterrence_SPE_entrant_profit :
    entryDeterrence.backwardInductionValue 1 = 0 := by
  rw [entryDeterrence_value]; norm_num

/-- **Deterrence beats accommodation.** The incumbent's SPE profit strictly exceeds the value of
committing to low capacity, which the entrant would meet with entry. -/
theorem entryDeterrence_deters :
    (entryNode ![4, 2] ![8, 0]).backwardInductionValue 0 <
      entryDeterrence.backwardInductionValue 0 := by
  rw [entryDeterrence_SPE_incumbent_profit, incumbentValue_low]; norm_num

/-- **The entry threat is costly (strategic overinvestment).** A protected monopolist would pick
low capacity and earn `8`; the mere threat of entry forces the deterring medium capacity and caps
the incumbent at `6 < 8`. -/
theorem entryDeterrence_overinvestment_cost :
    entryDeterrence.backwardInductionValue 0 < 8 := by
  rw [entryDeterrence_SPE_incumbent_profit]; norm_num

/-! ## Uniqueness of the SPE -/

/-- **Entry nodes are generic** whenever the entrant's two payoffs differ. -/
private lemma entryNode_isGeneric (enterPay stayOutPay : Fin 2 → ℝ)
    (hne : enterPay 1 ≠ stayOutPay 1) :
    (entryNode enterPay stayOutPay).IsGeneric := by
  unfold entryNode
  bi_generic <;> exact FinitePerfectInfoTree.isGeneric_terminal _

/-- **The entry-deterrence game is generic**: The entrant's payoffs differ at every entry node, and
the incumbent's three continuation profits `4, 6, 5` are pairwise distinct. -/
theorem entryDeterrence_isGeneric : entryDeterrence.IsGeneric := by
  unfold entryDeterrence
  bi_generic [incumbentValue_low, incumbentValue_medium, incumbentValue_high]
  · exact entryNode_isGeneric _ _ (by norm_num)
  · exact entryNode_isGeneric _ _ (by norm_num)
  · exact entryNode_isGeneric _ _ (by norm_num)

/-- **The entry-deterrence SPE is unique.** Every subgame-perfect local strategy — pure or mixed —
equals the backward-induction strategy. -/
theorem entryDeterrence_SPE_unique (s : entryDeterrence.LocalBehavioralStrategy)
    (hs : entryDeterrence.IsSubgamePerfectStrategy s) :
    s = entryDeterrence.backwardInductionStrategy :=
  hs.eq_backwardInductionStrategy entryDeterrence_isGeneric

/-! ## Strategic Overinvestment: SPE Capacity vs. Protected-Monopoly Benchmark

The profit theorems above (`entryDeterrence_deters`, `entryDeterrence_overinvestment_cost`)
compare *payoffs*. The Dixit insight is fundamentally about *capacity*: The SPE incumbent installs
strictly more capacity than a protected monopolist would. This section makes the capacity
comparison formal by (1) establishing the protected-monopoly benchmark and its optimal (low)
capacity, (2) extracting the SPE capacity from the *actual* backward-induction root choice (not a
hand-set constant), and (3) proving the SPE capacity strictly exceeds the benchmark in the natural
capacity order `0 < 1 < 2`. -/

/-- **Protected-monopoly profit at each capacity.** With *no* entrant, the incumbent simply
collects the stay-out payoff of each capacity row — the first (incumbent) coordinate of
`stayOutPay`: Low→`8`, medium→`6`, high→`5`. These are exactly the `stayOutPay 0` entries of the
three `entryNode`s in `entryDeterrence` (`![8, 0] 0 = 8`, `![6, 0] 0 = 6`, `![5, 0] 0 = 5`): A
protected monopolist faces no entry threat, so each capacity yields its own stay-out value with
certainty. -/
def monopolyProfit : Fin 3 → ℝ := ![8, 6, 5]

/-- **The protected monopolist's optimal capacity is low (`0`).** Absent any entry threat, monopoly
profit is highest at the lowest capacity, so the unconstrained monopolist installs `low`. -/
def monopolyCapacity : Fin 3 := 0

/-- **Monopoly optimality.** Low capacity maximizes protected-monopoly profit over all
capacities. -/
theorem monopolyCapacity_optimal :
    ∀ c : Fin 3, monopolyProfit c ≤ monopolyProfit monopolyCapacity := by
  intro c
  fin_cases c <;> norm_num [monopolyProfit, monopolyCapacity]

/-- **Strict monopoly optimality.** Every capacity other than low yields strictly lower
protected-monopoly profit — low is the *unique* monopoly-optimal capacity. -/
theorem monopolyCapacity_unique_optimal :
    ∀ c : Fin 3, c ≠ monopolyCapacity → monopolyProfit c < monopolyProfit monopolyCapacity := by
  intro c hc
  fin_cases c <;> simp_all [monopolyProfit, monopolyCapacity] <;> norm_num

/-- **The SPE capacity, read off backward induction.** Defined as the root choice the
backward-induction algorithm actually selects at the incumbent's decision node — *not* hand-set to
a constant. `speCapacity_eq_medium` then proves it equals medium (`1`). -/
def speCapacity : Fin 3 := entryDeterrence.backwardInductionRootChoice

/-- **The SPE capacity is medium (`1`).** Backward induction at the root compares the incumbent's
three continuation profits — `4` (low, entry accommodated), `6` (medium, deterred), `5` (high,
deterred wastefully) — and the strict argmax is medium. This is what makes `speCapacity` *derived*
from the equilibrium rather than asserted. -/
theorem speCapacity_eq_medium : speCapacity = 1 := by
  unfold speCapacity entryDeterrence FinitePerfectInfoTree.backwardInductionRootChoice
  refine FinitePerfectInfoTree.bestChoice_eq_of_strictArgmax (Fin 3) _ 1 ?_
  intro c hc
  fin_cases c <;> first | exact absurd rfl hc | exact medium_beats_low | exact medium_beats_high

/-- **Strategic overinvestment (capacity form).** Predicate: The SPE capacity strictly exceeds the
benchmark capacity in the natural capacity order. -/
def Overinvests (benchmark spe : Fin 3) : Prop := benchmark < spe

/-- **Strategic overinvestment, the central capacity claim.** The SPE incumbent's capacity
(`medium`) strictly exceeds the protected monopolist's optimal capacity (`low`) in the order
`0 < 1 < 2`. The mere *threat* of entry distorts the capacity choice strictly upward — the formal
content of Dixit's "overinvestment," stated on capacities rather than on profits. -/
theorem entryDeterrence_strategic_overinvestment : monopolyCapacity < speCapacity := by
  rw [speCapacity_eq_medium]; decide

/-- **Overinvestment verdict (bundled).** The strategic-overinvestment verdict, conjoining the
load-bearing facts (subgame perfection and SPE uniqueness are the separate
`entryDeterrence_backwardInduction_is_SPE` and `entryDeterrence_SPE_unique`):

* `monopolyCapacity = 0` — the protected monopolist installs *low* capacity;
* `speCapacity = 1` — backward induction selects *medium* capacity at the root;
* `monopolyCapacity < speCapacity` — the SPE capacity strictly exceeds the benchmark
  (`Overinvests monopolyCapacity speCapacity`): Strategic overinvestment holds;
* entry is *deterred* at the SPE capacity — at the medium entry node the entrant's value resolves
  to its stay-out payoff `![6, 0]` (so the entrant stays out, collecting its outside option `0`);
* no over-deterrence — the incumbent's SPE continuation profit `6` (medium) strictly exceeds the
  `5` it would earn by deterring with *high* capacity, so it stops at the cheapest deterring
  level. -/
theorem entryDeterrence_overinvestment_verdict :
    monopolyCapacity = 0 ∧ speCapacity = 1 ∧
      Overinvests monopolyCapacity speCapacity ∧
      (∀ i, (entryNode ![2, -1] ![6, 0]).backwardInductionValue i = ![6, 0] i) ∧
      (entryNode ![1, -2] ![5, 0]).backwardInductionValue 0 <
        (entryNode ![2, -1] ![6, 0]).backwardInductionValue 0 := by
  refine ⟨rfl, speCapacity_eq_medium, entryDeterrence_strategic_overinvestment, ?_, ?_⟩
  · -- Entry deterred at medium: the node value is the stay-out payoff vector, entrant gets `0`.
    intro i
    exact entryNode_value_stayOut _ _ i (by norm_num)
  · -- No over-deterrence: medium deterring profit `6` beats high deterring profit `5`.
    exact medium_beats_high

end EconlibExamples.GameTheory.EntryDeterrence

end
