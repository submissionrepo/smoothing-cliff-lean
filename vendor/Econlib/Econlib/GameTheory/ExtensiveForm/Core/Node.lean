/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Simplex
public import Econlib.Probability.ProbDist.Basic

/-!
# Extensive-form nodes

This file defines the node-level data for the extensive-form API: The four node-kind constructors
(`PlayerNode`, `JointNode`, `ChanceFiniteNode`, `ChanceGeneralNode`), the `NodeKind` inductive that
wraps them, and the local choice and probability operations attached to each node.

The node API defines the per-kind choice, behavior, and pure-choice types; node-local probabilities
and total mixedness; and the player-local participation predicates for information structures. It
also includes the finite-to-general chance-node bridge and the convenience constructors for general
chance nodes.

These node kinds are the local data of the history-based extensive-form model (Kuhn 1953).

## Main definitions

* `PlayerNode`, `JointNode`, `ChanceFiniteNode`, `ChanceGeneralNode`: Node-local data.
* `NodeKind`: Unified node kind for history-based extensive forms.
* `NodeKind.PureChoice`, `NodeKind.Behavior`, `NodeKind.eventProb`: Node-local choice and behavior
  API.
* `ChanceGeneralNode.ofMeasurable`, `ChanceGeneralNode.dirac`, `ChanceGeneralNode.ofChanceFinite`:
  Convenience constructors for general chance nodes.
* `ChanceFiniteNode.toGeneral`: Finite chance node as a general chance node.

## Main statements

* `NodeKind.iChoiceTypeAt'_eq_iChoiceTypeAt`: The total and partial player-choice types agree when
  the player moves.
* `ChanceGeneralNode.eventProb_ofChanceFinite`: Finite-to-general chance-node event probabilities
  agree.
* `ChanceFiniteNode.eventProb_eq_toGeneral_eventProb`: Finite chance probability agrees with the
  coerced general chance node.

## References

* Kuhn, H. W. 1953. “Extensive Games and the Problem of Information.” In *Contributions to the
  Theory of Games, Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

extensive form, node, chance, behavior
-/

@[expose] public noncomputable section

open BigOperators Econlib.Probability

namespace Econlib.GameTheory

universe u

/-- A single-player decision node with a node-local finite choice type. The `[Inhabited]` bracket
rules out empty-choice nodes at the type level. -/
structure PlayerNode (I : Type u) (E : Type u) where
  /-- The player who moves at this node. -/
  mover : I
  /-- The legal choices available at this node. -/
  Choice : Type u
  [instFintypeChoice : Fintype Choice]
  [instDecidableEqChoice : DecidableEq Choice]
  [instInhabitedChoice : Inhabited Choice]
  /-- The public event emitted by a legal choice. -/
  emit : Choice → E

/-- A simultaneous decision node. Each active local decision maker has a node-local choice type.
Each player has at most one active local decision per joint node (`player_injective`), matching the
textbook one-info-set-per-(player, node) story. -/
structure JointNode (I : Type u) (E : Type u) where
  /-- The finite set of active local decision makers at this node. -/
  Active : Type u
  [instFintypeActive : Fintype Active]
  [instDecidableEqActive : DecidableEq Active]
  [instInhabitedActive : Inhabited Active]
  /-- The strategic player represented by an active local decision maker. -/
  player : Active → I
  /-- Each player has at most one active decision-maker at a joint node. -/
  player_injective : Function.Injective player
  /-- The legal choices for each active local decision maker. -/
  Choice : Active → Type u
  [instFintypeChoice : ∀ a, Fintype (Choice a)]
  [instDecidableEqChoice : ∀ a, DecidableEq (Choice a)]
  [instInhabitedChoice : ∀ a, Inhabited (Choice a)]
  /-- The public event emitted by a joint profile of local choices. -/
  emit : ((a : Active) → Choice a) → E

/-- A finite chance node with a node-local finite outcome space. -/
structure ChanceFiniteNode (E : Type u) where
  /-- The finite chance outcome space at this node. -/
  Outcome : Type u
  [instFintypeOutcome : Fintype Outcome]
  [instDecidableEqOutcome : DecidableEq Outcome]
  /-- Nature's finite distribution over outcomes. -/
  dist : FinDist Outcome
  /-- The public event emitted by a chance outcome. -/
  emit : Outcome → E

/-- A general chance node: A measurable outcome space with a probability distribution and an event
emitter whose singleton preimages are measurable. The per-singleton measurability field is
sufficient to compute event probabilities (`eventProb`) without requiring `MeasurableSpace E` to
propagate into the rest of the extensive-form API.

For common construction patterns see the convenience constructors `ChanceGeneralNode.ofMeasurable`
(measurable emit into a discrete-singleton event type), `ChanceGeneralNode.dirac` (a deterministic
event), and `ChanceGeneralNode.ofChanceFinite` (the bridge from finite chance nodes). -/
structure ChanceGeneralNode (E : Type u) where
  /-- The outcome space at this chance node. -/
  Outcome : Type u
  [instMeasurableSpaceOutcome : MeasurableSpace Outcome]
  /-- Nature's probability distribution on the outcome space. -/
  dist : Probability.ProbDist Outcome
  /-- The public event emitted by an outcome. -/
  emit : Outcome → E
  /-- Singleton preimages under `emit` are measurable, so each event has a well-defined probability
  `dist (emit ⁻¹' {e})`. -/
  emit_measurable_singleton : ∀ e : E, MeasurableSet (emit ⁻¹' {e})

attribute [instance]
  PlayerNode.instFintypeChoice PlayerNode.instDecidableEqChoice PlayerNode.instInhabitedChoice
  JointNode.instFintypeActive JointNode.instDecidableEqActive JointNode.instInhabitedActive
  JointNode.instFintypeChoice JointNode.instDecidableEqChoice JointNode.instInhabitedChoice
  ChanceFiniteNode.instFintypeOutcome ChanceFiniteNode.instDecidableEqOutcome
  ChanceGeneralNode.instMeasurableSpaceOutcome

/-- Node kinds for the unified extensive-form API. Histories are lists of public events. -/
inductive NodeKind (I : Type u) (E : Type u) where
  /-- A terminal node with realized payoffs. -/
  | terminal (payoff : I → ℝ)
  /-- A single-player decision node. -/
  | player (node : PlayerNode I E)
  /-- A simultaneous decision node. -/
  | joint (node : JointNode I E)
  /-- A finite chance node. -/
  | chanceFinite (node : ChanceFiniteNode E)
  /-- A reserved general chance node. -/
  | chanceGeneral (node : ChanceGeneralNode E)

namespace NodeKind

variable {I : Type u} {E : Type u}

/-- The pure local choice object appropriate for a node. Terminal and chance nodes have no
strategic choice, represented by `PUnit`. -/
def PureChoice : NodeKind I E → Type u
  | .terminal _ => PUnit
  | .player n => n.Choice
  | .joint n => (a : n.Active) → n.Choice a
  | .chanceFinite _ => PUnit
  | .chanceGeneral _ => PUnit

/-- The mixed/behavioral object appropriate for a node. Player and joint nodes use standard
simplices over their node-local legal choice types. -/
def Behavior : NodeKind I E → Type u
  | .terminal _ => PUnit
  | .player n => stdSimplex ℝ n.Choice
  | .joint n => (a : n.Active) → stdSimplex ℝ (n.Choice a)
  | .chanceFinite _ => PUnit
  | .chanceGeneral _ => PUnit

/-- Embed a pure local choice as a node-local behavioral object. -/
def pureBehavior : (k : NodeKind I E) → k.PureChoice → k.Behavior
  | .terminal _, _ => PUnit.unit
  | .player n, c => (stdSimplex.vertex c : stdSimplex ℝ n.Choice)
  | .joint n, c => (fun a => stdSimplex.vertex (c a) : (a : n.Active) → stdSimplex ℝ (n.Choice a))
  | .chanceFinite _, _ => PUnit.unit
  | .chanceGeneral _, _ => PUnit.unit

/-- Probability that a node-local behavioral object emits public event `e`. For general chance
nodes this is the probability of the singleton preimage of `e` under the node's distribution. -/
def eventProb [DecidableEq E] : (k : NodeKind I E) → k.Behavior → E → ℝ
  | .terminal _, _, _ => 0
  | .player n, b, e =>
      ∑ c : n.Choice, if n.emit c = e then (b : stdSimplex ℝ n.Choice).val c else 0
  | .joint n, b, e =>
      ∑ c : ((a : n.Active) → n.Choice a),
        if n.emit c = e then
          ∏ a : n.Active, (b : (a : n.Active) → stdSimplex ℝ (n.Choice a)) a (c a)
        else 0
  | .chanceFinite n, _, e =>
      ∑ ω : n.Outcome, if n.emit ω = e then n.dist ω else 0
  | .chanceGeneral n, _, e => ((n.dist (n.emit ⁻¹' {e}) : NNReal) : ℝ)

/-- A node-local behavior is totally mixed if every legal strategic choice receives positive
probability. Terminal and chance nodes satisfy this vacuously. -/
def IsTotallyMixed : (k : NodeKind I E) → k.Behavior → Prop
  | .terminal _, _ => True
  | .player n, b => ∀ c : n.Choice, 0 < (b : stdSimplex ℝ n.Choice).val c
  | .joint n, b =>
      ∀ (a : n.Active) (c : n.Choice a),
        0 < (b : (a : n.Active) → stdSimplex ℝ (n.Choice a)) a c
  | .chanceFinite _, _ => True
  | .chanceGeneral _, _ => True

/-- Whether player `i` makes a strategic choice at this node: True at a single-player node when `i`
is the mover, true at a joint node when some active local decision maker represents `i`, false at
terminal and chance nodes. -/
def movesAt : NodeKind I E → I → Prop
  | .terminal _, _ => False
  | .player n, i => n.mover = i
  | .joint n, i => ∃ a : n.Active, n.player a = i
  | .chanceFinite _, _ => False
  | .chanceGeneral _, _ => False

/-- Two node-local behaviors agree on every component not controlled by player `i`. For player
nodes where `i` is not the mover, the behaviors must be equal; for joint nodes, every active local
decision maker representing a player other than `i` must have identical behavior under both. Chance
and terminal nodes have no strategic choice and so the predicate is vacuous. -/
def iAgrees : (k : NodeKind I E) → (i : I) → k.Behavior → k.Behavior → Prop
  | .terminal _, _, _, _ => True
  | .player n, i, b, b' => n.mover ≠ i → b = b'
  | .joint n, i, b, b' => ∀ a : n.Active, n.player a ≠ i → b a = b' a
  | .chanceFinite _, _, _, _ => True
  | .chanceGeneral _, _, _, _ => True

/-- Equal node-local behaviors trivially `iAgrees` for every player: Equality is stronger than
agreement on non-`i` components. -/
lemma iAgrees_of_eq {k : NodeKind I E} (i : I) {b b' : k.Behavior} (heq : b = b') :
    k.iAgrees i b b' := by
  subst heq; cases k <;> simp [NodeKind.iAgrees]

/-- **Event probabilities are nonnegative.** Each per-kind formula is a finite sum of nonnegative
terms (simplex masses, products of simplex masses, or chance-distribution masses), or an `NNReal`
cast, all of which are `≥ 0`. -/
lemma eventProb_nonneg [DecidableEq E] (k : NodeKind I E) (b : k.Behavior) (e : E) :
    0 ≤ k.eventProb b e := by
  cases k with
  | terminal _ => simp [eventProb]
  | player n =>
      -- Each term is `if … then (simplex mass) else 0`, nonnegative by simplex membership.
      refine Finset.sum_nonneg (fun c _ => ?_)
      split_ifs with h
      · exact (b : stdSimplex ℝ n.Choice).2.1 c
      · exact le_rfl
  | joint n =>
      -- Each term is `if … then (∏ simplex masses) else 0`, a product of nonnegatives.
      refine Finset.sum_nonneg (fun c _ => ?_)
      split_ifs with h
      · exact Finset.prod_nonneg (fun a _ =>
          (b : (a : n.Active) → stdSimplex ℝ (n.Choice a)) a |>.2.1 (c a))
      · exact le_rfl
  | chanceFinite n =>
      -- Each term is `if … then (chance mass) else 0`, nonnegative by `FinDist.nonneg`.
      refine Finset.sum_nonneg (fun ω _ => ?_)
      split_ifs with h
      · exact n.dist.nonneg ω
      · exact le_rfl
  | chanceGeneral n => exact NNReal.coe_nonneg _

/-- **`eventProb` transports along a kind equality.** When two kinds are equal, the event
probability of a behavior equals that of its transported behavior at the other kind. -/
lemma eventProb_cast [DecidableEq E] {k1 k2 : NodeKind I E} (hk : k1 = k2)
    (b : k1.Behavior) (e : E) :
    k1.eventProb b e = k2.eventProb (cast (congrArg Behavior hk) b) e := by
  subst hk; rfl

end NodeKind

/-- The unique active position representing player `i` at a joint node where `i` moves. Uses
`Classical.choose` on the existential in `movesAt`; uniqueness comes from `player_injective`. -/
noncomputable def JointNode.iPosition {I E : Type u} (n : JointNode I E) (i : I)
    (hm : ∃ a : n.Active, n.player a = i) : n.Active :=
  Classical.choose hm

/-- The active position `iPosition i hm` does represent player `i`:
`n.player (n.iPosition i hm) =
i`. -/
lemma JointNode.iPosition_player {I E : Type u} (n : JointNode I E) (i : I)
    (hm : ∃ a : n.Active, n.player a = i) :
    n.player (n.iPosition i hm) = i :=
  Classical.choose_spec hm

namespace NodeKind

variable {I E : Type u}

/-- Player `i`'s local choice type at a node where `i` moves. Player nodes: `n.Choice`. Joint
nodes: `n.Choice (n.iPosition i hm)`. Terminal and chance nodes have no choice (absurd). -/
noncomputable def iChoiceTypeAt : (k : NodeKind I E) → (i : I) → k.movesAt i → Type u
  | .terminal _, _, hm => absurd hm id
  | .player n, _, _ => n.Choice
  | .joint n, i, hm => n.Choice (n.iPosition i hm)
  | .chanceFinite _, _, hm => absurd hm id
  | .chanceGeneral _, _, hm => absurd hm id

noncomputable instance instFintypeIChoiceTypeAt (k : NodeKind I E) (i : I) (hm : k.movesAt i) :
    Fintype (k.iChoiceTypeAt i hm) := by
  match k, hm with
  | .player n, _ => exact n.instFintypeChoice
  | .joint n, hm => exact n.instFintypeChoice (n.iPosition i hm)

noncomputable instance instDecidableEqIChoiceTypeAt (k : NodeKind I E) (i : I)
    (hm : k.movesAt i) : DecidableEq (k.iChoiceTypeAt i hm) := by
  match k, hm with
  | .player n, _ => exact n.instDecidableEqChoice
  | .joint n, hm => exact n.instDecidableEqChoice (n.iPosition i hm)

noncomputable instance instInhabitedIChoiceTypeAt (k : NodeKind I E) (i : I)
    (hm : k.movesAt i) : Inhabited (k.iChoiceTypeAt i hm) := by
  match k, hm with
  | .player n, _ => exact n.instInhabitedChoice
  | .joint n, hm => exact n.instInhabitedChoice (n.iPosition i hm)

/-- A total version of `iChoiceTypeAt`: When player `i` does not move at this node, returns
`PUnit`. Used by `InfoStructure` builders that must declare `iChoiceType` over every observation,
not only ones where the player moves. For joint nodes we use `Classical.dec` on the existential
`∃ a, n.player a = i`. -/
noncomputable def iChoiceTypeAt' : NodeKind I E → I → Type u
  | .terminal _, _ => PUnit
  | .player n, i =>
      open Classical in
      if n.mover = i then n.Choice else PUnit
  | .joint n, i =>
      open Classical in
      if h : ∃ a : n.Active, n.player a = i then n.Choice (n.iPosition i h) else PUnit
  | .chanceFinite _, _ => PUnit
  | .chanceGeneral _, _ => PUnit

noncomputable instance instFintypeIChoiceTypeAt' (k : NodeKind I E) (i : I) :
    Fintype (k.iChoiceTypeAt' i) := by
  classical
  cases k <;> dsimp only [iChoiceTypeAt'] <;>
    first | infer_instance | (split_ifs <;> infer_instance)

noncomputable instance instDecidableEqIChoiceTypeAt' (k : NodeKind I E) (i : I) :
    DecidableEq (k.iChoiceTypeAt' i) := by
  classical
  cases k <;> dsimp only [iChoiceTypeAt'] <;> infer_instance

noncomputable instance instInhabitedIChoiceTypeAt' (k : NodeKind I E) (i : I) :
    Inhabited (k.iChoiceTypeAt' i) := by
  classical
  cases k <;> dsimp only [iChoiceTypeAt'] <;>
    first | infer_instance | (split_ifs <;> infer_instance)

/-- At histories where player `i` actually moves, the total `iChoiceTypeAt'` agrees with the
partial `iChoiceTypeAt`. Used as the `iChoice_compatible` proof obligation in the perfect-info
builder. -/
lemma iChoiceTypeAt'_eq_iChoiceTypeAt (k : NodeKind I E) (i : I)
    (hm : k.movesAt i) : k.iChoiceTypeAt' i = k.iChoiceTypeAt i hm := by
  match k, hm with
  | .player n, hm =>
      change iChoiceTypeAt' (.player n) i = n.Choice
      unfold iChoiceTypeAt'
      have h2 : n.mover = i := hm
      simp only [h2, if_true]
  | .joint n, hm =>
      change iChoiceTypeAt' (.joint n) i = n.Choice (n.iPosition i hm)
      unfold iChoiceTypeAt'
      have h2 : ∃ a : n.Active, n.player a = i := hm
      simp only [h2, dif_pos]

/-- Project player `i`'s local-behavior component out of a node-local Behavior. For player nodes,
the whole behavior is `i`'s simplex. For joint nodes, look up the active position representing
`i`. -/
noncomputable def iLocalBehavior : (k : NodeKind I E) → (i : I) → (hm : k.movesAt i) →
    k.Behavior → stdSimplex ℝ (k.iChoiceTypeAt i hm)
  | .player _, _, _, b => b
  | .joint n, i, hm, b => b (n.iPosition i hm)

end NodeKind

/-! ## `ChanceGeneralNode` convenience constructors and the finite/general bridge -/

namespace ChanceGeneralNode

variable {E : Type u}

open MeasureTheory

/-- Build a general chance node from a measurable event-emitter into a type whose singletons are
measurable. Use this when `E` carries a `MeasurableSpace` instance with measurable singletons (e.g.
any countable or finite-discrete event type). -/
def ofMeasurable {Outcome : Type u}
    [MeasurableSpace Outcome] [MeasurableSpace E] [MeasurableSingletonClass E]
    (dist : Econlib.Probability.ProbDist Outcome) (emit : Outcome → E) (h : Measurable emit) :
    ChanceGeneralNode E where
  Outcome := Outcome
  dist := dist
  emit := emit
  emit_measurable_singleton e := h (MeasurableSet.singleton e)

/-- Deterministic chance node: Emits a single fixed event with probability one. The outcome space
is `PUnit` with the discrete σ-algebra and the Dirac measure on its unique element. -/
def dirac (e : E) : ChanceGeneralNode E where
  Outcome := PUnit
  dist := Econlib.Probability.ProbDist.dirac PUnit.unit
  emit := fun _ => e
  emit_measurable_singleton _ := trivial

/-- Bridge a finite chance node to a general chance node. The finite outcome space is given the
discrete σ-algebra (so every set is measurable, including singleton preimages of `emit`), and the
finite distribution is realized as a finite mixture of Dirac measures. -/
def ofChanceFinite (n : ChanceFiniteNode E) : ChanceGeneralNode E :=
  letI ms : MeasurableSpace n.Outcome := ⊤
  haveI : MeasurableSingletonClass n.Outcome := ⟨fun _ => trivial⟩
  let μ : Measure n.Outcome := ∑ ω : n.Outcome, ENNReal.ofReal (n.dist ω) • Measure.dirac ω
  have hprob : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    change (∑ ω : n.Outcome, ENNReal.ofReal (n.dist ω) • Measure.dirac ω) Set.univ = 1
    simp only [Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    have h_pull : ENNReal.ofReal (∑ ω : n.Outcome, n.dist ω)
        = ∑ ω : n.Outcome, ENNReal.ofReal (n.dist ω) :=
      ENNReal.ofReal_sum_of_nonneg (fun ω _ => n.dist.nonneg ω)
    have h_sum_one : ∑ ω : n.Outcome, n.dist ω = (1 : ℝ) := n.dist.sum_one
    rw [← h_pull, h_sum_one, ENNReal.ofReal_one]
  { Outcome := n.Outcome
    instMeasurableSpaceOutcome := ms
    dist := ⟨μ, hprob⟩
    emit := n.emit
    emit_measurable_singleton _ := trivial }

/-- Lifting a finite chance node to a general chance node preserves event probabilities: The
general-chance probability of an event equals the finite-chance combinatorial sum. -/
theorem eventProb_ofChanceFinite {I : Type u} [DecidableEq E]
    (n : ChanceFiniteNode E) (e : E) :
    NodeKind.eventProb (I := I) (.chanceGeneral (ofChanceFinite n)) PUnit.unit e
      = NodeKind.eventProb (I := I) (.chanceFinite n) PUnit.unit e := by
  letI : MeasurableSpace n.Outcome := ⊤
  haveI : MeasurableSingletonClass n.Outcome := ⟨fun _ => trivial⟩
  have h_meas : MeasurableSet (n.emit ⁻¹' {e}) := trivial
  unfold NodeKind.eventProb ofChanceFinite
  dsimp only
  change ((∑ ω : n.Outcome, ENNReal.ofReal (n.dist ω) • Measure.dirac ω)
        (n.emit ⁻¹' {e})).toReal
    = ∑ ω : n.Outcome, if n.emit ω = e then n.dist ω else 0
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ h_meas]
  have h_term : ∀ ω : n.Outcome,
      ENNReal.ofReal (n.dist ω) * (n.emit ⁻¹' {e}).indicator (1 : n.Outcome → ENNReal) ω
        = ENNReal.ofReal (if n.emit ω = e then n.dist ω else 0) := by
    intro ω
    by_cases hω : n.emit ω = e <;> simp [hω]
  simp_rw [h_term]
  have h_nonneg : ∀ ω : n.Outcome,
      0 ≤ if n.emit ω = e then n.dist ω else 0 := fun ω => by
    split_ifs
    exacts [n.dist.nonneg ω, le_rfl]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => h_nonneg ω),
    ENNReal.toReal_ofReal (Finset.sum_nonneg (fun ω _ => h_nonneg ω))]

end ChanceGeneralNode

namespace ChanceFiniteNode

/-- Coerce a finite chance node to the general form. Uses the discrete (`⊤`) σ-algebra on `Outcome`
and the finite-mixture-of-Diracs realization of `n.dist`. Singleton measurability is trivial under
the discrete σ-algebra. A thin wrapper around `ChanceGeneralNode.ofChanceFinite`, named on the
finite-node side so consumers can write `n.toGeneral`. -/
noncomputable def toGeneral {E : Type u} (n : ChanceFiniteNode E) : ChanceGeneralNode E :=
  ChanceGeneralNode.ofChanceFinite n

/-- Concrete `Finset.sum`-based `eventProb` on a finite chance node, exposed independently of the
`NodeKind`-level `eventProb` so theorems can talk about the two formulas side by side. -/
def eventProb {E : Type u} [DecidableEq E] (n : ChanceFiniteNode E) (e : E) : ℝ :=
  ∑ ω : n.Outcome, if n.emit ω = e then n.dist ω else 0

/-- The two `eventProb` formulas agree on the coerced image: The concrete `Finset.sum` on the
finite side equals the measure-theoretic `dist (emit ⁻¹' {e})` on the general side. Bridges
finite-chance arithmetic to general-chance measure theory for theorems that want to state results
on the general form while concrete computation lives on the finite form. -/
theorem eventProb_eq_toGeneral_eventProb {I E : Type u} [DecidableEq E]
    (n : ChanceFiniteNode E) (e : E) :
    n.eventProb e =
      NodeKind.eventProb (I := I) (.chanceGeneral n.toGeneral) PUnit.unit e := by
  unfold toGeneral eventProb
  rw [ChanceGeneralNode.eventProb_ofChanceFinite (I := I) n e]
  rfl

end ChanceFiniteNode

end Econlib.GameTheory
