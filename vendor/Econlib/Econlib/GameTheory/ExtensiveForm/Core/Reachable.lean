/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Core.Tree

/-!
# Finite extensive forms

A `FiniteExtensiveForm` bundles an `ExtensiveForm` with the finiteness data Kuhn's theorem
requires: A `Finset` enumeration of reachable histories, finite player-observation types, exclusion
of joint and general-chance nodes from reachable positions, and injectivity of player-node emit
functions.

Per-history emission and reachability are predicates on the underlying `ExtensiveForm`. The
`FiniteExtensiveForm` structure carries the finite witnesses needed to enumerate histories,
quantify over finite observations, and rule out reachable joint or general-chance nodes.

## Main definitions

* `NodeKind.emits`: Positive-support emitted events of a node kind.
* `ExtensiveForm.IsReachable`: Inductive reachability of histories.
* `FiniteExtensiveForm`: Finite extensive form suitable for Kuhn-style arguments.

## Main statements

* `ExtensiveForm.IsReachable.of_prefix`: Prefixes of a reachable history are reachable.
* `ExtensiveForm.emits_of_isReachable_concat`: A reachable one-edge extension emits that edge.

## Tags

extensive form, reachability, finite extensive form
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

universe u

variable {I E : Type u}

namespace NodeKind

/-- The events a node kind emits, i.e. the range of the emit map. For a chance-finite node this is
every event some outcome maps to, including zero-probability outcomes.

Terminal and (excluded for the finite layer) general-chance nodes emit nothing; player nodes emit
the player emit map's range; joint nodes the joint-profile-emit map's range. -/
def emits : NodeKind I E → E → Prop
  | .terminal _, _ => False
  | .player n, e => ∃ c : n.Choice, n.emit c = e
  | .joint n, e => ∃ c : ((a : n.Active) → n.Choice a), n.emit c = e
  | .chanceFinite n, e => ∃ ω : n.Outcome, n.emit ω = e
  | .chanceGeneral _, _ => False

/-- A terminal node emits nothing. -/
@[simp] lemma not_emits_terminal (payoff : I → ℝ) (e : E) :
    ¬ (NodeKind.terminal payoff : NodeKind I E).emits e := id

/-- A general-chance node emits nothing (it is excluded from the finite layer). -/
@[simp] lemma not_emits_chanceGeneral (n : ChanceGeneralNode E) (e : E) :
    ¬ (NodeKind.chanceGeneral n : NodeKind I E).emits e := id

/-- A player node emits `e` iff some legal choice emits `e`. -/
@[simp] lemma emits_player_iff (n : PlayerNode I E) (e : E) :
    (NodeKind.player n : NodeKind I E).emits e ↔ ∃ c : n.Choice, n.emit c = e := Iff.rfl

/-- A finite chance node emits `e` iff some outcome emits `e`. -/
@[simp] lemma emits_chanceFinite_iff (n : ChanceFiniteNode E) (e : E) :
    (NodeKind.chanceFinite n : NodeKind I E).emits e ↔ ∃ ω : n.Outcome, n.emit ω = e := Iff.rfl

/-- Every node kind's `PureChoice` type is a `Fintype`. PUnit for terminal and chance nodes; the
player's choice type for player nodes; the dependent product over active players for joint nodes. -/
instance instFintypePureChoice (k : NodeKind I E) : Fintype k.PureChoice := by
  -- `PureChoice` reduces once the constructor is exposed; each branch's instance (including the
  -- node-local `Fintype Choice` bracket fields) is then found by typeclass resolution.
  cases k <;> unfold NodeKind.PureChoice <;> exact inferInstance

/-- Every node kind's `PureChoice` type has decidable equality. -/
instance instDecidableEqPureChoice (k : NodeKind I E) : DecidableEq k.PureChoice := by
  -- As with `Fintype`: expose the constructor, reduce `PureChoice`, and let typeclass resolution
  -- supply each branch's `DecidableEq` (player/joint nodes via their `Choice` bracket fields).
  cases k <;> unfold NodeKind.PureChoice <;> exact inferInstance

end NodeKind

namespace ExtensiveForm

/-- A history is reachable if it is the empty root or extends a reachable history by an event
emitted at the predecessor's node kind. -/
inductive IsReachable (G : ExtensiveForm I E) : List E → Prop
  | root : G.IsReachable []
  | step (h : List E) (e : E) (hr : G.IsReachable h) (he : (G.tree.nodeKind h).emits e) :
      G.IsReachable (h ++ [e])

/-- The empty root history is reachable. -/
lemma isReachable_nil (G : ExtensiveForm I E) : G.IsReachable [] := IsReachable.root

/-- Player-node emit functions are injective. Restricted to player nodes because only those encode
strategic choices we need to invert when reconstructing a player's experience along a path.
Chance-node injectivity is not required for Kuhn. -/
def HasInjectiveEmit (G : ExtensiveForm I E) : Prop :=
  ∀ (h : List E) (n : PlayerNode I E),
    G.tree.nodeKind h = .player n → Function.Injective n.emit

end ExtensiveForm

/-- An extensive form bundled with the finite-layer data Kuhn's theorem requires.

* `reach` is a finite enumeration of reachable histories, materializing the inductive `IsReachable`
  predicate.
* Player observation types are finite with decidable equality, so info-set-indexed pure strategies
  form a `Fintype`.
* Joint and general-chance nodes are excluded from reachable positions: Kuhn's theorem in this
  presentation covers sequential player nodes plus finite chance only.
* Player-node emit functions are injective, allowing recovery of a player's action from the
  observed event. -/
structure FiniteExtensiveForm (I E : Type u) extends ExtensiveForm I E where
  /-- Finite enumeration of reachable histories. -/
  reach : Finset (List E)
  /-- The reach Finset is exactly the set of `IsReachable` histories. -/
  mem_reach_iff : ∀ h, h ∈ reach ↔ toExtensiveForm.IsReachable h
  /-- Each player's observation type is a `Fintype`. -/
  obsType_fintype : ∀ i : I, Fintype (toExtensiveForm.info.Obs i)
  /-- Each player's observation type has decidable equality. -/
  obsType_decidable : ∀ i : I, DecidableEq (toExtensiveForm.info.Obs i)
  /-- No history reaches a joint node. Stronger than just-reachable: Makes downstream `Behavior`
  typing total without Nonempty-Choice plumbing for joint nodes. -/
  no_joint : ∀ (h : List E) (n : JointNode I E), toExtensiveForm.tree.nodeKind h ≠ .joint n
  /-- No history reaches a general-chance node. -/
  no_general_chance : ∀ (h : List E) (n : ChanceGeneralNode E),
      toExtensiveForm.tree.nodeKind h ≠ .chanceGeneral n
  /-- Player-node emit functions are injective. -/
  has_injective_emit : toExtensiveForm.HasInjectiveEmit
  /-- Every player-node Choice type is nonempty. Required so pure strategies — which select an
  action at every information set — can always be constructed. -/
  nonempty_player_choice :
    ∀ (h : List E) (n : PlayerNode I E),
      toExtensiveForm.tree.nodeKind h = .player n → Nonempty n.Choice
namespace FiniteExtensiveForm

variable (G : FiniteExtensiveForm I E)

instance instFintypeObs (i : I) : Fintype (G.info.Obs i) := G.obsType_fintype i

instance instDecidableEqObs (i : I) : DecidableEq (G.info.Obs i) := G.obsType_decidable i

/-- The empty root history belongs to the reachability finset. -/
lemma nil_mem_reach : ([] : List E) ∈ G.reach :=
  (G.mem_reach_iff _).mpr ExtensiveForm.IsReachable.root

/-- A reachable history is terminal if its node kind is a terminal node. -/
def IsTerminalAt (h : List E) : Prop :=
  ∃ payoff : I → ℝ, G.tree.nodeKind h = .terminal payoff

/-- The finset of terminal reachable histories. Decidability of `IsTerminalAt` requires
case-splitting on the node kind; we use classical decidability via `Classical.dec`. -/
noncomputable def terminalReach : Finset (List E) :=
  G.reach.filter (fun h => Classical.propDecidable (G.IsTerminalAt h) |>.decide)

/-- Membership in `terminalReach`: A history lies in `terminalReach` iff it is reachable and
terminal. -/
lemma mem_terminalReach_iff (h : List E) :
    h ∈ G.terminalReach ↔ h ∈ G.reach ∧ G.IsTerminalAt h := by
  simp only [terminalReach, Finset.mem_filter, decide_eq_true_eq]

/-- **Move nodes are player nodes.** Where player `i` moves, the node kind is `.player n` with `i`
the mover. Joint and general-chance nodes are excluded by `no_joint` / `no_general_chance`; terminal
and finite-chance nodes have no mover. Packages the recurring five-way `nodeKind` case split. -/
lemma exists_playerNode_of_movesAt (h : List E) (i : I)
    (hm : (G.tree.nodeKind h).movesAt i) :
    ∃ n : PlayerNode I E, G.tree.nodeKind h = .player n ∧ n.mover = i := by
  rcases hk : G.tree.nodeKind h with _ | n | n | n | n
  · rw [hk] at hm; exact absurd hm id
  · exact ⟨n, rfl, by rw [hk] at hm; exact hm⟩
  · exact absurd hk (G.no_joint h n)
  · rw [hk] at hm; exact absurd hm id
  · exact absurd hk (G.no_general_chance h n)

end FiniteExtensiveForm

/-! ## Prefix reachability

Prefixes of a reachable history are reachable, and a reachable extension by one edge emits that
edge. -/
/-- **Prefixes of a reachable history are reachable.** A take-prefix of a reachable history is
itself reachable: By induction on the `IsReachable` derivation, dropping the last emitted step
keeps the shorter prefix inside the reachable tree. -/
theorem ExtensiveForm.IsReachable.take (G : ExtensiveForm I E) {h : List E}
    (hr : G.IsReachable h) (k : ℕ) : G.IsReachable (h.take k) := by
  induction hr with
  | root => simpa using ExtensiveForm.IsReachable.root
  | step h_path e hr he ih =>
    by_cases hk : k ≤ h_path.length
    · rwa [List.take_append_of_le_length hk]
    · push Not at hk
      have htake : (h_path ++ [e]).take k = h_path ++ [e] :=
        List.take_of_length_le (by rw [List.length_append]; simp; omega)
      rw [htake]
      exact ExtensiveForm.IsReachable.step h_path e hr he

/-- A prefix (`<+:`) of a reachable history is reachable. -/
theorem ExtensiveForm.IsReachable.of_prefix (G : ExtensiveForm I E) {h_full h_pre : List E}
    (hr : G.IsReachable h_full) (hpre : h_pre <+: h_full) : G.IsReachable h_pre := by
  obtain ⟨rest, hrfl⟩ := hpre
  have hpe : h_pre = h_full.take h_pre.length := by rw [← hrfl, List.take_left]
  rw [hpe]; exact ExtensiveForm.IsReachable.take G hr h_pre.length

/-- Reachability inversion at a step: If `z ++ [e]` is reachable then `z`'s node emits `e`. -/
theorem ExtensiveForm.emits_of_isReachable_concat (G : ExtensiveForm I E) {z : List E} {e : E}
    (h : G.IsReachable (z ++ [e])) : (G.tree.nodeKind z).emits e := by
  generalize hzx : z ++ [e] = zx at h
  cases h with
  | root => exact absurd hzx (by simp)
  | step h' e' hr he =>
    obtain ⟨rfl, he2⟩ := List.append_inj' hzx rfl
    obtain rfl : e = e' := by injection he2
    exact he

end Econlib.GameTheory
