/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Core.Reachable

/-!
# Pure strategies on a finite extensive form

A **pure strategy** (Kuhn 1953) for player `i` selects a single action at every information set.
Information sets are indexed by observations `obs : G.info.Obs i`, and the chosen action is an
element of the `PureChoice` type at a canonical reachable representative of that information set.

Choice-type uniqueness across an information set rests on `iChoice_compatible`: At every history in
player `i`'s information set the node-local `iChoiceTypeAt` coincides with the information
structure's `iChoiceType i obs`. The `FiniteExtensiveForm` carrier excludes joint and
general-chance nodes (`no_joint`, `no_general_chance`), so at any reachable history with `i` moving
the `PureChoice` type agrees with `iChoiceTypeAt`; `pureChoice_eq_canonicalRep` records the
resulting per-information-set equality. Perfect recall is not assumed here. Unreached information
sets are assigned `PureChoice` at the root `[]`; the pure-strategy type there is degenerate but
always inhabited (via `nonempty_player_choice` for a player-node root, `PUnit` otherwise).

## Main definitions

* `FiniteExtensiveForm.IsReachedInfoSet`: An information set is reached by some reachable history.
* `FiniteExtensiveForm.canonicalRep`: A canonical reachable representative of an information set.
* `FiniteExtensiveForm.infoSetChoiceForObs`: The pure-choice type at an information set.
* `FiniteExtensiveForm.PureStrategy`: Pure strategy for a player.
* `FiniteExtensiveForm.PureStrategy.applyAt`: Node-local choice induced at a reachable history.

## Main statements

* `FiniteExtensiveForm.nonempty_pureChoice_at`: The `PureChoice` type at any history is nonempty.
* `FiniteExtensiveForm.pureChoice_eq_canonicalRep`: The `PureChoice` type at a reachable history
  where `i` moves equals that at the canonical representative of `i`'s information set.

## References

* Kuhn, H. W. 1953. “Extensive Games and the Problem of Information.” In *Contributions to the
  Theory of Games, Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

extensive form, pure strategy, finite extensive form
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

universe u

variable {I E : Type u}

namespace FiniteExtensiveForm

variable (G : FiniteExtensiveForm I E)

/-- Player `i`'s information set with observation `obs` is *reached* if some reachable history
witnesses that observation and has `i` moving. -/
def IsReachedInfoSet (i : I) (obs : G.info.Obs i) : Prop :=
  ∃ h : List E, h ∈ G.reach ∧ G.info.observe i h = obs ∧ (G.tree.nodeKind h).movesAt i

/-- A canonical reachable representative of player `i`'s info set with observation `obs`. If the
info set is reached, returns a `Classical.choose`-extracted witness; otherwise returns the root
`[]`. -/
noncomputable def canonicalRep (i : I) (obs : G.info.Obs i) : List E :=
  open Classical in
  if h : G.IsReachedInfoSet i obs then Classical.choose h else []

/-- When player `i`'s information set with observation `obs` is reached, its `canonicalRep` is a
reachable history that witnesses `obs` and at which `i` moves. -/
theorem canonicalRep_spec (i : I) (obs : G.info.Obs i) (h_reached : G.IsReachedInfoSet i obs) :
    G.canonicalRep i obs ∈ G.reach ∧
    G.info.observe i (G.canonicalRep i obs) = obs ∧
    (G.tree.nodeKind (G.canonicalRep i obs)).movesAt i := by
  unfold canonicalRep
  rw [dif_pos h_reached]
  exact Classical.choose_spec h_reached

/-- The canonical representative of any information set is a reachable history: The chosen witness
when the set is reached, and the root `[]` otherwise. -/
theorem canonicalRep_mem_reach (i : I) (obs : G.info.Obs i) : G.canonicalRep i obs ∈ G.reach := by
  unfold canonicalRep
  by_cases h : G.IsReachedInfoSet i obs
  · rw [dif_pos h]; exact (Classical.choose_spec h).1
  · rw [dif_neg h]; exact G.nil_mem_reach

/-- The pure-choice type at player `i`'s information set with observation `obs`, defined as the
`PureChoice` type at the canonical reachable representative. This is well-defined across the whole
information set: Any two reachable histories in it have equal `PureChoice` types
(`pureChoice_eq_canonicalRep`). -/
def infoSetChoiceForObs (i : I) (obs : G.info.Obs i) : Type u :=
  (G.tree.nodeKind (G.canonicalRep i obs)).PureChoice

instance instFintypeInfoSetChoiceForObs (i : I) (obs : G.info.Obs i) :
    Fintype (G.infoSetChoiceForObs i obs) :=
  inferInstanceAs (Fintype (G.tree.nodeKind (G.canonicalRep i obs)).PureChoice)

instance instDecidableEqInfoSetChoiceForObs (i : I) (obs : G.info.Obs i) :
    DecidableEq (G.infoSetChoiceForObs i obs) :=
  inferInstanceAs (DecidableEq (G.tree.nodeKind (G.canonicalRep i obs)).PureChoice)

/-- The PureChoice type at any history is nonempty. Joint and general-chance nodes are excluded
globally by the `FiniteExtensiveForm` fields; for player nodes, `nonempty_player_choice` supplies
nonemptiness; terminal and chance-finite nodes give `PUnit`. -/
theorem nonempty_pureChoice_at (h : List E) :
    Nonempty (G.tree.nodeKind h).PureChoice := by
  rcases hk : G.tree.nodeKind h with payoff | n | n | n | n
  · exact ⟨PUnit.unit⟩
  · -- player n
    exact G.nonempty_player_choice h n hk
  · -- joint n: excluded globally by no_joint
    exact absurd hk (G.no_joint h n)
  · -- chanceFinite n
    exact ⟨PUnit.unit⟩
  · -- chanceGeneral n: excluded globally by no_general_chance
    exact absurd hk (G.no_general_chance h n)

instance instInhabitedInfoSetChoiceForObs (i : I) (obs : G.info.Obs i) :
    Inhabited (G.infoSetChoiceForObs i obs) :=
  Classical.inhabited_of_nonempty (G.nonempty_pureChoice_at (G.canonicalRep i obs))

/-- A pure strategy for player `i`: At every information set (indexed by observation `obs`),
specify a pure choice in the canonical-rep choice type at that info set. -/
def PureStrategy (i : I) : Type u :=
  (obs : G.info.Obs i) → G.infoSetChoiceForObs i obs

instance instFintypePureStrategy (i : I) : Fintype (G.PureStrategy i) :=
  Pi.instFintype

instance instDecidableEqPureStrategy (i : I) : DecidableEq (G.PureStrategy i) :=
  inferInstanceAs (DecidableEq ((obs : G.info.Obs i) → G.infoSetChoiceForObs i obs))

instance instInhabitedPureStrategy (i : I) : Inhabited (G.PureStrategy i) :=
  ⟨fun _ => default⟩

/-- Per-player choice-type equality across an info set: At a reachable history `h` where player `i`
moves, the node-local `iChoiceTypeAt` at `(h, i)` coincides with the same at
`(canonicalRep i (observe i h), i)`. -/
theorem iChoiceTypeAt_eq_canonicalRep (i : I) (h : List E) (hr : h ∈ G.reach)
    (hm : (G.tree.nodeKind h).movesAt i) :
    (G.tree.nodeKind h).iChoiceTypeAt i hm =
      (G.tree.nodeKind (G.canonicalRep i (G.info.observe i h))).iChoiceTypeAt i
        (G.canonicalRep_spec i (G.info.observe i h) ⟨h, hr, rfl, hm⟩).2.2 := by
  set obs := G.info.observe i h with h_obs
  have h_reached : G.IsReachedInfoSet i obs := ⟨h, hr, rfl, hm⟩
  obtain ⟨_, h_obs_eq, hm_canon⟩ := G.canonicalRep_spec i obs h_reached
  have h_compat_h : (G.tree.nodeKind h).iChoiceTypeAt i hm = G.info.iChoiceType i obs :=
    G.iChoice_compatible i h hm
  have h_compat_canon :
      (G.tree.nodeKind (G.canonicalRep i obs)).iChoiceTypeAt i hm_canon =
        G.info.iChoiceType i (G.info.observe i (G.canonicalRep i obs)) :=
    G.iChoice_compatible i (G.canonicalRep i obs) hm_canon
  rw [h_obs_eq] at h_compat_canon
  exact h_compat_h.trans h_compat_canon.symm

/-- At any node kind known to be `.player n`, `iChoiceTypeAt i hm` equals `n.Choice`. The node kind
`k` is kept general so the substitution is legal even when the call site's `k` is
`G.tree.nodeKind h`. -/
private theorem iChoiceTypeAt_of_player_eq {I E : Type u} {k : NodeKind I E}
    {n : PlayerNode I E} {i : I} (hk : k = NodeKind.player n) (hm : k.movesAt i) :
    k.iChoiceTypeAt i hm = n.Choice := by
  subst hk
  rfl

/-- `PureChoice`-type equality across an information set: At a reachable history `h` where player
`i` moves, `(nodeKind h).PureChoice` equals
`(nodeKind (canonicalRep i (observe i h))).PureChoice`. -/
theorem pureChoice_eq_canonicalRep (i : I) (h : List E) (hr : h ∈ G.reach)
    (hm : (G.tree.nodeKind h).movesAt i) :
    (G.tree.nodeKind h).PureChoice =
      (G.tree.nodeKind (G.canonicalRep i (G.info.observe i h))).PureChoice := by
  set obs := G.info.observe i h with h_obs
  have h_reached : G.IsReachedInfoSet i obs := ⟨h, hr, rfl, hm⟩
  obtain ⟨_, h_obs_eq, hm_canon⟩ := G.canonicalRep_spec i obs h_reached
  rcases hk_h : G.tree.nodeKind h with payoff_h | n_h | n_h | n_h | n_h
  · rw [hk_h] at hm; exact absurd hm id
  · rcases hk_c : G.tree.nodeKind (G.canonicalRep i obs) with payoff_c | n_c | n_c | n_c | n_c
    · rw [hk_c] at hm_canon; exact absurd hm_canon id
    · have h_compat_h := G.iChoice_compatible i h hm
      have h_compat_c := G.iChoice_compatible i (G.canonicalRep i obs) hm_canon
      rw [h_obs_eq] at h_compat_c
      -- Both `n_h.Choice` and `n_c.Choice` equal the shared `iChoiceType i obs`.
      have h_h_eq : n_h.Choice = G.info.iChoiceType i obs :=
        (iChoiceTypeAt_of_player_eq hk_h hm).symm.trans h_compat_h
      have h_c_eq : n_c.Choice = G.info.iChoiceType i obs :=
        (iChoiceTypeAt_of_player_eq hk_c hm_canon).symm.trans h_compat_c
      exact h_h_eq.trans h_c_eq.symm
    · exact absurd hk_c (G.no_joint _ n_c)
    · rw [hk_c] at hm_canon; exact absurd hm_canon id
    · exact absurd hk_c (G.no_general_chance _ n_c)
  · exact absurd hk_h (G.no_joint _ n_h)
  · rw [hk_h] at hm; exact absurd hm id
  · exact absurd hk_h (G.no_general_chance _ n_h)

/-- Pull a pure strategy down to the actual `PureChoice` type at a reachable history where player
`i` moves. `G` is implicit so this is callable via dot notation `s.applyAt h hr hm`. -/
noncomputable def PureStrategy.applyAt {G : FiniteExtensiveForm I E} {i : I}
    (s : G.PureStrategy i) (h : List E) (hr : h ∈ G.reach)
    (hm : (G.tree.nodeKind h).movesAt i) :
    (G.tree.nodeKind h).PureChoice :=
  (G.pureChoice_eq_canonicalRep i h hr hm).symm ▸ s (G.info.observe i h)

end FiniteExtensiveForm

end Econlib.GameTheory
