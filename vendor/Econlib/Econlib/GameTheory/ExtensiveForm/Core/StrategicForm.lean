/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Core.PureStrategy
public import Econlib.GameTheory.Strategic.Basic

/-!
# Strategic-form normalization of a finite extensive form

The **strategic form** (or normal form) of an extensive game (Kuhn 1953) is the strategic game
whose players are the original players, whose actions are pure strategies, and whose payoffs are
the expected payoffs induced by each pure-strategy profile. This file builds that reduction: A
`FiniteExtensiveForm` (with global `no_joint` / `no_general_chance` and finite choice and
observation types) gives rise to a `FiniteStrategicGame` whose action set for player `i` is
`PureStrategy i` and whose payoff is the expected terminal payoff under the pure profile.

The construction uses pure-profile reach probabilities at the finite extensive-form layer and is
well-defined for any `FiniteExtensiveForm`; perfect recall is not required. It is the
strategic-form representation on which realization-equivalence results can later compare mixed and
behavioral strategies.

## Main definitions

* `FiniteExtensiveForm.lookupPlayerChoice`: Node-local choice induced by a pure profile.
* `FiniteExtensiveForm.purePrefixStepAt`: One-step reach probability at a given node kind.
* `FiniteExtensiveForm.purePrefixStep`: One-step reach probability under a pure profile.
* `FiniteExtensiveForm.pureReachProbFrom`: Finite-suffix reach probability under a pure profile.
* `FiniteExtensiveForm.pureReachProb`: Reach probability of a finite history from the root.
* `FiniteExtensiveForm.terminalPayoffOf`: Terminal payoff at a history, or `0` if non-terminal.
* `FiniteExtensiveForm.toFiniteStrategicGame`: Strategic-form normalization.

## Main statements

* `FiniteExtensiveForm.purePrefixStep_of_terminal`, `..._of_chanceFinite`, `..._of_player`:
  Node-kind unfolding lemmas for `purePrefixStep`.
* `FiniteExtensiveForm.lookupPlayerChoice_eq_of_obs_agree`: `lookupPlayerChoice` depends on the
  mover's strategy only through its value at the current observation.

## References

* Kuhn, H. W. 1953. “Extensive Games and the Problem of Information.” In *Contributions to the
  Theory of Games, Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

extensive form, strategic form, pure strategy
-/

@[expose] public noncomputable section

open BigOperators Econlib.Probability

namespace Econlib.GameTheory

universe u

variable {I E : Type u}

namespace FiniteExtensiveForm

variable (G : FiniteExtensiveForm I E)

/-- The choice that pure profile `s` makes at history `h`'s player node, transported into the local
`n.Choice` type. At a reachable history this is `(s n.mover).applyAt h hr hm`; at an unreachable
history, where `applyAt`'s reachability hypothesis is unavailable, it falls back to an arbitrary
choice from the nonempty-player-choice witness. The explicit `h_kind` equality fixes the return
type to `n.Choice`. -/
noncomputable def lookupPlayerChoice (s : ∀ i, G.PureStrategy i) (h : List E)
    (n : PlayerNode I E) (h_kind : G.tree.nodeKind h = .player n) : n.Choice :=
  open Classical in
  if hr : h ∈ G.reach then
    have hm : (G.tree.nodeKind h).movesAt n.mover := h_kind ▸ rfl
    cast (by rw [h_kind]; rfl) ((s n.mover).applyAt h hr hm)
  else
    Classical.choice (G.nonempty_player_choice h n h_kind)

/-- One-step reach probability under a pure-strategy profile, parameterized by an explicit node
kind `k`. Taking `k` as a parameter rather than matching on `G.tree.nodeKind h` directly, with the
dependent transport into `n.Choice` wrapped behind a `dite` on the kind equation, keeps the
node-kind unfolding lemmas non-dependent. -/
noncomputable def purePrefixStepAt [DecidableEq E] (s : ∀ i, G.PureStrategy i) (h : List E)
    (k : NodeKind I E) (e : E) : ℝ :=
  open Classical in
  match k with
  | .terminal _ => 0
  | .player n =>
      if hk : G.tree.nodeKind h = .player n then
        if n.emit (G.lookupPlayerChoice s h n hk) = e then 1 else 0
      else
        0
  | .joint _ => 0
  | .chanceFinite n => ∑ ω : n.Outcome, if n.emit ω = e then n.dist ω else 0
  | .chanceGeneral _ => 0

/-- One-step reach probability under a pure-strategy profile, defined as `purePrefixStepAt` applied
to `G.tree.nodeKind h`. The dependent transport in `purePrefixStepAt` is hidden behind a `dite`, so
the node-kind unfolding lemmas (`purePrefixStep_of_terminal`, `purePrefixStep_of_player`,
`purePrefixStep_of_chanceFinite` below) reduce it to a direct computation. -/
noncomputable def purePrefixStep [DecidableEq E] (s : ∀ i, G.PureStrategy i) (h : List E)
    (e : E) : ℝ :=
  G.purePrefixStepAt s h (G.tree.nodeKind h) e

/-- Probability of a finite suffix from a current history under a pure-strategy profile. -/
noncomputable def pureReachProbFrom [DecidableEq E] (G : FiniteExtensiveForm I E)
    (s : ∀ i, G.PureStrategy i) : List E → List E → ℝ
  | _h, [] => 1
  | h, e :: rest =>
      G.purePrefixStep s h e * pureReachProbFrom G s (h ++ [e]) rest

/-- Probability of a finite history from the root under a pure-strategy profile. -/
noncomputable def pureReachProb [DecidableEq E] (s : ∀ i, G.PureStrategy i) (h : List E) : ℝ :=
  G.pureReachProbFrom s [] h

/-- The terminal payoff for player `i` at history `h`, if `h` is terminal; otherwise `0`. -/
noncomputable def terminalPayoffOf (h : List E) (i : I) : ℝ :=
  match G.tree.nodeKind h with
  | .terminal payoff => payoff i
  | _ => 0

/-- Strategic-form normalization of a finite extensive form. The action set for player `i` is the
pure-strategy type `PureStrategy i`; the payoff is the expected terminal payoff weighted by
`pureReachProb` over reachable terminal histories. -/
noncomputable def toFiniteStrategicGame [DecidableEq E] [Fintype I] [DecidableEq I]
    [Inhabited I] : FiniteStrategicGame where
  Player := I
  Action := G.PureStrategy
  payoff i s := ∑ h ∈ G.terminalReach, G.pureReachProb s h * G.terminalPayoffOf h i
  instInhabitedPlayer := inferInstance
  instDecidableEqPlayer := inferInstance
  instInhabitedAction := inferInstance
  instFintypePlayer := inferInstance
  instFintypeAction := inferInstance
  instDecidableEqAction := inferInstance

/-! ## Unfolding lemmas for `purePrefixStep` and `lookupPlayerChoice`

These node-kind unfolding lemmas reduce `purePrefixStep` and `lookupPlayerChoice` to their
concrete per-constructor values. -/

@[simp] lemma purePrefixStep_of_terminal [DecidableEq E] (s : ∀ i, G.PureStrategy i)
    {h : List E} {payoff : I → ℝ} (hk : G.tree.nodeKind h = .terminal payoff) (e : E) :
    G.purePrefixStep s h e = 0 := by
  unfold purePrefixStep
  rw [hk]
  rfl

@[simp] lemma purePrefixStep_of_chanceFinite [DecidableEq E] (s : ∀ i, G.PureStrategy i)
    {h : List E} {n : ChanceFiniteNode E} (hk : G.tree.nodeKind h = .chanceFinite n) (e : E) :
    G.purePrefixStep s h e = ∑ ω : n.Outcome, if n.emit ω = e then n.dist ω else 0 := by
  unfold purePrefixStep
  rw [hk]
  rfl

lemma purePrefixStep_of_player [DecidableEq E] (s : ∀ i, G.PureStrategy i)
    {h : List E} {n : PlayerNode I E} (hk : G.tree.nodeKind h = .player n) (e : E) :
    G.purePrefixStep s h e =
      (if n.emit (G.lookupPlayerChoice s h n hk) = e then 1 else 0) := by
  unfold purePrefixStep
  rw [hk]
  unfold purePrefixStepAt
  exact dif_pos hk

/-- `lookupPlayerChoice` depends on the mover's strategy only through its value at the current
observation: If `s` and `s'` agree at `(n.mover, observe n.mover h)`, they induce the same
choice. -/
lemma lookupPlayerChoice_eq_of_obs_agree (s s' : ∀ i, G.PureStrategy i) (h : List E)
    (n : PlayerNode I E) (hk : G.tree.nodeKind h = .player n)
    (h_eq : s n.mover (G.info.observe n.mover h) = s' n.mover (G.info.observe n.mover h)) :
    G.lookupPlayerChoice s h n hk = G.lookupPlayerChoice s' h n hk := by
  unfold lookupPlayerChoice
  by_cases hr : h ∈ G.reach
  · simp only [hr, dif_pos]
    have happ : (s n.mover).applyAt h hr (hk ▸ rfl) =
        (s' n.mover).applyAt h hr (hk ▸ rfl) := by
      unfold PureStrategy.applyAt; rw [h_eq]
    congr 1
  · simp only [hr, dif_neg, not_false_iff]

end FiniteExtensiveForm

end Econlib.GameTheory
