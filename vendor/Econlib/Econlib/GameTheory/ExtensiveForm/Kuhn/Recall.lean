/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Core.Reachable
public import Econlib.GameTheory.ExtensiveForm.Core.Strategy

/-!
# Recall predicates on a bare extensive form

This file defines named recall predicates on a bare `ExtensiveForm`, using the inductive
`IsReachable` reachability relation. Each predicate records one behavioral implication of perfect
recall: No information-set revisits and last-stop alignment. They are weaker than the conventional
perfect-recall predicate, but are stated directly on the unbundled extensive form where the
corresponding equilibrium and realization-equivalence statements are formulated.

## Main definitions

* `ExtensiveForm.NoInfoSetRevisit` — a player never revisits one of her own information sets along
  a reachable path.
* `ExtensiveForm.LastStopAlign` — two reachable histories in one information set agree on the
  structure and taken action of the player's last prior move.

## References

* Kuhn, H. W. 1953. “Extensive Games and the Problem of Information.” In *Contributions to the
  Theory of Games, Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

extensive form, perfect recall, no-revisit, last-stop alignment
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

universe u

variable {I E : Type u}

/-- **No information-set revisits.** Along any reachable path, a player never returns to the same
information set: If `h₁` is a prefix of `h₂`, both are reachable, the moving player observes the
same information set at both, and moves at both, then `h₁ = h₂`. Phrased on the inductive
`IsReachable` predicate so it applies to a bare `ExtensiveForm`.

This is **not** perfect recall — it is the single recall consequence that Kuhn's forward
(behavioral→mixed) realization theorem consumes. Perfect recall
(`FiniteExtensiveForm.IsPerfectRecall`) implies it (`IsPerfectRecall.noInfoSetRevisit`). -/
def ExtensiveForm.NoInfoSetRevisit (G : ExtensiveForm I E) : Prop :=
  ∀ (i : I) (h₁ h₂ : List E),
    G.IsReachable h₁ → G.IsReachable h₂ → h₁ <+: h₂ →
    G.info.observe i h₁ = G.info.observe i h₂ →
    (G.tree.nodeKind h₁).movesAt i → (G.tree.nodeKind h₂).movesAt i → h₁ = h₂

/-- **Last-stop alignment** (the stop-level content of perfect recall). Two reachable histories
`z, w` in the same information set of player `i` agree on the structure of `i`'s *last prior move*:
If `i` last moved before `z` at the prefix of length `m` (an `i`-mover with no later `i`-mover
strictly before `z`), then `i` also moved before `w` at some prefix `w.take m'`, in the *same*
information set, likewise with no later `i`-mover strictly before `w`, and the two paths take *the
same action* there — phrased strategy-quantified (the step probabilities of the two taken edges
agree under every behavioral strategy), which avoids transporting choices across the dependent
`iChoiceType`.

This is supplied as an explicit hypothesis of the one-shot deviation principle, not as perfect
recall: It is the stop-level content of the textbook notion ("a player remembers his own past moves
and what he knew when making them") and is a consequence of `FiniteExtensiveForm.IsPerfectRecall`
(`IsPerfectRecall.lastStopAlign`), so the hypothesis is free for any perfect-recall game. (Standard
builders also satisfy it directly — perfect information: `observe` is injective on reachable
histories, so `z = w`; staged forms such as signaling: No player moves twice along a path, so the
hypothesis is vacuous.) -/
def ExtensiveForm.LastStopAlign (G : ExtensiveForm I E) [DecidableEq E] : Prop :=
  ∀ (i : I) (z w : List E), G.IsReachable z → G.IsReachable w →
    (G.tree.nodeKind z).movesAt i → (G.tree.nodeKind w).movesAt i →
    G.info.observe i z = G.info.observe i w →
    ∀ m : ℕ, m < z.length → (G.tree.nodeKind (z.take m)).movesAt i →
      (∀ r : ℕ, m < r → r < z.length → ¬ (G.tree.nodeKind (z.take r)).movesAt i) →
      ∃ m' : ℕ, m' < w.length ∧ (G.tree.nodeKind (w.take m')).movesAt i ∧
        G.info.observe i (w.take m') = G.info.observe i (z.take m) ∧
        (∀ r : ℕ, m' < r → r < w.length → ¬ (G.tree.nodeKind (w.take r)).movesAt i) ∧
        ∀ (e e' : E), z.take (m + 1) = z.take m ++ [e] → w.take (m' + 1) = w.take m' ++ [e'] →
          ∀ ρ : G.BehavioralStrategy,
            G.stepProb ρ (z.take m) e = G.stepProb ρ (w.take m') e'

end Econlib.GameTheory
