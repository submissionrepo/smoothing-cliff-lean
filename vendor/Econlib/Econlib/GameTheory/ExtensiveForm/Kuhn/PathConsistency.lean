/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Core.StrategicForm

/-!
# Per-player path consistency

For a fixed player `i` and a pure strategy `s_i`, `iPathConsistent i s_i h` is the `0/1` weight
that `s_i` is consistent with reaching history `h`: At every prefix of `h` where player `i` moves,
the action `s_i` selects must emit the realized next event; at chance, other-player, and terminal
nodes player `i` imposes no constraint. This isolates player `i`'s own contribution to the
pure-profile reach probability `pureReachProb` and supports both strategic normalization and the
mixed → behavioral direction of Kuhn's theorem.

## Main definitions

* `FiniteExtensiveForm.singletonProfile`: A pure profile playing `s_i` for `i`, default elsewhere.
* `FiniteExtensiveForm.iStepIndicator`: One-step path-consistency indicator for player `i`.
* `FiniteExtensiveForm.iPathConsistentFrom` / `iPathConsistent`: Path-consistency weight.

## Main statements

* `FiniteExtensiveForm.iPathConsistentFrom_append`: Path consistency factorizes over a
  concatenation.
* `FiniteExtensiveForm.iPathConsistentFrom_eq_of_eq_on_path`: Path consistency depends only on the
  strategy's values at the observed info sets along the path.

## Notes

The action-recall consequence of perfect recall (`FiniteExtensiveForm.ActionRecall`) is phrased as
representative-independence of `iPathConsistent`: Histories in the same information set give the
same consistency weight for a fixed pure strategy.

## References

* Kuhn, H. W. 1953. “Extensive Games and the Problem of Information.” In *Contributions to the
  Theory of Games, Volume II*, edited by H. W. Kuhn and A. W. Tucker. Princeton University Press.

## Tags

extensive form, pure strategy, path consistency, perfect recall
-/

@[expose] public noncomputable section

open BigOperators Econlib.Probability

namespace Econlib.GameTheory

universe u

variable {I E : Type u}

namespace FiniteExtensiveForm

variable (G : FiniteExtensiveForm I E)

/-! ## Nonnegativity of `purePrefixStep` -/

lemma purePrefixStep_nonneg [DecidableEq E] (s : ∀ i, G.PureStrategy i) (h : List E) (e : E) :
    0 ≤ G.purePrefixStep s h e := by
  rcases hk : G.tree.nodeKind h with payoff | n | n | n | n
  · rw [G.purePrefixStep_of_terminal s hk]
  · rw [G.purePrefixStep_of_player s hk]; split <;> norm_num
  · exact absurd hk (G.no_joint h n)
  · rw [G.purePrefixStep_of_chanceFinite s hk]
    exact Finset.sum_nonneg fun ω _ => by split; exacts [n.dist.nonneg ω, le_rfl]
  · exact absurd hk (G.no_general_chance h n)

/-! ## Per-player path consistency -/

/-- The pure-strategy profile that plays `s_i` for player `i` and a fixed default for everyone
else. Used to read player `i`'s node-local action out of `purePrefixStep` without constraining the
other players. -/
noncomputable def singletonProfile [DecidableEq I] (i : I) (s_i : G.PureStrategy i) :
    ∀ j, G.PureStrategy j :=
  Function.update (fun j => (default : G.PureStrategy j)) i s_i

/-- Indicator that player `i`'s pure strategy `s_i` keeps the play on track to emit `e` at history
`h`: At `i`'s own decision nodes the chosen action must emit `e`; at every other node (chance,
other players, terminal) the indicator is `1` (player `i` imposes no constraint). -/
noncomputable def iStepIndicator [DecidableEq E] [DecidableEq I] (i : I) (s_i : G.PureStrategy i)
    (h : List E) (e : E) : ℝ :=
  open Classical in
  if (G.tree.nodeKind h).movesAt i then G.purePrefixStep (G.singletonProfile i s_i) h e else 1

lemma iStepIndicator_nonneg [DecidableEq E] [DecidableEq I] (i : I) (s_i : G.PureStrategy i)
    (h : List E) (e : E) : 0 ≤ G.iStepIndicator i s_i h e := by
  unfold iStepIndicator
  split
  · exact G.purePrefixStep_nonneg _ _ _
  · exact zero_le_one

/-- At a history where player `i` does not move, the step indicator is `1`. -/
lemma iStepIndicator_of_not_movesAt [DecidableEq E] [DecidableEq I] (i : I) (s_i : G.PureStrategy i)
    (h : List E) (e : E) (hm : ¬ (G.tree.nodeKind h).movesAt i) :
    G.iStepIndicator i s_i h e = 1 := by
  classical
  unfold iStepIndicator
  rw [if_neg hm]

/-- At a player history where `i` is the mover, the step indicator is the `0/1` indicator that
`s_i`'s local choice (looked up at `h`) emits `e`. -/
lemma iStepIndicator_of_player [DecidableEq E] [DecidableEq I] (i : I) (s_i : G.PureStrategy i)
    {h : List E} {n : PlayerNode I E} (hk : G.tree.nodeKind h = .player n) (hmover : n.mover = i)
    (e : E) :
    G.iStepIndicator i s_i h e =
      if n.emit (G.lookupPlayerChoice (G.singletonProfile i s_i) h n hk) = e then 1 else 0 := by
  classical
  have hm : (G.tree.nodeKind h).movesAt i := by rw [hk]; exact hmover
  unfold iStepIndicator
  rw [if_pos hm, G.purePrefixStep_of_player (G.singletonProfile i s_i) hk e]

/-- The step indicator depends on the pure strategy only through its value at `observe i h`. -/
lemma iStepIndicator_eq_of_obs_agree [DecidableEq E] [DecidableEq I] (i : I)
    (s_i s_i' : G.PureStrategy i) (h : List E) (e : E)
    (h_eq : s_i (G.info.observe i h) = s_i' (G.info.observe i h)) :
    G.iStepIndicator i s_i h e = G.iStepIndicator i s_i' h e := by
  classical
  unfold iStepIndicator
  by_cases hm : (G.tree.nodeKind h).movesAt i
  · rw [if_pos hm, if_pos hm]
    rcases hk : G.tree.nodeKind h with _ | n | n | n | n
    · rw [hk] at hm; exact absurd hm id
    · have hmover : n.mover = i := by rw [hk] at hm; exact hm
      rw [G.purePrefixStep_of_player (G.singletonProfile i s_i) hk e,
        G.purePrefixStep_of_player (G.singletonProfile i s_i') hk e]
      rw [G.lookupPlayerChoice_eq_of_obs_agree (G.singletonProfile i s_i)
        (G.singletonProfile i s_i') h n hk ?_]
      -- The singleton profiles agree at `n.mover = i` on the observation.
      unfold singletonProfile
      rw [hmover, Function.update_self, Function.update_self, h_eq]
    · exact absurd hk (G.no_joint h n)
    · rw [hk] at hm; exact absurd hm id
    · exact absurd hk (G.no_general_chance h n)
  · rw [if_neg hm, if_neg hm]

/-- Probability weight (under `s_i`) that player `i`'s choices stay consistent with the
continuation `path` starting from `h_start`. Product of per-step indicators. -/
noncomputable def iPathConsistentFrom [DecidableEq E] [DecidableEq I]
    (G : FiniteExtensiveForm I E) (i : I) (s_i : G.PureStrategy i) : List E → List E → ℝ
  | _h, [] => 1
  | h, e :: rest => G.iStepIndicator i s_i h e * iPathConsistentFrom G i s_i (h ++ [e]) rest

/-- Player `i`'s path-consistency indicator from the root. -/
noncomputable def iPathConsistent [DecidableEq E] [DecidableEq I] (i : I)
    (s_i : G.PureStrategy i) (h : List E) : ℝ :=
  G.iPathConsistentFrom i s_i [] h

lemma iPathConsistentFrom_nonneg [DecidableEq E] [DecidableEq I] (i : I) (s_i : G.PureStrategy i)
    (h_start path : List E) : 0 ≤ G.iPathConsistentFrom i s_i h_start path := by
  induction path generalizing h_start with
  | nil => exact zero_le_one
  | cons e rest ih =>
      rw [iPathConsistentFrom]
      exact mul_nonneg (G.iStepIndicator_nonneg i s_i h_start e) (ih _)

lemma iPathConsistent_nonneg [DecidableEq E] [DecidableEq I] (i : I) (s_i : G.PureStrategy i)
    (h : List E) : 0 ≤ G.iPathConsistent i s_i h :=
  G.iPathConsistentFrom_nonneg i s_i [] h

/-- Path consistency factorizes over a concatenation: The indicator of `path₁ ++ path₂` from
`h_start` is the product of the indicator of `path₁` from `h_start` and the indicator of `path₂`
from `h_start ++ path₁`. -/
lemma iPathConsistentFrom_append [DecidableEq E] [DecidableEq I] (i : I) (s_i : G.PureStrategy i)
    (h_start path₁ path₂ : List E) :
    G.iPathConsistentFrom i s_i h_start (path₁ ++ path₂) =
      G.iPathConsistentFrom i s_i h_start path₁ *
        G.iPathConsistentFrom i s_i (h_start ++ path₁) path₂ := by
  induction path₁ generalizing h_start with
  | nil => simp [iPathConsistentFrom]
  | cons e rest ih =>
      rw [List.cons_append, iPathConsistentFrom, iPathConsistentFrom, ih (h_start ++ [e]),
        List.append_assoc, List.cons_append, List.nil_append, mul_assoc]

/-- One-step append: The consistency of `h_start ++ [e]` (from the root) factorizes as the
consistency of `h_start` times the single step indicator at `h_start`. -/
lemma iPathConsistent_append_singleton [DecidableEq E] [DecidableEq I] (i : I)
    (s_i : G.PureStrategy i) (h_start : List E) (e : E) :
    G.iPathConsistent i s_i (h_start ++ [e]) =
      G.iPathConsistent i s_i h_start * G.iStepIndicator i s_i h_start e := by
  unfold iPathConsistent
  rw [G.iPathConsistentFrom_append i s_i [] h_start [e], List.nil_append, iPathConsistentFrom,
    iPathConsistentFrom, mul_one]

/-- Path-consistency depends on the pure strategy only through its values at the observations along
the path where player `i` actually moves. -/
lemma iPathConsistentFrom_eq_of_eq_on_path [DecidableEq E] [DecidableEq I] (i : I)
    (s_i s_i' : G.PureStrategy i) (h_start path : List E)
    (h_eq : ∀ k : ℕ, k < path.length →
      (G.tree.nodeKind (h_start ++ path.take k)).movesAt i →
      s_i (G.info.observe i (h_start ++ path.take k)) =
        s_i' (G.info.observe i (h_start ++ path.take k))) :
    G.iPathConsistentFrom i s_i h_start path = G.iPathConsistentFrom i s_i' h_start path := by
  induction path generalizing h_start with
  | nil => rfl
  | cons e rest ih =>
      rw [iPathConsistentFrom, iPathConsistentFrom]
      have hstep : G.iStepIndicator i s_i h_start e = G.iStepIndicator i s_i' h_start e := by
        by_cases hm : (G.tree.nodeKind h_start).movesAt i
        · apply G.iStepIndicator_eq_of_obs_agree
          have := h_eq 0 (by simp)
          rw [List.take_zero, List.append_nil] at this
          exact this hm
        · rw [G.iStepIndicator_of_not_movesAt i s_i h_start e hm,
            G.iStepIndicator_of_not_movesAt i s_i' h_start e hm]
      have hrest : G.iPathConsistentFrom i s_i (h_start ++ [e]) rest =
          G.iPathConsistentFrom i s_i' (h_start ++ [e]) rest := by
        apply ih
        intro k hk_lt hk_move
        have hk_lt' : k + 1 < (e :: rest).length := by
          simp only [List.length_cons]; omega
        have hH := h_eq (k + 1) hk_lt'
        simp only [List.take_succ_cons] at hH
        have hlist : (h_start ++ [e]) ++ rest.take k = h_start ++ (e :: rest.take k) := by
          rw [List.append_assoc]; rfl
        rw [hlist]
        rw [hlist] at hk_move
        exact hH hk_move
      rw [hstep, hrest]

/-- `iPathConsistent` does not depend on the `DecidableEq` instances (they are subsingletons): The
classical-instance value coincides with the value at any ambient instances. This bridges the
`Classical`-stated `FiniteExtensiveForm.ActionRecall` predicate to ambient-instance call sites. -/
lemma iPathConsistent_classical_eq [DecidableEq E] [DecidableEq I] (i : I)
    (c : G.PureStrategy i) (h : List E) :
    @iPathConsistent I E G (Classical.decEq E) (Classical.decEq I) i c h =
      G.iPathConsistent i c h := by
  have hE : (Classical.decEq E) = ‹DecidableEq E› := Subsingleton.elim _ _
  have hI : (Classical.decEq I) = ‹DecidableEq I› := Subsingleton.elim _ _
  rw [hE, hI]

end FiniteExtensiveForm

end Econlib.GameTheory
