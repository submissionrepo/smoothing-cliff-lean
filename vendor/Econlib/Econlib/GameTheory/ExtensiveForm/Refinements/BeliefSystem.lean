/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Core.Reachable
public import Econlib.GameTheory.ExtensiveForm.Core.Strategy

/-!
# Belief systems and assessments

A **belief system** assigns to each information set a finite distribution over a finite support of
histories *inside* that information set, and an **assessment** pairs such a belief system with a
behavioral strategy (Kreps and Wilson 1982). The support is constrained on two axes:

* Type-level inclusion. Each support element carries a witness that the player moves there and that
  the observation matches the info set, so beliefs cannot place mass on histories where the player
  does not move or that lie in a different info set.
* Exhaustiveness (`support_exhaustive`). The support must contain every reachable history of the
  info set, so a belief system cannot omit a reachable history from the normalization: Every
  reachable history is in scope, receives well-defined belief mass, and is seen by Bayes
  consistency and the assessment value. Only unreachable histories (zero reach probability) may be
  dropped.

For information sets that no reachable history realizes (phantom observations) the support may be
empty and the belief sums to `0`; for info sets with at least one represented history the belief
sums to `1`. This makes `BeliefSystem` total over `(i, obs)` without requiring beliefs at
meaningless info sets, while exhaustiveness guarantees no reachable history is ignored.

## Main definitions

* `ExtensiveForm.InfoSet`: Subtype of histories in a player's information set.
* `BeliefSystem`: Finite-support beliefs at each information set.
* `BeliefSystem.prob`: Belief probability assigned to a concrete history.
* `Assessment`: Behavioral strategy paired with beliefs.
* `trivialBeliefs`: Canonical beliefs for perfect information.

## Main statements

* `BeliefSystem.sum_support_prob`: Represented belief mass is one on a nonempty information set.
* `trivialBeliefs_prob_self`: Perfect-information beliefs put mass one on the observed history.

## References

* Kreps, David M., and Robert Wilson. 1982. “Sequential Equilibria.” *Econometrica* 50 (4): 863.
  [https://doi.org/10.2307/1912767](https://doi.org/10.2307/1912767).

## Tags

extensive form, beliefs, assessment
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

universe u

variable {I E : Type u}

namespace ExtensiveForm

/-- A history that lies in player `i`'s information set at observation `obs`: Player `i` moves at
the history and the observation matches. -/
@[reducible] def InfoSet (G : ExtensiveForm I E) (i : I) (obs : G.info.Obs i) : Type u :=
  {h : List E // (G.tree.nodeKind h).movesAt i ∧ G.info.observe i h = obs}

end ExtensiveForm

/-- A belief system assigns to each information set `(i, obs)` a finite support of subtype
histories (forced to lie inside the info set) together with a real-valued belief that sums to `1`
on a non-empty info set and to `0` on an empty info set.

The `support_exhaustive` field is a type-level guarantee that the support drops no reachable
history: Every reachable history of the info set is represented, so a malformed belief system
cannot place zero mass on a reachable history and have it ignored by Bayes consistency or the
assessment value. -/
structure BeliefSystem [DecidableEq E] (G : ExtensiveForm I E) where
  /-- Finite support of histories considered possible inside the info set `(i, obs)`. By
  `support_exhaustive` this support contains every reachable history of the info set, so it cannot
  drop a reachable history; only unreachable histories may be absent. -/
  support : ∀ (i : I) (obs : G.info.Obs i), Finset (G.InfoSet i obs)
  /-- Belief mass on each subtype element of `(i, obs)`. -/
  belief : ∀ (i : I) (obs : G.info.Obs i), G.InfoSet i obs → ℝ
  /-- Beliefs are non-negative. -/
  belief_nonneg : ∀ i obs x, 0 ≤ belief i obs x
  /-- Mass is zero outside the represented support. -/
  belief_eq_zero_of_not_mem :
    ∀ i obs x, x ∉ support i obs → belief i obs x = 0
  /-- Exhaustiveness: The support contains every reachable history of the info set. This makes it
  impossible to express a belief system that omits a reachable history from the normalization;
  reachable histories always receive well-defined belief mass and are seen by Bayes consistency and
  the assessment value. Only unreachable histories (zero reach probability) may be dropped. -/
  support_exhaustive :
    ∀ (i : I) (obs : G.info.Obs i) (x : G.InfoSet i obs),
      G.IsReachable x.1 → x ∈ support i obs
  /-- Sums to `1` on a non-empty info set. (The empty case is automatic since `∑ ∅ = 0`.) -/
  belief_sum_one :
    ∀ i obs, (support i obs).Nonempty →
      ∑ x ∈ support i obs, belief i obs x = 1

namespace BeliefSystem

variable [DecidableEq E] {G : ExtensiveForm I E}

/-- Probability assigned to a concrete history `h : List E`. Returns `0` when `h` is not in the
info set `(i, obs)` at all. The `belief_eq_zero_of_not_mem` field handles the off-support case when
`h` is in the info set but not represented. -/
def prob (μ : BeliefSystem G) (i : I) (obs : G.info.Obs i) (h : List E) : ℝ := by
  classical
  exact
    if hmem : (G.tree.nodeKind h).movesAt i ∧ G.info.observe i h = obs then
      μ.belief i obs ⟨h, hmem⟩
    else 0

lemma prob_of_mem (μ : BeliefSystem G) (i : I) (obs : G.info.Obs i)
    {h : List E} (hmem : (G.tree.nodeKind h).movesAt i ∧ G.info.observe i h = obs) :
    μ.prob i obs h = μ.belief i obs ⟨h, hmem⟩ := by
  classical
  change (if hmem' : _ then μ.belief i obs ⟨h, hmem'⟩ else 0) = _
  rw [dif_pos hmem]

lemma prob_of_not_mem (μ : BeliefSystem G) (i : I) (obs : G.info.Obs i)
    {h : List E} (hmem : ¬ ((G.tree.nodeKind h).movesAt i ∧ G.info.observe i h = obs)) :
    μ.prob i obs h = 0 := by
  classical
  change (if hmem' : _ then μ.belief i obs ⟨h, hmem'⟩ else 0) = _
  rw [dif_neg hmem]

lemma prob_nonneg (μ : BeliefSystem G) (i : I) (obs : G.info.Obs i) (h : List E) :
    0 ≤ μ.prob i obs h := by
  classical
  by_cases hmem : (G.tree.nodeKind h).movesAt i ∧ G.info.observe i h = obs
  · rw [prob_of_mem μ i obs hmem]; exact μ.belief_nonneg _ _ _
  · rw [prob_of_not_mem μ i obs hmem]

/-- Sum of `prob` over the represented support: Equals `1` on a non-empty info set. -/
lemma sum_support_prob (μ : BeliefSystem G) (i : I) (obs : G.info.Obs i)
    (hne : (μ.support i obs).Nonempty) :
    ∑ x ∈ μ.support i obs, μ.prob i obs x.1 = 1 := by
  rw [← μ.belief_sum_one i obs hne]
  exact Finset.sum_congr rfl (fun x _ => prob_of_mem μ i obs x.2)

/-- A subtype element `x : G.InfoSet i obs` automatically satisfies the info-set hypothesis on
`x.1`, so `prob i obs x.1 = belief i obs x`. -/
lemma prob_subtype (μ : BeliefSystem G) (i : I) (obs : G.info.Obs i) (x : G.InfoSet i obs) :
    μ.prob i obs x.1 = μ.belief i obs x :=
  prob_of_mem μ i obs x.2

end BeliefSystem

/-- An assessment bundles a behavioral strategy with a belief system over the same extensive form.
The strategy is necessarily info-set-respecting (by being a `BehavioralStrategy`); the belief
system's support is type-level constrained to lie inside the relevant information sets and, by
`BeliefSystem.support_exhaustive`, to contain every reachable history of each info set. -/
structure Assessment [DecidableEq E] (G : ExtensiveForm I E) where
  /-- The behavioral strategy profile. -/
  strategy : G.BehavioralStrategy
  /-- The belief system. -/
  beliefs : BeliefSystem G

/-- Under perfect information, the support at `(i, obs)` is the singleton `{⟨obs, _⟩}` when `i`
moves at history `obs`, and empty otherwise. The latter case covers `(i, obs)` pairs where player
`i` never moves at the history `obs`, so no beliefs are required there. -/
noncomputable def trivialBeliefs (I E : Type u) [DecidableEq I] [DecidableEq E]
    (t : GameTree I E) :
    BeliefSystem (ExtensiveForm.ofGameTreePerfectInfo t) := by
  classical
  refine
    { support := fun i obs =>
        if hm : (t.nodeKind obs).movesAt i then
          ({⟨obs, hm, rfl⟩} : Finset _)
        else ∅
      belief := fun _ _ _ => 1
      belief_nonneg := fun _ _ _ => zero_le_one
      belief_eq_zero_of_not_mem := ?_
      support_exhaustive := ?_
      belief_sum_one := ?_ }
  · intro i obs x hxnotmem
    exfalso
    obtain ⟨hmoves_x, hobs_x⟩ := x.2
    have hxval : x.1 = obs := hobs_x
    have hmoves_obs : (t.nodeKind obs).movesAt i := hxval ▸ hmoves_x
    apply hxnotmem
    show x ∈ (if hm : (t.nodeKind obs).movesAt i then
                ({⟨obs, hm, rfl⟩} : Finset _) else ∅)
    rw [dif_pos hmoves_obs, Finset.mem_singleton]
    exact Subtype.ext hxval
  · -- support_exhaustive: every info-set history equals the canonical singleton history `obs`
    -- (under perfect information `observe i h = h`), so it is in the singleton support.
    -- Reachability is not needed here: the perfect-info support already enumerates the whole
    -- info set.
    intro i obs x _hreach
    obtain ⟨hmoves_x, hobs_x⟩ := x.2
    have hxval : x.1 = obs := hobs_x
    have hmoves_obs : (t.nodeKind obs).movesAt i := hxval ▸ hmoves_x
    change x ∈ (if hm : (t.nodeKind obs).movesAt i then
                ({⟨obs, hm, rfl⟩} : Finset _) else ∅)
    rw [dif_pos hmoves_obs, Finset.mem_singleton]
    exact Subtype.ext hxval
  · -- belief_sum_one: only the movesAt branch yields nonempty support.
    intro i obs hne
    obtain ⟨x, hx⟩ := hne
    by_cases hm : (t.nodeKind obs).movesAt i
    · rw [dif_pos hm, Finset.sum_singleton]
    · -- support is empty, contradicting hne.
      exfalso
      rw [dif_neg hm] at hx
      exact (Finset.notMem_empty x) hx

/-- Trivial perfect-information beliefs assign probability one to the observed history when the
player moves at it. -/
@[simp] lemma trivialBeliefs_prob_self [DecidableEq I] [DecidableEq E] (t : GameTree I E)
    (i : I) (h : List E) (hmoves : (t.nodeKind h).movesAt i) :
    (trivialBeliefs I E t).prob i h h = 1 := by
  classical
  have hmem :
      ((ExtensiveForm.ofGameTreePerfectInfo t).tree.nodeKind h).movesAt i ∧
        (ExtensiveForm.ofGameTreePerfectInfo t).info.observe i h = h := ⟨hmoves, rfl⟩
  rw [BeliefSystem.prob_of_mem (trivialBeliefs I E t) i h hmem]
  rfl

/-- Trivial perfect-information beliefs assign zero probability when the player does not move at
the observed history. -/
@[simp] lemma trivialBeliefs_prob_zero_of_not_movesAt [DecidableEq I] [DecidableEq E]
    (t : GameTree I E) (i : I) (obs h : List E)
    (hnot : ¬ (t.nodeKind h).movesAt i) :
    (trivialBeliefs I E t).prob i obs h = 0 :=
  BeliefSystem.prob_of_not_mem _ _ _ (fun ⟨hmoves, _⟩ => hnot hmoves)

/-- Trivial perfect-information beliefs assign zero probability when the observation does not match
the history. -/
@[simp] lemma trivialBeliefs_prob_zero_of_ne [DecidableEq I] [DecidableEq E]
    (t : GameTree I E) (i : I) (obs h : List E) (hne : h ≠ obs) :
    (trivialBeliefs I E t).prob i obs h = 0 :=
  BeliefSystem.prob_of_not_mem _ _ _ (fun ⟨_, hobs⟩ => hne hobs)

end Econlib.GameTheory
