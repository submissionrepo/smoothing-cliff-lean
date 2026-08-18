/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.OneShotDeviation

/-!
# Constructing Kreps–Wilson consistent beliefs

`HasConsistentBeliefs` is an existential over totally mixed approximating sequences, so consuming
it is easy but witnessing it on a concrete game requires building the trembles by hand. This file
provides the standard construction (Kreps and Wilson 1982): The **tremble** of a behavioral
strategy mixes every information-set component with the uniform (barycentric) point at rate `ε`
(`BehavioralStrategy.tremble`), is totally mixed for `0 < ε` (`isTotallyMixed_tremble`), and its
behavioral coordinates converge to the original strategy's as `ε → 0`
(`stdSimplex.tremble_val_tendsto`). The derived `stepProb_tremble_tendsto` remains available for
event-level continuity arguments.

`HasConsistentBeliefs.of_subsingleton_support` then witnesses Kreps–Wilson consistency for any
assessment whose belief supports are subsingletons of positively-reachable histories — the
degenerate-beliefs case covering perfect-information games (where every information set is a
singleton, so beliefs are forced) and, more generally, any game whose information sets contain at
most one relevant history. On a subsingleton support the Bayesian posterior under any totally mixed
strategy is identically the point mass the belief system declares, so the tremble sequence
witnesses the limit condition with a constant posterior sequence.

## Main definitions

* `ExtensiveForm.BehavioralStrategy.tremble`: The `ε`-tremble of a behavioral strategy.

## Main statements

* `ExtensiveForm.isTotallyMixed_tremble`: Trembles at positive rate are totally mixed.
* `ExtensiveForm.stepProb_tremble`: Step probabilities of a tremble are affine in the tremble rate.
* `ExtensiveForm.stepProb_tremble_tendsto`: Step probabilities of vanishing trembles converge.
* `HasConsistentBeliefs.of_subsingleton_support`: Kreps–Wilson consistency for assessments with
  subsingleton belief supports.

## References

* Kreps, David M., and Robert Wilson. 1982. “Sequential Equilibria.” *Econometrica* 50 (4): 863.
  [https://doi.org/10.2307/1912767](https://doi.org/10.2307/1912767).

## Tags

extensive form, sequential equilibrium, consistent beliefs, tremble, totally mixed
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

universe u

variable {I E : Type u}

namespace ExtensiveForm

/-- The **`ε`-tremble** of a behavioral strategy: Every information-set component is mixed with the
uniform point at rate `ε` via `stdSimplex.tremble`. -/
noncomputable def BehavioralStrategy.tremble {G : ExtensiveForm I E} (σ : G.BehavioralStrategy)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : G.BehavioralStrategy :=
  fun i obs => stdSimplex.tremble ε hε0 hε1 (σ i obs)

/-- Trembles at a strictly positive rate are totally mixed: Every legal choice at every information
set receives at least `ε / card` mass. -/
lemma isTotallyMixed_tremble {G : ExtensiveForm I E} (σ : G.BehavioralStrategy)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    G.IsTotallyMixed (σ.tremble ε hε.le hε1) :=
  fun i obs c => stdSimplex.tremble_val_pos hε hε1 (σ i obs) c

/-- The node-local behavior of a tremble at a player node is the tremble of the node-local
behavior: `playerBehavior` commutes with the tremble, coordinatewise. -/
lemma BehavioralStrategy.playerBehavior_tremble_val {G : ExtensiveForm I E}
    (σ : G.BehavioralStrategy) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {h : List E} {n : PlayerNode I E} (hnk : G.tree.nodeKind h = .player n) (c : n.Choice) :
    ((σ.tremble ε hε0 hε1).playerBehavior h hnk).val c =
      (1 - ε) * (σ.playerBehavior h hnk).val c + ε * (Fintype.card n.Choice : ℝ)⁻¹ := by
  -- The choice-type equality the `atHistory` player branch transports along.
  have hm : (G.tree.nodeKind h).movesAt n.mover := by rw [hnk]; rfl
  have hcompat : (G.tree.nodeKind h).iChoiceTypeAt n.mover hm =
      G.info.iChoiceType n.mover (G.info.observe n.mover h) :=
    G.iChoice_compatible n.mover h hm
  have hbridge : (G.tree.nodeKind h).iChoiceTypeAt n.mover hm = n.Choice := by
    clear hcompat; revert hm; rw [hnk]; intro _; rfl
  have hchoice : n.Choice = G.info.iChoiceType n.mover (G.info.observe n.mover h) :=
    hbridge.symm.trans hcompat
  -- Read off both `playerBehavior`s through the transport, coordinatewise.
  have hval_tremble : ((σ.tremble ε hε0 hε1).playerBehavior h hnk).val c =
      ((σ.tremble ε hε0 hε1) n.mover (G.info.observe n.mover h)).val (hchoice ▸ c) :=
    stdSimplex.heq_val hchoice _ _
      ((cast_heq _ _).trans ((σ.tremble ε hε0 hε1).atHistory_player_heq hnk)) c
  have hval_base : (σ.playerBehavior h hnk).val c =
      (σ n.mover (G.info.observe n.mover h)).val (hchoice ▸ c) :=
    stdSimplex.heq_val hchoice _ _ ((cast_heq _ _).trans (σ.atHistory_player_heq hnk)) c
  rw [hval_tremble, hval_base]
  change (stdSimplex.tremble ε hε0 hε1 (σ n.mover (G.info.observe n.mover h))).val _ = _
  rw [stdSimplex.tremble_val]
  -- The two cardinalities agree across the choice-type equality.
  rw [Fintype.card_congr (Equiv.cast hchoice.symm)]

/-- **Step probabilities of a tremble are affine in the tremble rate.** At every history there is a
constant `K` (depending only on the history and the event, not on the rate) with
`stepProb (tremble ε σ) h e = (1 - ε) · stepProb σ h e + ε · K`. At non-player nodes the step
probability is strategy-independent, so `K` is the common value; at a player node `K` is the
uniform mass of the choices emitting `e`. Joint nodes are excluded by `hno_joint`. -/
lemma stepProb_tremble [DecidableEq E] (G : ExtensiveForm I E)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.tree.nodeKind h ≠ .joint n)
    (σ : G.BehavioralStrategy) (h : List E) (e : E) :
    ∃ K : ℝ, ∀ (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1),
      G.stepProb (σ.tremble ε hε0 hε1) h e = (1 - ε) * G.stepProb σ h e + ε * K := by
  rcases hk : G.tree.nodeKind h with payoff | n | n | n | n
  case player =>
    -- `K` is the uniform mass of the choices emitting `e`.
    refine ⟨∑ c : n.Choice, if n.emit c = e then (Fintype.card n.Choice : ℝ)⁻¹ else 0,
      fun ε hε0 hε1 => ?_⟩
    rw [G.stepProb_player (σ.tremble ε hε0 hε1) hk e, G.stepProb_player σ hk e,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [σ.playerBehavior_tremble_val hε0 hε1 hk c]
    split_ifs <;> ring
  case joint => exact absurd hk (hno_joint h n)
  all_goals
    -- Non-player, non-joint nodes: `stepProb` is strategy-independent (no player moves at `h`),
    -- so `K := stepProb σ h e` and the affine identity collapses to `(1 - ε + ε) · K = K`.
    refine ⟨G.stepProb σ h e, fun ε hε0 hε1 => ?_⟩
    rw [stepProb_congr_movers G (σ.tremble ε hε0 hε1) σ h e
      (fun j hj => by rw [hk] at hj; exact hj.elim)]
    ring

/-- **Step probabilities of vanishing trembles converge** to the step probabilities of the base
strategy, at every history and event. -/
lemma stepProb_tremble_tendsto [DecidableEq E] (G : ExtensiveForm I E)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.tree.nodeKind h ≠ .joint n)
    (σ : G.BehavioralStrategy) {ε : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ ε n) (hε1 : ∀ n, ε n ≤ 1)
    (hlim : Filter.Tendsto ε Filter.atTop (nhds 0)) (h : List E) (e : E) :
    Filter.Tendsto (fun n => G.stepProb (σ.tremble (ε n) (hε0 n) (hε1 n)) h e)
      Filter.atTop (nhds (G.stepProb σ h e)) := by
  obtain ⟨K, hK⟩ := stepProb_tremble G hno_joint σ h e
  simp only [fun n => hK (ε n) (hε0 n) (hε1 n)]
  have hlim' : Filter.Tendsto (fun n => (1 - ε n) * G.stepProb σ h e + ε n * K) Filter.atTop
      (nhds ((1 - 0) * G.stepProb σ h e + 0 * K)) :=
    ((tendsto_const_nhds.sub hlim).mul tendsto_const_nhds).add (hlim.mul tendsto_const_nhds)
  simpa using hlim'

end ExtensiveForm

/-- **Kreps–Wilson consistency for degenerate beliefs.** An assessment whose belief supports are
subsingletons of positively-reachable histories has consistent beliefs. This applies in particular
to perfect-information games (every information set is a singleton) and to any game whose belief
supports contain at most one history per information set. The `hreach` hypothesis requires positive
reach of each supported history under some strategy. -/
theorem HasConsistentBeliefs.of_subsingleton_support [DecidableEq E] (G : ExtensiveGame I E)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (a : Assessment G.toExtensiveForm)
    (hsub : ∀ (i : I) (obs : G.info.Obs i),
      ((a.beliefs.support i obs : Set (G.toExtensiveForm.InfoSet i obs))).Subsingleton)
    (hreach : ∀ (i : I) (obs : G.info.Obs i) (x : G.toExtensiveForm.InfoSet i obs),
      x ∈ a.beliefs.support i obs →
        ∃ τ : G.toExtensiveForm.BehavioralStrategy, 0 < reachProb G.toExtensiveForm τ x.1) :
    HasConsistentBeliefs G.toExtensiveForm a := by
  classical
  have hrate0 : ∀ n : ℕ, (0 : ℝ) < 1 / (n + 1) := fun n => by positivity
  have hrate1 : ∀ n : ℕ, (1 : ℝ) / (n + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hrate_lim : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun n => a.strategy.tremble (1 / (n + 1)) (hrate0 n).le (hrate1 n),
    fun n => ExtensiveForm.isTotallyMixed_tremble a.strategy (hrate0 n) (hrate1 n),
    fun i obs c => stdSimplex.tremble_val_tendsto (fun n => (hrate0 n).le) hrate1 hrate_lim
      (a.strategy i obs) c, ?_⟩
  -- The belief clause: the posterior sequence is *constant* at the declared belief.
  intro i obs h
  set σseq : ℕ → G.toExtensiveForm.BehavioralStrategy :=
    fun n => a.strategy.tremble (1 / (n + 1)) (hrate0 n).le (hrate1 n) with hσseq
  have hmix : ∀ n, G.toExtensiveForm.IsTotallyMixed (σseq n) :=
    fun n => ExtensiveForm.isTotallyMixed_tremble a.strategy (hrate0 n) (hrate1 n)
  by_cases hin : (G.toExtensiveForm.tree.nodeKind h).movesAt i ∧
      G.toExtensiveForm.info.observe i h = obs
  · by_cases hmem : (⟨h, hin⟩ : G.toExtensiveForm.InfoSet i obs) ∈ a.beliefs.support i obs
    · -- Singleton support `{⟨h, hin⟩}`: the posterior is the point mass `1`, constantly.
      have hsupp_eq : a.beliefs.support i obs = {⟨h, hin⟩} :=
        Finset.eq_singleton_iff_unique_mem.mpr
          ⟨hmem, fun y hy => hsub i obs (Finset.mem_coe.mpr hy) (Finset.mem_coe.mpr hmem)⟩
      have hbel_one : a.beliefs.belief i obs ⟨h, hin⟩ = 1 := by
        have hsum := a.beliefs.belief_sum_one i obs ⟨⟨h, hin⟩, hmem⟩
        rwa [hsupp_eq, Finset.sum_singleton] at hsum
      have hprob : a.beliefs.prob i obs h = 1 := by
        rw [a.beliefs.prob_of_mem i obs hin, hbel_one]
      -- Positive reach of `h` under each tremble, transferred from the `hreach` witness.
      obtain ⟨τ, hτ⟩ := hreach i obs ⟨h, hin⟩ hmem
      have hreach_pos : ∀ n, 0 < reachProb G.toExtensiveForm (σseq n) h :=
        fun n => reachProb_pos_of_totallyMixed_of_pos G hno_joint (σseq n) τ (hmix n) hτ
      have hbayes_one : ∀ n, bayesBeliefAt G.toExtensiveForm (σseq n) a.beliefs i obs h = 1 := by
        intro n
        have hIP : infoSetProb G.toExtensiveForm (σseq n) a.beliefs i obs =
            reachProb G.toExtensiveForm (σseq n) h := by
          rw [infoSetProb, hsupp_eq, Finset.sum_singleton]
        have hIP_pos : 0 < infoSetProb G.toExtensiveForm (σseq n) a.beliefs i obs := by
          rw [hIP]; exact hreach_pos n
        unfold bayesBeliefAt
        rw [dif_pos hin, if_pos hmem, dif_pos hIP_pos, hIP,
          div_self (hreach_pos n).ne']
      rw [hprob]
      simp only [hbayes_one]
      exact tendsto_const_nhds
    · -- In the info set but off support: posterior and belief both vanish identically.
      have hbayes_zero : ∀ n, bayesBeliefAt G.toExtensiveForm (σseq n) a.beliefs i obs h = 0 := by
        intro n; unfold bayesBeliefAt; rw [dif_pos hin, if_neg hmem]
      have hprob : a.beliefs.prob i obs h = 0 := by
        rw [a.beliefs.prob_of_mem i obs hin]
        exact a.beliefs.belief_eq_zero_of_not_mem i obs ⟨h, hin⟩ hmem
      rw [hprob]
      simp only [hbayes_zero]
      exact tendsto_const_nhds
  · -- Outside the info set: posterior and belief both vanish identically.
    have hbayes_zero : ∀ n, bayesBeliefAt G.toExtensiveForm (σseq n) a.beliefs i obs h = 0 := by
      intro n; unfold bayesBeliefAt; rw [dif_neg hin]
    have hprob : a.beliefs.prob i obs h = 0 := a.beliefs.prob_of_not_mem i obs hin
    rw [hprob]
    simp only [hbayes_zero]
    exact tendsto_const_nhds

end Econlib.GameTheory
