/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.ReachCoherent

/-!
# Consistency belief tower for the one-shot deviation principle

The cross-information-set weight transport underlying the extensive-form one-shot deviation
principle. Under Kreps–Wilson consistency (Kreps and Wilson 1982) and perfect recall, the
equilibrium beliefs at a deeper information set are proportional to the reach induced by any
unilateral deviation, and the weight a backward induction accumulates at a deeper support
transports back to that set's own beliefs. The file also collects the reach/belief degeneracy facts
and the interior Bellman event sum that the towers consume.

## Main definitions

* `deviatedSeq`: The deviated consistency sequence used to transport the proportionality.

## Main statements

* `consistency_belief_tower`: Deviation-invariant belief proportionality at an information set.
* `chain_belief_tower`: Cross-information-set transport of accumulated belief weights.

## Notes

The towers transport their proportionality along `deviatedSeq`, which copies the deviation `σ'` at
player `i` and the consistency witness elsewhere.

## References

* Kreps, David M., and Robert Wilson. 1982. “Sequential Equilibria.” *Econometrica* 50 (4): 863.
  [https://doi.org/10.2307/1912767](https://doi.org/10.2307/1912767).

## Tags

extensive form, one-shot deviation principle, perfect recall, sequential equilibrium
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

universe u

variable {I E : Type u} [DecidableEq E]

/-- **Totally-mixed step positivity.** Under a totally mixed strategy, the one-step probability of
an emitted event is strictly positive at player nodes. (At chance/terminal nodes total mixing says
nothing, so this is restricted to the moving-player case, which is all the belief tower consumes —
the information-set nodes are player nodes.) -/
theorem stepProb_pos_of_totallyMixed (G : ExtensiveForm I E)
    (σ : G.BehavioralStrategy) (hmix : G.IsTotallyMixed σ)
    {h : List E} {n : PlayerNode I E} (hnk : G.tree.nodeKind h = .player n)
    {e : E} (he : ∃ c : n.Choice, n.emit c = e) :
    0 < G.stepProb σ h e := by
  -- `stepProb σ h e = ∑ c, if emit c = e then (playerBehavior).val c else 0`, a sum of nonnegative
  -- terms with at least one strictly positive term (the witnessing `c`, positive by total mixing).
  -- Total mixing is stated on `σ i obs`; `playerBehavior` is a `cast`/transport of `σ.atHistory h`,
  -- which at a player node is `simplexTransport _ (σ n.mover (observe n.mover h))`. The transport
  -- preserves `.val` up to the choice-type equality, so each component stays positive.
  have hval_pos : ∀ c : n.Choice, 0 < (σ.playerBehavior h hnk).val c := by
    -- `playerBehavior h hnk` is HEq to `σ n.mover (observe n.mover h)` (both equal `σ.atHistory h`
    -- up to a transport cast), so their `.val` functions are HEq; total mixing of the latter
    -- transfers to positivity of the former coordinatewise.
    have hheq : HEq (σ.playerBehavior h hnk) (σ n.mover (G.info.observe n.mover h)) :=
      (cast_heq _ _).trans (σ.atHistory_player_heq hnk)
    -- The choice types match: this is exactly the `heq` the `atHistory` player branch transports
    -- along (`iChoice_compatible` composed with the player-node bridge).
    have hm : (G.tree.nodeKind h).movesAt n.mover := by rw [hnk]; rfl
    have hcompat : (G.tree.nodeKind h).iChoiceTypeAt n.mover hm =
        G.info.iChoiceType n.mover (G.info.observe n.mover h) :=
      G.iChoice_compatible n.mover h hm
    have hbridge : (G.tree.nodeKind h).iChoiceTypeAt n.mover hm = n.Choice := by
      clear hcompat; revert hm; rw [hnk]; intro _; rfl
    have hchoice : n.Choice = G.info.iChoiceType n.mover (G.info.observe n.mover h) :=
      (hcompat.symm.trans hbridge).symm
    -- Transport the simplex HEq through `.val` coordinatewise via the helper.
    intro c
    rw [stdSimplex.heq_val hchoice (σ.playerBehavior h hnk)
      (σ n.mover (G.info.observe n.mover h)) hheq c]
    exact hmix n.mover (G.info.observe n.mover h) (hchoice ▸ c)
  rw [G.stepProb_player σ hnk e]
  obtain ⟨c₀, hc₀⟩ := he
  refine Finset.sum_pos' (fun c _ => ?_) ⟨c₀, Finset.mem_univ c₀, ?_⟩
  · split_ifs with hc
    · exact (hval_pos c).le
    · exact le_refl 0
  · rw [if_pos hc₀]; exact hval_pos c₀

/-- **Deviation-invariant belief proportionality.** Under Kreps–Wilson consistency and perfect
recall, at any information set `v = (i, obs'')` the equilibrium belief profile `μ.belief i obs''`
is proportional to the reach induced by any unilateral `i`-deviation `σ'` of `σ = a.strategy`: For
two `IsReachable` nodes `y, y'` in `v`,

`μ.belief i obs'' y · reachProb σ' y'.1 = μ.belief i obs'' y' · reachProb σ' y.1`.

On path with `σ' = σ` this is Bayes consistency; off path it is the limit of the totally-mixed
posteriors, transported from `σseq`-reach to `σ'`-reach by `reachInvariant`. -/
theorem consistency_belief_tower (G : ExtensiveGame I E)
    (hpr : G.toExtensiveForm.IsReachCoherent)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (a : Assessment G.toExtensiveForm) (hcons : HasConsistentBeliefs G.toExtensiveForm a)
    (i : I) (obs'' : G.info.Obs i)
    (σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i a.strategy σ')
    (y y' : G.toExtensiveForm.InfoSet i obs'')
    (hy : y ∈ a.beliefs.support i obs'') (hy' : y' ∈ a.beliefs.support i obs'')
    (hyr : G.toExtensiveForm.IsReachable y.1) (hy'r : G.toExtensiveForm.IsReachable y'.1) :
    a.beliefs.belief i obs'' y * reachProb G.toExtensiveForm σ' y'.1 =
      a.beliefs.belief i obs'' y' * reachProb G.toExtensiveForm σ' y.1 := by
  -- Split on whether `v = (i, obs'')` is on path under `σ = a.strategy`.
  by_cases hpos : 0 < infoSetProb G.toExtensiveForm a.strategy a.beliefs i obs''
  · -- On path. Bayes consistency rewrites each `μ(y|v)` as `reachProb σ y.1 / IP`, and
    -- `reachInvariant` (applied to the fixed pair `σ, σ'`, both `IsReachable`) gives the
    -- cross-multiplied proportionality `reachProb σ' y · reachProb σ y' = reachProb σ' y' · σ y`.
    have hbayes : IsBayesConsistent G.toExtensiveForm a :=
      isBayesConsistent_of_hasConsistentBeliefs G a hcons
    -- `μ(y|v) = reachProb σ y.1 / IP`.
    have hbel_y : a.beliefs.belief i obs'' y =
        reachProb G.toExtensiveForm a.strategy y.1 /
          infoSetProb G.toExtensiveForm a.strategy a.beliefs i obs'' := by
      rw [← a.beliefs.prob_subtype i obs'' y, hbayes i obs'' hpos y.1]
      unfold bayesBeliefAt
      rw [dif_pos y.2, if_pos (by simpa using hy), dif_pos hpos]
    have hbel_y' : a.beliefs.belief i obs'' y' =
        reachProb G.toExtensiveForm a.strategy y'.1 /
          infoSetProb G.toExtensiveForm a.strategy a.beliefs i obs'' := by
      rw [← a.beliefs.prob_subtype i obs'' y', hbayes i obs'' hpos y'.1]
      unfold bayesBeliefAt
      rw [dif_pos y'.2, if_pos (by simpa using hy'), dif_pos hpos]
    -- The reach-invariance cross relation for the fixed pair `σ, σ'` at the info set `(i, obs'')`.
    have hinv := hpr.reachInvariant i a.strategy σ' hdev obs'' y.1 y'.1 hyr hy'r y.2 y'.2
    rw [hbel_y, hbel_y', div_mul_eq_mul_div, div_mul_eq_mul_div]
    -- Equal denominators: reduce to equality of numerators, which is `reachInvariant` (commuted).
    congr 1
    linarith [hinv]
  · -- Off path. `μ(·|v)` is the limit of the totally-mixed posteriors `B_n`. The bridge
    -- to `σ'` is the **deviated sequence** `τ_n := σ' at coordinate i, σseq n elsewhere`: it is a
    -- unilateral `i`-deviation of `σseq n` (so `reachInvariant` applies to `(σseq n, τ_n)`), and it
    -- converges to `σ'` (off `i`, `τ_n = σseq n → σ = σ'` by `hstep`+`hdev`; on `i`, `τ_n = σ'`
    -- constant). The per-`n` identity `B_n(y)·reachProb τ_n y' = B_n(y')·reachProb τ_n y` (from
    -- `reachInvariant`, both branches of `IP_n > 0`) passes to the limit.
    classical
    obtain ⟨σseq, hmix, hstrategy, hbel⟩ := hcons
    have hstep := hstrategy.stepProb
    set μ := a.beliefs with hμ
    set σ := a.strategy with hσ
    -- The deviated sequence.
    set τ : ℕ → G.toExtensiveForm.BehavioralStrategy :=
      fun n j obs => if j = i then σ' j obs else σseq n j obs with hτ
    -- `τ n` is a unilateral `i`-deviation of `σseq n`.
    have hτ_dev : ∀ n, G.toExtensiveForm.unilateralDeviation i (σseq n) (τ n) := by
      intro n j obs hji; simp only [hτ, if_neg hji]
    -- Step probabilities of `τ n` converge to those of `σ'`. `stepProb` reads only the movers'
    -- coordinates (`stepProb_congr_movers`), on which `τ n` either equals `σ'` (`i`-mover player
    -- node, exact, constant in `n`) or equals `σseq n → σ = σ'` (no `i`-mover, `hstep` + `hdev`).
    have hstep' : ∀ h e, Filter.Tendsto (fun n => G.toExtensiveForm.stepProb (τ n) h e)
        Filter.atTop (nhds (G.toExtensiveForm.stepProb σ' h e)) := by
      intro h e
      by_cases hi : (G.toExtensiveForm.tree.nodeKind h).movesAt i
      · -- `i` moves at `h`. At a single-player node (`i` the unique mover) `τ n` reads `σ'` at the
        -- only relevant coordinate, so `stepProb (τ n) h e = stepProb σ' h e` exactly. (Joint nodes
        -- with `i` active are unreachable in the finite layer carrying `reachInvariant`.)
        rcases hk : G.toExtensiveForm.tree.nodeKind h with _ | n_p | n_j | n_c | n_g
        · rw [hk] at hi; exact absurd hi id
        · -- player node: the unique mover is `n_p.mover`; `hi` forces `n_p.mover = i`.
          have hmover : n_p.mover = i := by rw [hk] at hi; exact hi
          have heq : ∀ m, G.toExtensiveForm.stepProb (τ m) h e =
              G.toExtensiveForm.stepProb σ' h e := by
            intro m
            have hag : ∀ j : I, (G.toExtensiveForm.tree.nodeKind h).movesAt j →
                (τ m) j (G.toExtensiveForm.info.observe j h) =
                  σ' j (G.toExtensiveForm.info.observe j h) := by
              intro j hj
              -- The only mover is `n_p.mover = i`, where `τ m = σ'`.
              have hji : j = i := by rw [hk] at hj; rw [← hj]; exact hmover
              subst hji
              simp only [hτ, if_pos rfl]
            exact stepProb_congr_movers G.toExtensiveForm (τ m) σ' h e hag
          simp only [heq]; exact tendsto_const_nhds
        · -- joint node: excluded by `hno_joint`. The OSDP realization layer is over sequential
          -- forms — `reachProb_infoSet_invariant_unilateral` already requires
          -- `FiniteExtensiveForm`, which has `no_joint` — so a joint node where `i` is active
          -- cannot occur in this limit argument.
          exact absurd hk (hno_joint h n_j)
        · rw [hk] at hi; exact absurd hi id
        · rw [hk] at hi; exact absurd hi id
      · -- `i` does not move at `h`: every mover `j` has `j ≠ i`, so `τ n` reads `σseq n` and `σ'`
        -- reads `σ`. The target reduces to `stepProb σseq n → stepProb σ`, which is `hstep`.
        have hτσseq : ∀ m, G.toExtensiveForm.stepProb (τ m) h e =
            G.toExtensiveForm.stepProb (σseq m) h e := by
          intro m
          have hag : ∀ j : I, (G.toExtensiveForm.tree.nodeKind h).movesAt j →
              (τ m) j (G.toExtensiveForm.info.observe j h) =
                (σseq m) j (G.toExtensiveForm.info.observe j h) := by
            intro j hj
            have hji : j ≠ i := fun h0 => hi (h0 ▸ hj)
            simp only [hτ, if_neg hji]
          exact stepProb_congr_movers G.toExtensiveForm (τ m) (σseq m) h e hag
        have hσ'σ : G.toExtensiveForm.stepProb σ' h e = G.toExtensiveForm.stepProb σ h e := by
          have hag : ∀ j : I, (G.toExtensiveForm.tree.nodeKind h).movesAt j →
              σ' j (G.toExtensiveForm.info.observe j h) =
                σ j (G.toExtensiveForm.info.observe j h) := by
            intro j hj
            exact hdev j (G.toExtensiveForm.info.observe j h) (fun h0 => hi (h0 ▸ hj))
          exact stepProb_congr_movers G.toExtensiveForm σ' σ h e hag
        simp only [hτσseq, hσ'σ]
        exact hstep h e
    -- `B_n(y) := bayesBeliefAt (σseq n) μ i obs'' y.1`, converging to `μ.belief i obs'' y` (`hbel`
    -- + `prob_subtype`).
    have hB : ∀ (z : G.toExtensiveForm.InfoSet i obs''),
        Filter.Tendsto (fun n => bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs'' z.1)
          Filter.atTop (nhds (μ.belief i obs'' z)) := by
      intro z
      have h := hbel i obs'' z.1
      rwa [μ.prob_subtype i obs'' z] at h
    -- `reachProb (τ n) ·` converges to `reachProb σ' ·`.
    have hRτ : ∀ (z : List E),
        Filter.Tendsto (fun n => reachProb G.toExtensiveForm (τ n) z) Filter.atTop
          (nhds (reachProb G.toExtensiveForm σ' z)) :=
      fun z => reachProb_tendsto G.toExtensiveForm τ σ' hstep' z
    -- Per-`n` identity: `B_n(y)·reachProb τ_n y' = B_n(y')·reachProb τ_n y`.
    have hpern : ∀ n,
        bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs'' y.1 *
            reachProb G.toExtensiveForm (τ n) y'.1 =
          bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs'' y'.1 *
            reachProb G.toExtensiveForm (τ n) y.1 := by
      intro n
      by_cases hIPn : 0 < infoSetProb G.toExtensiveForm (σseq n) μ i obs''
      · -- `B_n(z) = reachProb σseq_n z / IP_n`; `reachInvariant` for `(σseq n, τ n)` closes it.
        have hBy : bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs'' y.1 =
            reachProb G.toExtensiveForm (σseq n) y.1 /
              infoSetProb G.toExtensiveForm (σseq n) μ i obs'' := by
          unfold bayesBeliefAt; rw [dif_pos y.2, if_pos (by simpa using hy), dif_pos hIPn]
        have hBy' : bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs'' y'.1 =
            reachProb G.toExtensiveForm (σseq n) y'.1 /
              infoSetProb G.toExtensiveForm (σseq n) μ i obs'' := by
          unfold bayesBeliefAt; rw [dif_pos y'.2, if_pos (by simpa using hy'), dif_pos hIPn]
        have hinv := hpr.reachInvariant i (σseq n) (τ n) (hτ_dev n) obs'' y.1 y'.1 hyr hy'r y.2 y'.2
        rw [hBy, hBy', div_mul_eq_mul_div, div_mul_eq_mul_div]
        congr 1
        -- `reachProb σseq_n y · reachProb τ_n y' = reachProb σseq_n y' · reachProb τ_n y`.
        linarith [hinv]
      · -- `IP_n = 0`: both posteriors are zero (the `dif_neg hIPn` branch), so both sides vanish.
        have hz : ∀ z : G.toExtensiveForm.InfoSet i obs'',
            bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs'' z.1 = 0 := by
          intro z; unfold bayesBeliefAt
          rw [dif_pos z.2]
          split_ifs <;> rfl
        rw [hz y, hz y', zero_mul, zero_mul]
    -- Take limits of the per-`n` identity: LHS → `μ(y|v)·reachProb σ' y'`, RHS → the mirror.
    have hlimL : Filter.Tendsto
        (fun n => bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs'' y.1 *
          reachProb G.toExtensiveForm (τ n) y'.1) Filter.atTop
        (nhds (μ.belief i obs'' y * reachProb G.toExtensiveForm σ' y'.1)) :=
      (hB y).mul (hRτ y'.1)
    have hlimR : Filter.Tendsto
        (fun n => bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs'' y'.1 *
          reachProb G.toExtensiveForm (τ n) y.1) Filter.atTop
        (nhds (μ.belief i obs'' y' * reachProb G.toExtensiveForm σ' y.1)) :=
      (hB y').mul (hRτ y.1)
    exact tendsto_nhds_unique (Filter.Tendsto.congr hpern hlimL) hlimR

/-! ### Reach and belief degeneracy -/

/-- A one-step probability vanishes on an event the node does not emit, away from general-chance
nodes (where `eventProb` is a distribution mass on a preimage and `emits` is `False`, so the
implication can fail). At player / joint / chance-finite kinds `stepProb` is a sum of
`if emit · = e then … else 0`, and `¬ emits e` empties the positive branch; the excluded
general-chance kind never occurs in an `ExtensiveGame` (`no_chanceGeneral`). -/
theorem ExtensiveForm.stepProb_eq_zero_of_not_emits (G : ExtensiveForm I E)
    (σ : G.BehavioralStrategy) (h : List E) (e : E)
    (hng : ∀ n : ChanceGeneralNode E, G.tree.nodeKind h ≠ .chanceGeneral n)
    (hne : ¬ (G.tree.nodeKind h).emits e) :
    G.stepProb σ h e = 0 := by
  -- Commit `stepProb` to its per-kind event-sum formula (the committed lemmas handle the dependent
  -- `atHistory` cast), then in each non-vacuous branch the guard `emit · = e` is false (else `e`
  -- would be emitted), so every term is `0`.
  rcases hk : G.tree.nodeKind h with p | n | n | n | n
  · rw [ExtensiveForm.stepProb_of_terminal G σ hk e]
  · -- player node: `¬ ∃ c, emit c = e`.
    rw [G.stepProb_player σ hk e]
    rw [hk] at hne
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [if_neg (fun hc => hne ⟨c, hc⟩)]
  · -- joint node: `¬ ∃ c, emit c = e`.
    rw [G.stepProb_joint σ hk e]
    rw [hk] at hne
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [if_neg (fun hc => hne ⟨c, hc⟩)]
  · -- chance-finite node: `¬ ∃ ω, emit ω = e`.
    rw [ExtensiveForm.stepProb_of_chanceFinite G σ hk e]
    rw [hk] at hne
    refine Finset.sum_eq_zero (fun ω _ => ?_)
    rw [if_neg (fun hc => hne ⟨ω, hc⟩)]
  · -- general-chance node: excluded by `hng`.
    exact absurd hk (hng n)

/-- **Reach vanishes off the reachable tree.** A history that is not `IsReachable` has zero reach
probability under every strategy: Somewhere along it a step into a non-emitted event occurs, and
that zero factor annihilates the whole product (`reachProb_append` and the previous lemma). Stated
for an `ExtensiveGame` so `no_chanceGeneral` discharges the general-chance branch. -/
theorem ExtensiveGame.reachProb_eq_zero_of_not_isReachable (G : ExtensiveGame I E)
    (σ : G.toExtensiveForm.BehavioralStrategy) (h : List E)
    (hnr : ¬ G.toExtensiveForm.IsReachable h) :
    reachProb G.toExtensiveForm σ h = 0 := by
  -- Induction via `List.reverseRecOn`: `[]` is reachable (root), so the nil case is vacuous; for
  -- `pre ++ [e]`, either `pre` is unreachable (IH kills `reachProb pre`, factored out by
  -- `reachProb_append`), or `pre` is reachable but `e` is not emitted (else `pre ++ [e]` would be
  -- reachable by `IsReachable.step`), so the final `stepProb` factor is zero.
  induction h using List.reverseRecOn with
  | nil => exact absurd ExtensiveForm.IsReachable.root hnr
  | append_singleton pre e ih =>
    rw [reachProb_append G.toExtensiveForm σ pre [e],
      G.toExtensiveForm.finitePrefixProbFrom_cons σ pre e [],
      G.toExtensiveForm.finitePrefixProbFrom_nil σ (pre ++ [e]), mul_one]
    by_cases hpre : G.toExtensiveForm.IsReachable pre
    · -- `pre` reachable ⇒ `e` not emitted (else `pre ++ [e]` reachable), so the step factor is `0`.
      have hnemit : ¬ (G.toExtensiveForm.tree.nodeKind pre).emits e := fun he =>
        hnr (ExtensiveForm.IsReachable.step pre e hpre he)
      rw [ExtensiveForm.stepProb_eq_zero_of_not_emits G.toExtensiveForm σ pre e
        (fun n => G.no_chanceGeneral pre n) hnemit, mul_zero]
    · -- `pre` unreachable ⇒ `reachProb pre = 0` by IH, killing the product.
      rw [ih hpre, zero_mul]

/-- **Positive reach lies on the reachable tree.** The contrapositive of
`reachProb_eq_zero_of_not_isReachable`: A history with positive reach probability under any
strategy is `IsReachable`. This is the bridge that makes the type-level
`BeliefSystem.support_exhaustive` field subsume the strategy-relative reachability-completeness of
belief supports: Combined with `support_exhaustive`, it shows every positive-reach in-info-set
history is represented in the support, for every strategy. Stated for an `ExtensiveGame` so
`no_chanceGeneral` discharges the general-chance branch (where positive `stepProb` need not witness
`emits`). -/
theorem ExtensiveGame.reachProb_pos_imp_isReachable (G : ExtensiveGame I E)
    (σ : G.toExtensiveForm.BehavioralStrategy) (h : List E)
    (hpos : 0 < reachProb G.toExtensiveForm σ h) :
    G.toExtensiveForm.IsReachable h := by
  by_contra hnr
  rw [G.reachProb_eq_zero_of_not_isReachable σ h hnr] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **Unreachable support nodes carry zero belief.** Consuming Kreps–Wilson consistency: An
information-set support node `x` that is not `IsReachable` has zero reach under each totally-mixed
`σseq n` (`reachProb_eq_zero_of_not_isReachable`), so its Bayesian posterior `bayesBeliefAt` under
`σseq n` is identically zero, and the consistency limit `hbel` forces `μ.belief i obs x = 0`. This
lets the recursion silently drop unreachable support nodes, leaving only the `IsReachable` nodes
`consistency_belief_tower` / `reachInvariant` can consume. -/
theorem belief_eq_zero_of_not_isReachable (G : ExtensiveGame I E)
    (a : Assessment G.toExtensiveForm) (hcons : HasConsistentBeliefs G.toExtensiveForm a)
    (i : I) (obs : G.info.Obs i) (x : G.toExtensiveForm.InfoSet i obs)
    (hnr : ¬ G.toExtensiveForm.IsReachable x.1) :
    a.beliefs.belief i obs x = 0 := by
  classical
  obtain ⟨σseq, _hmix, _hstrategy, hbel⟩ := hcons
  -- The posterior under every `σseq n` is `0`: the reachProb numerator vanishes (unreachable node),
  -- so on the positive branch `reachProb / IP = 0`, and the other branches are `0` outright.
  have hzero : ∀ n, bayesBeliefAt G.toExtensiveForm (σseq n) a.beliefs i obs x.1 = 0 := by
    intro n
    unfold bayesBeliefAt
    rw [dif_pos x.2]
    split_ifs with _hmem _hpos
    · rw [G.reachProb_eq_zero_of_not_isReachable (σseq n) x.1 hnr, zero_div]
    · rfl
    · rfl
  -- `μ.prob i obs x.1 = lim bayesBeliefAt (σseq n) = lim 0 = 0`, and `prob_subtype` is `belief`.
  have hlim := hbel i obs x.1
  rw [a.beliefs.prob_subtype i obs x] at hlim
  simp only [hzero] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-- **Positive-belief support nodes have positive reach under the consistency sequence.** Consuming
Kreps–Wilson consistency: A support node `x` with strictly positive equilibrium belief
`μ.belief i obs x` is reached with positive probability under some totally-mixed `σseq n` of the
witnessing sequence. Otherwise its Bayesian posterior `bayesBeliefAt (σseq n)` would be `0` for
every `n`, forcing the consistency limit `μ.belief i obs x` to `0`, contradicting positivity. This
recovers (via `support_exhaustive`) every positive-belief node — including those reachable only
through a chance edge — inside the support of its information set, the frontier-coverage
recursion's anchor. -/
theorem reachProb_pos_of_belief_pos (G : ExtensiveGame I E)
    (a : Assessment G.toExtensiveForm)
    (σseq : ℕ → G.toExtensiveForm.BehavioralStrategy)
    (hlim : ∀ (i : I) (obs : G.info.Obs i) (h : List E),
      Filter.Tendsto (fun n => bayesBeliefAt G.toExtensiveForm (σseq n) a.beliefs i obs h)
        Filter.atTop (nhds (a.beliefs.prob i obs h)))
    (i : I) (obs : G.info.Obs i) (x : G.toExtensiveForm.InfoSet i obs)
    (hbel : 0 < a.beliefs.belief i obs x) :
    ∃ n, 0 < reachProb G.toExtensiveForm (σseq n) x.1 := by
  classical
  -- Suppose every `σseq n` zero-reaches `x`. Then each posterior is `0` (zero numerator), so the
  -- consistency limit `μ.belief i obs x = lim 0 = 0`, contradicting `hbel`.
  by_contra hcon
  push Not at hcon
  have hzero : ∀ n, bayesBeliefAt G.toExtensiveForm (σseq n) a.beliefs i obs x.1 = 0 := by
    intro n
    have hr0 : reachProb G.toExtensiveForm (σseq n) x.1 = 0 :=
      le_antisymm (hcon n) (reachProb_nonneg G.toExtensiveForm (σseq n) x.1)
    unfold bayesBeliefAt
    rw [dif_pos x.2]
    split_ifs with _hmem _hpos
    · rw [hr0, zero_div]
    · rfl
    · rfl
  have hlimx := hlim i obs x.1
  rw [a.beliefs.prob_subtype i obs x] at hlimx
  simp only [hzero] at hlimx
  have : a.beliefs.belief i obs x = 0 := tendsto_nhds_unique hlimx tendsto_const_nhds
  rw [this] at hbel
  exact lt_irrefl 0 hbel

/-! ### Interior Bellman event sum -/

/-- **Chance-node Bellman as an event sum.** The chance-finite analog of
`continuationValue_player_eventSum`: Regroup the per-outcome `dist`-weighted sum by emitted event,
each event class carrying the strategy-independent weight `stepProb σ y e`. -/
theorem ExtensiveGame.continuationValue_chanceFinite_eventSum (G : ExtensiveGame I E)
    (σ : G.toExtensiveForm.BehavioralStrategy) (y : List E) (i : I)
    {n : ChanceFiniteNode E} (hnk : G.toExtensiveForm.tree.nodeKind y = .chanceFinite n) :
    G.continuationValue σ y i =
      ∑ e ∈ Finset.univ.image n.emit,
        G.toExtensiveForm.stepProb σ y e *
          (G.stepPayoff y e i + G.discount * G.continuationValue σ (y ++ [e]) i) := by
  rw [G.continuationValue_eq σ y i]
  have hrw : nodeStepValue G.toExtensiveForm σ y i (G.toExtensiveForm.tree.nodeKind y) rfl
        (G.no_chanceGeneral y) G.stepPayoff G.discount G.continuationValue =
      nodeStepValue G.toExtensiveForm σ y i (.chanceFinite n) hnk (by simp)
        G.stepPayoff G.discount G.continuationValue := by congr 1
  rw [hrw, nodeStepValue_chanceFinite _ _ _ _ _ hnk,
    ExtensiveForm.sum_choice_eq_sum_tag (E := E) n.emit (fun ω => n.dist.pmf ω)
      (fun e => G.stepPayoff y e i + G.discount * G.continuationValue σ (y ++ [e]) i)]
  exact Finset.sum_congr rfl (fun e _ => by
    rw [ExtensiveForm.stepProb_of_chanceFinite G.toExtensiveForm σ hnk e])

/-- **Uniform interior Bellman event sum.** At a reachable non-terminal node (joint and
general-chance excluded by `hno_joint` / `G.no_chanceGeneral`), the continuation value is the
`stepProb`-weighted sum over `emitImage y` of the per-edge `(stepPayoff + δ·V(child))`. Unifies the
player and chance-finite event sums under the single index `emitImage y`. -/
theorem ExtensiveGame.continuationValue_eventSum (G : ExtensiveGame I E)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (σ : G.toExtensiveForm.BehavioralStrategy) (y : List E) (i : I)
    (hnt : ∀ p : I → ℝ, G.toExtensiveForm.tree.nodeKind y ≠ .terminal p) :
    G.continuationValue σ y i =
      ∑ e ∈ G.toExtensiveForm.emitImage y,
        G.toExtensiveForm.stepProb σ y e *
          (G.stepPayoff y e i + G.discount * G.continuationValue σ (y ++ [e]) i) := by
  unfold ExtensiveForm.emitImage
  rcases hk : G.toExtensiveForm.tree.nodeKind y with p | n | n | n | n
  · exact absurd hk (hnt p)
  · exact G.continuationValue_player_eventSum σ y i hk
  · exact absurd hk (hno_joint y n)
  · exact G.continuationValue_chanceFinite_eventSum σ y i hk
  · exact absurd hk (G.no_chanceGeneral y n)

/-! ### Totally-mixed reach domination -/

/-- **A totally-mixed strategy dominates the reach of any other strategy step-by-step.** At a
single history `h`, if some strategy `σ'` assigns positive step probability to an event `e`, then
so does a totally-mixed strategy `σmix`: At a player node every emitted event has positive mass
under total mixing (and `σ'`'s positive mass witnesses that `e` is emitted); at a chance-finite
node the step probability is strategy-independent; terminal / general-chance nodes assign `0` to
everything, contradicting the hypothesis. -/
theorem stepProb_pos_of_totallyMixed_of_pos (G : ExtensiveGame I E)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (σmix σ' : G.toExtensiveForm.BehavioralStrategy)
    (hmix : G.toExtensiveForm.IsTotallyMixed σmix)
    (h : List E) (e : E) (hpos : 0 < G.toExtensiveForm.stepProb σ' h e) :
    0 < G.toExtensiveForm.stepProb σmix h e := by
  rcases hk : G.toExtensiveForm.tree.nodeKind h with p | n | n | n | n
  · -- terminal: `stepProb = 0`, contradicting `hpos`.
    rw [G.toExtensiveForm.stepProb_of_terminal σ' hk e] at hpos; exact absurd hpos (lt_irrefl 0)
  · -- player node: positivity of `σ'`'s step witnesses `∃ c, emit c = e`, then total mixing.
    have hemit : ∃ c : n.Choice, n.emit c = e := by
      by_contra hcon
      have : ¬ (G.toExtensiveForm.tree.nodeKind h).emits e := by rw [hk]; exact hcon
      rw [G.toExtensiveForm.stepProb_eq_zero_of_not_emits σ' h e
        (fun ng => G.no_chanceGeneral h ng) this] at hpos
      exact absurd hpos (lt_irrefl 0)
    exact stepProb_pos_of_totallyMixed G.toExtensiveForm σmix hmix hk hemit
  · -- joint node: excluded by `hno_joint`.
    exact absurd hk (hno_joint h n)
  · -- chance-finite node: step probability is strategy-independent.
    rw [G.toExtensiveForm.stepProb_of_chanceFinite σmix hk e,
      ← G.toExtensiveForm.stepProb_of_chanceFinite σ' hk e]
    exact hpos
  · -- general-chance node: excluded.
    exact absurd hk (G.no_chanceGeneral h n)

/-! ### The deviated consistency sequence and the chain tower -/

/-- **A totally-mixed strategy dominates the whole-path reach of any other strategy.** If `σ'`
reaches `z` with positive probability, then so does a totally-mixed `σmix`: Factor the reach along
the path with `reachProb_append` and dominate the final step with
`stepProb_pos_of_totallyMixed_of_pos`, inducting on the prefix. -/
theorem reachProb_pos_of_totallyMixed_of_pos (G : ExtensiveGame I E)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (σmix σ' : G.toExtensiveForm.BehavioralStrategy)
    (hmix : G.toExtensiveForm.IsTotallyMixed σmix)
    {z : List E} (hpos : 0 < reachProb G.toExtensiveForm σ' z) :
    0 < reachProb G.toExtensiveForm σmix z := by
  induction z using List.reverseRecOn with
  | nil =>
    -- `reachProb · [] = 1 > 0`.
    simp only [reachProb, ExtensiveForm.finitePrefixProb,
      ExtensiveForm.finitePrefixProbFrom_nil]
    exact one_pos
  | append_singleton pre e ih =>
    -- Factor the last step on both strategies; positivity is preserved factorwise.
    rw [reachProb_append G.toExtensiveForm σ' pre [e],
      G.toExtensiveForm.finitePrefixProbFrom_cons σ' pre e [],
      G.toExtensiveForm.finitePrefixProbFrom_nil σ' (pre ++ [e]), mul_one] at hpos
    rw [reachProb_append G.toExtensiveForm σmix pre [e],
      G.toExtensiveForm.finitePrefixProbFrom_cons σmix pre e [],
      G.toExtensiveForm.finitePrefixProbFrom_nil σmix (pre ++ [e]), mul_one]
    -- Both factors are positive: the prefix by IH, the step by the step-domination lemma.
    have hpre : 0 < reachProb G.toExtensiveForm σ' pre := by
      by_contra hle
      push Not at hle
      have : reachProb G.toExtensiveForm σ' pre = 0 :=
        le_antisymm hle (reachProb_nonneg G.toExtensiveForm σ' pre)
      rw [this, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
    have hstep : 0 < G.toExtensiveForm.stepProb σ' pre e := by
      by_contra hle
      push Not at hle
      have : G.toExtensiveForm.stepProb σ' pre e = 0 :=
        le_antisymm hle (G.toExtensiveForm.stepProb_nonneg σ' pre e)
      rw [this, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    exact mul_pos (ih hpre)
      (stepProb_pos_of_totallyMixed_of_pos G hno_joint σmix σ' hmix pre e hstep)

open Classical in
/-- The deviated consistency sequence: `σ'` at every coordinate of player `i`, `σseq n` at every
other coordinate. It is a unilateral `i`-deviation of `σseq n` (`deviatedSeq_unilateralDeviation`),
and its step probabilities converge to those of `σ'` whenever `σseq n → σ` and `σ'` is a unilateral
`i`-deviation of `σ` (`stepProb_deviatedSeq_tendsto`). -/
noncomputable def deviatedSeq (G : ExtensiveForm I E) (i : I) (σ' : G.BehavioralStrategy)
    (σseq : ℕ → G.BehavioralStrategy) (n : ℕ) : G.BehavioralStrategy :=
  fun j obs => if j = i then σ' j obs else σseq n j obs

omit [DecidableEq E] in
/-- The deviated sequence is a unilateral `i`-deviation of `σseq n`. -/
theorem deviatedSeq_unilateralDeviation (G : ExtensiveForm I E) (i : I)
    (σ' : G.BehavioralStrategy) (σseq : ℕ → G.BehavioralStrategy) (n : ℕ) :
    G.unilateralDeviation i (σseq n) (deviatedSeq G i σ' σseq n) := by
  intro j obs hji
  simp only [deviatedSeq, if_neg hji]

/-- At a history where `i` moves (a player node — joint nodes excluded), the deviated sequence's
step probabilities read `σ'` exactly: The node's unique mover is `i`, where `deviatedSeq` copies
`σ'`. -/
theorem stepProb_deviatedSeq_eq_of_movesAt (G : ExtensiveForm I E)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.tree.nodeKind h ≠ .joint n)
    (i : I) (σ' : G.BehavioralStrategy) (σseq : ℕ → G.BehavioralStrategy) (n : ℕ)
    {h : List E} (hi : (G.tree.nodeKind h).movesAt i) (e : E) :
    G.stepProb (deviatedSeq G i σ' σseq n) h e = G.stepProb σ' h e := by
  rcases hk : G.tree.nodeKind h with p | n_p | n_j | n_c | n_g
  · rw [hk] at hi; exact absurd hi id
  · have hmover : n_p.mover = i := by rw [hk] at hi; exact hi
    refine stepProb_congr_movers G _ σ' h e (fun j hj => ?_)
    have hji : j = i := by rw [hk] at hj; rw [← hj]; exact hmover
    subst hji
    simp only [deviatedSeq, if_true]
  · exact absurd hk (hno_joint h n_j)
  · rw [hk] at hi; exact absurd hi id
  · rw [hk] at hi; exact absurd hi id

/-- At a history where `i` does not move, the deviated sequence's step probabilities read `σseq n`
exactly: Every mover is some `j ≠ i`, where `deviatedSeq` copies `σseq n`. -/
theorem stepProb_deviatedSeq_eq_of_not_movesAt (G : ExtensiveForm I E)
    (i : I) (σ' : G.BehavioralStrategy) (σseq : ℕ → G.BehavioralStrategy) (n : ℕ)
    {h : List E} (hi : ¬ (G.tree.nodeKind h).movesAt i) (e : E) :
    G.stepProb (deviatedSeq G i σ' σseq n) h e = G.stepProb (σseq n) h e := by
  refine stepProb_congr_movers G _ _ h e (fun j hj => ?_)
  have hji : j ≠ i := fun h0 => hi (h0 ▸ hj)
  simp only [deviatedSeq, if_neg hji]

/-- **Step probabilities of the deviated sequence converge to those of `σ'`.** At an `i`-mover the
sequence is constantly `σ'`; elsewhere it is `σseq n → σ = σ'` (the deviation is unilateral). The
limit step extracted from `consistency_belief_tower`. -/
theorem stepProb_deviatedSeq_tendsto (G : ExtensiveForm I E)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.tree.nodeKind h ≠ .joint n)
    (i : I) (σ σ' : G.BehavioralStrategy) (hdev : G.unilateralDeviation i σ σ')
    (σseq : ℕ → G.BehavioralStrategy)
    (hstep : ∀ (h : List E) (e : E),
      Filter.Tendsto (fun n => G.stepProb (σseq n) h e) Filter.atTop
        (nhds (G.stepProb σ h e))) :
    ∀ (h : List E) (e : E),
      Filter.Tendsto (fun n => G.stepProb (deviatedSeq G i σ' σseq n) h e) Filter.atTop
        (nhds (G.stepProb σ' h e)) := by
  intro h e
  by_cases hi : (G.tree.nodeKind h).movesAt i
  · -- Constantly `σ'` at `i`-movers.
    simp only [fun n => stepProb_deviatedSeq_eq_of_movesAt G hno_joint i σ' σseq n hi e]
    exact tendsto_const_nhds
  · -- Off `i`: the sequence reads `σseq n → σ`, and `σ'` reads `σ`.
    have hσ'σ : G.stepProb σ' h e = G.stepProb σ h e := by
      refine stepProb_congr_movers G σ' σ h e (fun j hj => ?_)
      exact hdev j (G.info.observe j h) (fun h0 => hi (h0 ▸ hj))
    simp only [fun n => stepProb_deviatedSeq_eq_of_not_movesAt G i σ' σseq n hi e, hσ'σ]
    exact hstep h e

/-- **The chain belief tower (cross-information-set weight transport).** For two support nodes
`w, w'` of a deeper information set `(i, ω'')` whose last `i`-stops `x, x'` lie in the support of
an upstream information set `(i, obs)` (`x = w.take |x|` an `i`-mover, with no `i`-mover strictly
between), the weight the backward induction accumulates at the deeper support — the upstream belief
times the `σ'`-transition probability from the stop — is cross-proportional to the deeper set's own
equilibrium beliefs:

`μ(x) · P_{σ'}(x → w) · μ''(w') = μ(x') · P_{σ'}(x' → w') · μ''(w)`.

Last-stop alignment makes the two paths take the same action at their stops, so the identity holds
along the deviated sequence and passes to the equilibrium beliefs with no positivity of any reach
required. -/
theorem chain_belief_tower (G : ExtensiveGame I E)
    (hpr : G.toExtensiveForm.IsReachCoherent)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (hsa : G.toExtensiveForm.LastStopAlign)
    (a : Assessment G.toExtensiveForm) (hcons : HasConsistentBeliefs G.toExtensiveForm a)
    (i : I) (obs ω'' : G.info.Obs i)
    (σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i a.strategy σ')
    (x x' : G.toExtensiveForm.InfoSet i obs)
    (hx : x ∈ a.beliefs.support i obs) (hx' : x' ∈ a.beliefs.support i obs)
    (w w' : G.toExtensiveForm.InfoSet i ω'')
    (hw : w ∈ a.beliefs.support i ω'') (hw' : w' ∈ a.beliefs.support i ω'')
    (hwr : G.toExtensiveForm.IsReachable w.1) (hw'r : G.toExtensiveForm.IsReachable w'.1)
    (hxw : w.1.take x.1.length = x.1) (hlt : x.1.length < w.1.length)
    (hbet : ∀ r : ℕ, x.1.length < r → r < w.1.length →
      ¬ (G.toExtensiveForm.tree.nodeKind (w.1.take r)).movesAt i)
    (hx'w' : w'.1.take x'.1.length = x'.1) (hlt' : x'.1.length < w'.1.length)
    (hbet' : ∀ r : ℕ, x'.1.length < r → r < w'.1.length →
      ¬ (G.toExtensiveForm.tree.nodeKind (w'.1.take r)).movesAt i) :
    a.beliefs.belief i obs x *
        G.toExtensiveForm.finitePrefixProbFrom σ' x.1 (w.1.drop x.1.length) *
        a.beliefs.belief i ω'' w' =
      a.beliefs.belief i obs x' *
        G.toExtensiveForm.finitePrefixProbFrom σ' x'.1 (w'.1.drop x'.1.length) *
        a.beliefs.belief i ω'' w := by
  classical
  obtain ⟨σseq, _hmix, hstrategy, hbel⟩ := hcons
  have hstep := hstrategy.stepProb
  set μ := a.beliefs with hμ
  -- The head edges out of the stops: `w` continues from `x` with `e₁`, `w'` from `x'` with `e₂`.
  obtain ⟨e₁, hxe⟩ : ∃ e, w.1.take (x.1.length + 1) = x.1 ++ [e] := by
    refine ⟨w.1[x.1.length], ?_⟩
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, hxw]
    rfl
  obtain ⟨e₂, hxe'⟩ : ∃ e, w'.1.take (x'.1.length + 1) = x'.1 ++ [e] := by
    refine ⟨w'.1[x'.1.length], ?_⟩
    rw [List.take_add_one, List.getElem?_eq_getElem hlt', hx'w']
    rfl
  -- Reach factors through the stop, and the transition splits off its head step.
  have hreach_split : ∀ ρ : G.toExtensiveForm.BehavioralStrategy,
      reachProb G.toExtensiveForm ρ w.1 =
        reachProb G.toExtensiveForm ρ x.1 *
          G.toExtensiveForm.finitePrefixProbFrom ρ x.1 (w.1.drop x.1.length) := by
    intro ρ
    conv_lhs => rw [← List.take_append_drop x.1.length w.1, hxw]
    exact reachProb_append G.toExtensiveForm ρ x.1 (w.1.drop x.1.length)
  have hreach_split' : ∀ ρ : G.toExtensiveForm.BehavioralStrategy,
      reachProb G.toExtensiveForm ρ w'.1 =
        reachProb G.toExtensiveForm ρ x'.1 *
          G.toExtensiveForm.finitePrefixProbFrom ρ x'.1 (w'.1.drop x'.1.length) := by
    intro ρ
    conv_lhs => rw [← List.take_append_drop x'.1.length w'.1, hx'w']
    exact reachProb_append G.toExtensiveForm ρ x'.1 (w'.1.drop x'.1.length)
  have hdrop_cons : w.1.drop x.1.length = e₁ :: w.1.drop (x.1.length + 1) := by
    rw [List.drop_eq_getElem_cons hlt]
    congr 1
    have := hxe
    rw [List.take_add_one, List.getElem?_eq_getElem hlt, hxw] at this
    simpa using List.append_inj_right this rfl
  have hdrop_cons' : w'.1.drop x'.1.length = e₂ :: w'.1.drop (x'.1.length + 1) := by
    rw [List.drop_eq_getElem_cons hlt']
    congr 1
    have := hxe'
    rw [List.take_add_one, List.getElem?_eq_getElem hlt', hx'w'] at this
    simpa using List.append_inj_right this rfl
  have hdecompP : ∀ ρ : G.toExtensiveForm.BehavioralStrategy,
      G.toExtensiveForm.finitePrefixProbFrom ρ x.1 (w.1.drop x.1.length) =
        G.toExtensiveForm.stepProb ρ x.1 e₁ *
          G.toExtensiveForm.finitePrefixProbFrom ρ (x.1 ++ [e₁]) (w.1.drop (x.1.length + 1)) := by
    intro ρ
    rw [hdrop_cons]
    exact G.toExtensiveForm.finitePrefixProbFrom_cons ρ x.1 e₁ _
  have hdecompP' : ∀ ρ : G.toExtensiveForm.BehavioralStrategy,
      G.toExtensiveForm.finitePrefixProbFrom ρ x'.1 (w'.1.drop x'.1.length) =
        G.toExtensiveForm.stepProb ρ x'.1 e₂ *
          G.toExtensiveForm.finitePrefixProbFrom ρ (x'.1 ++ [e₂])
            (w'.1.drop (x'.1.length + 1)) := by
    intro ρ
    rw [hdrop_cons']
    exact G.toExtensiveForm.finitePrefixProbFrom_cons ρ x'.1 e₂ _
  -- Along the `i`-free segment below the stop, the deviated sequence reads `σseq n`.
  have hseg : ∀ n : ℕ,
      G.toExtensiveForm.finitePrefixProbFrom (deviatedSeq G.toExtensiveForm i σ' σseq n)
          (x.1 ++ [e₁]) (w.1.drop (x.1.length + 1)) =
        G.toExtensiveForm.finitePrefixProbFrom (σseq n) (x.1 ++ [e₁])
          (w.1.drop (x.1.length + 1)) := by
    intro n
    refine G.toExtensiveForm.finitePrefixProbFrom_congr _ _ _ _ (fun pre hpre hne e => ?_)
    have hlen_pre : pre.length < (w.1.drop (x.1.length + 1)).length :=
      lt_of_le_of_ne hpre.length_le (fun hl => hne (List.IsPrefix.eq_of_length hpre hl))
    have hdl : (w.1.drop (x.1.length + 1)).length = w.1.length - (x.1.length + 1) :=
      List.length_drop
    have hnode : (x.1 ++ [e₁]) ++ pre = w.1.take (x.1.length + 1 + pre.length) := by
      have hpre_take : pre = (w.1.drop (x.1.length + 1)).take pre.length :=
        List.prefix_iff_eq_take.mp hpre
      rw [List.take_add, ← hxe, ← hpre_take]
    have hmov : ¬ (G.toExtensiveForm.tree.nodeKind ((x.1 ++ [e₁]) ++ pre)).movesAt i := by
      rw [hnode]
      exact hbet _ (by omega) (by omega)
    exact stepProb_deviatedSeq_eq_of_not_movesAt G.toExtensiveForm i σ' σseq n hmov e
  have hseg' : ∀ n : ℕ,
      G.toExtensiveForm.finitePrefixProbFrom (deviatedSeq G.toExtensiveForm i σ' σseq n)
          (x'.1 ++ [e₂]) (w'.1.drop (x'.1.length + 1)) =
        G.toExtensiveForm.finitePrefixProbFrom (σseq n) (x'.1 ++ [e₂])
          (w'.1.drop (x'.1.length + 1)) := by
    intro n
    refine G.toExtensiveForm.finitePrefixProbFrom_congr _ _ _ _ (fun pre hpre hne e => ?_)
    have hlen_pre : pre.length < (w'.1.drop (x'.1.length + 1)).length :=
      lt_of_le_of_ne hpre.length_le (fun hl => hne (List.IsPrefix.eq_of_length hpre hl))
    have hdl : (w'.1.drop (x'.1.length + 1)).length = w'.1.length - (x'.1.length + 1) :=
      List.length_drop
    have hnode : (x'.1 ++ [e₂]) ++ pre = w'.1.take (x'.1.length + 1 + pre.length) := by
      have hpre_take : pre = (w'.1.drop (x'.1.length + 1)).take pre.length :=
        List.prefix_iff_eq_take.mp hpre
      rw [List.take_add, ← hxe', ← hpre_take]
    have hmov : ¬ (G.toExtensiveForm.tree.nodeKind ((x'.1 ++ [e₂]) ++ pre)).movesAt i := by
      rw [hnode]
      exact hbet' _ (by omega) (by omega)
    exact stepProb_deviatedSeq_eq_of_not_movesAt G.toExtensiveForm i σ' σseq n hmov e
  -- At the stops the deviated sequence reads `σ'`.
  have hhead : ∀ n : ℕ,
      G.toExtensiveForm.stepProb (deviatedSeq G.toExtensiveForm i σ' σseq n) x.1 e₁ =
        G.toExtensiveForm.stepProb σ' x.1 e₁ :=
    fun n => stepProb_deviatedSeq_eq_of_movesAt G.toExtensiveForm hno_joint i σ' σseq n x.2.1 e₁
  have hhead' : ∀ n : ℕ,
      G.toExtensiveForm.stepProb (deviatedSeq G.toExtensiveForm i σ' σseq n) x'.1 e₂ =
        G.toExtensiveForm.stepProb σ' x'.1 e₂ :=
    fun n => stepProb_deviatedSeq_eq_of_movesAt G.toExtensiveForm hno_joint i σ' σseq n x'.2.1 e₂
  -- **Last-stop alignment**: the two paths take the same action at their stops, under every
  -- strategy. `hsa` produces an aligned stop of `w'`; `noRevisit` forces it to `x'`.
  have hS : ∀ ρ : G.toExtensiveForm.BehavioralStrategy,
      G.toExtensiveForm.stepProb ρ x.1 e₁ = G.toExtensiveForm.stepProb ρ x'.1 e₂ := by
    have hmov_take : (G.toExtensiveForm.tree.nodeKind (w.1.take x.1.length)).movesAt i := by
      rw [hxw]; exact x.2.1
    obtain ⟨m'', hm''lt, hm''mov, hm''obs, hm''bet, hm''step⟩ :=
      hsa i w.1 w'.1 hwr hw'r w.2.1 w'.2.1 (w.2.2.trans w'.2.2.symm) x.1.length hlt
        hmov_take hbet
    -- The aligned stop `q = w'.take m''` is a reachable `i`-mover observing `obs`.
    have hq_reach : G.toExtensiveForm.IsReachable (w'.1.take m'') :=
      ExtensiveForm.IsReachable.take G.toExtensiveForm hw'r m''
    have hx'_reach : G.toExtensiveForm.IsReachable x'.1 := by
      rw [← hx'w']
      exact ExtensiveForm.IsReachable.take G.toExtensiveForm hw'r x'.1.length
    have hq_obs : G.info.observe i (w'.1.take m'') = obs := by
      rw [hm''obs, hxw]
      exact x.2.2
    -- `q` and `x'` are comparable prefixes of `w'`, both `i`-movers at `obs`: `noRevisit` ⟹ equal.
    have hqx' : w'.1.take m'' = x'.1 := by
      rcases Nat.le_total m'' x'.1.length with hle | hle
      · have htt : w'.1.take m'' = (w'.1.take x'.1.length).take m'' := by
          rw [List.take_take, min_eq_left hle]
        have hq_pre : w'.1.take m'' <+: x'.1 := by
          rw [htt, hx'w']
          exact List.take_prefix _ _
        exact hpr.noRevisit i (w'.1.take m'') x'.1 hq_reach hx'_reach hq_pre
          (hq_obs.trans x'.2.2.symm) hm''mov x'.2.1
      · have htt : x'.1 = (w'.1.take m'').take x'.1.length := by
          rw [List.take_take, min_eq_left hle, hx'w']
        have hx'_pre : x'.1 <+: w'.1.take m'' := by
          rw [htt]
          exact List.take_prefix _ _
        exact (hpr.noRevisit i x'.1 (w'.1.take m'') hx'_reach hq_reach hx'_pre
          (x'.2.2.trans hq_obs.symm) x'.2.1 hm''mov).symm
    have hm''eq : m'' = x'.1.length := by
      have hlen := congrArg List.length hqx'
      rwa [List.length_take, min_eq_left hm''lt.le] at hlen
    intro ρ
    have hstep_eq := hm''step e₁ e₂ (by rw [hxw]; exact hxe)
      (by rw [hm''eq, hx'w']; exact hxe') ρ
    rwa [hxw, hqx'] at hstep_eq
  -- **The per-`n` exact identity** along the deviated sequence.
  have hpern : ∀ n : ℕ,
      bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs x.1 *
          G.toExtensiveForm.finitePrefixProbFrom (deviatedSeq G.toExtensiveForm i σ' σseq n) x.1
            (w.1.drop x.1.length) *
          bayesBeliefAt G.toExtensiveForm (σseq n) μ i ω'' w'.1 =
        bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs x'.1 *
          G.toExtensiveForm.finitePrefixProbFrom (deviatedSeq G.toExtensiveForm i σ' σseq n) x'.1
            (w'.1.drop x'.1.length) *
          bayesBeliefAt G.toExtensiveForm (σseq n) μ i ω'' w.1 := by
    intro n
    by_cases hIPo : 0 < infoSetProb G.toExtensiveForm (σseq n) μ i obs
    · by_cases hIPd : 0 < infoSetProb G.toExtensiveForm (σseq n) μ i ω''
      · -- Both information sets carry `σseq n`-mass: unfold the four posteriors to `reach / IP`.
        have hBx : bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs x.1 =
            reachProb G.toExtensiveForm (σseq n) x.1 /
              infoSetProb G.toExtensiveForm (σseq n) μ i obs := by
          unfold bayesBeliefAt; rw [dif_pos x.2, if_pos (by simpa using hx), dif_pos hIPo]
        have hBx' : bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs x'.1 =
            reachProb G.toExtensiveForm (σseq n) x'.1 /
              infoSetProb G.toExtensiveForm (σseq n) μ i obs := by
          unfold bayesBeliefAt; rw [dif_pos x'.2, if_pos (by simpa using hx'), dif_pos hIPo]
        have hBw : bayesBeliefAt G.toExtensiveForm (σseq n) μ i ω'' w.1 =
            reachProb G.toExtensiveForm (σseq n) w.1 /
              infoSetProb G.toExtensiveForm (σseq n) μ i ω'' := by
          unfold bayesBeliefAt; rw [dif_pos w.2, if_pos (by simpa using hw), dif_pos hIPd]
        have hBw' : bayesBeliefAt G.toExtensiveForm (σseq n) μ i ω'' w'.1 =
            reachProb G.toExtensiveForm (σseq n) w'.1 /
              infoSetProb G.toExtensiveForm (σseq n) μ i ω'' := by
          unfold bayesBeliefAt; rw [dif_pos w'.2, if_pos (by simpa using hw'), dif_pos hIPd]
        rw [hBx, hBx', hBw, hBw']
        -- Cross numerator identity: expand reach through the stop, split heads, cancel by `hS`.
        have hnum : reachProb G.toExtensiveForm (σseq n) x.1 *
              G.toExtensiveForm.finitePrefixProbFrom (deviatedSeq G.toExtensiveForm i σ' σseq n)
                x.1 (w.1.drop x.1.length) *
              reachProb G.toExtensiveForm (σseq n) w'.1 =
            reachProb G.toExtensiveForm (σseq n) x'.1 *
              G.toExtensiveForm.finitePrefixProbFrom (deviatedSeq G.toExtensiveForm i σ' σseq n)
                x'.1 (w'.1.drop x'.1.length) *
              reachProb G.toExtensiveForm (σseq n) w.1 := by
          rw [hreach_split (σseq n), hreach_split' (σseq n)]
          rw [hdecompP (deviatedSeq G.toExtensiveForm i σ' σseq n),
            hdecompP' (deviatedSeq G.toExtensiveForm i σ' σseq n)]
          rw [hdecompP (σseq n), hdecompP' (σseq n)]
          rw [hseg n, hseg' n, hhead n, hhead' n, hS σ', hS (σseq n)]
          ring
        have hIPo0 : infoSetProb G.toExtensiveForm (σseq n) μ i obs ≠ 0 := ne_of_gt hIPo
        have hIPd0 : infoSetProb G.toExtensiveForm (σseq n) μ i ω'' ≠ 0 := ne_of_gt hIPd
        field_simp
        linear_combination hnum
      · -- The deeper set carries no `σseq n`-mass: both posteriors there are `0`.
        have hz : ∀ z : G.toExtensiveForm.InfoSet i ω'',
            bayesBeliefAt G.toExtensiveForm (σseq n) μ i ω'' z.1 = 0 := by
          intro z; unfold bayesBeliefAt
          rw [dif_pos z.2]
          split_ifs <;> rfl
        rw [hz w, hz w', mul_zero, mul_zero]
    · -- The upstream set carries no `σseq n`-mass: both posteriors there are `0`.
      have hz : ∀ z : G.toExtensiveForm.InfoSet i obs,
          bayesBeliefAt G.toExtensiveForm (σseq n) μ i obs z.1 = 0 := by
        intro z; unfold bayesBeliefAt
        rw [dif_pos z.2]
        split_ifs <;> rfl
      rw [hz x, hz x', zero_mul, zero_mul, zero_mul, zero_mul]
  -- Take limits: Bayes factors → equilibrium beliefs, deviated transition → `σ'`-transition.
  have hτstep := stepProb_deviatedSeq_tendsto G.toExtensiveForm hno_joint i a.strategy σ' hdev
    σseq hstep
  have hB : ∀ (ob : G.info.Obs i) (z : G.toExtensiveForm.InfoSet i ob),
      Filter.Tendsto (fun n => bayesBeliefAt G.toExtensiveForm (σseq n) μ i ob z.1)
        Filter.atTop (nhds (μ.belief i ob z)) := by
    intro ob z
    have h := hbel i ob z.1
    rwa [μ.prob_subtype i ob z] at h
  have hP_lim : Filter.Tendsto
      (fun n => G.toExtensiveForm.finitePrefixProbFrom (deviatedSeq G.toExtensiveForm i σ' σseq n)
        x.1 (w.1.drop x.1.length)) Filter.atTop
      (nhds (G.toExtensiveForm.finitePrefixProbFrom σ' x.1 (w.1.drop x.1.length))) :=
    finitePrefixProbFrom_tendsto G.toExtensiveForm _ σ' hτstep x.1 (w.1.drop x.1.length)
  have hP_lim' : Filter.Tendsto
      (fun n => G.toExtensiveForm.finitePrefixProbFrom (deviatedSeq G.toExtensiveForm i σ' σseq n)
        x'.1 (w'.1.drop x'.1.length)) Filter.atTop
      (nhds (G.toExtensiveForm.finitePrefixProbFrom σ' x'.1 (w'.1.drop x'.1.length))) :=
    finitePrefixProbFrom_tendsto G.toExtensiveForm _ σ' hτstep x'.1 (w'.1.drop x'.1.length)
  exact tendsto_nhds_unique
    (Filter.Tendsto.congr hpern (((hB obs x).mul hP_lim).mul (hB ω'' w')))
    (((hB obs x').mul hP_lim').mul (hB ω'' w))

omit [DecidableEq E] in
/-- **Reachability-relative locality of `continuationValue`.** If two strategies agree at every
reachable history extending a reachable `h` (for every player, at the observation that history
induces), they induce the same continuation value at `h`. Unlike `continuationValue_congr`, the
agreement need hold only on reachable continuations: The Bellman recursion only ever steps into
emitted children (`continuationValue_eventSum`), which stay reachable
(`isReachable_concat_of_mem_emitImage`), so unreachable off-path histories are never consulted. -/
theorem ExtensiveGame.continuationValue_congr_reachable (G : ExtensiveGame I E) {N : ℕ}
    (hfd : G.toExtensiveForm.FiniteDepth N)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (σ τ : G.toExtensiveForm.BehavioralStrategy) (h : List E) (i : I)
    (hhr : G.toExtensiveForm.IsReachable h)
    (hagree : ∀ (g : List E), h <+: g → G.toExtensiveForm.IsReachable g →
      ∀ j : I, (G.tree.nodeKind g).movesAt j →
        σ j (G.info.observe j g) = τ j (G.info.observe j g)) :
    G.continuationValue σ h i = G.continuationValue τ h i := by
  classical
  -- Strong induction on the depth budget `k ≥ N − h.length`, generalizing the (reachable) history.
  suffices haux : ∀ (k : ℕ) (h' : List E), N - h'.length ≤ k → G.toExtensiveForm.IsReachable h' →
      (∀ (g : List E), h' <+: g → G.toExtensiveForm.IsReachable g →
        ∀ j : I, (G.tree.nodeKind g).movesAt j →
          σ j (G.info.observe j g) = τ j (G.info.observe j g)) →
      G.continuationValue σ h' i = G.continuationValue τ h' i from
    haux (N - h.length) h le_rfl hhr hagree
  intro k
  induction k with
  | zero =>
    intro h' hk _hr _hag
    have hge : N ≤ h'.length := by omega
    obtain ⟨p, hp⟩ := hfd h' hge
    rw [G.continuationValue_eq σ h' i, G.continuationValue_eq τ h' i]
    simp only [hp, nodeStepValue_terminal]
  | succ k ih =>
    intro h' _hk hr' hag
    -- Terminal vs non-terminal at `h'`.
    by_cases hterm : ∃ p : I → ℝ, G.toExtensiveForm.tree.nodeKind h' = .terminal p
    · obtain ⟨p, hp⟩ := hterm
      rw [G.continuationValue_eq σ h' i, G.continuationValue_eq τ h' i]
      simp only [hp, nodeStepValue_terminal]
    · push Not at hterm
      -- Peel via the uniform interior event sum; agree at `h'` and recurse into emitted children.
      rw [G.continuationValue_eventSum hno_joint σ h' i hterm,
        G.continuationValue_eventSum hno_joint τ h' i hterm]
      have hag_h' : ∀ j : I, (G.tree.nodeKind h').movesAt j →
          σ j (G.info.observe j h') = τ j (G.info.observe j h') :=
        hag h' (List.prefix_refl h') hr'
      refine Finset.sum_congr rfl (fun e he => ?_)
      have hchild : G.toExtensiveForm.IsReachable (h' ++ [e]) :=
        G.toExtensiveForm.isReachable_concat_of_mem_emitImage hr' he
      -- The head step weight agrees (`stepProb_congr_movers` from `hag_h'`); recurse on the child.
      have hstep : G.toExtensiveForm.stepProb σ h' e = G.toExtensiveForm.stepProb τ h' e :=
        stepProb_congr_movers G.toExtensiveForm σ τ h' e hag_h'
      have hcv : G.continuationValue σ (h' ++ [e]) i = G.continuationValue τ (h' ++ [e]) i :=
        ih (h' ++ [e]) (by simp only [List.length_append, List.length_singleton]; omega) hchild
          (fun g hg hgr j hjm => hag g ((List.prefix_append h' [e]).trans hg) hgr j hjm)
      rw [hstep, hcv]

/-! ### Aliveness glue: Supports, beliefs, and the consistency witness -/

/-- **Belief-carrying nodes are alive**: A support node with nonzero equilibrium belief has
positive reach under some element of the consistency witness — otherwise its totally-mixed
posteriors vanish identically and so does the limit belief. -/
theorem exists_seq_reach_pos_of_belief_ne_zero (G : ExtensiveGame I E)
    (a : Assessment G.toExtensiveForm) (σseq : ℕ → G.toExtensiveForm.BehavioralStrategy)
    (hbel : ∀ (j : I) (ob : G.info.Obs j) (h : List E),
      Filter.Tendsto (fun n => bayesBeliefAt G.toExtensiveForm (σseq n) a.beliefs j ob h)
        Filter.atTop (nhds (a.beliefs.prob j ob h)))
    (i : I) (obs : G.info.Obs i) (y : G.toExtensiveForm.InfoSet i obs)
    (hyμ : a.beliefs.belief i obs y ≠ 0) :
    ∃ n, 0 < reachProb G.toExtensiveForm (σseq n) y.1 := by
  by_contra hnone
  push Not at hnone
  have hzero : ∀ n, reachProb G.toExtensiveForm (σseq n) y.1 = 0 := fun n =>
    le_antisymm (hnone n) (reachProb_nonneg G.toExtensiveForm (σseq n) y.1)
  have hB0 : ∀ n, bayesBeliefAt G.toExtensiveForm (σseq n) a.beliefs i obs y.1 = 0 := by
    intro n
    unfold bayesBeliefAt
    rw [dif_pos y.2]
    split_ifs
    · rw [hzero n, zero_div]
    · rfl
    · rfl
  have hlim : Filter.Tendsto (fun n => bayesBeliefAt G.toExtensiveForm (σseq n) a.beliefs i obs y.1)
      Filter.atTop (nhds (a.beliefs.belief i obs y)) := by
    have h := hbel i obs y.1
    rwa [a.beliefs.prob_subtype i obs y] at h
  have hlim0 : Filter.Tendsto
      (fun n => bayesBeliefAt G.toExtensiveForm (σseq n) a.beliefs i obs y.1)
      Filter.atTop (nhds (0 : ℝ)) := by
    simpa only [hB0] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
  exact hyμ (tendsto_nhds_unique hlim hlim0)

/-- **Total mixing dominates transition positivity**: A `σ'`-positive finite-prefix transition is
positive under any totally-mixed strategy (stepwise `stepProb_pos_of_totallyMixed_of_pos`). -/
theorem finitePrefixProbFrom_pos_of_totallyMixed_of_pos (G : ExtensiveGame I E)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (σmix σ' : G.toExtensiveForm.BehavioralStrategy)
    (hmix : G.toExtensiveForm.IsTotallyMixed σmix) (start suf : List E)
    (hpos : 0 < G.toExtensiveForm.finitePrefixProbFrom σ' start suf) :
    0 < G.toExtensiveForm.finitePrefixProbFrom σmix start suf := by
  induction suf generalizing start with
  | nil =>
    rw [G.toExtensiveForm.finitePrefixProbFrom_nil]
    exact one_pos
  | cons e rest ih =>
    rw [G.toExtensiveForm.finitePrefixProbFrom_cons] at hpos ⊢
    have hstep_pos : 0 < G.toExtensiveForm.stepProb σ' start e := by
      by_contra hle
      push Not at hle
      have h0 : G.toExtensiveForm.stepProb σ' start e = 0 :=
        le_antisymm hle (G.toExtensiveForm.stepProb_nonneg σ' start e)
      rw [h0, zero_mul] at hpos
      exact absurd hpos (lt_irrefl 0)
    have hrest_pos : 0 < G.toExtensiveForm.finitePrefixProbFrom σ' (start ++ [e]) rest := by
      by_contra hle
      push Not at hle
      have h0 : G.toExtensiveForm.finitePrefixProbFrom σ' (start ++ [e]) rest = 0 :=
        le_antisymm hle (G.toExtensiveForm.finitePrefixProbFrom_nonneg σ' (start ++ [e]) rest)
      rw [h0, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    exact mul_pos
      (stepProb_pos_of_totallyMixed_of_pos G hno_joint σmix σ' hmix start e hstep_pos)
      (ih (start ++ [e]) hrest_pos)

/-- **Alive stops are supported**: An `i`-mover `w` reached from an alive node `x` through a
`σ'`-positive transition is alive itself, hence (`reachProb_pos_imp_isReachable` +
`BeliefSystem.support_exhaustive`) in its information set's support. -/
theorem stop_mem_support_of_alive (G : ExtensiveGame I E)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (a : Assessment G.toExtensiveForm) (σseq : ℕ → G.toExtensiveForm.BehavioralStrategy)
    (hmix : ∀ n, G.toExtensiveForm.IsTotallyMixed (σseq n))
    (i : I) (ω'' : G.info.Obs i) {x w : List E} {n₀ : ℕ}
    (hx_alive : 0 < reachProb G.toExtensiveForm (σseq n₀) x)
    (hin : (G.toExtensiveForm.tree.nodeKind w).movesAt i ∧ G.info.observe i w = ω'')
    (hxw : x <+: w) (σ' : G.toExtensiveForm.BehavioralStrategy)
    (hP : G.toExtensiveForm.finitePrefixProbFrom σ' x (w.drop x.length) ≠ 0) :
    (⟨w, hin⟩ : G.toExtensiveForm.InfoSet i ω'') ∈ a.beliefs.support i ω'' ∧
      0 < reachProb G.toExtensiveForm (σseq n₀) w := by
  have hP_pos : 0 < G.toExtensiveForm.finitePrefixProbFrom σ' x (w.drop x.length) :=
    lt_of_le_of_ne (G.toExtensiveForm.finitePrefixProbFrom_nonneg σ' x (w.drop x.length))
      (Ne.symm hP)
  have hsplit : x ++ w.drop x.length = w := by
    obtain ⟨t, rfl⟩ := hxw
    rw [List.drop_left]
  have hw_alive : 0 < reachProb G.toExtensiveForm (σseq n₀) w := by
    rw [← hsplit, reachProb_append]
    exact mul_pos hx_alive
      (finitePrefixProbFrom_pos_of_totallyMixed_of_pos G hno_joint (σseq n₀) σ' (hmix n₀) x
        (w.drop x.length) hP_pos)
  exact ⟨a.beliefs.support_exhaustive i ω'' ⟨w, hin⟩
    (G.reachProb_pos_imp_isReachable (σseq n₀) w hw_alive), hw_alive⟩

/-- **Block completeness**: Given one stop pair — an `i`-mover `w₀` at `ω''` whose last `i`-stop
`x₀` observes `obs` — every alive `i`-mover `y` at `ω''` has a last `i`-stop `q` observing `obs`,
alive (a prefix of an alive node) and hence in the support of `(i, obs)`. The transfer is
`LastStopAlign` applied to the pair `(w₀, y)`. -/
theorem exists_supp_ancestor_of_alive (G : ExtensiveGame I E)
    (hsa : G.toExtensiveForm.LastStopAlign)
    (a : Assessment G.toExtensiveForm) (σseq : ℕ → G.toExtensiveForm.BehavioralStrategy)
    (i : I) (obs ω'' : G.info.Obs i)
    {w₀ x₀ : List E} (hw₀r : G.toExtensiveForm.IsReachable w₀)
    (hw₀mv : (G.toExtensiveForm.tree.nodeKind w₀).movesAt i)
    (hw₀obs : G.info.observe i w₀ = ω'')
    (hx₀mv : (G.toExtensiveForm.tree.nodeKind x₀).movesAt i)
    (hx₀obs : G.info.observe i x₀ = obs)
    (hx₀w₀ : w₀.take x₀.length = x₀) (hlt₀ : x₀.length < w₀.length)
    (hbet₀ : ∀ r : ℕ, x₀.length < r → r < w₀.length →
      ¬ (G.toExtensiveForm.tree.nodeKind (w₀.take r)).movesAt i)
    {y : List E} (hymv : (G.toExtensiveForm.tree.nodeKind y).movesAt i)
    (hyobs : G.info.observe i y = ω'')
    {n₀ : ℕ} (hy_alive : 0 < reachProb G.toExtensiveForm (σseq n₀) y) :
    ∃ (q : List E) (hq : (G.toExtensiveForm.tree.nodeKind q).movesAt i ∧
        G.info.observe i q = obs),
      (⟨q, hq⟩ : G.toExtensiveForm.InfoSet i obs) ∈ a.beliefs.support i obs ∧
      y.take q.length = q ∧ q.length < y.length ∧
      (∀ r : ℕ, q.length < r → r < y.length →
        ¬ (G.toExtensiveForm.tree.nodeKind (y.take r)).movesAt i) ∧
      0 < reachProb G.toExtensiveForm (σseq n₀) q := by
  have hyr : G.toExtensiveForm.IsReachable y := by
    by_contra hnr
    rw [G.reachProb_eq_zero_of_not_isReachable (σseq n₀) y hnr] at hy_alive
    exact absurd hy_alive (lt_irrefl 0)
  obtain ⟨m', hm'lt, hm'mov, hm'obs, hm'bet, _⟩ :=
    hsa i w₀ y hw₀r hyr hw₀mv hymv (hw₀obs.trans hyobs.symm) x₀.length hlt₀
      (by rw [hx₀w₀]; exact hx₀mv) hbet₀
  have hq_obs : G.info.observe i (y.take m') = obs := by
    rw [hm'obs, hx₀w₀]
    exact hx₀obs
  have hq_len : (y.take m').length = m' := by
    rw [List.length_take, min_eq_left hm'lt.le]
  have hq_alive : 0 < reachProb G.toExtensiveForm (σseq n₀) (y.take m') :=
    reachProb_pos_of_prefix G.toExtensiveForm (σseq n₀) (List.take_prefix m' y) hy_alive
  refine ⟨y.take m', ⟨hm'mov, hq_obs⟩,
    a.beliefs.support_exhaustive i obs ⟨y.take m', hm'mov, hq_obs⟩
      (G.reachProb_pos_imp_isReachable (σseq n₀) (y.take m') hq_alive),
    ?_, ?_, ?_, hq_alive⟩
  · rw [hq_len]
  · rw [hq_len]
    exact hm'lt
  · rw [hq_len]
    exact hm'bet

end Econlib.GameTheory
