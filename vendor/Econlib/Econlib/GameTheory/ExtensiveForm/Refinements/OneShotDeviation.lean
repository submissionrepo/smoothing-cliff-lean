/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.NextStopFrontier

/-!
# One-shot deviation principle for extensive-form sequential rationality

Under perfect recall (via reach-coherence and last-stop alignment), finite depth, no simultaneous
moves, and undiscounted terminal payoffs, **one-shot** sequential rationality of a Kreps–Wilson
consistent assessment recovers full (Fudenberg–Tirole) **sequential rationality** (Fudenberg and
Tirole 1991; Selten 1975). The statement is at the sequential-equilibrium level (Kreps and Wilson
1982): The bare-PBE analog is false, since off-path beliefs are then unconstrained.

## Main statements

* `assessmentValue_le_of_oneShot`: Belief-weighted dominance at every information set.
* `isSequentiallyRational_of_oneShot`: One-shot sequential rationality implies full sequential
  rationality.
* `IsSequentialEquilibrium_of_oneShot`: The one-shot deviation principle for sequential equilibrium.

## Notes

The hypotheses `discount = 1` and `LastStopAlign` are each necessary, even at the
sequential-equilibrium level; see `Econlib.GameTheory.ExtensiveForm.Kuhn.Recall` for the latter.
The repeated-game one-shot deviation principle (`Econlib.GameTheory.Repeated.OneShotDeviation`)
compares raw `continuationValue` rather than belief-weighted `assessmentValue`, so its per-node
induction does not transfer here.

## References

* Fudenberg, Drew, and Jean Tirole. 1993. *Game Theory*. The MIT Press.
* Kreps, David M., and Robert Wilson. 1982. “Sequential Equilibria.” *Econometrica* 50 (4): 863.
  [https://doi.org/10.2307/1912767](https://doi.org/10.2307/1912767).
* Selten, R. 1975. “Reexamination of the Perfectness Concept for Equilibrium Points in Extensive
  Games.” *International Journal of Game Theory* 4 (1): 25–55. [https://doi.org/10.1007/bf01766400](https://doi.org/10.1007/bf01766400).

## Tags

extensive form, one-shot deviation principle, osdp, sequential rationality, perfect recall
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

universe u

variable {I E : Type u} [DecidableEq E]

/-- **Belief-weighted deeper-deviation step.** With `τ₀ := oneShotSurgery σ σ' i obs` the one-shot
surgery sharing `σ'`'s head action at `(i, obs)` and reverting to `σ` everywhere else, `σ'` differs
from `τ₀` only strictly below the support nodes of `(i, obs)`, and the belief-weighted comparison

`∑ x ∈ supp, μ.belief(x) · V_{σ'}(x.1, i) ≤ ∑ x ∈ supp, μ.belief(x) · V_{τ₀}(x.1, i)`

holds: Reverting every deviation below the head cannot hurt.

Beyond perfect recall and finite depth, the hypotheses `hδ : G.discount = 1` and
`hsa : LastStopAlign` are each necessary. With `discount < 1` the backward peel accumulates one
`δ`-factor per tree layer while the one-shot inequalities run on each information set's local
clocks, and perfect recall permits an information set's nodes to sit at unequal tree depths; the
two bookkeepings then disagree and the principle fails. Without last-stop alignment an information
set may mix a node whose path passes through the upstream set with a sibling whose path does not,
so the one-shot average at the deeper set governs a different mixture than the upstream deviation
steers into. -/
theorem assessmentValue_le_of_deeper (G : ExtensiveGame I E) {N : ℕ}
    (hfd : G.toExtensiveForm.FiniteDepth N) (hpr : G.toExtensiveForm.IsReachCoherent)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (hsa : G.toExtensiveForm.LastStopAlign) (hδ : G.discount = 1)
    (a : Assessment G.toExtensiveForm) (hcons : HasConsistentBeliefs G.toExtensiveForm a)
    (hone : IsSequentiallyRationalOneShot G a) (i : I) (obs : G.info.Obs i)
    (σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i a.strategy σ') :
    (∑ x ∈ a.beliefs.support i obs,
        a.beliefs.belief i obs x * G.continuationValue σ' x.1 i) ≤
      (∑ x ∈ a.beliefs.support i obs,
        a.beliefs.belief i obs x *
          G.continuationValue (oneShotSurgery G.toExtensiveForm a.strategy σ' i obs) x.1 i) := by
  classical
  -- Fix one consistency witness for the whole induction; keep `hcons` for the lemmas that
  -- re-obtain their own.
  obtain ⟨σseq, hmix, _hstrategy, hbel⟩ := id hcons
  -- Master statement: belief-weighted surgery dominance at every information set of `i`, by
  -- induction on a depth budget `k` covering the *alive* part of the support (positive
  -- `σseq n`-reach for some `n` — the transferable finiteness, since belief-carrying nodes are
  -- alive and aliveness propagates to last `i`-stops). The top call takes `k := N`.
  suffices haux : ∀ (k : ℕ) (ob : G.info.Obs i),
      (∀ x ∈ a.beliefs.support i ob, (∃ n, 0 < reachProb G.toExtensiveForm (σseq n) x.1) →
        N ≤ x.1.length + k) →
      (∑ x ∈ a.beliefs.support i ob, a.beliefs.belief i ob x * G.continuationValue σ' x.1 i) ≤
        (∑ x ∈ a.beliefs.support i ob, a.beliefs.belief i ob x *
          G.continuationValue (oneShotSurgery G.toExtensiveForm a.strategy σ' i ob) x.1 i) by
    exact haux N obs (fun x _ _ => by omega)
  intro k
  induction k with
  | zero =>
    -- Alive support nodes are `i`-movers, hence strictly shallower than `N`; budget `0` forces
    -- them beyond `N`, so every belief vanishes and both sums are `0`.
    intro ob hbud
    have hzero : ∀ x ∈ a.beliefs.support i ob, a.beliefs.belief i ob x = 0 := by
      intro x hx
      by_contra hne
      obtain ⟨n₀, halive⟩ := exists_seq_reach_pos_of_belief_ne_zero G a σseq hbel i ob x hne
      have hbound := hbud x hx ⟨n₀, halive⟩
      have hlt := length_lt_of_movesAt G.toExtensiveForm hfd x.2.1
      omega
    rw [Finset.sum_eq_zero (fun x hx => by rw [hzero x hx, zero_mul]),
      Finset.sum_eq_zero (fun x hx => by rw [hzero x hx, zero_mul])]
  | succ k ih =>
    intro ob hbud
    rw [← sub_nonneg, ← Finset.sum_sub_distrib]
    have hterm_eq : ∀ x ∈ a.beliefs.support i ob,
        a.beliefs.belief i ob x *
            G.continuationValue (oneShotSurgery G.toExtensiveForm a.strategy σ' i ob) x.1 i -
          a.beliefs.belief i ob x * G.continuationValue σ' x.1 i =
        a.beliefs.belief i ob x *
          (G.continuationValue (oneShotSurgery G.toExtensiveForm a.strategy σ' i ob) x.1 i -
            G.continuationValue σ' x.1 i) := fun x _ => by ring
    rw [Finset.sum_congr rfl hterm_eq]
    -- Restrict to the belief-carrying support `D`.
    set D := (a.beliefs.support i ob).filter (fun x => a.beliefs.belief i ob x ≠ 0) with hD
    rw [← Finset.sum_filter_of_ne (p := fun x => a.beliefs.belief i ob x ≠ 0)
      (fun x _ hne hμ0 => hne (by rw [hμ0, zero_mul]))]
    have hD_supp : ∀ x ∈ D, x ∈ a.beliefs.support i ob := by
      intro x hx
      rw [hD, Finset.mem_filter] at hx
      exact hx.1
    have hD_alive : ∀ x ∈ D, ∃ n, 0 < reachProb G.toExtensiveForm (σseq n) x.1 := by
      intro x hx
      rw [hD, Finset.mem_filter] at hx
      exact exists_seq_reach_pos_of_belief_ne_zero G a σseq hbel i ob x hx.2
    have hD_reach : ∀ x ∈ D, G.toExtensiveForm.IsReachable x.1 := by
      intro x hx
      obtain ⟨n₀, halive⟩ := hD_alive x hx
      by_contra hnr
      rw [G.reachProb_eq_zero_of_not_isReachable (σseq n₀) x.1 hnr] at halive
      exact absurd halive (lt_irrefl 0)
    -- Expand each surgery residual onto the next-stop frontier.
    have hexpand : ∀ x ∈ D,
        G.continuationValue (oneShotSurgery G.toExtensiveForm a.strategy σ' i ob) x.1 i -
          G.continuationValue σ' x.1 i =
        ∑ w ∈ G.toExtensiveForm.nextStops i k x.1,
          G.toExtensiveForm.finitePrefixProbFrom σ' x.1 (w.drop x.1.length) *
            (G.continuationValue a.strategy w i - G.continuationValue σ' w i) := by
      intro x hx
      have hsurg_eq : oneShotSurgery G.toExtensiveForm a.strategy σ' i (G.info.observe i x.1) =
          oneShotSurgery G.toExtensiveForm a.strategy σ' i ob := by rw [x.2.2]
      rw [← hsurg_eq]
      exact oneShotSurgery_residual_nextStops G hfd hpr hno_joint hδ i a.strategy σ' hdev
        (hD_reach x hx) x.2.1 k (by
          have := hbud x (hD_supp x hx) (hD_alive x hx)
          omega)
    rw [Finset.sum_congr rfl (fun x hx => by rw [hexpand x hx, Finset.mul_sum])]
    -- The total stop set `S` and the accumulated weight `W`.
    set S := D.biUnion (fun x => G.toExtensiveForm.nextStops i k x.1) with hS
    set W : List E → ℝ := fun w => ∑ x ∈ D,
      if w ∈ G.toExtensiveForm.nextStops i k x.1 then
        a.beliefs.belief i ob x *
          G.toExtensiveForm.finitePrefixProbFrom σ' x.1 (w.drop x.1.length)
      else 0 with hW
    clear_value W
    -- Each stop has a *unique* `D`-ancestor (`noRevisit`), so `W` collapses pointwise.
    have hUniq : ∀ x₁ ∈ D, ∀ x₂ ∈ D, ∀ w : List E,
        w ∈ G.toExtensiveForm.nextStops i k x₁.1 →
        w ∈ G.toExtensiveForm.nextStops i k x₂.1 → x₁ = x₂ := by
      intro x₁ hx₁ x₂ hx₂ w hw₁ hw₂
      obtain ⟨hpre₁, -, -, -, -, -⟩ :=
        (G.toExtensiveForm.mem_nextStops_iff i k (hD_reach x₁ hx₁)).mp hw₁
      obtain ⟨hpre₂, -, -, -, -, -⟩ :=
        (G.toExtensiveForm.mem_nextStops_iff i k (hD_reach x₂ hx₂)).mp hw₂
      have hobs12 : G.info.observe i x₁.1 = G.info.observe i x₂.1 :=
        x₁.2.2.trans x₂.2.2.symm
      refine Subtype.ext ?_
      rcases List.prefix_or_prefix_of_prefix hpre₁ hpre₂ with h | h
      · exact hpr.noRevisit i x₁.1 x₂.1 (hD_reach x₁ hx₁) (hD_reach x₂ hx₂) h hobs12
          x₁.2.1 x₂.2.1
      · exact (hpr.noRevisit i x₂.1 x₁.1 (hD_reach x₂ hx₂) (hD_reach x₁ hx₁) h hobs12.symm
          x₂.2.1 x₁.2.1).symm
    have hW_eq : ∀ x ∈ D, ∀ w ∈ G.toExtensiveForm.nextStops i k x.1,
        W w = a.beliefs.belief i ob x *
          G.toExtensiveForm.finitePrefixProbFrom σ' x.1 (w.drop x.1.length) := by
      intro x hx w hw
      simp only [hW]
      rw [Finset.sum_eq_single_of_mem x hx
        (fun x₂ hx₂ hne => if_neg (fun hw₂ => hne (hUniq x₂ hx₂ x hx w hw₂ hw)))]
      rw [if_pos hw]
    -- Regroup the pair sum as a `W`-weighted sum over `S`.
    have hR1 : (∑ w ∈ S, W w *
          (G.continuationValue a.strategy w i - G.continuationValue σ' w i)) =
        ∑ x ∈ D, ∑ w ∈ G.toExtensiveForm.nextStops i k x.1,
          a.beliefs.belief i ob x *
            (G.toExtensiveForm.finitePrefixProbFrom σ' x.1 (w.drop x.1.length) *
              (G.continuationValue a.strategy w i - G.continuationValue σ' w i)) := by
      simp only [hW]
      simp only [Finset.sum_mul, ite_mul, zero_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      have hsub : G.toExtensiveForm.nextStops i k x.1 ⊆ S := by
        intro w hw
        rw [hS, Finset.mem_biUnion]
        exact ⟨x, hx, hw⟩
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
      exact Finset.sum_congr rfl (fun w _ => by ring)
    rw [← hR1]
    -- Fiber `S` by the observed information set of the stop.
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun w => G.info.observe i w)
      (t := S.image (fun w => G.info.observe i w)) (fun w hw => Finset.mem_image_of_mem _ hw)]
    refine Finset.sum_nonneg (fun ω'' hω'' => ?_)
    -- ## Per-fiber block
    -- Witness stop pair for the fiber: some stop `w₀` observing `ω''` with `D`-ancestor `x₀`.
    obtain ⟨w₀, hw₀S, hw₀obs⟩ := Finset.mem_image.mp hω''
    have hS_struct : ∀ w ∈ S, ∃ x ∈ D, w ∈ G.toExtensiveForm.nextStops i k x.1 := by
      intro w hw
      rw [hS, Finset.mem_biUnion] at hw
      exact hw
    obtain ⟨x₀, hx₀D, hw₀x₀⟩ := hS_struct w₀ hw₀S
    obtain ⟨hpre₀, hne₀, hw₀r, hw₀mv, hbet₀, -⟩ :=
      (G.toExtensiveForm.mem_nextStops_iff i k (hD_reach x₀ hx₀D)).mp hw₀x₀
    have htake₀ : w₀.take x₀.1.length = x₀.1 := (List.prefix_iff_eq_take.mp hpre₀).symm
    have hlt₀ : x₀.1.length < w₀.length := by
      rcases Nat.eq_or_lt_of_le hpre₀.length_le with heq | hlt
      · exact absurd (List.IsPrefix.eq_of_length hpre₀ heq) hne₀
      · exact hlt
    -- Budget transfer to the deeper information set, via the last-stop ancestor.
    have hbud'' : ∀ y ∈ a.beliefs.support i ω'',
        (∃ n, 0 < reachProb G.toExtensiveForm (σseq n) y.1) → N ≤ y.1.length + k := by
      intro y hy halive
      obtain ⟨n₁, hy_alive⟩ := halive
      obtain ⟨q, hq, hq_supp, -, hq_lt, -, hq_alive⟩ :=
        exists_supp_ancestor_of_alive G hsa a σseq i ob ω'' hw₀r hw₀mv hw₀obs
          x₀.2.1 x₀.2.2 htake₀ hlt₀ hbet₀ y.2.1 y.2.2 hy_alive
      have hqbud : N ≤ q.length + (k + 1) := hbud ⟨q, hq⟩ hq_supp ⟨n₁, hq_alive⟩
      omega
    -- The deeper master quantity is nonnegative: atom + inductive call.
    have hM : 0 ≤ ∑ y ∈ a.beliefs.support i ω'', a.beliefs.belief i ω'' y *
        (G.continuationValue a.strategy y.1 i - G.continuationValue σ' y.1 i) := by
      have hatom := beliefWeighted_oneShot_step G a hone i ω''
        (oneShotSurgery G.toExtensiveForm a.strategy σ' i ω'')
        (oneShotSurgery_isInfoSetDeviation G.toExtensiveForm a.strategy σ' i ω'')
      have hT := ih ω'' hbud''
      have h1 : (∑ y ∈ a.beliefs.support i ω'', a.beliefs.belief i ω'' y *
            (G.continuationValue a.strategy y.1 i - G.continuationValue σ' y.1 i)) =
          (∑ y ∈ a.beliefs.support i ω'', a.beliefs.belief i ω'' y *
            G.continuationValue a.strategy y.1 i) -
          ∑ y ∈ a.beliefs.support i ω'', a.beliefs.belief i ω'' y *
            G.continuationValue σ' y.1 i := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun y _ => by ring)
      rw [h1]
      linarith [hatom, hT]
    -- Convert the fiber sum to a support-indexed sum.
    set Sfib := S.filter (fun w => G.info.observe i w = ω'') with hSfib
    clear_value Sfib
    have hSfib_struct : ∀ w ∈ Sfib, G.info.observe i w = ω'' ∧ ∃ x ∈ D,
        w ∈ G.toExtensiveForm.nextStops i k x.1 ∧ G.toExtensiveForm.IsReachable w ∧
        (G.toExtensiveForm.tree.nodeKind w).movesAt i ∧
        w.take x.1.length = x.1 ∧ x.1.length < w.length ∧
        (∀ r : ℕ, x.1.length < r → r < w.length →
          ¬ (G.toExtensiveForm.tree.nodeKind (w.take r)).movesAt i) := by
      intro w hw
      rw [hSfib, Finset.mem_filter] at hw
      obtain ⟨hwS, hwobs⟩ := hw
      obtain ⟨x, hxD, hwx⟩ := hS_struct w hwS
      obtain ⟨hpre, hne, hwr, hwmv, hbet, -⟩ :=
        (G.toExtensiveForm.mem_nextStops_iff i k (hD_reach x hxD)).mp hwx
      have hlt : x.1.length < w.length := by
        rcases Nat.eq_or_lt_of_le hpre.length_le with heq | hlt
        · exact absurd (List.IsPrefix.eq_of_length hpre heq) hne
        · exact hlt
      exact ⟨hwobs, x, hxD, hwx, hwr, hwmv, (List.prefix_iff_eq_take.mp hpre).symm, hlt, hbet⟩
    -- A belief-carrying-ancestored alive node of the deeper set lies in the fiber.
    have hfiber_of_D : ∀ (y' : G.toExtensiveForm.InfoSet i ω'') (q : List E)
        (hq : (G.toExtensiveForm.tree.nodeKind q).movesAt i ∧ G.info.observe i q = ob),
        (⟨q, hq⟩ : G.toExtensiveForm.InfoSet i ob) ∈ D →
        y'.1.take q.length = q → q.length < y'.1.length →
        (∀ r : ℕ, q.length < r → r < y'.1.length →
          ¬ (G.toExtensiveForm.tree.nodeKind (y'.1.take r)).movesAt i) →
        G.toExtensiveForm.IsReachable y'.1 → y'.1 ∈ Sfib := by
      intro y' q hq hqD htake hlt hbet hy'r
      have hy'len := length_lt_of_movesAt G.toExtensiveForm hfd y'.2.1
      have hbudq : N ≤ q.length + (k + 1) := hbud ⟨q, hq⟩ (hD_supp _ hqD) (hD_alive _ hqD)
      have hq_pre : q <+: y'.1 := by
        rw [← htake]
        exact List.take_prefix _ _
      have hq_reach : G.toExtensiveForm.IsReachable q := hD_reach ⟨q, hq⟩ hqD
      have hmem : y'.1 ∈ G.toExtensiveForm.nextStops i k q :=
        (G.toExtensiveForm.mem_nextStops_iff i k hq_reach).mpr
          ⟨hq_pre, fun heq => by rw [heq] at hlt; exact absurd hlt (lt_irrefl _),
            hy'r, y'.2.1, hbet, by omega⟩
      rw [hSfib, Finset.mem_filter]
      refine ⟨?_, y'.2.2⟩
      rw [hS]
      exact Finset.mem_biUnion.mpr ⟨⟨q, hq⟩, hqD, hmem⟩
    -- Cross-proportionality of the accumulated weight with the deeper beliefs.
    have hcross : ∀ y ∈ a.beliefs.support i ω'', ∀ y' ∈ a.beliefs.support i ω'',
        (if y.1 ∈ Sfib then W y.1 else 0) * a.beliefs.belief i ω'' y' =
        (if y'.1 ∈ Sfib then W y'.1 else 0) * a.beliefs.belief i ω'' y := by
      have hside : ∀ y ∈ a.beliefs.support i ω'', ∀ y' ∈ a.beliefs.support i ω'',
          y.1 ∈ Sfib → y'.1 ∉ Sfib → W y.1 * a.beliefs.belief i ω'' y' = 0 := by
        intro y hy y' hy' hyS hy'S
        obtain ⟨-, x, hxD, hyx, hyr, -, hytake, hylt, hybet⟩ := hSfib_struct y.1 hyS
        by_cases hy'μ : a.beliefs.belief i ω'' y' = 0
        · rw [hy'μ, mul_zero]
        · obtain ⟨n₁, hy'_alive⟩ :=
            exists_seq_reach_pos_of_belief_ne_zero G a σseq hbel i ω'' y' hy'μ
          have hy'r : G.toExtensiveForm.IsReachable y'.1 := by
            by_contra hnr
            rw [G.reachProb_eq_zero_of_not_isReachable (σseq n₁) y'.1 hnr] at hy'_alive
            exact absurd hy'_alive (lt_irrefl 0)
          obtain ⟨q, hq, hq_supp, hq_take, hq_lt, hq_bet, -⟩ :=
            exists_supp_ancestor_of_alive G hsa a σseq i ob ω'' hw₀r hw₀mv hw₀obs
              x₀.2.1 x₀.2.2 htake₀ hlt₀ hbet₀ y'.2.1 y'.2.2 hy'_alive
          -- `q` carries zero belief — otherwise `y'` would lie in the fiber.
          have hqμ : a.beliefs.belief i ob ⟨q, hq⟩ = 0 := by
            by_contra hqne
            have hqD : (⟨q, hq⟩ : G.toExtensiveForm.InfoSet i ob) ∈ D := by
              rw [hD, Finset.mem_filter]
              exact ⟨hq_supp, hqne⟩
            exact hy'S (hfiber_of_D y' q hq hqD hq_take hq_lt hq_bet hy'r)
          have hCT := chain_belief_tower G hpr hno_joint hsa a hcons i ob ω'' σ' hdev
            x ⟨q, hq⟩ (hD_supp x hxD) hq_supp y y' hy hy' hyr hy'r
            hytake hylt hybet hq_take hq_lt hq_bet
          rw [hqμ, zero_mul, zero_mul] at hCT
          rw [hW_eq x hxD y.1 hyx]
          exact hCT
      intro y hy y' hy'
      by_cases hyS : y.1 ∈ Sfib
      · by_cases hy'S : y'.1 ∈ Sfib
        · rw [if_pos hyS, if_pos hy'S]
          obtain ⟨-, x, hxD, hyx, hyr, -, hytake, hylt, hybet⟩ := hSfib_struct y.1 hyS
          obtain ⟨-, x', hx'D, hy'x', hy'r, -, hy'take, hy'lt, hy'bet⟩ :=
            hSfib_struct y'.1 hy'S
          rw [hW_eq x hxD y.1 hyx, hW_eq x' hx'D y'.1 hy'x']
          exact chain_belief_tower G hpr hno_joint hsa a hcons i ob ω'' σ' hdev
            x x' (hD_supp x hxD) (hD_supp x' hx'D) y y' hy hy' hyr hy'r
            hytake hylt hybet hy'take hy'lt hy'bet
        · rw [if_pos hyS, if_neg hy'S, zero_mul]
          exact hside y hy y' hy' hyS hy'S
      · rw [if_neg hyS, zero_mul]
        by_cases hy'S : y'.1 ∈ Sfib
        · rw [if_pos hy'S]
          exact (hside y' hy' y hy hy'S hyS).symm
        · rw [if_neg hy'S, zero_mul]
    -- The fiber sum equals the support-indexed weighted sum.
    have hfib_in : ∀ w ∈ Sfib,
        (G.toExtensiveForm.tree.nodeKind w).movesAt i ∧ G.info.observe i w = ω'' := by
      intro w hw
      obtain ⟨hobs, x, hxD, -, -, hwmv, -, -, -⟩ := hSfib_struct w hw
      exact ⟨hwmv, hobs⟩
    have hC1 : (∑ w ∈ Sfib, W w *
          (G.continuationValue a.strategy w i - G.continuationValue σ' w i)) =
        ∑ y ∈ a.beliefs.support i ω'', (if y.1 ∈ Sfib then W y.1 else 0) *
          (G.continuationValue a.strategy y.1 i - G.continuationValue σ' y.1 i) := by
      have hrhs : (∑ y ∈ a.beliefs.support i ω'', (if y.1 ∈ Sfib then W y.1 else 0) *
            (G.continuationValue a.strategy y.1 i - G.continuationValue σ' y.1 i)) =
          ∑ y ∈ (a.beliefs.support i ω'').filter (fun y => y.1 ∈ Sfib), W y.1 *
            (G.continuationValue a.strategy y.1 i - G.continuationValue σ' y.1 i) := by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl (fun y _ => by rw [ite_mul, zero_mul])
      have hlhs' : (∑ w ∈ Sfib, W w *
            (G.continuationValue a.strategy w i - G.continuationValue σ' w i)) =
          ∑ w ∈ Sfib.filter (fun w => W w ≠ 0), W w *
            (G.continuationValue a.strategy w i - G.continuationValue σ' w i) :=
        (Finset.sum_filter_of_ne (p := fun w => W w ≠ 0)
          (fun w _ hne hW0 => hne (by rw [hW0, zero_mul]))).symm
      have hrhs' : (∑ y ∈ (a.beliefs.support i ω'').filter (fun y => y.1 ∈ Sfib), W y.1 *
            (G.continuationValue a.strategy y.1 i - G.continuationValue σ' y.1 i)) =
          ∑ y ∈ ((a.beliefs.support i ω'').filter (fun y => y.1 ∈ Sfib)).filter
              (fun y => W y.1 ≠ 0), W y.1 *
            (G.continuationValue a.strategy y.1 i - G.continuationValue σ' y.1 i) :=
        (Finset.sum_filter_of_ne
          (p := fun y : G.toExtensiveForm.InfoSet i ω'' => W y.1 ≠ 0)
          (fun y _ hne hW0 => hne (by rw [hW0, zero_mul]))).symm
      rw [hrhs, hlhs', hrhs']
      refine Finset.sum_bij (fun w hw =>
        (⟨w, hfib_in w (Finset.mem_filter.mp hw).1⟩ : G.toExtensiveForm.InfoSet i ω''))
        ?_ ?_ ?_ ?_
      · -- maps into the doubly-filtered support
        intro w hw
        obtain ⟨hwfib, hWne⟩ := Finset.mem_filter.mp hw
        obtain ⟨hobs, x, hxD, hwx, hwr, hwmv, hwtake, hwlt, -⟩ := hSfib_struct w hwfib
        have hWne' := hWne
        rw [hW_eq x hxD w hwx] at hWne'
        obtain ⟨hμne, hPne⟩ := mul_ne_zero_iff.mp hWne'
        obtain ⟨n₀, hx_alive⟩ := hD_alive x hxD
        have hpre : x.1 <+: w := by
          rw [← hwtake]
          exact List.take_prefix _ _
        have hmem := (stop_mem_support_of_alive G hno_joint a σseq hmix i ω''
          hx_alive (hfib_in w hwfib) hpre σ' hPne).1
        rw [Finset.mem_filter, Finset.mem_filter]
        exact ⟨⟨hmem, hwfib⟩, hWne⟩
      · intro w₁ hw₁ w₂ hw₂ heq
        exact congrArg Subtype.val heq
      · intro y hy
        rw [Finset.mem_filter, Finset.mem_filter] at hy
        exact ⟨y.1, Finset.mem_filter.mpr ⟨hy.1.2, hy.2⟩, rfl⟩
      · intro w hw
        rfl
    rw [hC1]
    -- Proportional conversion to the deeper beliefs, then atom + induction close the block.
    have hconv := sum_mul_sum_proportional (a.beliefs.support i ω'')
      (fun y => if y.1 ∈ Sfib then W y.1 else 0)
      (fun y => a.beliefs.belief i ω'' y)
      (fun y => G.continuationValue a.strategy y.1 i - G.continuationValue σ' y.1 i)
      hcross
    by_cases hsupp_ne : (a.beliefs.support i ω'').Nonempty
    · rw [a.beliefs.belief_sum_one i ω'' hsupp_ne, one_mul] at hconv
      rw [hconv]
      refine mul_nonneg (Finset.sum_nonneg (fun y _ => ?_)) hM
      split_ifs with h
      · simp only [hW]
        refine Finset.sum_nonneg (fun x hx => ?_)
        split_ifs with h2
        · exact mul_nonneg (a.beliefs.belief_nonneg i ob x)
            (G.toExtensiveForm.finitePrefixProbFrom_nonneg σ' x.1 _)
        · exact le_refl 0
      · exact le_refl 0
    · rw [Finset.not_nonempty_iff_eq_empty] at hsupp_ne
      rw [hsupp_ne, Finset.sum_empty]

/-- **Belief-weighted dominance (unified, on and off path).** At every information set `(i, obs)`,
one-shot sequential rationality of a Kreps–Wilson consistent assessment implies that the
equilibrium strategy `σ = a.strategy` belief-weighted-dominates any unilateral `i`-deviation
`σ'`:

`∑ x ∈ supp, μ.belief(x) · V_{σ'}(x.1, i) ≤ ∑ x ∈ supp, μ.belief(x) · V_σ(x.1, i)`.

An on-path/off-path split is unsound here: A one-shot-optimal `σ` may be steered by `σ'` into
`σ`-off-path deeper information sets, where the σ-reach-weighted atom is vacuous, so the two
contributions are entangled. The argument instead runs at the belief-weighted level, where one-shot
rationality holds at every information set with no positivity, reverting `σ'` to `σ` deepest-first
via the one-shot surgery `τ₀`. -/
theorem assessmentValue_le_of_oneShot (G : ExtensiveGame I E) {N : ℕ}
    (hfd : G.toExtensiveForm.FiniteDepth N) (hpr : G.toExtensiveForm.IsReachCoherent)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (hsa : G.toExtensiveForm.LastStopAlign) (hδ : G.discount = 1)
    (a : Assessment G.toExtensiveForm) (hcons : HasConsistentBeliefs G.toExtensiveForm a)
    (hone : IsSequentiallyRationalOneShot G a) (i : I) (obs : G.info.Obs i)
    (σ' : G.toExtensiveForm.BehavioralStrategy)
    (hdev : G.toExtensiveForm.unilateralDeviation i a.strategy σ') :
    assessmentValue G { strategy := σ', beliefs := a.beliefs } i obs ≤
      assessmentValue G a i obs := by
  -- `τ₀`: the one-shot surgery copying `σ'`'s head action at `(i, obs)`, `σ` elsewhere.
  set τ₀ := oneShotSurgery G.toExtensiveForm a.strategy σ' i obs with hτ₀
  -- Unfold both `assessmentValue`s to the belief-weighted sum form.
  unfold assessmentValue
  -- Chain the deeper-deviation step (recursive crux) with the single-layer atom at `(i, obs)`. The
  -- atom is `beliefWeighted_oneShot_step` for the one-shot info-set deviation `τ₀` — valid with NO
  -- positivity, so it applies whether or not `(i, obs)` is on path.
  refine le_trans
    (assessmentValue_le_of_deeper G hfd hpr hno_joint hsa hδ a hcons hone i obs σ' hdev) ?_
  exact beliefWeighted_oneShot_step G a hone i obs τ₀
    (oneShotSurgery_isInfoSetDeviation G.toExtensiveForm a.strategy σ' i obs)

/-- **One-shot deviation principle for sequential rationality.** Under perfect recall, last-stop
alignment, finite depth, no simultaneous moves, and undiscounted values (`discount = 1`, the
terminal-payoff setting), one-shot sequential rationality of a Kreps–Wilson–consistent assessment
implies full (Fudenberg–Tirole) sequential rationality.

Consistency, not merely Bayes consistency, is essential: At an off-path information set Bayes
consistency is vacuous, leaving the belief free, and the bare-PBE analog is false. The proof is the
unified belief-weighted dominance `assessmentValue_le_of_oneShot`, valid at every information set
on or off path. -/
theorem isSequentiallyRational_of_oneShot (G : ExtensiveGame I E) {N : ℕ}
    (hfd : G.toExtensiveForm.FiniteDepth N) (hpr : G.toExtensiveForm.IsReachCoherent)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (hsa : G.toExtensiveForm.LastStopAlign) (hδ : G.discount = 1)
    (a : Assessment G.toExtensiveForm) (hcons : HasConsistentBeliefs G.toExtensiveForm a)
    (hone : IsSequentiallyRationalOneShot G a) :
    IsSequentiallyRational G a := by
  -- Unified belief-weighted dominance: at *every* information set the equilibrium strategy
  -- belief-weighted-dominates any unilateral `i`-deviation. The (unsound) on-path/off-path split is
  -- gone — `assessmentValue_le_of_oneShot` handles both via the belief tower (`hcons`) directly.
  intro i obs σ' hdev
  rw [ge_iff_le]
  exact assessmentValue_le_of_oneShot G hfd hpr hno_joint hsa hδ a hcons hone i obs σ' hdev

/-- **One-shot deviation principle for sequential equilibrium.** A one-shot sequential equilibrium
of a finite-depth, perfect-recall, last-stop-aligned, sequential-move (no joint nodes),
undiscounted game is a (full) sequential equilibrium. The discount and alignment hypotheses are
each necessary; see `assessmentValue_le_of_deeper`. -/
theorem IsSequentialEquilibrium_of_oneShot (G : ExtensiveGame I E) {N : ℕ}
    (hfd : G.toExtensiveForm.FiniteDepth N) (hpr : G.toExtensiveForm.IsReachCoherent)
    (hno_joint : ∀ (h : List E) (n : JointNode I E), G.toExtensiveForm.tree.nodeKind h ≠ .joint n)
    (hsa : G.toExtensiveForm.LastStopAlign) (hδ : G.discount = 1)
    (a : Assessment G.toExtensiveForm) (hone : IsSequentialEquilibriumOneShot G a) :
    IsSequentialEquilibrium G a :=
  ⟨isSequentiallyRational_of_oneShot G hfd hpr hno_joint hsa hδ a hone.2 hone.1, hone.2⟩

end Econlib.GameTheory
