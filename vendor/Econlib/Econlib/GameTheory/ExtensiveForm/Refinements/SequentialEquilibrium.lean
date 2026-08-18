/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.PBE

/-!
# Sequential equilibrium (Kreps-Wilson 1982)

A sequential equilibrium is a sequentially rational assessment that is **consistent** in the sense
of Kreps–Wilson: Every belief is the pointwise limit of the Bayesian posteriors induced by a
sequence of totally mixed behavioral strategies whose behavioral choice probabilities converge to
those of the equilibrium strategy. Event-level step-probability convergence is then derived from
behavioral convergence. Sequential equilibrium implies perfect Bayesian equilibrium.

## Main definitions

* `HasConsistentBeliefs`: Kreps-Wilson consistency of an assessment.
* `IsSequentialEquilibrium`: Sequential equilibrium predicate (full sequential rationality).
* `IsSequentialEquilibriumOneShot`: The one-shot variant characterized by `seqEqPred`.

## Main statements

* `finitePrefixProbFrom_tendsto`: Finite-prefix probabilities are continuous in step probabilities.
* `isBayesConsistent_of_hasConsistentBeliefs`: Kreps–Wilson consistency implies Bayes consistency.
* `IsPerfectBayesianEquilibrium_of_IsSequentialEquilibrium`: Sequential equilibrium implies perfect
  Bayesian equilibrium.

## References

* Kreps, David M., and Robert Wilson. 1982. “Sequential Equilibria.” *Econometrica* 50 (4): 863.
  [https://doi.org/10.2307/1912767](https://doi.org/10.2307/1912767).

## Tags

extensive form, sequential equilibrium, perfect bayesian equilibrium
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

/-- Coordinatewise convergence of behavioral strategies.

This is the behavioral-strategy convergence used in Kreps-Wilson consistency: Every information-set
simplex coordinate of `σseq n` converges to the corresponding coordinate of `σ`. Event-level
transition convergence is derived from this below; it is not the primitive condition, because
multiple choices may emit the same public event. -/
def ExtensiveForm.BehavioralStrategy.Tendsto {G : ExtensiveForm I E}
    (σseq : ℕ → G.BehavioralStrategy) (σ : G.BehavioralStrategy) : Prop :=
  ∀ (i : I) (obs : G.info.Obs i) (c : G.info.iChoiceType i obs),
    Filter.Tendsto (fun n => (σseq n i obs).val c) Filter.atTop
      (nhds ((σ i obs).val c))

lemma behavioralStrategy_tendsto_playerBehavior_val {G : ExtensiveForm I E}
    {σseq : ℕ → G.BehavioralStrategy} {σ : G.BehavioralStrategy}
    (hσ : ExtensiveForm.BehavioralStrategy.Tendsto σseq σ)
    {h : List E} {n : PlayerNode I E} (hnk : G.tree.nodeKind h = .player n)
    (c : n.Choice) :
    Filter.Tendsto (fun m => ((σseq m).playerBehavior h hnk).val c) Filter.atTop
      (nhds ((σ.playerBehavior h hnk).val c)) := by
  have hm : (G.tree.nodeKind h).movesAt n.mover := by rw [hnk]; rfl
  have hcompat : (G.tree.nodeKind h).iChoiceTypeAt n.mover hm =
      G.info.iChoiceType n.mover (G.info.observe n.mover h) :=
    G.iChoice_compatible n.mover h hm
  have hbridge : (G.tree.nodeKind h).iChoiceTypeAt n.mover hm = n.Choice := by
    clear hcompat
    revert hm
    rw [hnk]
    intro _
    rfl
  have hchoice : n.Choice = G.info.iChoiceType n.mover (G.info.observe n.mover h) :=
    hbridge.symm.trans hcompat
  have hseq : ∀ m : ℕ, ((σseq m).playerBehavior h hnk).val c =
      (σseq m n.mover (G.info.observe n.mover h)).val (hchoice ▸ c) := by
    intro m
    exact stdSimplex.heq_val hchoice ((σseq m).playerBehavior h hnk)
      (σseq m n.mover (G.info.observe n.mover h))
      ((cast_heq _ _).trans ((σseq m).atHistory_player_heq hnk)) c
  have hlim : (σ.playerBehavior h hnk).val c =
      (σ n.mover (G.info.observe n.mover h)).val (hchoice ▸ c) :=
    stdSimplex.heq_val hchoice (σ.playerBehavior h hnk)
      (σ n.mover (G.info.observe n.mover h))
      ((cast_heq _ _).trans (σ.atHistory_player_heq hnk)) c
  simpa only [hseq, hlim] using hσ n.mover (G.info.observe n.mover h) (hchoice ▸ c)

lemma behavioralStrategy_tendsto_jointBehavior_val {G : ExtensiveForm I E}
    {σseq : ℕ → G.BehavioralStrategy} {σ : G.BehavioralStrategy}
    (hσ : ExtensiveForm.BehavioralStrategy.Tendsto σseq σ)
    {h : List E} {n : JointNode I E} (hnk : G.tree.nodeKind h = .joint n)
    (a : n.Active) (c : n.Choice a) :
    Filter.Tendsto (fun m => ((σseq m).jointBehavior h hnk a).val c) Filter.atTop
      (nhds ((σ.jointBehavior h hnk a).val c)) := by
  let i : I := n.player a
  -- Each active player's local choice type at `n` matches their information-set choice type.
  have hchoiceAt : ∀ a' : n.Active,
      n.Choice a' = G.info.iChoiceType (n.player a') (G.info.observe (n.player a') h) := by
    intro a'
    have hm' : (G.tree.nodeKind h).movesAt (n.player a') := by rw [hnk]; exact ⟨a', rfl⟩
    have hcompat' : (G.tree.nodeKind h).iChoiceTypeAt (n.player a') hm' =
        G.info.iChoiceType (n.player a') (G.info.observe (n.player a') h) :=
      G.iChoice_compatible (n.player a') h hm'
    have hbridge' : (G.tree.nodeKind h).iChoiceTypeAt (n.player a') hm' = n.Choice a' := by
      clear hcompat'
      revert hm'
      rw [hnk]
      intro hm''
      change n.Choice (n.iPosition (n.player a') hm'') = n.Choice a'
      congr 1
      apply n.player_injective
      rw [n.iPosition_player (n.player a') hm'']
    exact hbridge'.symm.trans hcompat'
  have hchoice : n.Choice a = G.info.iChoiceType i (G.info.observe i h) := hchoiceAt a
  -- Both `σseq m` and `σ` reduce their joint behavior at `a` to player `i`'s info-set coordinate;
  -- transport the value across `hchoice`. The transport is identical for either strategy, so we
  -- prove it once for a generic `τ`.
  have key : ∀ τ : G.BehavioralStrategy,
      (τ.jointBehavior h hnk a).val c = (τ i (G.info.observe i h)).val (hchoice ▸ c) := by
    intro τ
    have hfun : HEq (τ.jointBehavior h hnk)
        (fun a : n.Active => τ (n.player a) (G.info.observe (n.player a) h)) :=
      (cast_heq _ _).trans (τ.atHistory_joint_heq hnk)
    have hs : HEq (τ.jointBehavior h hnk a)
        ((fun a : n.Active => τ (n.player a) (G.info.observe (n.player a) h)) a) :=
      dcongr_heq (a₁ := a) (a₂ := a) HEq.rfl
        (fun a₁ a₂ ha => by
          cases eq_of_heq ha
          exact stdSimplex.coeSort_eq (hchoiceAt a₁))
        (fun _ _ => hfun)
    exact stdSimplex.heq_val hchoice (τ.jointBehavior h hnk a)
      (τ i (G.info.observe i h)) hs c
  simpa only [fun m => key (σseq m), key σ] using hσ i (G.info.observe i h) (hchoice ▸ c)

variable [DecidableEq E]

/-- Behavioral-strategy convergence implies convergence of the emitted-event one-step probabilities
used by the reach and belief tower. This lemma is intentionally derived rather than part of
`HasConsistentBeliefs`: `stepProb` aggregates all choices in an `emit` fiber, while Kreps-Wilson
consistency is about convergence of behavioral choice probabilities. -/
lemma ExtensiveForm.BehavioralStrategy.Tendsto.stepProb {G : ExtensiveForm I E}
    {σseq : ℕ → G.BehavioralStrategy} {σ : G.BehavioralStrategy}
    (hσ : ExtensiveForm.BehavioralStrategy.Tendsto σseq σ) :
    ∀ (h : List E) (e : E),
      Filter.Tendsto (fun n => G.stepProb (σseq n) h e) Filter.atTop
        (nhds (G.stepProb σ h e)) := by
  intro h e
  rcases hk : G.tree.nodeKind h with payoff | n | n | n | n
  · rw [G.stepProb_of_terminal σ hk e]
    simp only [fun m => G.stepProb_of_terminal (σseq m) hk e]
    exact tendsto_const_nhds
  · rw [G.stepProb_player σ hk e]
    simp only [fun m => G.stepProb_player (σseq m) hk e]
    refine tendsto_finset_sum _ (fun c _ => ?_)
    by_cases hc : n.emit c = e
    · simp only [hc, if_true]
      exact behavioralStrategy_tendsto_playerBehavior_val hσ hk c
    · simp only [hc, if_false]
      exact tendsto_const_nhds
  · rw [G.stepProb_joint σ hk e]
    simp only [fun m => G.stepProb_joint (σseq m) hk e]
    refine tendsto_finset_sum _ (fun c _ => ?_)
    by_cases hc : n.emit c = e
    · simp only [hc, if_true]
      refine tendsto_finset_prod _ (fun a _ => ?_)
      exact behavioralStrategy_tendsto_jointBehavior_val hσ hk a (c a)
    · simp only [hc, if_false]
      exact tendsto_const_nhds
  · rw [G.stepProb_of_chanceFinite σ hk e]
    simp only [fun m => G.stepProb_of_chanceFinite (σseq m) hk e]
    exact tendsto_const_nhds
  · unfold ExtensiveForm.stepProb
    rw [NodeKind.eventProb_cast hk (σ.atHistory h) e]
    simp only [fun m => NodeKind.eventProb_cast hk ((σseq m).atHistory h) e]
    exact tendsto_const_nhds

/-- Kreps–Wilson consistency of an assessment.

There exists a sequence `σseq` of totally mixed behavioral strategies such that:

* `σseq n` behavioral-strategy coordinates converge pointwise to those of `assess.strategy`;
* at every information set `(i, obs)` and every public history `h`, the assessment's belief
  `assess.beliefs.prob i obs h` is the limit of the Bayesian posteriors `bayesBeliefAt` computed
  under `σseq n`.

Reachability-completeness of the support under each `σseq n` — which the Kreps–Wilson requirement
needs, so the limiting posterior is the full-info-set posterior rather than a truncation — is not a
conjunct: It holds at the type level via `BeliefSystem.support_exhaustive` (every `IsReachable`
history of an info set is in its support), and a totally-mixed `σseq n` reaches exactly the
`IsReachable` histories.

Bayes consistency of the assessment on positive-probability information sets follows from this
limit condition because behavioral-coordinate convergence implies continuity of the emitted-event
step-probability profile; see `ExtensiveForm.BehavioralStrategy.Tendsto.stepProb`,
`bayesBeliefAt_tendsto_of_pos`, and `IsPerfectBayesianEquilibrium_of_IsSequentialEquilibrium`. -/
def HasConsistentBeliefs (G : ExtensiveForm I E) (assess : Assessment G) : Prop :=
  ∃ σseq : ℕ → G.BehavioralStrategy,
    (∀ n, G.IsTotallyMixed (σseq n)) ∧
    ExtensiveForm.BehavioralStrategy.Tendsto σseq assess.strategy ∧
    (∀ (i : I) (obs : G.info.Obs i) (h : List E),
      Filter.Tendsto (fun n => bayesBeliefAt G (σseq n) assess.beliefs i obs h)
        Filter.atTop (nhds (assess.beliefs.prob i obs h)))

/-- Sequential equilibrium (Kreps–Wilson 1982): (full) sequential rationality of the assessment
plus Kreps–Wilson consistency of the belief system. -/
structure IsSequentialEquilibrium (G : ExtensiveGame I E) (assess : Assessment G.toExtensiveForm) :
    Prop where
  /-- The assessment is (fully) sequentially rational. -/
  sequentiallyRational : IsSequentiallyRational G assess
  /-- The belief system is Kreps–Wilson consistent. -/
  consistentBeliefs : HasConsistentBeliefs G.toExtensiveForm assess

/-- One-shot sequential equilibrium: One-shot sequential rationality plus Kreps–Wilson consistency.
This is the predicate characterized by the `seqEqPred` refinement scaffold; it coincides with
`IsSequentialEquilibrium` under perfect recall and finite depth (or discounting) via the one-shot
deviation principle — its Kreps–Wilson consistency supplies the belief consistency that principle
needs. -/
structure IsSequentialEquilibriumOneShot (G : ExtensiveGame I E)
    (assess : Assessment G.toExtensiveForm) : Prop where
  /-- The assessment is one-shot sequentially rational. -/
  sequentiallyRationalOneShot : IsSequentiallyRationalOneShot G assess
  /-- The belief system is Kreps–Wilson consistent. -/
  consistentBeliefs : HasConsistentBeliefs G.toExtensiveForm assess

/-- Continuity of `ExtensiveForm.finitePrefixProbFrom` in the step-probability profile. Given
pointwise convergence of step probabilities, the finite-prefix probability of any continuation
suffix starting from any history converges. -/
lemma finitePrefixProbFrom_tendsto (G : ExtensiveForm I E)
    (σseq : ℕ → G.BehavioralStrategy) (σ : G.BehavioralStrategy)
    (hstep : ∀ h e, Filter.Tendsto (fun n => G.stepProb (σseq n) h e) Filter.atTop
                       (nhds (G.stepProb σ h e))) :
    ∀ (start hist : List E),
      Filter.Tendsto (fun n => G.finitePrefixProbFrom (σseq n) start hist)
        Filter.atTop (nhds (G.finitePrefixProbFrom σ start hist)) := by
  intro start hist
  induction hist generalizing start with
  | nil => simpa only [ExtensiveForm.finitePrefixProbFrom_nil] using tendsto_const_nhds
  | cons e suffix ih =>
    simpa only [ExtensiveForm.finitePrefixProbFrom_cons]
      using (hstep start e).mul (ih (start ++ [e]))

/-- Continuity of `reachProb` in the step-probability profile. -/
lemma reachProb_tendsto (G : ExtensiveForm I E)
    (σseq : ℕ → G.BehavioralStrategy) (σ : G.BehavioralStrategy)
    (hstep : ∀ h e, Filter.Tendsto (fun n => G.stepProb (σseq n) h e) Filter.atTop
                       (nhds (G.stepProb σ h e)))
    (hist : List E) :
    Filter.Tendsto (fun n => reachProb G (σseq n) hist) Filter.atTop
      (nhds (reachProb G σ hist)) :=
  finitePrefixProbFrom_tendsto G σseq σ hstep [] hist

/-- Continuity of `infoSetProb` in the step-probability profile. -/
lemma infoSetProb_tendsto (G : ExtensiveForm I E) (μ : BeliefSystem G)
    (σseq : ℕ → G.BehavioralStrategy) (σ : G.BehavioralStrategy)
    (hstep : ∀ h e, Filter.Tendsto (fun n => G.stepProb (σseq n) h e) Filter.atTop
                       (nhds (G.stepProb σ h e)))
    (i : I) (obs : G.info.Obs i) :
    Filter.Tendsto (fun n => infoSetProb G (σseq n) μ i obs) Filter.atTop
      (nhds (infoSetProb G σ μ i obs)) := by
  unfold infoSetProb
  exact tendsto_finset_sum _ (fun x _ => reachProb_tendsto G σseq σ hstep x.1)

/-- Continuity of `bayesBeliefAt` at any limit strategy where the represented information set has
positive reach probability. -/
lemma bayesBeliefAt_tendsto_of_pos (G : ExtensiveForm I E) (μ : BeliefSystem G)
    (σseq : ℕ → G.BehavioralStrategy) (σ : G.BehavioralStrategy)
    (hstep : ∀ h e, Filter.Tendsto (fun n => G.stepProb (σseq n) h e) Filter.atTop
                       (nhds (G.stepProb σ h e)))
    (i : I) (obs : G.info.Obs i) (hpos : 0 < infoSetProb G σ μ i obs) (hist : List E) :
    Filter.Tendsto (fun n => bayesBeliefAt G (σseq n) μ i obs hist) Filter.atTop
      (nhds (bayesBeliefAt G σ μ i obs hist)) := by
  classical
  -- Off the positive-reach branch, `bayesBeliefAt` is identically zero for every strategy `τ`, so
  -- the sequence and its claimed limit both vanish. This `tendstoZero` packages that tail; the two
  -- vanishing cases (not in support, not in info set) supply the per-strategy zero proof.
  have tendstoZero : (∀ τ : G.BehavioralStrategy, bayesBeliefAt G τ μ i obs hist = 0) →
      Filter.Tendsto (fun n => bayesBeliefAt G (σseq n) μ i obs hist) Filter.atTop
        (nhds (bayesBeliefAt G σ μ i obs hist)) := fun hzero => by
    simp_rw [fun n => hzero (σseq n), hzero σ]; exact tendsto_const_nhds
  by_cases hin : (G.tree.nodeKind hist).movesAt i ∧ G.info.observe i hist = obs
  · by_cases hmem : (⟨hist, hin⟩ : G.InfoSet i obs) ∈ μ.support i obs
    · -- In info set, in support: bayesBeliefAt = reachProb / infoSetProb under positivity.
      have hI := infoSetProb_tendsto G μ σseq σ hstep i obs
      have hR := reachProb_tendsto G σseq σ hstep hist
      have hev : ∀ᶠ n in Filter.atTop, 0 < infoSetProb G (σseq n) μ i obs :=
        hI.eventually (eventually_gt_nhds hpos)
      have hrhs : bayesBeliefAt G σ μ i obs hist
          = reachProb G σ hist / infoSetProb G σ μ i obs := by
        unfold bayesBeliefAt
        rw [dif_pos hin, if_pos hmem, dif_pos hpos]
      rw [hrhs]
      have htdiv : Filter.Tendsto
          (fun n => reachProb G (σseq n) hist / infoSetProb G (σseq n) μ i obs)
          Filter.atTop
          (nhds (reachProb G σ hist / infoSetProb G σ μ i obs)) :=
        hR.div hI hpos.ne'
      apply htdiv.congr'
      filter_upwards [hev] with n hn
      unfold bayesBeliefAt
      rw [dif_pos hin, if_pos hmem, dif_pos hn]
    · -- In info set, not in support: bayesBeliefAt is identically zero.
      exact tendstoZero fun τ => by unfold bayesBeliefAt; rw [dif_pos hin, if_neg hmem]
  · -- Not in info set at all: bayesBeliefAt is identically zero.
    exact tendstoZero fun τ => by unfold bayesBeliefAt; rw [dif_neg hin]

/-- **Kreps–Wilson consistency implies Bayes consistency.** On positive-probability information
sets, the limit condition `HasConsistentBeliefs` forces the belief to equal the Bayesian posterior,
by uniqueness of limits in ℝ. -/
theorem isBayesConsistent_of_hasConsistentBeliefs (G : ExtensiveGame I E)
    (assess : Assessment G.toExtensiveForm)
    (hcons : HasConsistentBeliefs G.toExtensiveForm assess) :
    IsBayesConsistent G.toExtensiveForm assess := by
  obtain ⟨σseq, _hmix, hstrategy, hbel⟩ := hcons
  have hstep := hstrategy.stepProb
  intro i obs hpos hist
  exact tendsto_nhds_unique (hbel i obs hist)
    (bayesBeliefAt_tendsto_of_pos (G := G.toExtensiveForm) (μ := assess.beliefs)
      (σseq := σseq) (σ := assess.strategy) hstep i obs hpos hist)

/-- Every sequential equilibrium is a PBE. The non-trivial half is that Kreps–Wilson limit
consistency of the belief system implies Bayes consistency on positive-probability information sets
(`isBayesConsistent_of_hasConsistentBeliefs`). -/
theorem
IsPerfectBayesianEquilibrium_of_IsSequentialEquilibrium (G : ExtensiveGame I E)
    (assess : Assessment G.toExtensiveForm)
    (hseq : IsSequentialEquilibrium G assess) : IsPerfectBayesianEquilibrium G assess :=
  ⟨hseq.1, isBayesConsistent_of_hasConsistentBeliefs G assess hseq.2⟩

/-! ## SeqEq as an `EquilibriumRefinement`

Sequential equilibrium uses the same deviation half as PBE; only the validity predicate is
strengthened from Bayes consistency to Kreps–Wilson consistency. So `seqEqPred` reuses `pbePred`'s
strategy/deviator/swap/value and overrides `valid`. -/

/-- The sequential-equilibrium refinement: Same deviation half as `pbePred`, validity is
Kreps–Wilson consistency. -/
def ExtensiveGame.seqEqPred (G : ExtensiveGame I E) : EquilibriumRefinement := { G.pbePred with
valid := HasConsistentBeliefs G.toExtensiveForm }

/-- `IsSequentialEquilibriumOneShot` is exactly `IsRefinedEquilibrium` of `seqEqPred` (whose
deviation half, inherited from `pbePred`, fixes all but one information-set coordinate). -/
theorem IsSequentialEquilibriumOneShot_iff_seqEqPred (G : ExtensiveGame I E)
    (a : Assessment G.toExtensiveForm) :
    IsSequentialEquilibriumOneShot G a ↔ G.seqEqPred.IsRefinedEquilibrium a := by
  constructor
  · rintro ⟨hSR, hCons⟩
    refine ⟨hCons, ?_⟩
    rintro ⟨i, obs⟩ ⟨s', b'⟩ ⟨hbeliefs, hdev⟩
    subst hbeliefs
    exact hSR i obs s' hdev
  · rintro ⟨hCons, hIsEq⟩
    exact ⟨fun i obs σ' hdev => hIsEq ⟨i, obs⟩ ⟨σ', a.beliefs⟩ ⟨rfl, hdev⟩, hCons⟩

end Econlib.GameTheory
