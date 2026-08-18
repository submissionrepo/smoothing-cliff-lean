/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Repeated.OneShotDeviation

/-!
# Grim trigger as a subgame-perfect equilibrium

This file lifts the pure-action grim-trigger rule `RepeatedGame.grimTrigger` to a behavioral
`PublicStrategy` and proves it is a subgame-perfect equilibrium whenever the punishment profile is
a stage-game Nash equilibrium and the discount factor is calibrated so that no one-shot deviation
on the cooperative path pays.

The argument is the textbook one-shot deviation check (Fudenberg and Tirole 1991). A public history
is **clean** when every realized profile so far is the cooperative profile `cooperate`; grim
trigger plays `cooperate` on clean histories and reverts to the absorbing punishment `punish`
forever after any deviation. Two facts close the equilibrium:

* on a clean history, the deviator's one-shot gain is offset by permanent reversion, which is
  exactly the calibration hypothesis
  `(1 - δ)·payoff i (update cooperate i aᵢ) + δ·payoff i punish ≤
  payoff i cooperate`;
* on a dirty history, grim trigger plays the stage Nash `punish` forever, so deviating cannot pay —
  this is `IsNash punish`.

## Main definitions

* `RepeatedGame.pureStrategy`: The perfect-information behavioral lift of an arbitrary per-history
  pure-action rule (every player puts point mass on the prescribed action).
* `RepeatedGame.grimTriggerStrategy`: The grim-trigger public strategy, the `pureStrategy` lift of
  the `grimTrigger` rule.
* `RepeatedGame.IsClean`: A public history all of whose realized profiles equal `cooperate`.

## Main statements

* `RepeatedGame.continuationValue_grimTriggerStrategy_of_isClean` /
  `RepeatedGame.continuationValue_grimTriggerStrategy_of_not_isClean`: Grim trigger's continuation
  value is `payoff i cooperate` on clean histories and `payoff i punish` on dirty ones.
* `RepeatedGame.grimTrigger_noProfitableOneShotDeviation`: With a Nash punishment and a calibrated
  discount factor, no one-shot deviation against grim trigger pays.
* `RepeatedGame.grimTrigger_isSubgamePerfectEquilibrium`: Grim trigger is a subgame-perfect
  equilibrium, by the one-shot deviation principle.

## References

* Fudenberg, Drew, and Jean Tirole. 1993. *Game Theory*. The MIT Press.

## Tags

repeated games, grim trigger, Nash reversion, subgame perfect equilibrium, folk theorem
-/

@[expose] public noncomputable section

open BigOperators

namespace Econlib.GameTheory

namespace RepeatedGame

variable (R : RepeatedGame)

/-! ### Pure-action public strategies

Any per-history pure-action rule lifts to a behavioral `PublicStrategy` by placing point mass
on the prescribed action at every node. `grimTriggerStrategy` is the instance for the `grimTrigger`
rule. -/

/-- The per-history `Behavior` data of a pure-action rule: Every player places point mass on their
prescribed pure action. Every node of `R.toGameTree` is a joint node, so the target `Behavior` type
unfolds to `(i : R.stage.Player) → stdSimplex ℝ (R.stage.Action i)`. -/
def pureBehavior (rule : (i : R.stage.Player) → R.stage.PublicHistory → R.stage.Action i)
    (h : R.stage.PublicHistory) : (R.toGameTree.nodeKind h).Behavior :=
  fun i => stdSimplex.vertex (rule i h)

/-- The perfect-information public-strategy lift of a per-history pure-action rule, via
`BehavioralStrategy.ofPerfectInfo`. -/
def pureStrategy (rule : (i : R.stage.Player) → R.stage.PublicHistory → R.stage.Action i) :
    R.PublicStrategy :=
  ExtensiveForm.BehavioralStrategy.ofPerfectInfo (R.pureBehavior rule)

/-- The per-history accessor of a `pureStrategy` recovers the prescribed vertex. -/
lemma atHistory_pureStrategy
    (rule : (i : R.stage.Player) → R.stage.PublicHistory → R.stage.Action i)
    (i : R.stage.Player) (h : R.stage.PublicHistory) :
    R.atHistory (R.pureStrategy rule) i h = stdSimplex.vertex (rule i h) :=
  R.atHistory_ofPerfectInfo (R.pureBehavior rule) i h

/-- The raw lifted strategy value of a `pureStrategy` at `(j, obs)` is heterogeneously equal to the
prescribed vertex — the `ofPerfectInfo` round-trip stripped to the raw simplex. -/
lemma pureStrategy_apply_heq_vertex
    (rule : (i : R.stage.Player) → R.stage.PublicHistory → R.stage.Action i)
    (j : R.stage.Player) (obs : R.stage.PublicHistory) :
    HEq (R.pureStrategy rule j obs) (stdSimplex.vertex (S := ℝ) (rule j obs)) := by
  have hm : (R.toGameTree.nodeKind obs).movesAt j := ⟨j, rfl⟩
  have hpos : R.stageJointNode.iPosition j hm = j :=
    R.stageJointNode.iPosition_player j hm
  -- `j` moves at every joint node, so `ofPerfectInfo` takes the `dif_pos` branch.
  have hofp : R.pureStrategy rule j obs =
      simplexTransport ((NodeKind.iChoiceTypeAt'_eq_iChoiceTypeAt _ _ hm).symm)
        ((R.toGameTree.nodeKind obs).iLocalBehavior j hm (R.pureBehavior rule obs)) := by
    unfold pureStrategy ExtensiveForm.BehavioralStrategy.ofPerfectInfo
    split
    · rfl
    · exact absurd hm (by assumption)
  have hilb : HEq ((R.toGameTree.nodeKind obs).iLocalBehavior j hm (R.pureBehavior rule obs))
      (R.pureBehavior rule obs j) :=
    congr_arg_heq (R.pureBehavior rule obs) hpos
  rw [hofp]
  exact (simplexTransport_heq _ _).trans hilb

/-- Two pure-action rules that agree at player `j`'s action at `obs` lift to raw strategy values
that agree there. This is exactly what the info-set-deviation predicate compares, so it is the
bridge for constructing pure deviations from grim trigger. -/
lemma pureStrategy_apply_eq_of_apply_eq
    (rule₁ rule₂ : (i : R.stage.Player) → R.stage.PublicHistory → R.stage.Action i)
    (j : R.stage.Player) (obs : R.stage.PublicHistory) (hagree : rule₁ j obs = rule₂ j obs) :
    R.pureStrategy rule₁ j obs = R.pureStrategy rule₂ j obs := by
  refine eq_of_heq ((R.pureStrategy_apply_heq_vertex rule₁ j obs).trans ?_)
  rw [hagree]
  exact (R.pureStrategy_apply_heq_vertex rule₂ j obs).symm

/-- The stage-profile mass under a `pureStrategy` is the indicator of the prescribed pure profile:
The degenerate product of vertices concentrates on `fun j => rule j h`. -/
lemma stageProfileProb_pureStrategy
    (rule : (i : R.stage.Player) → R.stage.PublicHistory → R.stage.Action i)
    (h : R.stage.PublicHistory) (a : R.stage.ActionProfile) :
    R.stageProfileProb (R.pureStrategy rule) h a =
      if a = (fun j => rule j h) then (1 : ℝ) else 0 := by
  classical
  unfold stageProfileProb
  have hfactor : ∀ j : R.stage.Player,
      (R.atHistory (R.pureStrategy rule) j h) (a j) = if a j = rule j h then (1 : ℝ) else 0 := by
    intro j
    rw [R.atHistory_pureStrategy rule j h]
    by_cases hj : a j = rule j h
    · rw [if_pos hj]; exact stdSimplex.vertex_apply_eq hj.symm
    · rw [if_neg hj]; exact stdSimplex.vertex_apply_ne (fun heq => hj heq.symm)
  simp only [hfactor]
  by_cases ha : a = (fun j => rule j h)
  · rw [if_pos ha]; exact Finset.prod_eq_one (fun j _ => by rw [if_pos (congrFun ha j)])
  · rw [if_neg ha]
    obtain ⟨j, hj⟩ : ∃ j, a j ≠ rule j h := by
      by_contra hcon; push Not at hcon; exact ha (funext hcon)
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj])

/-! ### Clean histories

A public history is **clean** when no deviation has been observed: Every realized profile
equals the cooperative profile. Cleanliness is preserved by appending `cooperate`; dirtiness is
absorbing. -/

/-- A public history is **clean** for the cooperative profile `cooperate` when every realized stage
profile equals `cooperate` — no deviation has been observed yet. -/
def IsClean (cooperate : R.stage.ActionProfile) (h : R.stage.PublicHistory) : Prop :=
  ∀ a ∈ h, a = cooperate

variable {R}

/-- The empty history is clean. -/
lemma isClean_nil (cooperate : R.stage.ActionProfile) :
    R.IsClean cooperate ([] : R.stage.PublicHistory) :=
  fun _ ha => by simp at ha

/-- Cleanliness is preserved by appending the cooperative profile. -/
lemma isClean_append {cooperate : R.stage.ActionProfile} {h : R.stage.PublicHistory}
    (hclean : R.IsClean cooperate h) : R.IsClean cooperate (h ++ [cooperate]) := by
  intro a ha
  rcases List.mem_append.mp ha with hmem | hmem
  · exact hclean a hmem
  · rw [List.mem_singleton.mp hmem]

/-- Dirtiness is absorbing: Any one-step extension of a dirty history is dirty. -/
lemma not_isClean_append {cooperate : R.stage.ActionProfile} {h : R.stage.PublicHistory}
    (hdirty : ¬ R.IsClean cooperate h) (a : R.stage.ActionProfile) :
    ¬ R.IsClean cooperate (h ++ [a]) :=
  fun hclean => hdirty (fun b hb => hclean b (List.mem_append.mpr (Or.inl hb)))

/-! ### The grim-trigger rule on clean and dirty histories -/

/-- On a clean history grim trigger prescribes the cooperative action, for every player. -/
lemma grimTrigger_of_isClean {cooperate punish : R.stage.ActionProfile}
    {h : R.stage.PublicHistory} (hclean : R.IsClean cooperate h) (i : R.stage.Player) :
    R.grimTrigger cooperate punish i h = cooperate i := by
  unfold grimTrigger
  split
  · rfl
  · exact absurd hclean (by assumption)

/-- On a dirty history grim trigger prescribes the punishment action, for every player. -/
lemma grimTrigger_of_not_isClean {cooperate punish : R.stage.ActionProfile}
    {h : R.stage.PublicHistory} (hdirty : ¬ R.IsClean cooperate h) (i : R.stage.Player) :
    R.grimTrigger cooperate punish i h = punish i := by
  unfold grimTrigger
  split
  · exact absurd (by assumption) hdirty
  · rfl

/-- The profile grim trigger prescribes at a clean history is the cooperative profile. -/
lemma grimTriggerProfile_of_isClean {cooperate punish : R.stage.ActionProfile}
    {h : R.stage.PublicHistory} (hclean : R.IsClean cooperate h) :
    (fun j => R.grimTrigger cooperate punish j h) = cooperate :=
  funext fun j => R.grimTrigger_of_isClean hclean j

/-- The profile grim trigger prescribes at a dirty history is the punishment profile. -/
lemma grimTriggerProfile_of_not_isClean {cooperate punish : R.stage.ActionProfile}
    {h : R.stage.PublicHistory} (hdirty : ¬ R.IsClean cooperate h) :
    (fun j => R.grimTrigger cooperate punish j h) = punish :=
  funext fun j => R.grimTrigger_of_not_isClean hdirty j

variable (R)

/-! ### The grim-trigger public strategy -/

/-- **Grim trigger** as a public strategy: The `pureStrategy` lift of the grim-trigger pure rule.
Play `cooperate` while the public history is clean, and revert to `punish` forever after any
deviation. -/
def grimTriggerStrategy (cooperate punish : R.stage.ActionProfile) : R.PublicStrategy :=
  R.pureStrategy (R.grimTrigger cooperate punish)

/-- The per-history accessor of grim trigger recovers the prescribed grim-trigger vertex. -/
lemma atHistory_grimTriggerStrategy (cooperate punish : R.stage.ActionProfile)
    (i : R.stage.Player) (h : R.stage.PublicHistory) :
    R.atHistory (R.grimTriggerStrategy cooperate punish) i h
      = stdSimplex.vertex (R.grimTrigger cooperate punish i h) :=
  R.atHistory_pureStrategy (R.grimTrigger cooperate punish) i h

/-- The grim-trigger stage-profile mass is the indicator of the prescribed grim-trigger profile. -/
lemma stageProfileProb_grimTriggerStrategy (cooperate punish : R.stage.ActionProfile)
    (h : R.stage.PublicHistory) (a : R.stage.ActionProfile) :
    R.stageProfileProb (R.grimTriggerStrategy cooperate punish) h a =
      if a = (fun j => R.grimTrigger cooperate punish j h) then (1 : ℝ) else 0 :=
  R.stageProfileProb_pureStrategy (R.grimTrigger cooperate punish) h a

/-! ### Stage and continuation payoffs along the grim-trigger path -/

/-- The grim-trigger stage payoff at a clean history is the cooperative stage payoff. -/
lemma stagePayoff_grimTriggerStrategy_of_isClean {cooperate punish : R.stage.ActionProfile}
    {h : R.stage.PublicHistory} (hclean : R.IsClean cooperate h) (i : R.stage.Player) :
    R.stagePayoff (R.grimTriggerStrategy cooperate punish) h i = R.stage.payoff i cooperate := by
  rw [R.stagePayoff_eq_sum_stageProfileProb]
  simp only [stageProfileProb_grimTriggerStrategy, ite_mul, one_mul, zero_mul]
  rw [grimTriggerProfile_of_isClean hclean]
  exact (Finset.sum_eq_single_of_mem cooperate (Finset.mem_univ _)
    (fun b _ hb => if_neg hb)).trans (if_pos rfl)

/-- The grim-trigger stage payoff at a dirty history is the punishment stage payoff. -/
lemma stagePayoff_grimTriggerStrategy_of_not_isClean {cooperate punish : R.stage.ActionProfile}
    {h : R.stage.PublicHistory} (hdirty : ¬ R.IsClean cooperate h) (i : R.stage.Player) :
    R.stagePayoff (R.grimTriggerStrategy cooperate punish) h i = R.stage.payoff i punish := by
  rw [R.stagePayoff_eq_sum_stageProfileProb]
  simp only [stageProfileProb_grimTriggerStrategy, ite_mul, one_mul, zero_mul]
  rw [grimTriggerProfile_of_not_isClean hdirty]
  exact (Finset.sum_eq_single_of_mem punish (Finset.mem_univ _)
    (fun b _ hb => if_neg hb)).trans (if_pos rfl)

/-- Along the grim-trigger path from a clean history, every period's expected payoff is the
cooperative stage payoff: Cleanliness is preserved by appending `cooperate`. -/
lemma periodExpectedPayoff_grimTriggerStrategy_of_isClean
    (cooperate punish : R.stage.ActionProfile) (i : R.stage.Player) :
    ∀ (t : ℕ) (h : R.stage.PublicHistory), R.IsClean cooperate h →
      R.periodExpectedPayoff (R.grimTriggerStrategy cooperate punish) h t i =
        R.stage.payoff i cooperate := by
  intro t
  induction t with
  | zero =>
    intro h hclean
    rw [R.periodExpectedPayoff_zero, R.stagePayoff_grimTriggerStrategy_of_isClean hclean]
  | succ t ih =>
    intro h hclean
    rw [R.periodExpectedPayoff_succ]
    simp only [stageProfileProb_grimTriggerStrategy, ite_mul, one_mul, zero_mul]
    rw [grimTriggerProfile_of_isClean hclean]
    refine (Finset.sum_eq_single_of_mem cooperate (Finset.mem_univ _)
      (fun b _ hb => if_neg hb)).trans ?_
    rw [if_pos rfl]
    exact ih (h ++ [cooperate]) (isClean_append hclean)

/-- Along the grim-trigger path from a dirty history, every period's expected payoff is the
punishment stage payoff: Dirtiness is absorbing. -/
lemma periodExpectedPayoff_grimTriggerStrategy_of_not_isClean
    (cooperate punish : R.stage.ActionProfile) (i : R.stage.Player) :
    ∀ (t : ℕ) (h : R.stage.PublicHistory), ¬ R.IsClean cooperate h →
      R.periodExpectedPayoff (R.grimTriggerStrategy cooperate punish) h t i =
        R.stage.payoff i punish := by
  intro t
  induction t with
  | zero =>
    intro h hdirty
    rw [R.periodExpectedPayoff_zero, R.stagePayoff_grimTriggerStrategy_of_not_isClean hdirty]
  | succ t ih =>
    intro h hdirty
    rw [R.periodExpectedPayoff_succ]
    simp only [stageProfileProb_grimTriggerStrategy, ite_mul, one_mul, zero_mul]
    rw [grimTriggerProfile_of_not_isClean hdirty]
    refine (Finset.sum_eq_single_of_mem punish (Finset.mem_univ _)
      (fun b _ hb => if_neg hb)).trans ?_
    rw [if_pos rfl]
    exact ih (h ++ [punish]) (not_isClean_append hdirty punish)

/-- A strategy whose every period-`t` expected payoff is the constant `K` has continuation value
`K`, at any discount factor: `(1 - δ) ∑' δᵗ·K = K`. -/
lemma continuationValue_of_const {σ : R.PublicStrategy} {h : R.stage.PublicHistory}
    (i : R.stage.Player) (K : ℝ) (hconst : ∀ t : ℕ, R.periodExpectedPayoff σ h t i = K) :
    R.continuationValue σ h i = K := by
  unfold continuationValue
  simp only [hconst]
  rw [tsum_mul_right, tsum_geometric_of_lt_one R.discount_nonneg R.discount_lt_one]
  have h1mδ : (1 : ℝ) - R.discount ≠ 0 := by linarith [R.discount_lt_one]
  field_simp

/-- On a clean history, grim trigger plays `cooperate` forever, so its continuation value is the
cooperative stage payoff. -/
lemma continuationValue_grimTriggerStrategy_of_isClean {cooperate punish : R.stage.ActionProfile}
    (h : R.stage.PublicHistory) (hclean : R.IsClean cooperate h) (i : R.stage.Player) :
    R.continuationValue (R.grimTriggerStrategy cooperate punish) h i = R.stage.payoff i cooperate :=
  R.continuationValue_of_const i (R.stage.payoff i cooperate)
    (fun t => R.periodExpectedPayoff_grimTriggerStrategy_of_isClean cooperate punish i t h hclean)

/-- On a dirty history, grim trigger plays the absorbing punishment `punish` forever, so its
continuation value is the punishment stage payoff. -/
lemma continuationValue_grimTriggerStrategy_of_not_isClean
    {cooperate punish : R.stage.ActionProfile}
    (h : R.stage.PublicHistory) (hdirty : ¬ R.IsClean cooperate h) (i : R.stage.Player) :
    R.continuationValue (R.grimTriggerStrategy cooperate punish) h i = R.stage.payoff i punish :=
  R.continuationValue_of_const i (R.stage.payoff i punish)
    (fun t =>
      R.periodExpectedPayoff_grimTriggerStrategy_of_not_isClean cooperate punish i t h hdirty)

/-! ### The one-shot deviation check -/

/-- The expected value of a continuation functional `G` over stage profiles, under a one-shot
deviator `σ'` at history `h`: With every opponent `j ≠ i` fixed at the grim-trigger vertex, the
stage expectation reduces to a one-dimensional sum over the deviator's own actions against the
fixed grim-trigger profile. -/
private lemma grimTrigger_expand_sum {cooperate punish : R.stage.ActionProfile}
    (i : R.stage.Player) (h : R.stage.PublicHistory) (σ' : R.PublicStrategy)
    (hopp : ∀ j : R.stage.Player, j ≠ i →
      R.atHistory σ' j h = stdSimplex.vertex (R.grimTrigger cooperate punish j h))
    (G : R.stage.ActionProfile → ℝ) :
    (∑ c : R.stage.ActionProfile, R.stageProfileProb σ' h c * G c) =
      ∑ aᵢ : R.stage.Action i, (R.atHistory σ' i h) aᵢ *
        G (Function.update (fun j => R.grimTrigger cooperate punish j h) i aᵢ) :=
  R.stage.sum_prod_marginal_pin i (fun k => R.atHistory σ' k h)
    (fun j => R.grimTrigger cooperate punish j h) hopp G

/-- **No one-shot deviation against grim trigger is profitable**, provided the punishment profile
is a stage Nash equilibrium and the discount factor is calibrated so that, on the cooperative path,
the one-shot gain never exceeds the loss from permanent reversion. The check splits on whether the
history is clean:

* on clean histories the deviator faces cooperating opponents; the calibration hypothesis bounds
  the payoff of any pure deviation followed by reversion;
* on dirty histories grim trigger plays the absorbing stage Nash `punish`, so `IsNash punish` rules
  out any gain. -/
theorem grimTrigger_noProfitableOneShotDeviation {cooperate punish : R.stage.ActionProfile}
    (hpunish : R.stage.IsNash punish)
    (hcalib : ∀ (i : R.stage.Player) (aᵢ : R.stage.Action i),
      (1 - R.discount) * R.stage.payoff i (Function.update cooperate i aᵢ)
        + R.discount * R.stage.payoff i punish ≤ R.stage.payoff i cooperate) :
    R.NoProfitableOneShotDeviation (R.grimTriggerStrategy cooperate punish) := by
  intro i h σ' hdev
  -- Bellman one-step decomposition of the deviation's continuation value at `h`.
  rw [R.continuationValue_eq_step σ' h i]
  -- Locality: at every continuation of `h ++ [c]` the deviator already coincides with grim trigger,
  -- since those histories are strictly longer than `h`.
  have hsucc : ∀ c : R.stage.ActionProfile,
      R.continuationValue σ' (h ++ [c]) i =
        R.continuationValue (R.grimTriggerStrategy cooperate punish) (h ++ [c]) i := by
    intro c
    refine R.continuationValue_congr (h ++ [c]) i (fun j suffix => ?_)
    refine hdev j ((h ++ [c]) ++ suffix) (fun hcontra => ?_)
    have hlen : ((h ++ [c]) ++ suffix).length = h.length := by
      have hlists : (h ++ [c]) ++ suffix = h :=
        eq_of_heq (Sigma.mk.inj_iff.mp hcontra).2
      rw [hlists]
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen
    omega
  simp only [hsucc]
  -- The deviator's marginal at `h` is a distribution.
  have hμ_nonneg : ∀ aᵢ : R.stage.Action i, 0 ≤ (R.atHistory σ' i h) aᵢ :=
    (R.atHistory σ' i h).property.1
  have hμ_sum : ∑ aᵢ : R.stage.Action i, (R.atHistory σ' i h) aᵢ = 1 :=
    (R.atHistory σ' i h).property.2
  -- Off the deviator the strategy is still grim trigger, so opponents play the grim vertex at `h`.
  have hopp : ∀ j : R.stage.Player, j ≠ i →
      R.atHistory σ' j h = stdSimplex.vertex (R.grimTrigger cooperate punish j h) := by
    intro j hji
    have hσ'j : σ' j h = R.grimTriggerStrategy cooperate punish j h :=
      hdev j h (fun hcontra => hji (congrArg Sigma.fst hcontra))
    rw [← R.atHistory_grimTriggerStrategy cooperate punish j h]
    simp only [RepeatedGame.atHistory, hσ'j]
  rw [R.stagePayoff_eq_sum_stageProfileProb σ' h i]
  have h1mδ : 0 ≤ 1 - R.discount := by linarith [R.discount_lt_one]
  by_cases hclean : R.IsClean cooperate h
  · -- Clean: opponents cooperate; calibration bounds every pure deviation.
    rw [R.continuationValue_grimTriggerStrategy_of_isClean h hclean i,
      R.grimTrigger_expand_sum i h σ' hopp (R.stage.payoff i),
      R.grimTrigger_expand_sum i h σ' hopp
        (fun c => R.continuationValue (R.grimTriggerStrategy cooperate punish) (h ++ [c]) i),
      grimTriggerProfile_of_isClean hclean]
    -- Continuation after deviating to `aᵢ`: cooperative value if `aᵢ` keeps the history clean,
    -- punishment value otherwise.
    have hcont : ∀ aᵢ : R.stage.Action i,
        R.continuationValue (R.grimTriggerStrategy cooperate punish)
            (h ++ [Function.update cooperate i aᵢ]) i =
          if aᵢ = cooperate i then R.stage.payoff i cooperate else R.stage.payoff i punish := by
      intro aᵢ
      by_cases haᵢ : aᵢ = cooperate i
      · subst haᵢ
        rw [if_pos rfl, Function.update_eq_self]
        exact R.continuationValue_grimTriggerStrategy_of_isClean _ (isClean_append hclean) i
      · rw [if_neg haᵢ]
        refine R.continuationValue_grimTriggerStrategy_of_not_isClean _ (fun hclean' => haᵢ ?_) i
        have hmem : Function.update cooperate i aᵢ ∈ (h ++ [Function.update cooperate i aᵢ]) :=
          List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
        have hupd := congrFun (hclean' _ hmem) i
        rwa [Function.update_self] at hupd
    simp only [hcont]
    -- Combine into a single weighted sum and compare termwise against `payoff i cooperate`.
    have hcombine :
        (1 - R.discount) *
            ∑ aᵢ : R.stage.Action i, (R.atHistory σ' i h) aᵢ *
              R.stage.payoff i (Function.update cooperate i aᵢ)
          + R.discount *
            ∑ aᵢ : R.stage.Action i, (R.atHistory σ' i h) aᵢ *
              (if aᵢ = cooperate i then R.stage.payoff i cooperate else R.stage.payoff i punish)
        = ∑ aᵢ : R.stage.Action i, (R.atHistory σ' i h) aᵢ *
            ((1 - R.discount) * R.stage.payoff i (Function.update cooperate i aᵢ)
              + R.discount *
                (if aᵢ = cooperate i then R.stage.payoff i cooperate
                  else R.stage.payoff i punish)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun aᵢ _ => by ring)
    rw [hcombine]
    calc ∑ aᵢ : R.stage.Action i, (R.atHistory σ' i h) aᵢ *
            ((1 - R.discount) * R.stage.payoff i (Function.update cooperate i aᵢ)
              + R.discount *
                (if aᵢ = cooperate i then R.stage.payoff i cooperate
                  else R.stage.payoff i punish))
        ≤ ∑ aᵢ : R.stage.Action i, (R.atHistory σ' i h) aᵢ * R.stage.payoff i cooperate := by
          refine Finset.sum_le_sum (fun aᵢ _ => mul_le_mul_of_nonneg_left ?_ (hμ_nonneg aᵢ))
          by_cases haᵢ : aᵢ = cooperate i
          · subst haᵢ
            rw [if_pos rfl, Function.update_eq_self]
            have hid : (1 - R.discount) * R.stage.payoff i cooperate
                + R.discount * R.stage.payoff i cooperate = R.stage.payoff i cooperate := by ring
            linarith [hid]
          · rw [if_neg haᵢ]; exact hcalib i aᵢ
      _ = R.stage.payoff i cooperate := by rw [← Finset.sum_mul, hμ_sum, one_mul]
  · -- Dirty: punishment is absorbing and a stage Nash, so deviating cannot pay.
    rw [R.continuationValue_grimTriggerStrategy_of_not_isClean h hclean i,
      R.grimTrigger_expand_sum i h σ' hopp (R.stage.payoff i),
      R.grimTrigger_expand_sum i h σ' hopp
        (fun c => R.continuationValue (R.grimTriggerStrategy cooperate punish) (h ++ [c]) i),
      grimTriggerProfile_of_not_isClean hclean]
    -- Every successor of a dirty history is dirty, so the continuation is the punishment value.
    have hcont : ∀ aᵢ : R.stage.Action i,
        R.continuationValue (R.grimTriggerStrategy cooperate punish)
            (h ++ [Function.update punish i aᵢ]) i = R.stage.payoff i punish :=
      fun aᵢ => R.continuationValue_grimTriggerStrategy_of_not_isClean _
        (not_isClean_append hclean _) i
    simp only [hcont]
    -- The continuation sum collapses (weights sum to one); the stage sum is bounded by `IsNash`.
    have hcontsum :
        ∑ aᵢ : R.stage.Action i, (R.atHistory σ' i h) aᵢ * R.stage.payoff i punish =
          R.stage.payoff i punish := by
      rw [← Finset.sum_mul, hμ_sum, one_mul]
    rw [hcontsum]
    have hnash : ∀ aᵢ : R.stage.Action i,
        R.stage.payoff i (Function.update punish i aᵢ) ≤ R.stage.payoff i punish := by
      rw [R.stage.isNash_iff] at hpunish
      exact fun aᵢ => hpunish i aᵢ
    have hstage_le :
        ∑ aᵢ : R.stage.Action i, (R.atHistory σ' i h) aᵢ *
            R.stage.payoff i (Function.update punish i aᵢ) ≤ R.stage.payoff i punish := by
      calc ∑ aᵢ : R.stage.Action i, (R.atHistory σ' i h) aᵢ *
              R.stage.payoff i (Function.update punish i aᵢ)
          ≤ ∑ aᵢ : R.stage.Action i, (R.atHistory σ' i h) aᵢ * R.stage.payoff i punish :=
            Finset.sum_le_sum (fun aᵢ _ => mul_le_mul_of_nonneg_left (hnash aᵢ) (hμ_nonneg aᵢ))
        _ = R.stage.payoff i punish := hcontsum
    nlinarith [mul_nonneg h1mδ (sub_nonneg.mpr hstage_le)]

/-- **Grim trigger is a subgame-perfect equilibrium** when the punishment profile is a stage Nash
equilibrium and the discount factor is calibrated so that no one-shot deviation on the cooperative
path pays. The one-shot deviation principle upgrades the one-period checks of
`grimTrigger_noProfitableOneShotDeviation` to full subgame perfection. -/
theorem grimTrigger_isSubgamePerfectEquilibrium {cooperate punish : R.stage.ActionProfile}
    (hpunish : R.stage.IsNash punish)
    (hcalib : ∀ (i : R.stage.Player) (aᵢ : R.stage.Action i),
      (1 - R.discount) * R.stage.payoff i (Function.update cooperate i aᵢ)
        + R.discount * R.stage.payoff i punish ≤ R.stage.payoff i cooperate) :
    R.IsSubgamePerfectEquilibrium (R.grimTriggerStrategy cooperate punish) :=
  (R.grimTrigger_noProfitableOneShotDeviation hpunish hcalib).isSubgamePerfectEquilibrium

end RepeatedGame

end Econlib.GameTheory
