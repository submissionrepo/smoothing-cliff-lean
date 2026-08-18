/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import EconlibTest.GameTheory.ExtensiveFormCore
import Mathlib

/-!
# Extensive-Form Sequential Equilibrium — OSDP Endpoint Witness

End-to-end instantiation of `IsSequentialEquilibrium_of_oneShot` on the concrete one-decision game
`oneShotFEF` from `ExtensiveFormCore`. All six OSDP hypotheses are discharged on genuine data:
finite depth, reach coherence via perfect recall, no joint nodes, last-stop alignment, undiscounted
values, and a concrete `IsSequentialEquilibriumOneShot` witness with Kreps–Wilson consistent
beliefs from `HasConsistentBeliefs.of_subsingleton_support`.

`oneShotGame` is `ExtensiveGame.ofFiniteHorizonTree` over `oneShotEF`: player 0 picks `e : Fin 2`
at the root (payoff `e + 1`); player 1 is a bystander (payoff `2 - e`). The assessment
`oneShotAssess` plays the optimal root vertex `1` (payoff `2`) with a point-mass belief on the
root for player 0 and empty support for player 1. Sequential rationality follows by a convexity
bound: any strategy's root value is a convex combination of the leaf payoffs `1` and `2`.

## Main definitions

- `oneShotGame`: the undiscounted extensive game over `oneShotEF`
- `oneShotBestσ`: the optimal behavioral strategy
- `oneShotBeliefs`: the forced belief system
- `oneShotAssess`: the assessment (strategy + beliefs)
- `rootWeight`: the behavioral probability weight on a root choice

## Main statements

- `oneShot_isSeqRatOneShot`: the assessment is one-shot sequentially rational
- `oneShot_hasConsistentBeliefs`: the assessment has Kreps–Wilson consistent beliefs
- `oneShot_isSeqEqOneShot`: the assessment is a one-shot sequential equilibrium
- `oneShot_isSequentialEquilibrium`: the assessment is a sequential equilibrium (OSDP endpoint)
- `oneShot_reachWeighted_step`: the reach-weighted one-shot inequality at the on-path
  information set

## Tags

extensive form, sequential equilibrium, one-shot deviation principle, Kreps-Wilson
-/

noncomputable section

namespace EconlibTest.GameTheory.ExtensiveFormSeqEq

open Econlib.GameTheory
open EconlibTest.GameTheory.ExtensiveFormCore
  (oneShotFEF oneShotEF oneShotTree oneShotRootNode oneShotTree_movesAt_iff
    oneShotTree_nodeKind_nil oneShotTree_nodeKind_cons)

/-! ## The extensive game: `ofFiniteHorizonTree` over the one-decision form -/

/-- `FiniteDepth` holds for `oneShotEF`: every history of length `≥ 1` is terminal. -/
lemma oneShotEF_finiteDepth : oneShotEF.FiniteDepth 1 := by
  intro h hlen
  cases h with
  | nil => simp at hlen
  | cons e rest => exact ⟨![(e.val : ℝ) + 1, 2 - (e.val : ℝ)], rfl⟩

/-- The canonical undiscounted (`discount = 1`) extensive game over the one-decision form,
with continuation values given by the finite-horizon backward recursion. -/
def oneShotGame : ExtensiveGame (Fin 2) (Fin 2) :=
  ExtensiveGame.ofFiniteHorizonTree oneShotEF oneShotEF_finiteDepth oneShotFEF.no_general_chance

/-! ## The assessment: Optimal root vertex plus forced beliefs -/

/-- The optimal behavioral strategy: Player 0 plays the root vertex `1` (leaf payoff `2 > 1`);
player 1 (who never moves) plays the trivial vertex. -/
def oneShotBestσ : oneShotEF.BehavioralStrategy := fun i =>
  match i with
  | 0 => fun _ => stdSimplex.vertex (S := ℝ) (1 : Fin 2)
  | 1 => fun _ => stdSimplex.vertex (S := ℝ) ()

/-- The root history `[]` lies in player 0's single information set. -/
lemma oneShot_root_mem_infoSet :
    (oneShotEF.tree.nodeKind []).movesAt 0 ∧ oneShotEF.info.observe 0 [] = () :=
  ⟨rfl, rfl⟩

/-- The forced belief system: Point mass on the root for player 0's single information set
(`support 0 () = {[]}`), empty support for player 1, who never moves. -/
def oneShotBeliefs : BeliefSystem oneShotEF where
  support i := match i with
    | 0 => fun _ => {⟨[], oneShot_root_mem_infoSet⟩}
    | 1 => fun _ => ∅
  belief i := match i with
    | 0 => fun _ _ => 1
    | 1 => fun _ _ => 0
  belief_nonneg i := by
    match i with
    | 0 => exact fun _ _ => zero_le_one
    | 1 => exact fun _ _ => le_refl 0
  belief_eq_zero_of_not_mem i := by
    match i with
    | 0 =>
      intro obs x hxnot
      exfalso
      apply hxnot
      have hx_nil : x.1 = [] := ((oneShotTree_movesAt_iff 0 x.1).mp x.2.1).1
      simp only [Finset.mem_singleton]
      exact Subtype.ext hx_nil
    | 1 => exact fun _ _ _ => rfl
  support_exhaustive i := by
    match i with
    | 0 =>
      intro obs x _hreach
      have hx_nil : x.1 = [] := ((oneShotTree_movesAt_iff 0 x.1).mp x.2.1).1
      simp only [Finset.mem_singleton]
      exact Subtype.ext hx_nil
    | 1 =>
      intro obs x _hreach
      exact absurd ((oneShotTree_movesAt_iff 1 x.1).mp x.2.1).2 (by decide)
  belief_sum_one i := by
    match i with
    | 0 => intro obs _; rw [Finset.sum_singleton]
    | 1 => intro obs hne; exact absurd hne (by simp)

/-- The assessment: Optimal vertex strategy plus forced beliefs. -/
def oneShotAssess : Assessment oneShotEF :=
  { strategy := oneShotBestσ, beliefs := oneShotBeliefs }

/-! ## Continuation values by computation -/

/-- Continuation value at a terminal history equals the terminal payoff. -/
lemma oneShot_cv_terminal (σ : oneShotEF.BehavioralStrategy) (e : Fin 2)
    (rest : List (Fin 2)) (i : Fin 2) :
    oneShotGame.continuationValue σ (e :: rest) i = ![(e.val : ℝ) + 1, 2 - (e.val : ℝ)] i := by
  rw [oneShotGame.continuationValue_eq]
  rfl

/-- The probability weight a behavioral strategy places on root choice `c`. The node's `Choice`
field is definitionally `Fin 2` but does not reduce for numeral elaboration, so the cast is
explicit. -/
def rootWeight (σ : oneShotEF.BehavioralStrategy) (c : Fin 2) : ℝ :=
  (σ.playerBehavior [] oneShotTree_nodeKind_nil).val (show oneShotRootNode.Choice from c)

/-- Root weights are nonneg (simplex membership). -/
lemma rootWeight_nonneg (σ : oneShotEF.BehavioralStrategy) (c : Fin 2) :
    0 ≤ rootWeight σ c :=
  (σ.playerBehavior [] oneShotTree_nodeKind_nil).2.1 _

/-- Root weights sum to one (simplex membership). -/
lemma rootWeight_sum (σ : oneShotEF.BehavioralStrategy) :
    rootWeight σ 0 + rootWeight σ 1 = 1 := by
  have hsum : (∑ c : Fin 2,
      (σ.playerBehavior [] oneShotTree_nodeKind_nil).val (show oneShotRootNode.Choice from c)) =
        1 := (σ.playerBehavior [] oneShotTree_nodeKind_nil).2.2
  rwa [Fin.sum_univ_two] at hsum

/-- Player 0's root continuation value of any strategy is the simplex-weighted average of the two
leaf payoffs `1` and `2`. -/
lemma oneShot_cv_root_player0 (σ : oneShotEF.BehavioralStrategy) :
    oneShotGame.continuationValue σ [] 0 = rootWeight σ 0 * 1 + rootWeight σ 1 * 2 := by
  rw [oneShotGame.continuationValue_eq]
  change (∑ c : Fin 2, rootWeight σ c *
      ((0 : ℝ) + 1 * oneShotGame.continuationValue σ ([] ++ [c]) 0)) = _
  rw [Fin.sum_univ_two]
  simp only [List.nil_append]
  rw [oneShot_cv_terminal σ 0 [] 0, oneShot_cv_terminal σ 1 [] 0]
  norm_num

/-- The optimal strategy's root behavior is the vertex at choice `1`, read coordinatewise. -/
lemma oneShotBestσ_rootWeight (c : Fin 2) :
    rootWeight oneShotBestσ c =
      (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)).val c := by
  have hheq : HEq (oneShotBestσ.playerBehavior [] oneShotTree_nodeKind_nil)
      (oneShotBestσ 0 (oneShotEF.info.observe 0 [])) :=
    (cast_heq _ _).trans (oneShotBestσ.atHistory_player_heq oneShotTree_nodeKind_nil)
  have hchoice : oneShotRootNode.Choice =
      oneShotEF.info.iChoiceType 0 (oneShotEF.info.observe 0 []) := rfl
  unfold rootWeight
  rw [stdSimplex.heq_val hchoice _ _ hheq (show oneShotRootNode.Choice from c)]
  rfl

/-- The assessment attains the optimal root value `2`. -/
lemma oneShot_cv_root_best : oneShotGame.continuationValue oneShotBestσ [] 0 = 2 := by
  rw [oneShot_cv_root_player0, oneShotBestσ_rootWeight 0, oneShotBestσ_rootWeight 1,
    show ((stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)).val (0 : Fin 2)) =
      (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)) 0 from rfl,
    show ((stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)).val (1 : Fin 2)) =
      (stdSimplex.vertex (S := ℝ) (1 : Fin 2) : stdSimplex ℝ (Fin 2)) 1 from rfl,
    stdSimplex.vertex_apply_ne (show (1 : Fin 2) ≠ 0 by decide), stdSimplex.vertex_apply_self]
  norm_num

/-! ## One-shot sequential rationality, by computation -/

/-- The belief-weighted assessment value at player 0's information set equals the root continuation
value. -/
lemma oneShot_assessmentValue_player0 (τ : oneShotEF.BehavioralStrategy) (obs : Unit) :
    assessmentValue oneShotGame { strategy := τ, beliefs := oneShotBeliefs } 0 obs =
      oneShotGame.continuationValue τ [] 0 := by
  unfold assessmentValue
  change (∑ x ∈ ({⟨[], oneShot_root_mem_infoSet⟩} :
      Finset (oneShotEF.InfoSet 0 obs)), 1 * oneShotGame.continuationValue τ x.1 0) = _
  rw [Finset.sum_singleton, one_mul]

/-- The belief-weighted assessment value at player 1's (never-reached) information set is zero. -/
lemma oneShot_assessmentValue_player1 (τ : oneShotEF.BehavioralStrategy) (obs : Unit) :
    assessmentValue oneShotGame { strategy := τ, beliefs := oneShotBeliefs } 1 obs = 0 := by
  unfold assessmentValue
  change (∑ x ∈ (∅ : Finset (oneShotEF.InfoSet 1 obs)),
    oneShotBeliefs.belief 1 obs x * oneShotGame.continuationValue τ x.1 1) = 0
  rw [Finset.sum_empty]

/-- The assessment is one-shot sequentially rational: At player 0's information set the assessment
attains the maximal root value `2`, while any deviation's value is a convex combination of the leaf
payoffs `1` and `2`; at player 1's unrealized information set both values vanish. -/
theorem oneShot_isSeqRatOneShot : IsSequentiallyRationalOneShot oneShotGame oneShotAssess := by
  intro i obs σ' _hdev
  match i with
  | 0 =>
    change assessmentValue oneShotGame { strategy := oneShotBestσ, beliefs := oneShotBeliefs }
        0 obs ≥ assessmentValue oneShotGame { strategy := σ', beliefs := oneShotBeliefs } 0 obs
    rw [oneShot_assessmentValue_player0 oneShotBestσ obs, oneShot_assessmentValue_player0 σ' obs,
      oneShot_cv_root_best, oneShot_cv_root_player0 σ']
    have hnonneg0 := rootWeight_nonneg σ' 0
    have hnonneg1 := rootWeight_nonneg σ' 1
    have hsum := rootWeight_sum σ'
    linarith
  | 1 =>
    change assessmentValue oneShotGame { strategy := oneShotBestσ, beliefs := oneShotBeliefs }
        1 obs ≥ assessmentValue oneShotGame { strategy := σ', beliefs := oneShotBeliefs } 1 obs
    rw [oneShot_assessmentValue_player1 oneShotBestσ obs, oneShot_assessmentValue_player1 σ' obs]

/-! ## Kreps–Wilson consistency via the tremble construction -/

/-- The assessment has Kreps–Wilson consistent beliefs: both supports are subsingletons (a point
mass and an empty set), and the supported root history is reached with probability one. -/
theorem oneShot_hasConsistentBeliefs : HasConsistentBeliefs oneShotEF oneShotAssess := by
  refine HasConsistentBeliefs.of_subsingleton_support oneShotGame oneShotFEF.no_joint
    oneShotAssess (fun i obs => ?_) (fun i obs x hx => ?_)
  · match i with
    | 0 =>
      change (({⟨[], oneShot_root_mem_infoSet⟩} :
        Finset (oneShotEF.InfoSet 0 obs)) : Set (oneShotEF.InfoSet 0 obs)).Subsingleton
      simp
    | 1 =>
      change ((∅ : Finset (oneShotEF.InfoSet 1 obs)) : Set (oneShotEF.InfoSet 1 obs)).Subsingleton
      simp
  · match i with
    | 0 =>
      have hx_nil : x.1 = [] := ((oneShotTree_movesAt_iff 0 x.1).mp x.2.1).1
      refine ⟨oneShotBestσ, ?_⟩
      rw [hx_nil]
      change (0 : ℝ) < 1
      norm_num
    | 1 => exact absurd hx (Finset.notMem_empty x)

/-- **`ExtensiveForm.stepProb_tremble_tendsto`.** The step probabilities of the vanishing trembles
`oneShotBestσ.tremble (1/(n+1))` converge to those of `oneShotBestσ` — here at the root history and
event `0`. This is the event-level continuity that `HasConsistentBeliefs` now *derives* from
behavioral convergence; we exercise the named lemma directly on the joint-free carrier with a
concrete convergent rate, confirming its hypotheses are satisfiable. -/
theorem oneShot_stepProb_tremble_tendsto :
    Filter.Tendsto
      (fun n : ℕ => oneShotEF.stepProb
        (oneShotBestσ.tremble (1 / (n + 1)) (by positivity)
          (by rw [div_le_one (by positivity)]; exact le_add_of_nonneg_left (Nat.cast_nonneg n)))
        [] 0)
      Filter.atTop (nhds (oneShotEF.stepProb oneShotBestσ [] 0)) :=
  ExtensiveForm.stepProb_tremble_tendsto oneShotEF oneShotFEF.no_joint oneShotBestσ
    (fun n => by positivity)
    (fun n => by rw [div_le_one (by positivity)]; exact le_add_of_nonneg_left (Nat.cast_nonneg n))
    tendsto_one_div_add_atTop_nhds_zero_nat [] 0

/-- The assessment is a one-shot sequential equilibrium. -/
theorem oneShot_isSeqEqOneShot : IsSequentialEquilibriumOneShot oneShotGame oneShotAssess :=
  ⟨oneShot_isSeqRatOneShot, oneShot_hasConsistentBeliefs⟩

/-! ## The OSDP endpoint -/

/-- `oneShotFEF` has perfect recall: the only mover history is the root `[]`. -/
lemma oneShotFEF_isPerfectRecall : oneShotFEF.IsPerfectRecall := by
  intro i h₁ h₂ _ _ hm₁ hm₂ _
  rw [((oneShotTree_movesAt_iff i h₁).mp hm₁).1, ((oneShotTree_movesAt_iff i h₂).mp hm₂).1]

/-- `LastStopAlign` holds vacuously on the one-decision game: the only mover history is the root,
whose length `0` admits no stop index. -/
lemma oneShotEF_lastStopAlign : oneShotEF.LastStopAlign := by
  intro i z w _ _ hmz _ _ m hm_lt _ _
  have hz : z = [] ∧ i = 0 := (oneShotTree_movesAt_iff i z).mp hmz
  rw [hz.1] at hm_lt
  exact absurd hm_lt (by simp)

/-- **`IsSequentialEquilibrium_of_oneShot`:** The OSDP endpoint, instantiated end-to-end on
`oneShotGame`. All six hypotheses are discharged: finite depth, reach coherence via perfect recall,
no joint nodes, last-stop alignment, undiscounted values, and the one-shot sequential equilibrium
witness. The assessment is a genuine sequential equilibrium. -/
theorem oneShot_isSequentialEquilibrium : IsSequentialEquilibrium oneShotGame oneShotAssess :=
  IsSequentialEquilibrium_of_oneShot oneShotGame oneShotEF_finiteDepth
    (IsPerfectRecall.reachCoherent oneShotFEF_isPerfectRecall) oneShotFEF.no_joint
    oneShotEF_lastStopAlign rfl oneShotAssess oneShot_isSeqEqOneShot

/-! ## The reach-weighted one-shot step -/

/-- The information-set probability of player 0's single information set is positive. -/
lemma oneShot_infoSetProb_pos :
    0 < infoSetProb oneShotEF oneShotAssess.strategy oneShotAssess.beliefs 0 () := by
  unfold infoSetProb
  change (0 : ℝ) < ∑ x ∈ ({⟨[], oneShot_root_mem_infoSet⟩} : Finset (oneShotEF.InfoSet 0 ())),
    reachProb oneShotEF oneShotAssess.strategy x.1
  rw [Finset.sum_singleton]
  change (0 : ℝ) < 1
  norm_num

/-- At player 0's on-path information set, a one-shot deviation weakly lowers the reach-weighted
continuation sum over the belief support. -/
lemma oneShot_reachWeighted_step (τ : oneShotEF.BehavioralStrategy)
    (hτ : IsInfoSetDeviation oneShotEF 0 () oneShotAssess.strategy τ) :
    (∑ x ∈ oneShotAssess.beliefs.support 0 (),
        reachProb oneShotEF oneShotAssess.strategy x.1 *
          oneShotGame.continuationValue τ x.1 0) ≤
      (∑ x ∈ oneShotAssess.beliefs.support 0 (),
        reachProb oneShotEF oneShotAssess.strategy x.1 *
          oneShotGame.continuationValue oneShotAssess.strategy x.1 0) :=
  reachWeighted_oneShot_step oneShotGame oneShotAssess
    (isBayesConsistent_of_hasConsistentBeliefs oneShotGame oneShotAssess
      oneShot_hasConsistentBeliefs)
    oneShot_isSeqRatOneShot 0 () oneShot_infoSetProb_pos τ hτ

end EconlibTest.GameTheory.ExtensiveFormSeqEq

end
