/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Grim Trigger in the Repeated Prisoner's Dilemma

The Prisoner's Dilemma is the canonical illustration of how individually rational play destroys
collectively profitable outcomes. In the one-shot game each player has a strict incentive to defect,
so the unique Nash equilibrium is mutual defection, yielding the Pareto-dominated payoff vector
`(1, 1)` rather than the cooperative `(3, 3)`. The folk theorems of repeated games reverse this
verdict once players are patient enough and play is observable: cooperation becomes sustainable as
an equilibrium of the repeated game, supported by the threat of punishment after any deviation.

This file instantiates the library grim-trigger API
(`Econlib.GameTheory.Repeated.GrimTrigger`) at the classical 2×2 Prisoner's Dilemma with payoffs
`T = 5`, `R = 3`, `P = 1`, `S = 0` and common discount factor `δ = 1/2`. At this threshold the
one-shot deviation is exactly indifferent on clean histories; the tightness of the threshold
(failure for `δ < 1/2`) is not formalized here.

## Main definitions

* `pd : FiniteStrategicGame` — the Prisoner's Dilemma stage game.
* `cooperate`, `defect : Fin 2` — the two stage actions.
* `cooperativeProfile, defectionProfile : pd.ActionProfile` — the all-cooperate and all-defect
  joint actions.
* `repeatedPD : RepeatedGame` — the `δ = 1/2`-discounted infinite repetition.
* `grimTrigger : repeatedPD.PublicStrategy` — the library grim-trigger behavioral strategy.

## Main statements

* `pd_defect_strictly_dominant` — defection is strictly dominant in the stage game.
* `pd_defectionProfile_is_nash` — `(D, D)` is a pure Nash equilibrium of the stage game.
* `pd_nash_unique` — `(D, D)` is the unique pure Nash equilibrium of the stage game.
* `continuationValue_grimTrigger_clean` — grim trigger's continuation value is `3` on clean
  histories.
* `continuationValue_grimTrigger_dirty` — grim trigger's continuation value is `1` on dirty
  histories.
* `grimTrigger_calibrated` — the one-period calibration inequality at `δ = 1/2`.
* `grimTrigger_is_SPE` — grim trigger is a subgame-perfect equilibrium.

## Tags

prisoner's dilemma, grim trigger, repeated game, subgame perfect equilibrium, folk theorem
-/

noncomputable section

namespace EconlibExamples.GameTheory.GrimTriggerPD

open Econlib.GameTheory

/-! ## The Stage Game: The Prisoner's Dilemma -/

/-- **Cooperate**, encoded as `0 : Fin 2`. -/
abbrev cooperate : Fin 2 := 0

/-- **Defect**, encoded as `1 : Fin 2`. -/
abbrev defect : Fin 2 := 1

/-- The Prisoner's Dilemma stage game. Two players each pick an action in `Fin 2` (`0 = cooperate`,
`1 = defect`). Payoffs follow the classical PD ranking `T > R > P > S` with `T = 5`, `R = 3`,
`P = 1`, `S = 0`. Concretely:

* `(C, C) ↦ (3, 3)` — mutual cooperation,
* `(C, D) ↦ (0, 5)` — player 0 is the sucker,
* `(D, C) ↦ (5, 0)` — player 1 is the sucker,
* `(D, D) ↦ (1, 1)` — mutual defection.

Both players have a dominant action to defect, so the unique pure Nash equilibrium of the stage
game is `(D, D)` with payoff vector `(1, 1)`. -/
abbrev pd : FiniteStrategicGame :=
  FiniteStrategicGame.mkFin 2 (fun _ => 2) fun i s =>
    if s i = cooperate then
      if s (1 - i) = cooperate then (3 : ℝ) else 0
    else
      if s (1 - i) = cooperate then (5 : ℝ) else 1

/-- The all-cooperate action profile `(C, C)`. -/
def cooperativeProfile : pd.ActionProfile := fun _ => cooperate

/-- The all-defect action profile `(D, D)`. -/
def defectionProfile : pd.ActionProfile := fun _ => defect

example : pd.payoff 0 cooperativeProfile = 3 := by
  simp [cooperativeProfile, cooperate]

example : pd.payoff 1 cooperativeProfile = 3 := by
  simp [cooperativeProfile, cooperate]

example : pd.payoff 0 defectionProfile = 1 := by
  simp [defectionProfile, defect, cooperate]

example : pd.payoff 1 defectionProfile = 1 := by
  simp [defectionProfile, defect, cooperate]

/-! ## The Stage Game's Unique Nash Equilibrium -/

/-- **Strict dominance of defection.** For every player `i` and profile `s`, defecting yields a
strictly higher stage payoff than cooperating, holding the opponent's action fixed. -/
theorem pd_defect_strictly_dominant (i : Fin 2) (s : pd.ActionProfile) :
    pd.payoff i (Function.update s i defect) > pd.payoff i (Function.update s i cooperate) := by
  have hne : (1 - i) ≠ i := by fin_cases i <;> decide
  by_cases hop : s (1 - i) = cooperate <;>
    norm_num [Function.update_of_ne hne, hop, cooperate, defect]

/-- **Mutual defection is a pure Nash equilibrium of the stage game.** -/
theorem pd_defectionProfile_is_nash : pd.IsNash defectionProfile := by
  rw [StrategicGame.isNash_iff]
  intro i aᵢ
  fin_cases i <;> fin_cases aᵢ <;>
    simp [pd, defectionProfile, Function.update_self, cooperate, defect]

/-- **Uniqueness of the stage game's pure Nash equilibrium.** Every pure Nash equilibrium of the
stage Prisoner's Dilemma equals the all-defect profile: in any profile containing a cooperator,
that cooperator strictly gains by switching to defect. -/
theorem pd_nash_unique (s : pd.ActionProfile) (hs : pd.IsNash s) : s = defectionProfile := by
  rw [StrategicGame.isNash_iff] at hs
  have hcoord : ∀ j : Fin 2, s j = defect := by
    intro j
    refine Fin.eq_one_of_ne_zero (s j) fun hC => ?_
    have hdev := hs j defect
    have hgt := pd_defect_strictly_dominant j s
    have hupd0 : Function.update s j cooperate = s := by
      rw [show (cooperate : Fin 2) = s j from hC.symm, Function.update_eq_self]
    rw [hupd0] at hgt
    linarith
  funext j; exact hcoord j

/-! ## The Repeated Game -/

/-- The infinitely repeated Prisoner's Dilemma with common discount factor `δ = 1/2`. Grim trigger
sustains `(R, R)`-cooperation when `δ ≥ (T - R) / (T - P) = 2/4 = 1/2`; we calibrate `δ` to
exactly this threshold, where the one-shot deviation is exactly indifferent. -/
def repeatedPD : RepeatedGame where
  stage := pd
  discount := 1 / 2
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

/-! ## The Grim-Trigger Strategy -/

/-- **Grim trigger** as a public strategy: cooperate while the public history is clean (every prior
period was `(C, C)`), and defect forever after any deviation. -/
def grimTrigger : repeatedPD.PublicStrategy :=
  repeatedPD.grimTriggerStrategy cooperativeProfile defectionProfile

/-- On a clean history, grim trigger plays `(C, C)` forever, so its normalized discounted
continuation value is `R = 3`. -/
lemma continuationValue_grimTrigger_clean {h : pd.PublicHistory}
    (hclean : repeatedPD.IsClean cooperativeProfile h) (i : Fin 2) :
    repeatedPD.continuationValue grimTrigger h i = 3 := by
  unfold grimTrigger
  rw [repeatedPD.continuationValue_grimTriggerStrategy_of_isClean h hclean i]
  fin_cases i <;> simp [repeatedPD, cooperativeProfile, cooperate]

/-- On a dirty history, grim trigger plays the stage Nash `(D, D)` forever, so its normalized
discounted continuation value is `P = 1`. -/
lemma continuationValue_grimTrigger_dirty {h : pd.PublicHistory}
    (hdirty : ¬ repeatedPD.IsClean cooperativeProfile h) (i : Fin 2) :
    repeatedPD.continuationValue grimTrigger h i = 1 := by
  unfold grimTrigger
  rw [repeatedPD.continuationValue_grimTriggerStrategy_of_not_isClean h hdirty i]
  fin_cases i <;> simp [repeatedPD, defectionProfile, defect, cooperate]

/-! ## The Equilibrium Statement -/

/-- **The one-period calibration inequality at `δ = 1/2`.** For every player `i` and deviation
action `aᵢ`, the one-shot deviation payoff does not exceed the cooperative payoff. Concretely,
deviating to defect against a cooperating opponent earns `(1/2)·5 + (1/2)·1 = 3`, exactly the
cooperative payoff (the threshold is tight); cooperating earns `(1/2)·3 + (1/2)·1 = 2 ≤ 3`. -/
lemma grimTrigger_calibrated (i : Fin 2) (aᵢ : Fin 2) :
    (1 - repeatedPD.discount) * pd.payoff i (Function.update cooperativeProfile i aᵢ)
      + repeatedPD.discount * pd.payoff i defectionProfile ≤ pd.payoff i cooperativeProfile := by
  have hδ : repeatedPD.discount = (1 / 2 : ℝ) := rfl
  rw [hδ]
  fin_cases i <;> fin_cases aᵢ <;>
    norm_num [pd, FiniteStrategicGame.mkFin, Function.update, cooperativeProfile, defectionProfile,
      cooperate, defect]

/-- **Grim trigger is a subgame-perfect equilibrium of the `δ = 1/2`-discounted repeated
Prisoner's Dilemma.**

At every public history, no player gains by a one-shot deviation. On clean histories the deviation
yields net gain `(1 - δ)(T - R) - δ(R - P) = (1/2)(2) - (1/2)(2) = 0`, so the deviator is
exactly indifferent; on dirty histories grim trigger prescribes mutual defection, which is the
static Nash of the stage game, so no deviation pays. -/
theorem grimTrigger_is_SPE :
    repeatedPD.IsSubgamePerfectEquilibrium grimTrigger :=
  repeatedPD.grimTrigger_isSubgamePerfectEquilibrium
    pd_defectionProfile_is_nash grimTrigger_calibrated

end EconlibExamples.GameTheory.GrimTriggerPD

end
