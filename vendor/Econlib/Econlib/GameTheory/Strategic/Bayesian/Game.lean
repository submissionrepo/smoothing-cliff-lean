/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Basic
public import Econlib.GameTheory.Strategic.Bayesian.TypeDist

/-!
# Bayesian Games and Interim Payoffs

This file defines **Bayesian games** (Harsanyi 1967–68), finite Bayesian games with a common prior,
and the **interim** payoff operations for pure and mixed Bayesian Nash equilibrium. The payoff
operators evaluate type-contingent deviations against the prior conditionals supplied by `TypeDist`.

## Main definitions

* `BayesianGame`: Players, type spaces, action spaces, and type-dependent payoffs.
* `FinBayesianGame`: Finite Bayesian games with a common prior.
* `FinBayesianGame.PureStrategy`: Pure behavioral strategy profiles.
* `FinBayesianGame.MixedBehavioralStrategy`: Mixed behavioral strategy profiles.
* `FinBayesianGame.interimPayoffAction`: Interim payoff from a pure deviation.
* `FinBayesianGame.interimPayoffMixedAction`: Interim payoff from a mixed deviation.

## Main statements

* `FinBayesianGame.interimPayoff_eq_interimPayoffAction`: Equilibrium action payoff identity.
* `FinBayesianGame.interimPayoffAction_eq_of_agree`: Pure interim payoff ignores the deviating
  player-type's original action.
* `FinBayesianGame.interimPayoffMixed_eq_of_agree`: Mixed interim payoff ignores the deviating
  player-type's original mixed action.
* `FinBayesianGame.interimPayoffMixed_pureToMixed`: Pure strategies embedded as Dirac mixed
  strategies recover pure interim payoffs.

## References

* Harsanyi, John C. 1968. “Games with Incomplete Information Played by 'Bayesian' Players, Parts
  I-Iii.” *Management Science* 14 : 159–82, 320–34, 486–502.

## Tags

bayesian games, interim payoff, behavioral strategies
-/

@[expose] public section

open Function BigOperators Econlib.Probability

noncomputable section
namespace Econlib.GameTheory

/-- A Bayesian game: Players, type spaces, action spaces, and type-dependent payoffs. -/
structure BayesianGame where
  Player : Type*
  [instInhabitedPlayer : Inhabited Player]
  Theta : Player → Type*
  Action : Player → Type*
  /-- Payoff to player `i` given action profile `s` and type profile `θ`. -/
  payoff : Player → (Π i, Action i) → (Π i, Theta i) → ℝ

attribute [instance] BayesianGame.instInhabitedPlayer

/-- A finite Bayesian game with a common prior. -/
structure FinBayesianGame extends BayesianGame where
  [instFintypePlayer : Fintype Player]
  [instDecEqPlayer : DecidableEq Player]
  [instFintypeTheta : ∀ i, Fintype (Theta i)]
  [instDecEqTheta : ∀ i, DecidableEq (Theta i)]
  [instFintypeAction : ∀ i, Fintype (Action i)]
  [instDecEqAction : ∀ i, DecidableEq (Action i)]
  [instInhabitedAction : ∀ i, Inhabited (Action i)]
  [instInhabitedTheta : ∀ i, Inhabited (Theta i)]
  prior : @TypeDist Player instFintypePlayer instDecEqPlayer Theta instFintypeTheta instDecEqTheta

attribute [instance] FinBayesianGame.instFintypePlayer FinBayesianGame.instDecEqPlayer
  FinBayesianGame.instFintypeTheta FinBayesianGame.instDecEqTheta
  FinBayesianGame.instFintypeAction FinBayesianGame.instDecEqAction
  FinBayesianGame.instInhabitedAction FinBayesianGame.instInhabitedTheta

namespace FinBayesianGame

variable (G : FinBayesianGame)

/-- A type profile in a finite Bayesian game. -/
abbrev TypeProfile := Π i, G.Theta i

/-- An action profile in a finite Bayesian game. -/
abbrev ActionProfile := Π i, G.Action i

/-- A pure behavioral strategy profile: Each player type chooses an action. -/
abbrev PureStrategy := ∀ i, G.Theta i → G.Action i

/-- The expanded-game player corresponding to a player-type pair. -/
abbrev PlayerType := Σ i, G.Theta i

/-- Construct the action profile from a strategy profile and type profile. -/
def actionProfile (s : G.PureStrategy) (θ : G.TypeProfile) : G.ActionProfile :=
  fun j => s j (θ j)

/-- Interim expected payoff for player `i` of type `θ_i` under strategy profile `s`. -/
def interimPayoff (i : G.Player) (θ_i : G.Theta i) (s : G.PureStrategy) : ℝ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : Π j, G.Theta j => θ i = θ_i),
    G.prior.condProbD i θ_i θ * G.payoff i (G.actionProfile s θ) θ

/-- Interim payoff when player `i` of type `θ_i` deviates to action `a_i` while everyone else
follows `s`. -/
def interimPayoffAction (i : G.Player) (θ_i : G.Theta i) (a_i : G.Action i)
    (s : G.PureStrategy) : ℝ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : Π j, G.Theta j => θ i = θ_i),
    G.prior.condProbD i θ_i θ *
      G.payoff i (Function.update (G.actionProfile s θ) i a_i) θ

/-- Interim payoff equals interimPayoffAction at the equilibrium action. -/
lemma interimPayoff_eq_interimPayoffAction (i : G.Player) (θ_i : G.Theta i)
    (s : ∀ j, G.Theta j → G.Action j) :
    G.interimPayoff i θ_i s = G.interimPayoffAction i θ_i (s i θ_i) s := by
  unfold interimPayoff interimPayoffAction
  refine Finset.sum_congr rfl fun θ hθ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  have h_eq : update (G.actionProfile s θ) i (s i θ_i) = G.actionProfile s θ := by
    have : s i θ_i = G.actionProfile s θ i := by unfold actionProfile; rw [hθ]
    rw [this]; exact update_eq_self i (G.actionProfile s θ)
  rw [h_eq]

/-- The interim payoff under a deviation vanishes at types with zero prior-marginal probability,
where the prior conditional is the junk value zero at every profile. -/
lemma interimPayoffAction_eq_zero_of_marginal_not_pos (i : G.Player) (θ_i : G.Theta i)
    (a_i : G.Action i) (s : G.PureStrategy) (h : ¬ 0 < G.prior.marginalD i θ_i) :
    G.interimPayoffAction i θ_i a_i s = 0 := by
  unfold interimPayoffAction
  refine Finset.sum_eq_zero fun θ _ => ?_
  rw [G.prior.condProbD_eq_zero_of_not_pos i θ_i θ h, zero_mul]

/-- The interim payoff action only depends on the strategy at player-type pairs other than
`(i, θ_i)`, because player `i`'s action is overwritten by `a_i`. -/
lemma interimPayoffAction_eq_of_agree (i : G.Player) (θ_i : G.Theta i) (a_i : G.Action i)
    (s₁ s₂ : ∀ j, G.Theta j → G.Action j)
    (h : ∀ (j : G.Player) (θ_j : G.Theta j),
      (⟨i, θ_i⟩ : Σ k, G.Theta k) ≠ ⟨j, θ_j⟩ →
        s₁ j θ_j = s₂ j θ_j) :
    G.interimPayoffAction i θ_i a_i s₁ = G.interimPayoffAction i θ_i a_i s₂ := by
  unfold interimPayoffAction actionProfile
  refine Finset.sum_congr rfl fun θ hθ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  congr 2
  ext j
  simp only [Function.update]
  split_ifs with hji
  · rfl
  · exact h j _ fun heq => hji (congr_arg Sigma.fst heq).symm

/-! ## Mixed Behavioral Strategies -/

/-- A mixed behavioral strategy profile: Each player-type randomizes over actions. -/
abbrev MixedBehavioralStrategy := ∀ i, G.Theta i → stdSimplex ℝ (G.Action i)

/-- Embed a pure behavioral strategy as a mixed one (Dirac on each action). -/
def pureToMixed (s : G.PureStrategy) : G.MixedBehavioralStrategy :=
  fun i θ_i => stdSimplex.vertex (s i θ_i)

/-- Interim expected payoff for player `i` of type `θ_i` from pure action `a_i`, when all other
players follow mixed behavioral strategy `σ`. Integrates over opponents' types (via conditional)
and opponents' mixing. The action sum is restricted to profiles with `a i = a_i` to avoid
overcounting (since the product is only over opponents `j ≠ i`). -/
def interimPayoffMixed (i : G.Player) (θ_i : G.Theta i) (a_i : G.Action i)
    (σ : G.MixedBehavioralStrategy) : ℝ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : Π j, G.Theta j => θ i = θ_i),
    G.prior.condProbD i θ_i θ *
      ∑ a ∈ Finset.univ.filter (fun a : Π j, G.Action j => a i = a_i),
        (∏ j ∈ Finset.univ.erase i, (σ j (θ j)) (a j)) *
          G.payoff i a θ

/-- Expected interim payoff under a mixed action `y` against `σ`. Linear in `y`. -/
def interimPayoffMixedAction (i : G.Player) (θ_i : G.Theta i)
    (y : stdSimplex ℝ (G.Action i)) (σ : G.MixedBehavioralStrategy) : ℝ :=
  ∑ a_i, y a_i * G.interimPayoffMixed i θ_i a_i σ

/-- The mixed interim payoff vanishes at types with zero prior-marginal probability, where the
prior conditional is the junk value zero at every profile. -/
lemma interimPayoffMixed_eq_zero_of_marginal_not_pos (i : G.Player) (θ_i : G.Theta i)
    (a_i : G.Action i) (σ : G.MixedBehavioralStrategy)
    (h : ¬ 0 < G.prior.marginalD i θ_i) :
    G.interimPayoffMixed i θ_i a_i σ = 0 := by
  unfold interimPayoffMixed
  refine Finset.sum_eq_zero fun θ _ => ?_
  rw [G.prior.condProbD_eq_zero_of_not_pos i θ_i θ h, zero_mul]

/-- The mixed interim payoff under a mixed deviation vanishes at zero-marginal types. -/
lemma interimPayoffMixedAction_eq_zero_of_marginal_not_pos (i : G.Player) (θ_i : G.Theta i)
    (y : stdSimplex ℝ (G.Action i)) (σ : G.MixedBehavioralStrategy)
    (h : ¬ 0 < G.prior.marginalD i θ_i) :
    G.interimPayoffMixedAction i θ_i y σ = 0 := by
  unfold interimPayoffMixedAction
  refine Finset.sum_eq_zero fun a_i _ => ?_
  rw [G.interimPayoffMixed_eq_zero_of_marginal_not_pos i θ_i a_i σ h, mul_zero]

/-- `interimPayoffMixed` only depends on the components of `σ` at player–type pairs other than
`(i, θ_i)`: The inner sum factors over `j ≠ i`, and any `θ` with `θ i = θ_i` has
`(j, θ j) ≠ (i, θ_i)` for `j ≠ i`. -/
lemma interimPayoffMixed_eq_of_agree (i : G.Player) (θ_i : G.Theta i) (a_i : G.Action i)
    (σ₁ σ₂ : G.MixedBehavioralStrategy)
    (h : ∀ (j : G.Player) (θ_j : G.Theta j),
      (⟨j, θ_j⟩ : Σ k, G.Theta k) ≠ ⟨i, θ_i⟩ →
        σ₁ j θ_j = σ₂ j θ_j) :
    G.interimPayoffMixed i θ_i a_i σ₁ = G.interimPayoffMixed i θ_i a_i σ₂ := by
  unfold interimPayoffMixed
  refine Finset.sum_congr rfl fun θ hθ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun j hj => ?_
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  rw [h j (θ j) fun heq => hji (congr_arg Sigma.fst heq)]

/-- `interimPayoffMixedAction` likewise agrees on strategies that match off `(i, θ_i)`. -/
lemma interimPayoffMixedAction_eq_of_agree (i : G.Player) (θ_i : G.Theta i)
    (y : stdSimplex ℝ (G.Action i)) (σ₁ σ₂ : G.MixedBehavioralStrategy)
    (h : ∀ (j : G.Player) (θ_j : G.Theta j),
      (⟨j, θ_j⟩ : Σ k, G.Theta k) ≠ ⟨i, θ_i⟩ →
        σ₁ j θ_j = σ₂ j θ_j) :
    G.interimPayoffMixedAction i θ_i y σ₁ = G.interimPayoffMixedAction i θ_i y σ₂ := by
  unfold interimPayoffMixedAction
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [G.interimPayoffMixed_eq_of_agree i θ_i a σ₁ σ₂ h]

/-- Under pure strategies, `interimPayoffMixed` reduces to `interimPayoffAction`. -/
lemma interimPayoffMixed_pureToMixed (s : G.PureStrategy) (i : G.Player)
    (θ_i : G.Theta i) (a_i : G.Action i) :
    G.interimPayoffMixed i θ_i a_i (G.pureToMixed s) =
      G.interimPayoffAction i θ_i a_i s := by
  unfold interimPayoffMixed interimPayoffAction pureToMixed
  refine Finset.sum_congr rfl fun θ hθ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  congr 1
  set a₀ : Π j, G.Action j := Function.update (G.actionProfile s θ) i a_i with ha₀_def
  have ha₀_mem : a₀ ∈ Finset.univ.filter (fun a : Π j, G.Action j => a i = a_i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Function.update_self ..⟩
  have ha₀_prod : (∏ j ∈ Finset.univ.erase i,
      (stdSimplex.vertex (s j (θ j)) : G.Action j → ℝ) (a₀ j)) = 1 := by
    refine Finset.prod_eq_one fun j hj => ?_
    have hji := Finset.ne_of_mem_erase hj
    simp [ha₀_def, Function.update_of_ne hji, actionProfile, stdSimplex.vertex_apply_self]
  have h_other : ∀ b ∈ Finset.univ.filter (fun a : Π j, G.Action j => a i = a_i),
      b ≠ a₀ → (∏ j ∈ Finset.univ.erase i,
        (stdSimplex.vertex (s j (θ j)) : G.Action j → ℝ) (b j)) * G.payoff i b θ = 0 := by
    intro b hb hne
    have hbi : b i = a_i := (Finset.mem_filter.mp hb).2
    have ⟨j, hji, hne_j⟩ : ∃ j, j ≠ i ∧ b j ≠ s j (θ j) := by
      by_contra h_all; push Not at h_all
      apply hne; ext j
      by_cases hji : j = i
      · subst hji; simp [ha₀_def, Function.update_self, hbi]
      · simp [ha₀_def, Function.update_of_ne hji, actionProfile, h_all j hji]
    have h_zero : (stdSimplex.vertex (s j (θ j)) : G.Action j → ℝ) (b j) = 0 :=
      stdSimplex.vertex_apply_ne (fun h => hne_j h.symm)
    have h_prod : ∏ k ∈ Finset.univ.erase i,
        (stdSimplex.vertex (s k (θ k)) : G.Action k → ℝ) (b k) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) h_zero
    rw [h_prod, zero_mul]
  rw [Finset.sum_eq_single_of_mem a₀ ha₀_mem h_other, ha₀_prod, one_mul]

end FinBayesianGame

end Econlib.GameTheory
end
