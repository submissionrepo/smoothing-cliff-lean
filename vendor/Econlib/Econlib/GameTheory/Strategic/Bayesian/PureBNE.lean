/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Equilibrium.Problem
public import Econlib.GameTheory.Strategic.Bayesian.Game

/-!
# Pure Bayesian Nash Equilibrium

This file defines pure **Bayesian Nash equilibrium** (Harsanyi 1967–68) for finite Bayesian games.
It packages the BNE predicate as an `EquilibriumProblem`, proves the concrete best-response
characterization, and relates pure BNE to pure Nash equilibrium in the expanded strategic-form game.

## Main definitions

* `FinBayesianGame.expandedGame`: Strategic-form game whose players are player-type pairs.
* `FinBayesianGame.bnePred`: Abstract equilibrium problem for pure BNE.
* `FinBayesianGame.IsBNE`: Pure Bayesian Nash equilibrium.
* `FinBayesianGame.bayesianToStrategicMorphism`: Morphism from pure BNE to expanded-game Nash.
* `FinBayesianGame.strategicToBayesianMorphism`: Morphism from expanded-game Nash to pure BNE.

## Main statements

* `FinBayesianGame.IsBNE_iff`: Concrete pure BNE best-response characterization.
* `FinBayesianGame.isBNE_iff_isNash_expanded`: Equivalence with pure Nash equilibrium in the
  expanded game.

## References

* Harsanyi, John C. 1968. “Games with Incomplete Information Played by 'Bayesian' Players, Parts
  I-Iii.” *Management Science* 14 : 159–82, 320–34, 486–502.

## Tags

bayesian games, pure bayesian nash equilibrium, expanded game, game morphism
-/

@[expose] public section

open Function BigOperators Econlib.Probability

noncomputable section
namespace Econlib.GameTheory

namespace FinBayesianGame

variable (G : FinBayesianGame)

/-- The expanded strategic-form game. Each "player" is a (player, type) pair. Player `(i, θ_i)`
chooses an action in `G.Action i` and receives the interim expected payoff given all other
player-types follow their strategies. -/
def expandedGame : Econlib.GameTheory.FiniteStrategicGame where
  toStrategicGame := {
    Player := Σ i, G.Theta i
    Action := fun p => G.Action p.1
    payoff := fun ⟨i, θ_i⟩ profile =>
      let s : ∀ j, G.Theta j → G.Action j := fun j θ_j => profile ⟨j, θ_j⟩
      G.interimPayoffAction i θ_i (profile ⟨i, θ_i⟩) s
  }

/-- Convert a Bayesian strategy profile to an expanded-game strategy profile. -/
def toExpandedProfile (s : G.PureStrategy) :
    Π (p : Σ i, G.Theta i), G.Action p.1 :=
  fun ⟨i, θ_i⟩ => s i θ_i

/-- Convert an expanded-game profile back to a Bayesian strategy profile. -/
def fromExpandedProfile (profile : Π (p : Σ i, G.Theta i), G.Action p.1) :
    G.PureStrategy :=
  fun i θ_i => profile ⟨i, θ_i⟩

/-- The equilibrium problem associated with pure-strategy Bayesian Nash equilibrium. The deviator
index is a player–type pair `⟨i, θ_i⟩`; the swap relation says the new strategy may differ only at
that pair; the value is the interim expected payoff. -/
noncomputable def bnePred (G : FinBayesianGame) : EquilibriumProblem where
  S := G.PureStrategy
  I := Σ i, G.Theta i
  swap := fun p s s' =>
    ∀ j θ_j, (⟨j, θ_j⟩ : Σ k, G.Theta k) ≠ p → s' j θ_j = s j θ_j
  value := fun p s => G.interimPayoffAction p.1 p.2 (s p.1 p.2) s

/-- Substrate-uniform pure-strategy Bayesian Nash equilibrium: A profile is a BNE iff no
deviator–type pair has a profitable pure deviation. -/
def IsBNE (G : FinBayesianGame) (s : G.PureStrategy) : Prop :=
  G.bnePred.IsEquilibrium s

@[simp] lemma bnePred_swap_iff (p : Σ i, G.Theta i) (s s' : G.PureStrategy) :
    G.bnePred.swap p s s' ↔
      ∀ j θ_j, (⟨j, θ_j⟩ : Σ k, G.Theta k) ≠ p → s' j θ_j = s j θ_j := Iff.rfl

@[simp] lemma bnePred_value_eq (p : Σ i, G.Theta i) (s : G.PureStrategy) :
    G.bnePred.value p s = G.interimPayoffAction p.1 p.2 (s p.1 p.2) s := rfl

/-- Canonical user-facing characterization: A profile is a BNE iff at every type with positive
prior-marginal probability, no profitable pure deviation exists.

Types outside the prior's support carry no incentive constraints: There the interim payoffs are
identically zero, the junk value of the prior conditional. -/
theorem IsBNE_iff (s : G.PureStrategy) :
    G.IsBNE s ↔
      ∀ (i : G.Player) (θ_i : G.Theta i), 0 < G.prior.marginalD i θ_i →
        ∀ (a_i : G.Action i),
          G.interimPayoffAction i θ_i (s i θ_i) s ≥ G.interimPayoffAction i θ_i a_i s := by
  unfold IsBNE
  dsimp only [bnePred, EquilibriumProblem.IsEquilibrium]
  refine ⟨?_, ?_⟩
  · -- abstract → concrete
    intro h i θ_i _hpos a_i
    classical
    let s' : G.PureStrategy := fun j θ_j =>
      if h : (⟨j, θ_j⟩ : Σ k, G.Theta k) = ⟨i, θ_i⟩ then
        ((Sigma.mk.inj h).1 ▸ a_i : G.Action j)
      else
        s j θ_j
    have hagree :
        ∀ j θ_j, (⟨j, θ_j⟩ : Σ k, G.Theta k) ≠ ⟨i, θ_i⟩ →
          s' j θ_j = s j θ_j := by
      intro j θ_j hne
      simp only [s', dif_neg hne]
    have hat : s' i θ_i = a_i := by
      simp only [s', dif_pos rfl]
    have habst := h ⟨i, θ_i⟩ s' hagree
    have heq : G.interimPayoffAction i θ_i (s' i θ_i) s' =
        G.interimPayoffAction i θ_i a_i s := by
      rw [hat]
      exact G.interimPayoffAction_eq_of_agree i θ_i a_i s' s
        (fun j θ_j hne => hagree j θ_j (fun heq => hne heq.symm))
    rwa [heq] at habst
  · -- concrete → abstract
    intro h p s' hagree
    have heq : G.interimPayoffAction p.1 p.2 (s' p.1 p.2) s' =
        G.interimPayoffAction p.1 p.2 (s' p.1 p.2) s :=
      G.interimPayoffAction_eq_of_agree p.1 p.2 (s' p.1 p.2) s' s
        (fun j θ_j hne => hagree j θ_j (fun heq => hne heq.symm))
    rw [heq]
    by_cases hpos : 0 < G.prior.marginalD p.1 p.2
    · exact h p.1 p.2 hpos (s' p.1 p.2)
    · rw [G.interimPayoffAction_eq_zero_of_marginal_not_pos p.1 p.2 _ s hpos,
          G.interimPayoffAction_eq_zero_of_marginal_not_pos p.1 p.2 _ s hpos]

/-- The forward `GameMorphism` from the pure BNE problem on `G` to the pure Nash problem on
`G.expandedGame`, with strategy map `toExpandedProfile`. -/
noncomputable def bayesianToStrategicMorphism (G : FinBayesianGame) :
    GameMorphism G.bnePred G.expandedGame.toStrategicGame.nashPred where
  toFun := G.toExpandedProfile
  deviatorMap := id
  swap_lifts := by
    intro p s σ' ⟨a, hσ'⟩
    classical
    refine ⟨fun j θ_j =>
      if h : (⟨j, θ_j⟩ : Σ k, G.Theta k) = p then
        ((Sigma.mk.inj h).1 ▸ a : G.Action j)
      else s j θ_j, ?_, ?_⟩
    · -- bnePred.swap p s s': agree off p
      intro j θ_j hne
      have hne' : (⟨j, θ_j⟩ : Σ k, G.Theta k) ≠ p := hne
      change (if h : (⟨j, θ_j⟩ : Σ k, G.Theta k) = p then _ else s j θ_j) = s j θ_j
      rw [dif_neg hne']
    · -- toExpandedProfile s' = σ' = update (toExpandedProfile s) p a
      subst hσ'
      funext q
      obtain ⟨j, θ_j⟩ := q
      by_cases hjp : (⟨j, θ_j⟩ : Σ k, G.Theta k) = p
      · subst hjp
        change (if h : (⟨j, θ_j⟩ : Σ k, G.Theta k) = ⟨j, θ_j⟩ then
            ((Sigma.mk.inj h).1 ▸ a : G.Action j) else s j θ_j) =
          Function.update (G.toExpandedProfile s) ⟨j, θ_j⟩ a ⟨j, θ_j⟩
        rw [dif_pos rfl, Function.update_self]
      · change (if h : (⟨j, θ_j⟩ : Σ k, G.Theta k) = p then _ else s j θ_j) =
          Function.update (G.toExpandedProfile s) p a ⟨j, θ_j⟩
        rw [dif_neg hjp, Function.update_of_ne hjp]
        rfl
  value_eq := fun _ _ => rfl

/-- The reverse `GameMorphism` from pure Nash on `G.expandedGame` back to pure BNE on `G`, with
strategy map `fromExpandedProfile`, the inverse of `toExpandedProfile`. -/
noncomputable def strategicToBayesianMorphism (G : FinBayesianGame) :
    GameMorphism G.expandedGame.toStrategicGame.nashPred G.bnePred where
  toFun := G.fromExpandedProfile
  deviatorMap := id
  swap_lifts := by
    intro p σ s' h
    refine ⟨Function.update σ p (s' p.1 p.2), ⟨_, rfl⟩, ?_⟩
    funext i θ_i
    by_cases hpair : (⟨i, θ_i⟩ : Σ k, G.Theta k) = p
    · subst hpair
      change (Function.update σ ⟨i, θ_i⟩ (s' i θ_i)) ⟨i, θ_i⟩ = s' i θ_i
      rw [Function.update_self]
    · have hupd : (Function.update σ p (s' p.1 p.2)) ⟨i, θ_i⟩ = σ ⟨i, θ_i⟩ :=
        Function.update_of_ne hpair (s' p.1 p.2) σ
      change (Function.update σ p (s' p.1 p.2)) ⟨i, θ_i⟩ = s' i θ_i
      rw [hupd]
      exact (h i θ_i hpair).symm
  value_eq := fun _ _ => rfl

/-- Pure BNE on `G` corresponds to pure Nash on `G.expandedGame`, via the Curry/uncurry strategy
maps `toExpandedProfile` and `fromExpandedProfile`. -/
theorem isBNE_iff_isNash_expanded (s : ∀ i, G.Theta i → G.Action i) :
    G.IsBNE s ↔
      G.expandedGame.toStrategicGame.IsNash (G.toExpandedProfile s) :=
  ⟨G.bayesianToStrategicMorphism.transport, G.strategicToBayesianMorphism.transport⟩

end FinBayesianGame

end Econlib.GameTheory
end
