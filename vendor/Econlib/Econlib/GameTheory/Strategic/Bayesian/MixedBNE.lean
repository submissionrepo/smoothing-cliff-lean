/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Bayesian.PureBNE
public import Econlib.Math.Analysis.Convex.StdSimplex

/-!
# Mixed Bayesian Nash Equilibrium

This file defines mixed behavioral **Bayesian Nash equilibrium** (Harsanyi 1967–68) for finite
Bayesian games. It packages the equilibrium predicate as an `EquilibriumProblem`, proves the
concrete best-response characterization, develops support and indifference lemmas, relates pure and
mixed BNE, and proves existence using the Kakutani equilibrium interface over player-type pairs.

## Main definitions

* `FinBayesianGame.mixedBnePred`: Abstract equilibrium problem for mixed behavioral BNE.
* `FinBayesianGame.IsMixedBNE`: Mixed behavioral Bayesian Nash equilibrium.
* `FinBayesianGame.toNashExistenceData`: Kakutani data whose players are player-type pairs.

## Main statements

* `FinBayesianGame.IsMixedBNE_iff`: Concrete mixed BNE best-response characterization.
* `FinBayesianGame.mixedBNE_support_eq_value`: Support actions attain the equilibrium payoff.
* `FinBayesianGame.mixedBNE_indifference`: Support actions have equal interim payoffs.
* `FinBayesianGame.pureBNE_implies_mixedBNE`: Pure BNE embeds into mixed BNE.
* `FinBayesianGame.exists_mixedBNE`: Existence of mixed behavioral BNE.

## References

* Harsanyi, John C. 1968. “Games with Incomplete Information Played by 'Bayesian' Players, Parts
  I-Iii.” *Management Science* 14 : 159–82, 320–34, 486–502.

## Tags

bayesian games, mixed bayesian nash equilibrium, behavioral strategies, kakutani
-/

@[expose] public section

open Function BigOperators Econlib.Probability

noncomputable section
namespace Econlib.GameTheory

namespace FinBayesianGame

variable (G : FinBayesianGame)

/-- The equilibrium problem associated with mixed Bayesian Nash equilibrium. The deviator index is
a player–type pair `⟨i, θ_i⟩`; the swap relation says the new strategy may differ only at that pair
(up to mixed action); the value is the interim mixed-action payoff. -/
noncomputable def mixedBnePred (G : FinBayesianGame) : EquilibriumProblem where
  S := G.MixedBehavioralStrategy
  I := Σ i, G.Theta i
  swap := fun p σ σ' =>
    ∀ j θ_j, (⟨j, θ_j⟩ : Σ k, G.Theta k) ≠ p → σ' j θ_j = σ j θ_j
  value := fun p σ => G.interimPayoffMixedAction p.1 p.2 (σ p.1 p.2) σ

/-- Substrate-uniform mixed-behavioral Bayesian Nash equilibrium: A profile is a mixed BNE iff no
deviator–type pair has a profitable mixed deviation. -/
def IsMixedBNE (G : FinBayesianGame) (σ : G.MixedBehavioralStrategy) : Prop :=
  G.mixedBnePred.IsEquilibrium σ

@[simp] lemma mixedBnePred_swap_iff (p : Σ i, G.Theta i) (σ σ' : G.MixedBehavioralStrategy) :
    G.mixedBnePred.swap p σ σ' ↔
      ∀ j θ_j, (⟨j, θ_j⟩ : Σ k, G.Theta k) ≠ p → σ' j θ_j = σ j θ_j := Iff.rfl

@[simp] lemma mixedBnePred_value_eq (p : Σ i, G.Theta i) (σ : G.MixedBehavioralStrategy) :
    G.mixedBnePred.value p σ = G.interimPayoffMixedAction p.1 p.2 (σ p.1 p.2) σ := rfl

/-- Canonical user-facing characterization: A profile is a mixed BNE iff at every type with
positive prior-marginal probability, no profitable mixed deviation exists.

Types outside the prior's support carry no incentive constraints — the interim payoffs there are
identically zero. -/
theorem IsMixedBNE_iff (σ : G.MixedBehavioralStrategy) :
    G.IsMixedBNE σ ↔
      ∀ (i : G.Player) (θ_i : G.Theta i), 0 < G.prior.marginalD i θ_i →
        ∀ (y : stdSimplex ℝ (G.Action i)),
          G.interimPayoffMixedAction i θ_i (σ i θ_i) σ ≥
            G.interimPayoffMixedAction i θ_i y σ := by
  unfold IsMixedBNE
  dsimp only [mixedBnePred, EquilibriumProblem.IsEquilibrium]
  refine ⟨?_, ?_⟩
  · intro h i θ_i _hpos y
    classical
    let σ' : G.MixedBehavioralStrategy := fun j θ_j =>
      if hp : (⟨j, θ_j⟩ : Σ k, G.Theta k) = ⟨i, θ_i⟩ then
        ((Sigma.mk.inj hp).1 ▸ y : stdSimplex ℝ (G.Action j))
      else
        σ j θ_j
    have hagree :
        ∀ j θ_j, (⟨j, θ_j⟩ : Σ k, G.Theta k) ≠ ⟨i, θ_i⟩ →
          σ' j θ_j = σ j θ_j := by
      intro j θ_j hne
      change
        (if hp : (⟨j, θ_j⟩ : Σ k, G.Theta k) = ⟨i, θ_i⟩ then _ else σ j θ_j) =
          σ j θ_j
      rw [dif_neg hne]
    have hat : σ' i θ_i = y := by
      change (if hp : (⟨i, θ_i⟩ : Σ k, G.Theta k) = ⟨i, θ_i⟩ then
        ((Sigma.mk.inj hp).1 ▸ y : stdSimplex ℝ (G.Action i)) else σ i θ_i) = y
      rw [dif_pos rfl]
    have habst := h ⟨i, θ_i⟩ σ' hagree
    have heq : G.interimPayoffMixedAction i θ_i (σ' i θ_i) σ' =
        G.interimPayoffMixedAction i θ_i y σ := by
      rw [hat]
      exact G.interimPayoffMixedAction_eq_of_agree i θ_i y σ' σ hagree
    rw [heq] at habst
    exact habst
  · intro h p σ' hagree
    have heq : G.interimPayoffMixedAction p.1 p.2 (σ' p.1 p.2) σ' =
        G.interimPayoffMixedAction p.1 p.2 (σ' p.1 p.2) σ :=
      G.interimPayoffMixedAction_eq_of_agree p.1 p.2 (σ' p.1 p.2) σ' σ hagree
    rw [heq]
    by_cases hpos : 0 < G.prior.marginalD p.1 p.2
    · exact h p.1 p.2 hpos (σ' p.1 p.2)
    · rw [G.interimPayoffMixedAction_eq_zero_of_marginal_not_pos p.1 p.2 _ σ hpos,
          G.interimPayoffMixedAction_eq_zero_of_marginal_not_pos p.1 p.2 _ σ hpos]

/-- In a mixed BNE, every action in the support of `σ i θ_i` yields the equilibrium expected payoff
(value of the game for that player-type). -/
theorem mixedBNE_support_eq_value (σ : G.MixedBehavioralStrategy)
    (hσ : G.IsMixedBNE σ)
    (i : G.Player) (θ_i : G.Theta i) (a : G.Action i) (ha : (σ i θ_i) a > 0) :
    G.interimPayoffMixed i θ_i a σ =
      G.interimPayoffMixedAction i θ_i (σ i θ_i) σ := by
  have hσ' := (G.IsMixedBNE_iff σ).mp hσ
  by_cases hpos : 0 < G.prior.marginalD i θ_i
  case neg =>
    rw [G.interimPayoffMixed_eq_zero_of_marginal_not_pos i θ_i a σ hpos,
        G.interimPayoffMixedAction_eq_zero_of_marginal_not_pos i θ_i _ σ hpos]
  case pos =>
    set V := G.interimPayoffMixedAction i θ_i (σ i θ_i) σ
    set f := fun b => G.interimPayoffMixed i θ_i b σ
    have h_le : ∀ b, f b ≤ V := by
      intro b
      have hopt := hσ' i θ_i hpos (stdSimplex.vertex b)
      simp only [V, interimPayoffMixedAction] at hopt ⊢
      calc f b = ∑ b', (stdSimplex.vertex b) b' * f b' := (stdSimplex.vertex_sum_mul b f).symm
      _ ≤ ∑ b', (σ i θ_i) b' * f b' := hopt
    by_contra h_ne
    have h_lt : f a < V := lt_of_le_of_ne (h_le a) h_ne
    have h1 : V < ∑ b, (σ i θ_i) b * V := by
      apply Finset.sum_lt_sum
      · intro b _; exact mul_le_mul_of_nonneg_left (h_le b) ((σ i θ_i).2.1 b)
      · exact ⟨a, Finset.mem_univ a, mul_lt_mul_of_pos_left h_lt ha⟩
    have h2 : ∑ b, (σ i θ_i) b * V = V := by
      change (∑ b, (σ i θ_i).val b * V) = V
      rw [← Finset.sum_mul, (σ i θ_i).2.2, one_mul]
    linarith

/-- **Indifference principle**: In a mixed BNE, all actions in the support of `σ i θ_i` yield the
same interim expected payoff. -/
theorem mixedBNE_indifference (σ : G.MixedBehavioralStrategy)
    (hσ : G.IsMixedBNE σ)
    (i : G.Player) (θ_i : G.Theta i) (a a' : G.Action i)
    (ha : (σ i θ_i) a > 0) (ha' : (σ i θ_i) a' > 0) :
    G.interimPayoffMixed i θ_i a σ = G.interimPayoffMixed i θ_i a' σ := by
  rw [G.mixedBNE_support_eq_value σ hσ i θ_i a ha,
      G.mixedBNE_support_eq_value σ hσ i θ_i a' ha']

/-- In a mixed BNE, support actions weakly dominate all actions. -/
theorem mixedBNE_support_ge (σ : G.MixedBehavioralStrategy)
    (hσ : G.IsMixedBNE σ)
    (i : G.Player) (θ_i : G.Theta i) (a_supp a : G.Action i)
    (ha : (σ i θ_i) a_supp > 0) :
    G.interimPayoffMixed i θ_i a_supp σ ≥ G.interimPayoffMixed i θ_i a σ := by
  have hσ' := (G.IsMixedBNE_iff σ).mp hσ
  by_cases hpos : 0 < G.prior.marginalD i θ_i
  case neg =>
    rw [G.interimPayoffMixed_eq_zero_of_marginal_not_pos i θ_i a_supp σ hpos,
        G.interimPayoffMixed_eq_zero_of_marginal_not_pos i θ_i a σ hpos]
  case pos =>
    rw [G.mixedBNE_support_eq_value σ hσ i θ_i a_supp ha]
    have hopt := hσ' i θ_i hpos (stdSimplex.vertex a)
    simp only [interimPayoffMixedAction] at hopt ⊢
    calc G.interimPayoffMixed i θ_i a σ
        = ∑ b, (stdSimplex.vertex a) b * G.interimPayoffMixed i θ_i b σ :=
          (stdSimplex.vertex_sum_mul a (G.interimPayoffMixed i θ_i · σ)).symm
      _ ≤ ∑ b, (σ i θ_i) b * G.interimPayoffMixed i θ_i b σ := hopt

/-- Pure BNE embeds into mixed BNE. A pure equilibrium, viewed as a degenerate mixed behavioral
strategy, satisfies the mixed BNE predicate even though `mixedBnePred` quantifies over the larger
class of mixed deviations. -/
theorem pureBNE_implies_mixedBNE (s : G.PureStrategy)
    (hs : G.IsBNE s) :
    G.IsMixedBNE (G.pureToMixed s) := by
  rw [G.IsMixedBNE_iff]
  have hs' := (G.IsBNE_iff s).mp hs
  intro i θ_i hpos y
  simp only [interimPayoffMixedAction]
  simp_rw [G.interimPayoffMixed_pureToMixed s i θ_i]
  have h_lhs : ∑ x, (G.pureToMixed s i θ_i) x * G.interimPayoffAction i θ_i x s =
      G.interimPayoffAction i θ_i (s i θ_i) s :=
    stdSimplex.vertex_sum_mul (s i θ_i) (G.interimPayoffAction i θ_i · s)
  rw [h_lhs]
  calc ∑ x, y x * G.interimPayoffAction i θ_i x s
      ≤ ∑ x, y x * G.interimPayoffAction i θ_i (s i θ_i) s :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hs' i θ_i hpos x) (y.2.1 x)
    _ = G.interimPayoffAction i θ_i (s i θ_i) s := by
        change (∑ x, y.val x * _) = _
        rw [← Finset.sum_mul, y.2.2, one_mul]

/-- A mixed BNE whose strategy is degenerate (mass 1 on one action for every player-type) is a pure
BNE. This is the converse direction of `pureBNE_implies_mixedBNE` restricted to pure-valued mixed
strategies. -/
lemma mixedBNE_of_pure_implies_pureBNE (σ : G.MixedBehavioralStrategy)
    (hσ : G.IsMixedBNE σ)
    (s : G.PureStrategy)
    (hs : ∀ i θ_i, σ i θ_i = stdSimplex.vertex (s i θ_i)) :
    G.IsBNE s := by
  rw [G.IsBNE_iff]
  have hσ' := (G.IsMixedBNE_iff σ).mp hσ
  have hσ_eq : σ = G.pureToMixed s := funext fun i => funext fun θ_i => hs i θ_i
  intro i θ_i hpos a_i
  have hmixed := hσ' i θ_i hpos (stdSimplex.vertex a_i)
  rw [hσ_eq] at hmixed
  simp only [interimPayoffMixedAction] at hmixed
  simp_rw [G.interimPayoffMixed_pureToMixed s i θ_i] at hmixed
  have collapse : ∀ (b : G.Action i), ∑ x, (stdSimplex.vertex b : G.Action i → ℝ) x *
      G.interimPayoffAction i θ_i x s = G.interimPayoffAction i θ_i b s :=
    fun b => stdSimplex.vertex_sum_mul b (G.interimPayoffAction i θ_i · s)
  simp only [pureToMixed] at hmixed
  rw [collapse (s i θ_i), collapse a_i] at hmixed
  exact hmixed

/-- When player `⟨i, θ_i⟩` deviates to pure action `a_i` in the expanded game, the expanded-game
mixed payoff equals the Bayesian game interim payoff. -/
lemma expandedMixed_eq_interimPayoffMixed (m : G.expandedGame.MixedStrategy)
    (i : G.Player) (θ_i : G.Theta i) (a_i : G.Action i) :
    G.expandedGame.expectedPayoff ⟨i, θ_i⟩
      (Function.update m ⟨i, θ_i⟩ (stdSimplex.vertex a_i)) =
      G.interimPayoffMixed i θ_i a_i (fun j θ_j => m ⟨j, θ_j⟩) := by
  unfold Econlib.GameTheory.FiniteStrategicGame.expectedPayoff
  have hprod : ∀ s : Π (p : Σ j, G.Theta j), G.Action p.1,
      (∏ p, (Function.update m ⟨i, θ_i⟩ (stdSimplex.vertex a_i) p) (s p)) =
      (stdSimplex.vertex a_i) (s ⟨i, θ_i⟩) *
        ∏ p ∈ Finset.univ.erase ⟨i, θ_i⟩, (m p) (s p) := by
    intro s
    have hpure_eq : ∀ p : Σ j, G.Theta j,
        (Function.update m ⟨i, θ_i⟩ (stdSimplex.vertex a_i) p) (s p) =
        if p = ⟨i, θ_i⟩
        then (stdSimplex.vertex a_i : G.Action i → ℝ) (s ⟨i, θ_i⟩)
        else (m p) (s p) := by
      intro p
      by_cases h : p = ⟨i, θ_i⟩
      · subst h; simp only [Function.update_self, ite_true,
          stdSimplex.vertex_coe, Pi.single_apply]
        split_ifs <;> aesop
      · rw [if_neg h]
        simp [Function.update]
        grind
    simp_rw [hpure_eq]
    rw [Finset.prod_ite]
    congr 1
    · rw [Finset.prod_filter]
      simp only [stdSimplex.vertex_coe, Pi.single_apply]
      split_ifs with h
      · simp_rw [ite_self]; exact Finset.prod_const_one
      · exact Finset.prod_eq_zero (Finset.mem_univ ⟨i, θ_i⟩)
          (by simp)
    · congr 1; ext x; simp [Finset.mem_filter, Finset.mem_erase, ne_eq]; grind
  simp_rw [hprod]
  simp only [expandedGame, interimPayoffAction, interimPayoffMixed]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro θ hθ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ
  let π : ((p : Σ j, G.Theta j) → G.Action p.1) → (Π j, G.Action j) :=
    fun x j => x ⟨j, θ j⟩
  subst hθ
  have h_update :
      ∀ x : (p : Σ j, G.Theta j) → G.Action p.1,
        update (G.actionProfile (fun j θ_j => x ⟨j, θ_j⟩) θ) i (x ⟨i, θ i⟩) = π x := by
    intro x
    ext j
    by_cases hj : j = i
    · subst hj
      simp [π]
    · simp [π, actionProfile, Function.update_of_ne hj]
  simp_rw [h_update]
  let U : Type _ := {q : Σ j, G.Theta j // q.2 ≠ θ q.1}
  let e :
      ((p : Σ j, G.Theta j) → G.Action p.1) ≃
        ((Π j, G.Action j) × ((q : U) → G.Action q.1.1)) :=
    { toFun := fun x => (π x, fun q => x q.1)
      invFun := fun y q => by
        by_cases hq : q.2 = θ q.1
        · exact y.1 q.1
        · exact y.2 ⟨q, hq⟩
      left_inv := by
        intro x
        funext q
        by_cases hq : q.2 = θ q.1
        · rcases q with ⟨j, τ⟩
          dsimp [π] at hq ⊢
          cases hq
          simp
        · simp [hq]
      right_inv := by
        intro y
        rcases y with ⟨a, u⟩
        apply Prod.ext
        · funext j; simp [π]
        · funext q; rcases q with ⟨q, hq⟩; simp [hq] }
  have hsum :
      ∑ x : (p : Σ j, G.Theta j) → G.Action p.1,
        ((stdSimplex.vertex a_i) (x ⟨i, θ i⟩) *
            ∏ x_1 ∈ Finset.univ.erase ⟨i, θ i⟩, (m x_1) (x x_1)) *
          G.prior.condProbD i (θ i) θ * G.payoff i (π x) θ =
      ∑ y : (Π j, G.Action j) × ((q : U) → G.Action q.1.1),
        ((stdSimplex.vertex a_i) ((e.symm y) ⟨i, θ i⟩) *
            ∏ x_1 ∈ Finset.univ.erase ⟨i, θ i⟩, (m x_1) ((e.symm y) x_1)) *
          G.prior.condProbD i (θ i) θ * G.payoff i (π (e.symm y)) θ := by
    simpa using
      (Fintype.sum_equiv e
        (fun x : (p : Σ j, G.Theta j) → G.Action p.1 =>
          ((stdSimplex.vertex a_i) (x ⟨i, θ i⟩) *
              ∏ x_1 ∈ Finset.univ.erase ⟨i, θ i⟩, (m x_1) (x x_1)) *
            G.prior.condProbD i (θ i) θ * G.payoff i (π x) θ)
        (fun y : (Π j, G.Action j) × ((q : U) → G.Action q.1.1) =>
          ((stdSimplex.vertex a_i) ((e.symm y) ⟨i, θ i⟩) *
              ∏ x_1 ∈ Finset.univ.erase ⟨i, θ i⟩, (m x_1) ((e.symm y) x_1)) *
            G.prior.condProbD i (θ i) θ * G.payoff i (π (e.symm y)) θ)
        (by intro x; simp))
  have hsum' :
      (∑ x,
        ((stdSimplex.vertex a_i) (x ⟨i, θ i⟩) *
            ∏ x_1 ∈ Finset.univ.erase ⟨i, θ i⟩, (m x_1) (x x_1)) *
          G.prior.condProbD i (θ i) θ * G.payoff i (π x) θ) =
      ∑ y : (Π j, G.Action j) × ((q : U) → G.Action q.1.1),
        ((stdSimplex.vertex a_i) ((e.symm y) ⟨i, θ i⟩) *
            ∏ x_1 ∈ Finset.univ.erase ⟨i, θ i⟩, (m x_1) ((e.symm y) x_1)) *
          G.prior.condProbD i (θ i) θ * G.payoff i (π (e.symm y)) θ := by
    simpa using hsum
  trans (∑ a : Π j, G.Action j, ∑ u : (q : U) → G.Action q.1.1,
      ((stdSimplex.vertex a_i) (e.symm (a, u) ⟨i, θ i⟩) *
          ∏ x_1 ∈ Finset.univ.erase ⟨i, θ i⟩, (m x_1) (e.symm (a, u) x_1)) *
        G.prior.condProbD i (θ i) θ * G.payoff i (π (e.symm (a, u))) θ)
  · convert hsum'.trans (Fintype.sum_prod_type _) using 1
  have he_match : ∀ (a : Π j, G.Action j) (u : (q : U) → G.Action q.1.1) (j : G.Player),
      e.symm (a, u) ⟨j, θ j⟩ = a j := by
    intro a u j; change dite _ _ _ = _; rw [dif_pos rfl]
  have he_pi : ∀ (a : Π j, G.Action j) (u : (q : U) → G.Action q.1.1),
      π (e.symm (a, u)) = a := by
    intro a u; ext j; exact he_match a u j
  simp_rw [he_match _ _ i, he_pi]
  have he_nonmatch : ∀ (a : Π j, G.Action j) (u : (q : U) → G.Action q.1.1)
      (p : Σ j, G.Theta j) (hp : p.2 ≠ θ p.1),
      e.symm (a, u) p = u ⟨p, hp⟩ := by
    intro a u p hp; change dite _ _ _ = _; rw [dif_neg hp]
  have hinner : ∀ (a : Π j, G.Action j),
      ∑ u : (q : U) → G.Action q.1.1,
        ∏ p ∈ Finset.univ.erase ⟨i, θ i⟩, (m p) (e.symm (a, u) p) =
      ∏ j ∈ Finset.univ.erase i, (m ⟨j, θ j⟩) (a j) := by
    intro a
    have hsplit : ∀ u : (q : U) → G.Action q.1.1,
        ∏ p ∈ Finset.univ.erase ⟨i, θ i⟩, (m p) (e.symm (a, u) p) =
        (∏ p ∈ (Finset.univ.erase ⟨i, θ i⟩).filter (fun p => p.2 = θ p.1),
          (m p) (a p.1)) *
        (∏ p ∈ (Finset.univ.erase ⟨i, θ i⟩).filter (fun p => ¬(p.2 = θ p.1)),
          (m p) (e.symm (a, u) p)) := by
      intro u
      rw [← Finset.prod_filter_mul_prod_filter_not _ (fun p => p.2 = θ p.1)]
      congr 1
      apply Finset.prod_congr rfl
      intro p hp
      simp only [Finset.mem_filter] at hp
      rcases p with ⟨j, τ⟩; simp only at hp; cases hp.2; rw [he_match a u j]
    simp_rw [hsplit]
    rw [← Finset.mul_sum]
    have hmatch :
        ∏ p ∈ (Finset.univ.erase ⟨i, θ i⟩).filter (fun p => p.2 = θ p.1),
          (m p) (a p.1) =
        ∏ j ∈ Finset.univ.erase i, (m ⟨j, θ j⟩) (a j) := by
      apply Finset.prod_nbij' (fun p => p.1) (fun j => ⟨j, θ j⟩)
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_erase, ne_eq] at hp
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro h; apply hp.1.1; exact Sigma.ext h (by subst h; exact heq_of_eq hp.2)
      · intro j hj
        simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true] at hj
        refine (Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩)
        intro h; exact hj (congr_arg Sigma.fst h)
      · intro p hp
        simp only [Finset.mem_filter] at hp
        rcases p with ⟨j, τ⟩; simp only at hp; cases hp.2; rfl
      · intro j _; rfl
      · intro p hp
        simp only [Finset.mem_filter] at hp
        rcases p with ⟨j, τ⟩; simp only at hp ⊢; cases hp.2; rfl
    rw [hmatch]
    suffices h1 :
        ∑ u : (q : U) → G.Action q.1.1,
          ∏ p ∈ (Finset.univ.erase ⟨i, θ i⟩).filter (fun p => ¬(p.2 = θ p.1)),
            (m p) (e.symm (a, u) p) = 1 by
      rw [h1, mul_one]
    have hfactor : ∀ (u : (q : U) → G.Action q.1.1),
        ∏ p ∈ (Finset.univ.erase ⟨i, θ i⟩).filter (fun p => ¬(p.2 = θ p.1)),
          (m p) (e.symm (a, u) p) =
        ∏ q : U, (m q.1) (u q) := by
      intro u
      symm
      apply Finset.prod_nbij (fun (q : U) => (q : Σ j, G.Theta j))
      · intro q _
        have hq := q.2
        simp only [ne_eq]
        refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, hq⟩
        intro h
        exact hq (by rw [h])
      · intro q₁ _ q₂ _ h; exact Subtype.val_injective h
      · intro p hp
        have hp' := (Finset.mem_filter.mp hp).2
        exact ⟨⟨p, hp'⟩, Finset.mem_univ _, rfl⟩
      · intro q _
        rw [he_nonmatch a u q.1 q.2]
    simp_rw [hfactor]
    rw [← Fintype.prod_sum]
    calc ∏ q : U, ∑ j, (m (q : Σ j, G.Theta j)) j
        = ∏ _ : U, (1 : ℝ) :=
          Finset.prod_congr rfl (fun q _ => (m (q : Σ j, G.Theta j)).2.2)
      _ = 1 := Finset.prod_const_one
  have hstep : ∀ (a : Π j, G.Action j),
      ∑ u : (q : U) → G.Action q.1.1,
        ((stdSimplex.vertex a_i) (a i) *
            ∏ p ∈ Finset.univ.erase ⟨i, θ i⟩, (m p) (e.symm (a, u) p)) *
          G.prior.condProbD i (θ i) θ * G.payoff i a θ =
      (stdSimplex.vertex a_i) (a i) *
        (∏ j ∈ Finset.univ.erase i, (m ⟨j, θ j⟩) (a j)) *
        G.prior.condProbD i (θ i) θ * G.payoff i a θ := by
    intro a
    calc _ = (stdSimplex.vertex a_i) (a i) * G.prior.condProbD i (θ i) θ * G.payoff i a θ *
        ∑ u, ∏ p ∈ Finset.univ.erase ⟨i, θ i⟩, (m p) (e.symm (a, u) p) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro u _; ring
      _ = _ := by rw [hinner a]; ring
  simp_rw [hstep]
  convert_to (∑ a ∈ Finset.univ.filter (fun a => a i = a_i),
      (G.prior.condProbD i (θ i) θ *
        ∏ j ∈ Finset.univ.erase i, (m ⟨j, θ j⟩) (a j)) * G.payoff i a θ) = _ using 1
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a i = a_i
    · rw [if_pos ha, stdSimplex.vertex_apply_eq ha.symm, one_mul, mul_comm
        (∏ j ∈ Finset.univ.erase i, (m ⟨j, θ j⟩) (a j)) (G.prior.condProbD _ _ _)]
    · rw [if_neg ha, stdSimplex.vertex_apply_ne (Ne.symm ha), zero_mul, zero_mul, zero_mul]
  · refine Finset.sum_congr ?_ (fun a _ => rfl)
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-! ### Direct Kakutani route for mixed BNE

We bundle a `FinBayesianGame` directly as `NashExistenceData` whose players are player-type
pairs `Σ i, G.Theta i` and whose slices are the standard simplices over actions. -/

/-- Bundle a finite Bayesian game directly as `NashExistenceData`: Per player-type pair `⟨i, θ_i⟩`,
the slice is the standard simplex over `G.Action i`, and the payoff is the interim mixed-action
payoff. -/
noncomputable def toNashExistenceData (G : FinBayesianGame) : NashExistenceData where
  Player := Σ i, G.Theta i
  V := fun p => G.Action p.1 → ℝ
  Slice := fun p => stdSimplex ℝ (G.Action p.1)
  hSlice_convex := fun p => convex_stdSimplex ℝ (G.Action p.1)
  hSlice_compact := fun p => isCompact_stdSimplex ℝ (G.Action p.1)
  hSlice_nonempty := fun p =>
    ⟨fun a => if a = default then 1 else 0,
     ⟨fun a => by dsimp; split_ifs <;> positivity, by simp [Finset.sum_ite_eq']⟩⟩
  payoff := fun p σ =>
    G.interimPayoffMixedAction p.1 p.2 (σ p) (fun j θ_j => σ ⟨j, θ_j⟩)
  payoff_continuous := fun p => by
    unfold interimPayoffMixedAction interimPayoffMixed
    apply continuous_finset_sum
    intro a_i _
    apply Continuous.mul
    · exact (continuous_apply a_i).comp
        (continuous_subtype_val.comp (continuous_apply p))
    · apply continuous_finset_sum
      intro θ _
      apply Continuous.mul continuous_const
      apply continuous_finset_sum
      intro a _
      apply Continuous.mul _ continuous_const
      apply continuous_finset_prod
      intro j _
      exact (continuous_apply (a j)).comp
        (continuous_subtype_val.comp
          (continuous_apply (⟨j, θ j⟩ : Σ k, G.Theta k)))
  payoff_affine_in_own := fun p σ => by
    rcases p with ⟨i, θ_i⟩
    let f : G.Action i → ℝ := fun a_i =>
      G.interimPayoffMixed i θ_i a_i (fun j θ_j => σ ⟨j, θ_j⟩)
    let ψ : (G.Action i → ℝ) →ₗ[ℝ] ℝ := {
      toFun := fun y => ∑ a_i, y a_i * f a_i
      map_add' := by
        intro y₁ y₂
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        simp only [Pi.add_apply]
        ring
      map_smul' := by
        intro c y
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    }
    refine ⟨ψ.toAffineMap, ?_⟩
    intro y
    rw [Function.update_self]
    unfold interimPayoffMixedAction
    apply Finset.sum_congr rfl
    intro a_i _
    congr 1
    apply G.interimPayoffMixed_eq_of_agree i θ_i a_i
      (fun j θ_j => σ ⟨j, θ_j⟩)
      (fun j θ_j => Function.update σ ⟨i, θ_i⟩ y ⟨j, θ_j⟩)
    intro j θ_j hne
    exact (Function.update_of_ne hne y σ).symm

/-- **Existence of mixed Bayesian Nash equilibrium**: Every finite Bayesian game has a mixed
behavioral BNE, via `NashExistenceData.exists_equilibrium` with player-type pairs as players. -/
theorem exists_mixedBNE (G : FinBayesianGame) :
    ∃ σ : G.MixedBehavioralStrategy, G.IsMixedBNE σ := by
  obtain ⟨σ_abs, hσ⟩ := G.toNashExistenceData.exists_equilibrium
  refine ⟨fun i θ_i => σ_abs ⟨i, θ_i⟩, ?_⟩
  intro p σ' hagree
  rcases p with ⟨i, θ_i⟩
  set y : ↑(stdSimplex ℝ (G.Action i)) := σ' i θ_i
  have hupd_eq : Function.update σ_abs ⟨i, θ_i⟩ y =
      fun (q : Σ k, G.Theta k) => σ' q.1 q.2 := by
    funext q
    by_cases hq : q = ⟨i, θ_i⟩
    · subst hq; rw [Function.update_self]
    · rw [Function.update_of_ne hq]
      have := hagree q.1 q.2 (by rcases q with ⟨j, τ⟩; exact hq)
      rw [this]
      rcases q with ⟨j, τ⟩; rfl
  have hopt := hσ ⟨i, θ_i⟩ (Function.update σ_abs ⟨i, θ_i⟩ y) ⟨y, rfl⟩
  change
    G.interimPayoffMixedAction i θ_i (σ_abs ⟨i, θ_i⟩)
      (fun j θ_j => σ_abs ⟨j, θ_j⟩) ≥
    G.interimPayoffMixedAction i θ_i (Function.update σ_abs ⟨i, θ_i⟩ y ⟨i, θ_i⟩)
      (fun j θ_j => Function.update σ_abs ⟨i, θ_i⟩ y ⟨j, θ_j⟩) at hopt
  rw [Function.update_self] at hopt
  have hfun : (fun (j : G.Player) (θ_j : G.Theta j) =>
      Function.update σ_abs ⟨i, θ_i⟩ y ⟨j, θ_j⟩) = σ' := by
    funext j θ_j
    exact congr_fun hupd_eq ⟨j, θ_j⟩
  rw [hfun] at hopt
  exact hopt

end FinBayesianGame

end Econlib.GameTheory
end
