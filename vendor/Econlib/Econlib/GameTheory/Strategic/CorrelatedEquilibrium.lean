/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Strategic.Basic

/-!
# Correlated Equilibrium

This file defines correlated strategies and correlated equilibrium (Aumann 1974) for finite
strategic-form games. A correlated strategy is a joint finite distribution over action profiles,
and the equilibrium condition is the obedience inequality for every player and recommended action.

## Main definitions

* `CorrelatedStrategy`: Joint distribution over pure action profiles.
* `CorrelatedStrategy.marginal`: Marginal probability of a player-action recommendation.
* `CorrelatedStrategy.weightedRecommendedPayoff`: Unnormalized payoff from obeying a recommendation.
* `FiniteStrategicGame.ResponsePolicy`: Maps recommendations to played actions.
* `FiniteStrategicGame.correlatedPred`: Abstract equilibrium problem for obedience.
* `IsCorrelatedEq`: Correlated-equilibrium predicate.

## Main statements

* `IsCorrelatedEq_iff`: Concrete obedience-inequality characterization.
* `support_plays_best`: Support actions are best replies under a mixed Nash first-order condition.
* `nash_is_correlated`: Every mixed Nash equilibrium induces a correlated equilibrium.
* `exists_correlatedEq`: Every finite strategic-form game has a correlated equilibrium.

## References

* Aumann, Robert J. 1974. “Subjectivity and Correlation in Randomized Strategies.” *Journal of
  Mathematical Economics* 1 (1): 67–96. [https://doi.org/10.1016/0304-4068(74)90037-8](https://doi.org/10.1016/0304-4068(74)90037-8).

## Tags

correlated equilibrium, mediated games, obedience, strategic games
-/

@[expose] public section

namespace Econlib.GameTheory

open Function Finset FiniteStrategicGame Econlib.Probability

noncomputable section

variable {G : FiniteStrategicGame}

/-- A correlated strategy is a joint probability distribution over pure strategy profiles. Unlike
Nash equilibrium (which uses independent mixed strategies), correlated strategies allow for
statistical dependence between players' actions. -/
structure CorrelatedStrategy (G : FiniteStrategicGame) where
  /-- Joint finite distribution over action profiles. -/
  dist : FinDist (Π i, G.Action i)

namespace CorrelatedStrategy

/-- Probability assigned to an action profile. -/
noncomputable def prob (μ : CorrelatedStrategy G) (s : Π i, G.Action i) : ℝ :=
  μ.dist s

lemma nonneg (μ : CorrelatedStrategy G) (s : Π i, G.Action i) : 0 ≤ μ.prob s :=
  μ.dist.nonneg s

lemma sum_one (μ : CorrelatedStrategy G) :
    ∑ s : Π i, G.Action i, μ.prob s = 1 :=
  μ.dist.sum_one

/-- Marginal probability that player `i` receives recommendation `si`: `FinDist.marginalD` of the
underlying joint distribution. -/
noncomputable def marginal (μ : CorrelatedStrategy G)
    (i : G.Player) (si : G.Action i) : ℝ :=
  μ.dist.marginalD i si

/-- Expected payoff to player `i` from obeying recommendation `si`, weighted by the joint
probability. This is an unnormalized payoff; the marginal denominator cancels in the obedience
inequality. -/
noncomputable def weightedRecommendedPayoff (μ : CorrelatedStrategy G)
    (i : G.Player) (si : G.Action i) : ℝ :=
  ∑ s ∈ Finset.univ.filter (fun s => s i = si), μ.prob s * G.payoff i s

lemma marginal_nonneg (μ : CorrelatedStrategy G) (i : G.Player) (si : G.Action i) :
    0 ≤ μ.marginal i si :=
  FinDist.marginalD_nonneg μ.dist i si

lemma marginal_sum_one (μ : CorrelatedStrategy G) (i : G.Player) :
    ∑ si : G.Action i, μ.marginal i si = 1 :=
  FinDist.marginalD_sum_one μ.dist i

/-- Construct a correlated strategy from independent mixed strategies (product distribution). -/
noncomputable def ofMixed (σ : G.MixedStrategy) : CorrelatedStrategy G where
  dist := FinDist.productD (fun i => FinDist.ofSimplex (σ i))

end CorrelatedStrategy

namespace FiniteStrategicGame

/-- A response policy assigns to each player `i` a function from recommendation type `G.Action i`
to action played, `G.Action i`. The truthful policy plays the recommendation unchanged. -/
abbrev ResponsePolicy (G : FiniteStrategicGame) : Type _ :=
  ∀ i : G.Player, G.Action i → G.Action i

/-- The truthful (obedient) response policy: Play the recommendation. -/
def truthfulResponse (G : FiniteStrategicGame) : G.ResponsePolicy :=
  fun _ si => si

/-- The equilibrium problem associated with correlated equilibrium. The strategy space is the joint
distribution paired with each player's response policy; the deviator index is a (player,
recommendation) pair `⟨i, si⟩`; a deviation may modify only player `i`'s response at recommendation
`si`, holding the joint distribution fixed; and the value is the joint- weighted expected payoff
conditional on `s i = si`, evaluated at the action the deviator's policy plays at `si`. A
correlated equilibrium is the truthful section `(μ, truthfulResponse)` of this problem. -/
def correlatedPred (G : FiniteStrategicGame) : EquilibriumProblem where
  S := CorrelatedStrategy G × G.ResponsePolicy
  I := Σ i : G.Player, G.Action i
  swap := fun p μρ μρ' =>
    μρ'.1 = μρ.1 ∧ ∃ si' : G.Action p.1,
      μρ'.2 = Function.update μρ.2 p.1 (Function.update (μρ.2 p.1) p.2 si')
  value := fun p μρ =>
    ∑ s ∈ Finset.univ.filter (fun s => s p.1 = p.2),
      μρ.1.prob s * G.payoff p.1 (Function.update s p.1 (μρ.2 p.1 p.2))

end FiniteStrategicGame

/-- Correlated equilibrium: The truthful section of `correlatedPred` is an equilibrium. -/
def IsCorrelatedEq (μ : CorrelatedStrategy G) : Prop :=
  G.correlatedPred.IsEquilibrium (μ, G.truthfulResponse)

@[simp] lemma correlatedPred_swap_iff (p : Σ i : G.Player, G.Action i)
    (μρ μρ' : CorrelatedStrategy G × G.ResponsePolicy) :
    G.correlatedPred.swap p μρ μρ' ↔
      μρ'.1 = μρ.1 ∧ ∃ si' : G.Action p.1,
        μρ'.2 = Function.update μρ.2 p.1 (Function.update (μρ.2 p.1) p.2 si') := Iff.rfl

@[simp] lemma correlatedPred_value_eq (p : Σ i : G.Player, G.Action i)
    (μρ : CorrelatedStrategy G × G.ResponsePolicy) :
    G.correlatedPred.value p μρ =
      ∑ s ∈ Finset.univ.filter (fun s => s p.1 = p.2),
        μρ.1.prob s * G.payoff p.1 (Function.update s p.1 (μρ.2 p.1 p.2)) := rfl

/-- Canonical user-facing characterization: For every player `i` and every pair of actions
`(si, si')`, the joint-weighted expected payoff from obeying recommendation `si` is at least the
expected payoff from deviating to `si'` on that fiber. The inequality is weighted by `prob(s)`, not
the conditional — the marginal denominator cancels on both sides. -/
theorem IsCorrelatedEq_iff (μ : CorrelatedStrategy G) :
    IsCorrelatedEq μ ↔
      ∀ (i : G.Player) (si si' : G.Action i),
        ∑ s ∈ Finset.univ.filter (fun s => s i = si), μ.prob s * G.payoff i s ≥
        ∑ s ∈ Finset.univ.filter (fun s => s i = si),
          μ.prob s * G.payoff i (Function.update s i si') := by
  unfold IsCorrelatedEq
  dsimp only [correlatedPred, EquilibriumProblem.IsEquilibrium]
  refine ⟨?_, ?_⟩
  · intro h i si si'
    have := h ⟨i, si⟩
      (μ, Function.update G.truthfulResponse i
            (Function.update (G.truthfulResponse i) si si'))
      ⟨rfl, si', rfl⟩
    simp only [truthfulResponse, Function.update_self] at this
    -- The truthful (LHS) section evaluates the payoff at the recommendation itself.
    have hLHS :
        ∑ s ∈ Finset.univ.filter (fun s => s i = si),
            μ.prob s * G.payoff i (Function.update s i si) =
          ∑ s ∈ Finset.univ.filter (fun s => s i = si),
            μ.prob s * G.payoff i s := by
      refine Finset.sum_congr rfl fun s hs => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      rw [← hs, Function.update_eq_self]
    rwa [hLHS] at this
  · intro h pair μρ' hswap
    obtain ⟨hμ, si', hρ'⟩ := hswap
    obtain ⟨i, si⟩ := pair
    have hLHS :
        ∑ s ∈ Finset.univ.filter (fun s => s i = si),
            μ.prob s *
              G.payoff i (Function.update s i ((μ, G.truthfulResponse).2 i si)) =
          ∑ s ∈ Finset.univ.filter (fun s => s i = si), μ.prob s * G.payoff i s := by
      refine Finset.sum_congr rfl fun s hs => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      simp only [truthfulResponse]
      rw [← hs, Function.update_eq_self]
    -- The deviated (RHS) section reads off `si'` via the updated response policy.
    have hρeval : μρ'.2 i si = si' := by rw [hρ']; simp
    rw [hLHS, show μρ'.1 = μ from hμ, hρeval]
    exact h i si si'

/-- If a mixed action is optimal against all pure deviations, then every support action is a best
reply. -/
lemma support_plays_best {α : Type*} [Fintype α] (σ : stdSimplex ℝ α) (f : α → ℝ)
    (si : α) (hpos : 0 < σ si) (hbr : ∀ y, ∑ a, σ a * f a ≥ f y) :
    ∀ y, f si ≥ f y := by
  intro y
  set M := ∑ a, σ a * f a
  have hle : ∀ a, f a ≤ M := fun a => hbr a
  have hsum_one : ∑ a, (σ : α → ℝ) a = 1 := σ.2.2
  -- The weighted slack `∑ σ a · (M − f a)` collapses to `M − M = 0`.
  have hsum_eq : ∑ a, σ a * (M - f a) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum_one, one_mul]
    exact sub_self M
  have hterm_nn : ∀ a, 0 ≤ σ a * (M - f a) :=
    fun a => mul_nonneg (σ.2.1 a) (sub_nonneg.mpr (hle a))
  have hterm_zero : ∀ a, σ a * (M - f a) = 0 := fun a =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hterm_nn a)).mp hsum_eq a (Finset.mem_univ a)
  have hfsi : f si = M := by
    rcases mul_eq_zero.mp (hterm_zero si) with h | h
    · exact absurd (le_of_eq h) (not_le.mpr hpos)
    · linarith
  linarith [hle y]

/-- Factor out the `i`-th component from a product distribution. -/
lemma prod_factor_i (σ : G.MixedStrategy) (i : G.Player) (si : G.Action i)
    (f : (Π j, G.Action j) → ℝ) :
    ∑ s ∈ Finset.univ.filter (fun s => s i = si),
      (∏ j, (σ j) (s j)) * f s =
    (σ i) si * ∑ s ∈ Finset.univ.filter (fun s => s i = si),
      (∏ j ∈ Finset.univ.erase i, (σ j) (s j)) * f s := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  rw [← mul_assoc]
  congr 1
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), hs]

/-- The filtered recommendation sum equals expected payoff with a pure strategy for player `i`. -/
lemma filtered_sum_eq_expectedPayoff (σ : G.MixedStrategy) (i : G.Player) (si : G.Action i) :
    ∑ s ∈ Finset.univ.filter (fun s => s i = si),
      (∏ j ∈ Finset.univ.erase i, (σ j) (s j)) * G.payoff i s =
    G.expectedPayoff i (update σ i (stdSimplex.vertex (S := ℝ) si)) := by
  unfold expectedPayoff
  conv_rhs =>
    arg 2; ext s
    rw [show (∏ j, (update σ i (stdSimplex.vertex (S := ℝ) si) j) (s j)) =
      (stdSimplex.vertex (S := ℝ) si) (s i) *
        ∏ j ∈ Finset.univ.erase i, (σ j) (s j) from by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]]
  have hsplit : ∀ s : Π j, G.Action j,
      (stdSimplex.vertex (S := ℝ) si) (s i) *
        (∏ j ∈ Finset.univ.erase i, (σ j) (s j)) * G.payoff i s =
      if s i = si then (∏ j ∈ Finset.univ.erase i, (σ j) (s j)) * G.payoff i s else 0 := by
    intro s
    by_cases h : s i = si
    · rw [if_pos h, h, stdSimplex.vertex_coe, Pi.single_eq_same, one_mul]
    · rw [if_neg h, stdSimplex.vertex_coe, Pi.single_eq_of_ne h, zero_mul, zero_mul]
  simp_rw [hsplit]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]

/-- The filtered recommendation sum with a deviation also equals expected payoff. -/
lemma filtered_sum_dev_eq_expectedPayoff (σ : G.MixedStrategy) (i : G.Player)
    (si si' : G.Action i) :
    ∑ s ∈ Finset.univ.filter (fun s => s i = si),
      (∏ j ∈ Finset.univ.erase i, (σ j) (s j)) * G.payoff i (Function.update s i si') =
    G.expectedPayoff i (update σ i (stdSimplex.vertex (S := ℝ) si')) := by
  -- Reindex the `s i = si` fiber onto the `s i = si'` fiber by `update s i si'`, with explicit
  -- inverse `update s i si`; the deviation only ever touches coordinate `i`.
  rw [← filtered_sum_eq_expectedPayoff σ i si']
  refine Finset.sum_bij' (fun s _ => Function.update s i si') (fun s _ => Function.update s i si)
    ?_ ?_ ?_ ?_ ?_
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_self]
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_self]
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    simp only [Function.update_idem, ← hs, Function.update_eq_self]
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    simp only [Function.update_idem, ← hs, Function.update_eq_self]
  · intro s _
    refine congrArg (· * _) (Finset.prod_congr rfl fun j hj => ?_)
    simp only [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- Every mixed Nash equilibrium induces a correlated equilibrium via the product distribution
`CorrelatedStrategy.ofMixed`. -/
theorem nash_is_correlated {σ : G.MixedStrategy}
    (hne : IsMixedNash σ) :
    IsCorrelatedEq (CorrelatedStrategy.ofMixed σ) := by
  rw [IsCorrelatedEq_iff]
  intro i si si'
  dsimp only [CorrelatedStrategy.ofMixed]
  simp only [CorrelatedStrategy.prob, FinDist.productD]
  change
    ∑ s ∈ Finset.univ.filter (fun s => s i = si),
      (∏ j, (σ j) (s j)) * G.payoff i s ≥
    ∑ s ∈ Finset.univ.filter (fun s => s i = si),
      (∏ j, (σ j) (s j)) * G.payoff i (Function.update s i si')
  rw [prod_factor_i σ i si (fun s => G.payoff i s),
      prod_factor_i σ i si (fun s => G.payoff i (Function.update s i si'))]
  by_cases hsi : (σ i) si = 0
  · simp [hsi]
  · have hpos : 0 < (σ i) si := lt_of_le_of_ne ((σ i).2.1 si) (Ne.symm hsi)
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hpos)
    rw [filtered_sum_eq_expectedPayoff, filtered_sum_dev_eq_expectedPayoff]
    have hbr : ∀ y, G.expectedPayoff i σ ≥ G.expectedPayoff i (update σ i y) :=
      ((G.isMixedNash_iff σ).mp hne) i
    have hlin : G.expectedPayoff i σ = G.expectedPayoff i (update σ i (σ i)) := by
      rw [Function.update_eq_self]
    rw [hlin, G.expectedPayoff_linear] at hbr
    exact support_plays_best (σ i)
      (fun a => G.expectedPayoff i (update σ i (stdSimplex.vertex (S := ℝ) a)))
      si hpos (fun y => hbr (stdSimplex.vertex (S := ℝ) y)) si'

/-- A correlated equilibrium exists for every finite game. -/
theorem exists_correlatedEq (G : FiniteStrategicGame) :
    ∃ μ : CorrelatedStrategy G, IsCorrelatedEq μ := by
  obtain ⟨σ, hσ⟩ := G.exists_mixedNash
  exact ⟨CorrelatedStrategy.ofMixed σ, nash_is_correlated hσ⟩

end
end Econlib.GameTheory
