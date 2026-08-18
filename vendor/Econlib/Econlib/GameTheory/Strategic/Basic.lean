/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Equilibrium.Existence
public import Econlib.Probability.FinDist.Simplex

/-!
# Strategic-Form Games and Nash Equilibrium

This file defines strategic-form games, their finite specialization, pure and mixed Nash
equilibrium predicates, and expected payoff under mixed strategies. It also instantiates the
Kakutani existence interface for finite mixed strategies and proves mixed Nash existence.

## Main definitions

* `StrategicGame`: Strategic-form games with dependent action spaces.
* `FiniteStrategicGame`: Finite strategic-form games.
* `StrategicGame.nashPred`: Abstract equilibrium problem for pure Nash equilibrium.
* `FiniteStrategicGame.MixedStrategy`: Mixed-strategy profiles.
* `FiniteStrategicGame.expectedPayoff`: Expected payoff under mixed-strategy profiles.
* `FiniteStrategicGame.mixedNashPred`: Abstract equilibrium problem for mixed Nash equilibrium.

## Main statements

* `StrategicGame.isNash_iff`: Concrete pure Nash best-response characterization.
* `FiniteStrategicGame.isMixedNash_iff`: Concrete mixed Nash best-response characterization.
* `FiniteStrategicGame.exists_mixedNash`: Existence of mixed Nash equilibrium in finite games (Nash
  1951).

## References

* Nash, John. 1951. “Non-Cooperative Games.” *The Annals of Mathematics* 54 (2): 286.
  [https://doi.org/10.2307/1969529](https://doi.org/10.2307/1969529).

## Tags

strategic games, nash equilibrium, mixed strategies, kakutani
-/

@[expose] public section

namespace Econlib.GameTheory

/-- A normal-form (strategic-form) game: Players, action spaces, and payoffs. -/
structure StrategicGame where
  Player : Type*
  Action : Player → Type*
  payoff : Player → (Π i, Action i) → ℝ
  [instInhabitedPlayer : Inhabited Player]
  [instDecidableEqPlayer : DecidableEq Player]
  [instInhabitedAction : ∀ i, Inhabited (Action i)]

attribute [instance] StrategicGame.instInhabitedPlayer StrategicGame.instDecidableEqPlayer
  StrategicGame.instInhabitedAction

namespace StrategicGame

variable (G : StrategicGame)

/-- The equilibrium problem associated with pure-strategy Nash equilibrium. The deviator index is
the player; permitted deviations are pointwise updates; the value is the raw payoff. -/
def nashPred : EquilibriumProblem where
  S := Π i, G.Action i
  I := G.Player
  swap i σ σ' := ∃ a : G.Action i, σ' = Function.update σ i a
  value := G.payoff

/-- A pure-strategy Nash equilibrium: No player can profitably deviate unilaterally. -/
def IsNash (x : Π i, G.Action i) : Prop :=
  G.nashPred.IsEquilibrium x

@[simp] lemma nashPred_swap_iff (i : G.Player) (σ σ' : Π i, G.Action i) :
    G.nashPred.swap i σ σ' ↔ ∃ a : G.Action i, σ' = Function.update σ i a := Iff.rfl

@[simp] lemma nashPred_value_eq (i : G.Player) (σ : Π i, G.Action i) :
    G.nashPred.value i σ = G.payoff i σ := rfl

/-- Concrete unfolding of pure Nash equilibrium: No profitable single-player deviation. -/
theorem isNash_iff (x : Π i, G.Action i) :
    G.IsNash x ↔
      ∀ (i : G.Player) (aᵢ : G.Action i),
        G.payoff i x ≥ G.payoff i (Function.update x i aᵢ) := by
  unfold IsNash nashPred EquilibriumProblem.IsEquilibrium
  constructor
  · intro h i aᵢ; exact h i (Function.update x i aᵢ) ⟨aᵢ, rfl⟩
  · intro h i x' ⟨a, ha⟩; subst ha; exact h i a

end StrategicGame

/-- A finite strategic-form game: Finitely many players and actions. -/
structure FiniteStrategicGame extends StrategicGame where
  [instFintypePlayer : Fintype Player]
  [instFintypeAction : ∀ i, Fintype (Action i)]
  [instDecidableEqAction : ∀ i, DecidableEq (Action i)]

attribute [instance] FiniteStrategicGame.instFintypePlayer
  FiniteStrategicGame.instFintypeAction
  FiniteStrategicGame.instDecidableEqAction

namespace FiniteStrategicGame

/-! ## Smart constructor: Finite strategic games on `Fin n` carriers

The `mkFin` smart constructor produces a `FiniteStrategicGame` whose abstract carriers `Player`
and `Action i` are *definitionally* `Fin nP` and `Fin (nA i)`. Marked `@[reducible]` so that
downstream `(0 : G.Player)` and `fin_cases (i : G.Player)` reduce through the field projection. See
`DesignNotes/WorkedExampleFrictions.md`. -/

/-- A finite strategic game on `Fin nP` players with `Fin (nA i)` actions per player. -/
@[reducible] def mkFin
    (nP : ℕ) [NeZero nP] (nA : Fin nP → ℕ) [∀ i, NeZero (nA i)]
    (payoff : (i : Fin nP) → (∀ j, Fin (nA j)) → ℝ) :
    FiniteStrategicGame where
  Player := Fin nP
  Action := fun i => Fin (nA i)
  payoff := payoff

@[simp] lemma mkFin_Player
    (nP : ℕ) [NeZero nP] (nA : Fin nP → ℕ) [∀ i, NeZero (nA i)]
    (payoff : (i : Fin nP) → (∀ j, Fin (nA j)) → ℝ) :
    (mkFin nP nA payoff).Player = Fin nP := rfl

@[simp] lemma mkFin_Action
    (nP : ℕ) [NeZero nP] (nA : Fin nP → ℕ) [∀ i, NeZero (nA i)]
    (payoff : (i : Fin nP) → (∀ j, Fin (nA j)) → ℝ) (i : Fin nP) :
    (mkFin nP nA payoff).Action i = Fin (nA i) := rfl

@[simp] lemma mkFin_payoff
    (nP : ℕ) [NeZero nP] (nA : Fin nP → ℕ) [∀ i, NeZero (nA i)]
    (payoff : (i : Fin nP) → (∀ j, Fin (nA j)) → ℝ) :
    (mkFin nP nA payoff).payoff = payoff := rfl

variable {G : FiniteStrategicGame}

instance instInhabitedActionOf (i : G.Player) : Inhabited (G.Action i) := G.instInhabitedAction i
instance instFintypeActionOf (i : G.Player) : Fintype (G.Action i) := G.instFintypeAction i
instance instDecidableEqActionOf (i : G.Player) : DecidableEq (G.Action i) :=
  G.instDecidableEqAction i

abbrev ActionProfile (G : FiniteStrategicGame) := Π i, G.Action i

variable (G) in
/-- A mixed-strategy profile: Each player chooses a distribution over their actions. -/
abbrev MixedStrategy := (i : G.Player) → stdSimplex ℝ (G.Action i)

/-- Expected payoff to player `i` under mixed-strategy profile `σ`. -/
noncomputable def expectedPayoff (G : FiniteStrategicGame) (i : G.Player)
    (σ : G.MixedStrategy) : ℝ :=
  ∑ s : G.ActionProfile, (∏ j, (σ j) (s j)) * G.payoff i s

/-- `expectedPayoff` as a sum over pure profiles, each weighted by the product of the players'
mixed-action probabilities. The discoverable entry rewrite for closed-form mixed-payoff
calculations. -/
theorem expectedPayoff_eq_sum (G : FiniteStrategicGame) (i : G.Player) (σ : G.MixedStrategy) :
    G.expectedPayoff i σ = ∑ s : G.ActionProfile, (∏ j, (σ j) (s j)) * G.payoff i s := rfl

/-- The degenerate mixed strategy that puts probability one on a pure action profile. -/
noncomputable def pureMixedStrategy (G : FiniteStrategicGame) (s : G.ActionProfile) :
    G.MixedStrategy :=
  fun i => stdSimplex.vertex (S := ℝ) (s i)

/-- The support of a mixed strategy for one player. -/
def support {G : FiniteStrategicGame} {i : G.Player}
    (σᵢ : stdSimplex ℝ (G.Action i)) : Set (G.Action i) :=
  {a | 0 < σᵢ a}

open Function in
lemma expectedPayoff_linear (i : G.Player) (σ : G.MixedStrategy)
    (y : stdSimplex ℝ (G.Action i)) :
    G.expectedPayoff i (update σ i y) =
    ∑ s : G.Action i, y s *
      G.expectedPayoff i (update σ i (stdSimplex.vertex (S := ℝ) s)) := by
  unfold expectedPayoff
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext f
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]; congr 1
  have split_prod (z : stdSimplex ℝ (G.Action i)) : ∏ j, (update σ i z j) (f j) =
      z (f i) * ∏ j ∈ Finset.univ.erase i, (σ j) (f j) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), update_self]
    refine congrArg _ (Finset.prod_congr rfl fun j hj => ?_)
    rw [update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [split_prod]
  -- Only the `s = f i` summand survives: `y s * vertex s (f i) = Pi.single s (y s) (f i)`.
  have h1 : y (f i) = ∑ s, y s * (stdSimplex.vertex (S := ℝ) s) (f i) := by
    simp_rw [stdSimplex.vertex_coe, Pi.single_apply, mul_ite, mul_one, mul_zero,
      ← Pi.single_apply]
    rw [Finset.sum_pi_single, if_pos (Finset.mem_univ _)]
  rw [h1, Finset.sum_mul]; congr 1; ext s
  rw [mul_assoc, split_prod]

open Function in
/-- If each opponent `j ≠ i` plays the vertex at `b j`, then summing any real functional `F` over
action profiles against the product of marginals `∏ j, σ j (c j)` reduces to a one-dimensional sum
over player `i`'s own actions, with every opponent held at `b`. -/
lemma sum_prod_marginal_pin (i : G.Player) (σ : G.MixedStrategy) (b : G.ActionProfile)
    (hpin : ∀ j, j ≠ i → σ j = stdSimplex.vertex (S := ℝ) (b j))
    (F : G.ActionProfile → ℝ) :
    (∑ c : G.ActionProfile, (∏ j, (σ j) (c j)) * F c) =
      ∑ aᵢ : G.Action i, (σ i) aᵢ * F (Function.update b i aᵢ) := by
  have hterm : ∀ c : G.ActionProfile,
      (∏ j, (σ j) (c j)) * F c =
        if c = Function.update b i (c i)
          then (σ i) (c i) * F c else 0 := by
    intro c
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have herase : (∏ j ∈ Finset.univ.erase i, (σ j) (c j)) =
        if ∀ j ∈ Finset.univ.erase i, c j = b j then (1 : ℝ) else 0 := by
      have hcongr : (∏ j ∈ Finset.univ.erase i, (σ j) (c j)) =
          ∏ j ∈ Finset.univ.erase i, if c j = b j then (1 : ℝ) else 0 := by
        refine Finset.prod_congr rfl fun j hj => ?_
        rw [hpin j (Finset.ne_of_mem_erase hj), stdSimplex.vertex_coe, Pi.single_apply]
      rw [hcongr, Finset.prod_boole]
      congr 1
    rw [herase]
    have hpred : (∀ j ∈ Finset.univ.erase i, c j = b j) ↔
        c = Function.update b i (c i) := by
      constructor
      · intro h
        funext j
        by_cases hj : j = i
        · subst hj; rw [Function.update_self]
        · rw [Function.update_of_ne hj]
          exact h j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
      · intro h j hj
        have hji : j ≠ i := Finset.ne_of_mem_erase hj
        have := congrFun h j
        rwa [Function.update_of_ne hji] at this
    by_cases hc : c = Function.update b i (c i)
    · rw [if_pos (hpred.mpr hc), if_pos hc, mul_one]
    · rw [if_neg (fun h => hc (hpred.mp h)), if_neg hc, mul_zero, zero_mul]
  rw [Finset.sum_congr rfl (fun c _ => hterm c)]
  -- Filter to profiles matching `update b i (c i)`, then reindex along `aᵢ ↦ update b i aᵢ`.
  rw [← Finset.sum_filter (fun c => c = Function.update b i (c i))]
  refine Finset.sum_bij' (fun c _ => c i) (fun aᵢ _ => Function.update b i aᵢ)
    ?_ ?_ ?_ ?_ ?_
  · intro c _; exact Finset.mem_univ _
  · intro aᵢ _
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simp only [Function.update_self]
  · intro c hc
    have hc' : c = Function.update b i (c i) := (Finset.mem_filter.mp hc).2
    exact hc'.symm
  · intro aᵢ _
    simp only [Function.update_self]
  · intro c hc
    have hc' : c = Function.update b i (c i) := (Finset.mem_filter.mp hc).2
    exact congrArg (fun d => (σ i) (c i) * F d) hc'

/-- The equilibrium problem associated with mixed-strategy Nash equilibrium. The deviator index is
the player; permitted deviations are pointwise updates of mixed strategies; the value is the
expected payoff. -/
noncomputable def mixedNashPred (G : FiniteStrategicGame) : EquilibriumProblem where
  S := G.MixedStrategy
  I := G.Player
  swap i σ σ' := ∃ y : stdSimplex ℝ (G.Action i), σ' = Function.update σ i y
  value := G.expectedPayoff

/-- A mixed-strategy Nash equilibrium: No player can gain by changing their mixed strategy. -/
def IsMixedNash (σ : G.MixedStrategy) : Prop :=
  G.mixedNashPred.IsEquilibrium σ

@[simp] lemma mixedNashPred_swap_iff (i : G.Player) (σ σ' : G.MixedStrategy) :
    G.mixedNashPred.swap i σ σ' ↔
      ∃ y : stdSimplex ℝ (G.Action i), σ' = Function.update σ i y :=
  Iff.rfl

@[simp] lemma mixedNashPred_value_eq (i : G.Player) (σ : G.MixedStrategy) :
    G.mixedNashPred.value i σ = G.expectedPayoff i σ := rfl

/-- Concrete unfolding of mixed Nash equilibrium. -/
theorem isMixedNash_iff (σ : G.MixedStrategy) :
    G.IsMixedNash σ ↔
    ∀ (i : G.Player) (y : stdSimplex ℝ (G.Action i)),
      G.expectedPayoff i σ ≥ G.expectedPayoff i (Function.update σ i y) := by
  unfold IsMixedNash mixedNashPred EquilibriumProblem.IsEquilibrium
  constructor
  · intro h i y; exact h i (Function.update σ i y) ⟨y, rfl⟩
  · intro h i σ' ⟨y, hy⟩; subst hy; exact h i y

/-- **Indifference characterization.** If at the mixed profile `σ`, every player is indifferent
between their equilibrium payoff and the deviation to any pure action (the opponents being held at
`σ`), then `σ` is a mixed Nash equilibrium. This is the standard textbook primitive for verifying
interior mixed equilibria, where the equilibrium-supporting deviator must be exactly indifferent
across their pure actions. -/
theorem isMixedNash_of_vertex_indifference (σ : G.MixedStrategy)
    (h : ∀ (i : G.Player) (a : G.Action i),
      G.expectedPayoff i σ = G.expectedPayoff i
        (Function.update σ i (stdSimplex.vertex (S := ℝ) a))) :
    G.IsMixedNash σ := by
  rw [isMixedNash_iff]
  intro i y
  rw [expectedPayoff_linear i σ y]
  -- Each summand `y s * expectedPayoff i (update σ i (vertex s))` equals
  -- `y s * expectedPayoff i σ`. Summing: `(∑ y s) * expectedPayoff i σ = expectedPayoff i σ`.
  have hsum_one : ∑ s : G.Action i, (y : G.Action i → ℝ) s = 1 := y.2.2
  -- Replace each `payoff(vertex s)` by `payoff σ` via indifference, factor it out, sum the weights.
  have eq : (∑ s : G.Action i, (y : G.Action i → ℝ) s *
        G.expectedPayoff i (Function.update σ i (stdSimplex.vertex (S := ℝ) s))) =
        G.expectedPayoff i σ := by
    simp_rw [← h i]
    rw [← Finset.sum_mul, hsum_one, one_mul]
  rw [eq]

end FiniteStrategicGame

/-! ## Nash Equilibrium Existence -/

section NashExistence
open FiniteStrategicGame

variable (G : FiniteStrategicGame)

/-- Bundle a finite strategic game as `NashExistenceData`: Per-player slice is the standard simplex
over actions, payoff is the expected payoff. The strategy ambient is `Action i → ℝ`, which is
canonically a finite-dimensional real-normed space. -/
noncomputable def FiniteStrategicGame.toNashExistenceData (G : FiniteStrategicGame) :
    NashExistenceData where
  Player := G.Player
  V := fun i => G.Action i → ℝ
  Slice := fun i => stdSimplex ℝ (G.Action i)
  hSlice_convex := fun i => convex_stdSimplex ℝ (G.Action i)
  hSlice_compact := fun i => isCompact_stdSimplex ℝ (G.Action i)
  hSlice_nonempty := fun i =>
    ⟨fun j => if j = default then 1 else 0,
     ⟨fun j => by dsimp; split_ifs <;> positivity, by simp [Finset.sum_ite_eq']⟩⟩
  payoff := fun i σ => G.expectedPayoff i σ
  payoff_continuous := fun i => by
    unfold expectedPayoff
    refine continuous_finset_sum _ fun s _ => ?_
    refine (continuous_finset_prod _ fun j _ => ?_).mul continuous_const
    exact (continuous_apply (s j)).comp
      (continuous_subtype_val.comp (continuous_apply j))
  payoff_affine_in_own := fun i σ => by
    let ψ : (G.Action i → ℝ) →ₗ[ℝ] ℝ := {
      toFun := fun y =>
        ∑ s : Π j, G.Action j,
          (∏ j ∈ Finset.univ.erase i, ((σ j).1 (s j))) * y (s i) * G.payoff i s
      map_add' := by
        intro y₁ y₂
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Pi.add_apply]
        ring
      map_smul' := by
        intro c y
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
    }
    refine ⟨ψ.toAffineMap, ?_⟩
    intro y
    unfold expectedPayoff
    refine Finset.sum_congr rfl fun s _ => ?_
    have h_split : (∏ j, (Function.update σ i y j) (s j)) =
        y.1 (s i) * ∏ j ∈ Finset.univ.erase i, (σ j).1 (s j) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
      refine congrArg _ (Finset.prod_congr rfl fun j hj => ?_)
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rfl
    rw [h_split]
    ring

namespace FiniteStrategicGame

/-- **Nash's theorem** (Nash 1951): Every finite strategic game has a mixed-strategy Nash
equilibrium. -/
theorem exists_mixedNash (G : FiniteStrategicGame) :
    ∃ σ : G.MixedStrategy, IsMixedNash σ := by
  obtain ⟨σ, hσ⟩ := G.toNashExistenceData.exists_equilibrium
  refine ⟨σ, ?_⟩
  rw [isMixedNash_iff]
  intro i y
  exact hσ i (Function.update σ i y) ⟨y, rfl⟩

end FiniteStrategicGame

end NashExistence

end Econlib.GameTheory
