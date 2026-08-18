/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Equilibrium.Refinement
public import Econlib.GameTheory.Strategic.Basic
public import Econlib.Math.Combinatorics.Fin2

/-!
# Symmetric Two-Player Games

This file defines finite symmetric two-player games from a single action type and payoff function,
their symmetric Nash and ESS predicates, the replicator vector field, and a bridge to the ordinary
two-player strategic-form game.

## Main definitions

* `SymmetricGame`: Finite symmetric two-player games with one action type.
* `SymmetricGame.MixedStrategy`: Population states over the common action set.
* `SymmetricGame.symmetricPred`: Abstract equilibrium problem for symmetric Nash equilibrium.
* `SymmetricGame.IsSymmetricNash`: Symmetric Nash equilibrium.
* `SymmetricGame.essPred`: Refinement object for ESS.
* `SymmetricGame.IsESS`: Evolutionarily stable strategy.
* `SymmetricGame.toTwoPlayerGame`: Two-player strategic-form asymmetrization.
* `SymmetricGame.toSymmetricExistenceData`: Kakutani data for symmetric fixed points.

## Main statements

* `SymmetricGame.IsSymmetricNash_iff`: Concrete symmetric Nash best-response characterization.
* `SymmetricGame.sum_replicator_eq_zero`: The finite replicator vector field has zero total mass.
* `SymmetricGame.isSymmetricNash_iff_diagonal_isMixedNash`: Equivalence with mixed Nash in the
  two-player asymmetrization.
* `SymmetricGame.exists_symmetricNash`: Existence of symmetric mixed Nash equilibrium (Nash 1951).

## References

* Nash, John. 1951. “Non-Cooperative Games.” *The Annals of Mathematics* 54 (2): 286.
  [https://doi.org/10.2307/1969529](https://doi.org/10.2307/1969529).

## Tags

symmetric games, symmetric nash equilibrium, ess, replicator dynamics
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

/-- A symmetric two-player finite game.

No `Player` field: Symmetric games are intrinsically one-sided. Players are introduced externally
via `toTwoPlayerGame` for the bridge to `FiniteStrategicGame`. -/
structure SymmetricGame where
  Action : Type*
  [instFintypeAction : Fintype Action]
  [instDecidableEqAction : DecidableEq Action]
  [instInhabitedAction : Inhabited Action]
  payoff : Action → Action → ℝ

attribute [instance] SymmetricGame.instFintypeAction SymmetricGame.instDecidableEqAction
  SymmetricGame.instInhabitedAction

namespace SymmetricGame

variable (G : SymmetricGame)

/-- A population state / mixed strategy. -/
abbrev MixedStrategy := stdSimplex ℝ G.Action

/-- Payoff to pure action `a` against population state `x`. -/
def purePayoff (a : G.Action) (x : G.MixedStrategy) : ℝ :=
  ∑ b, x b * G.payoff a b

/-- Expected payoff to mixed strategy `x` against population state `y`. -/
def expectedPayoff (x y : G.MixedStrategy) : ℝ :=
  ∑ a, x a * G.purePayoff a y

/-- The equilibrium problem associated with symmetric Nash equilibrium. The strategy space is
`(own, opponent)` pairs; the swap relation fixes the opponent and lets the deviator change `own`. A
symmetric Nash equilibrium is an equilibrium of this problem at the diagonal `(x, x)`. -/
noncomputable def symmetricPred (G : SymmetricGame) : EquilibriumProblem :=
  let S := G.MixedStrategy × G.MixedStrategy
  let I := Fin 1
  { S := S
    I := I
    swap := fun _ p p' => p'.2 = p.2
    value := fun _ p => G.expectedPayoff p.1 p.2 }

/-- Symmetric Nash equilibrium. -/
def IsSymmetricNash (x : G.MixedStrategy) : Prop :=
  G.symmetricPred.IsEquilibrium (x, x)

@[simp] lemma symmetricPred_swap_iff (i : Fin 1)
    (p p' : G.MixedStrategy × G.MixedStrategy) :
    G.symmetricPred.swap i p p' ↔ p'.2 = p.2 := Iff.rfl

@[simp] lemma symmetricPred_value_eq (i : Fin 1) (p : G.MixedStrategy × G.MixedStrategy) :
    G.symmetricPred.value i p = G.expectedPayoff p.1 p.2 := rfl

/-- Concrete unfolding: Symmetric NE asks no profitable deviation against the symmetric opponent. -/
theorem IsSymmetricNash_iff (x : G.MixedStrategy) :
    G.IsSymmetricNash x ↔
      ∀ y : G.MixedStrategy, G.expectedPayoff x x ≥ G.expectedPayoff y x := by
  unfold IsSymmetricNash
  dsimp only [symmetricPred, EquilibriumProblem.IsEquilibrium]
  refine ⟨fun h y => h 0 (y, x) rfl, ?_⟩
  intro h _ p hp
  rw [show p = (p.1, x) from Prod.ext rfl hp]
  exact h p.1

/-- ESS validity predicate: Every mutant strategy `y ≠ x` indifferent against `x` at the NE level
is strictly worse against itself than `x` is. -/
def IsESSValid (x : G.MixedStrategy) : Prop :=
  ∀ y : G.MixedStrategy, y ≠ x →
    G.expectedPayoff y x = G.expectedPayoff x x →
      G.expectedPayoff x y > G.expectedPayoff y y

/-- Substrate refinement object for ESS. Deviation skeleton inherits from `symmetricPred`; the
validity predicate is the indifference→strict-dominance condition. The carrier is
`MixedStrategy × MixedStrategy`; the validity is evaluated at the diagonal entry `.1`. -/
noncomputable def essPred (G : SymmetricGame) : EquilibriumRefinement :=
  { G.symmetricPred with valid := fun p => p.1 = p.2 ∧ G.IsESSValid p.1 }

/-- Evolutionarily stable strategy. -/
structure IsESS (x : G.MixedStrategy) : Prop where
  /-- An ESS is a symmetric Nash equilibrium. -/
  isSymmetricNash : G.IsSymmetricNash x
  /-- The ESS validity condition: Indifferent mutants are strictly worse against themselves. -/
  essValid : G.IsESSValid x

@[simp] lemma essPred_swap_iff (i : Fin 1) (p p' : G.MixedStrategy × G.MixedStrategy) :
    G.essPred.swap i p p' ↔ p'.2 = p.2 := Iff.rfl

@[simp] lemma essPred_value_eq (i : Fin 1) (p : G.MixedStrategy × G.MixedStrategy) :
    G.essPred.value i p = G.expectedPayoff p.1 p.2 := rfl

/-- Substrate-uniform characterization of ESS at the diagonal. -/
theorem IsESS_iff (x : G.MixedStrategy) :
    G.IsESS x ↔ G.essPred.IsRefinedEquilibrium (x, x) := by
  constructor
  · rintro ⟨hne, hval⟩; exact ⟨⟨rfl, hval⟩, hne⟩
  · rintro ⟨⟨_, hval⟩, hne⟩; exact ⟨hne, hval⟩

/-- Replicator vector field at population state `x`. -/
def replicator (x : G.MixedStrategy) (a : G.Action) : ℝ :=
  x a * (G.purePayoff a x - G.expectedPayoff x x)

/-- Every ESS is a symmetric Nash equilibrium. -/
theorem IsESS.is_symmetricNash {x : G.MixedStrategy} (hx : G.IsESS x) :
    G.IsSymmetricNash x :=
  hx.isSymmetricNash

/-- The finite replicator vector field has zero total mass. -/
theorem sum_replicator_eq_zero (x : G.MixedStrategy) :
    ∑ a, G.replicator x a = 0 := by
  unfold replicator expectedPayoff
  simp only [purePayoff]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  have hsum : (∑ i, (x : G.Action → ℝ) i) = 1 := x.2.2
  rw [hsum, one_mul, sub_self]

/-! ## 2-player asymmetrization bridge -/

/-- The 2-player asymmetric strategic-form game induced by `G`: Both players have action set
`G.Action`; each receives `G.payoff own opp` (player `i` is "own" in the pair, the other index is
"opp"). -/
noncomputable def toTwoPlayerGame (G : SymmetricGame) : FiniteStrategicGame where
  toStrategicGame :=
    { Player := Fin 2
      Action := fun _ => G.Action
      payoff := fun i s => G.payoff (s i) (s (1 - i)) }
  instFintypePlayer := inferInstance
  instFintypeAction := fun _ => G.instFintypeAction
  instDecidableEqAction := fun _ => G.instDecidableEqAction

/-- Helper: On the 2-player asymmetrization at an arbitrary mixed profile `σ`, the expected payoff
to player `i` factorizes as the symmetric expected payoff of `σ i` against `σ (1-i)`. -/
lemma toTwoPlayerGame_expectedPayoff_apply (G : SymmetricGame)
    (σ : G.toTwoPlayerGame.MixedStrategy) (i : Fin 2) :
    G.toTwoPlayerGame.expectedPayoff i σ = G.expectedPayoff (σ i) (σ (1 - i)) := by
  let τ : Fin 2 → stdSimplex ℝ G.Action := σ
  have hLHS : G.toTwoPlayerGame.expectedPayoff i σ =
      ∑ a : G.Action, ∑ b : G.Action,
        τ 0 a * τ 1 b * G.payoff (![a, b] i) (![a, b] (1 - i)) := by
    change (∑ s : Fin 2 → G.Action, (∏ j : Fin 2, τ j (s j)) * G.payoff (s i) (s (1 - i))) =
      ∑ a : G.Action, ∑ b : G.Action,
        τ 0 a * τ 1 b * G.payoff (![a, b] i) (![a, b] (1 - i))
    rw [sum_piFinTwo]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    -- The transported summand has the profile `![a, b]`; expand the product
    -- `∏ j, τ j (![a, b] j) = τ 0 a * τ 1 b` and evaluate the vector literal at each coordinate.
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hLHS]
  fin_cases i
  · change (∑ a : G.Action, ∑ b : G.Action, τ 0 a * τ 1 b * G.payoff a b) =
      G.expectedPayoff (τ 0) (τ 1)
    unfold SymmetricGame.expectedPayoff SymmetricGame.purePayoff
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  · change (∑ a : G.Action, ∑ b : G.Action, τ 0 a * τ 1 b * G.payoff b a) =
      G.expectedPayoff (τ 1) (τ 0)
    unfold SymmetricGame.expectedPayoff SymmetricGame.purePayoff
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

/-- A mixed strategy `x` is a symmetric Nash equilibrium of `G` iff the constant profile
`fun _ => x` is a mixed Nash equilibrium of the two-player asymmetrization `G.toTwoPlayerGame`. -/
theorem isSymmetricNash_iff_diagonal_isMixedNash (G : SymmetricGame) (x : G.MixedStrategy) :
    G.IsSymmetricNash x ↔ G.toTwoPlayerGame.IsMixedNash (fun _ => x) := by
  rw [G.IsSymmetricNash_iff (x := x), G.toTwoPlayerGame.isMixedNash_iff (σ := fun _ => x)]
  constructor
  · intro h iP y
    have : ∀ (i : Fin 2) (y : stdSimplex ℝ G.Action),
        G.toTwoPlayerGame.expectedPayoff i (fun _ => x) ≥
        G.toTwoPlayerGame.expectedPayoff i (Function.update (fun _ : Fin 2 => x) i y) := by
      intro i y
      rw [G.toTwoPlayerGame_expectedPayoff_apply (fun _ => x) i,
        G.toTwoPlayerGame_expectedPayoff_apply
          (Function.update (fun _ : Fin 2 => x) i y) i]
      change G.expectedPayoff x x ≥
        G.expectedPayoff (Function.update (fun _ : Fin 2 => x) i y i)
                         (Function.update (fun _ : Fin 2 => x) i y (1 - i))
      have hne : (1 - i) ≠ i := by fin_cases i <;> decide
      simp only [Function.update_self, Function.update_of_ne hne]
      exact h y
    exact this iP y
  · intro h y
    have h0 := h (0 : Fin 2) y
    have aux :
        G.toTwoPlayerGame.expectedPayoff (0 : Fin 2) (fun _ => x) ≥
        G.toTwoPlayerGame.expectedPayoff (0 : Fin 2)
          (Function.update (fun _ : Fin 2 => x) (0 : Fin 2) y) → G.expectedPayoff x x ≥
            G.expectedPayoff y x := by
      intro hh
      rw [G.toTwoPlayerGame_expectedPayoff_apply (fun _ => x) 0,
        G.toTwoPlayerGame_expectedPayoff_apply
          (Function.update (fun _ : Fin 2 => x) (0 : Fin 2) y) 0] at hh
      simp only [Function.update_self] at hh
      exact hh
    exact aux h0

/-- Bundle `G` as `SymmetricExistenceData` for the diagonal best-response Kakutani argument.
Ambient space is `G.Action → ℝ`, the slice is the standard simplex, and the asymmetric payoff
`payoff own opp = G.expectedPayoff own opp`. -/
noncomputable def toSymmetricExistenceData (G : SymmetricGame) : SymmetricExistenceData where
  V := G.Action → ℝ
  Slice := stdSimplex ℝ G.Action
  hSlice_convex   := convex_stdSimplex ℝ G.Action
  hSlice_compact  := isCompact_stdSimplex ℝ G.Action
  hSlice_nonempty :=
    ⟨fun a => if a = default then 1 else 0,
     ⟨fun a => by dsimp; split_ifs <;> positivity, by simp [Finset.sum_ite_eq']⟩⟩
  payoff := G.expectedPayoff
  payoff_continuous := by
    unfold SymmetricGame.expectedPayoff SymmetricGame.purePayoff
    apply continuous_finset_sum
    intro a _
    refine Continuous.mul ?_ ?_
    · exact (continuous_apply a).comp (continuous_subtype_val.comp continuous_fst)
    · apply continuous_finset_sum
      intro b _
      refine Continuous.mul ?_ continuous_const
      exact (continuous_apply b).comp (continuous_subtype_val.comp continuous_snd)
  payoff_affine_in_own := fun opp => by
    let ψ : (G.Action → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun y =>
          ∑ a : G.Action, y a *
            (∑ b : G.Action, (opp : G.Action → ℝ) b * G.payoff a b)
        map_add' := by
          intro y₁ y₂
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [Pi.add_apply]
          ring
        map_smul' := by
          intro c y
          simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          simp only [Pi.smul_apply, smul_eq_mul]
          ring_nf }
    exact ⟨ψ.toAffineMap, fun _ => rfl⟩

/-- **Existence of symmetric Nash equilibrium** (Nash 1951): Every `SymmetricGame` admits a
symmetric mixed-strategy Nash equilibrium. -/
theorem exists_symmetricNash (G : SymmetricGame) :
    ∃ x : G.MixedStrategy, G.IsSymmetricNash x := by
  obtain ⟨xstar, hxstar⟩ := G.toSymmetricExistenceData.exists_symmetric_fixed_point
  exact ⟨xstar, (G.IsSymmetricNash_iff xstar).mpr hxstar⟩

end SymmetricGame

end Econlib.GameTheory
