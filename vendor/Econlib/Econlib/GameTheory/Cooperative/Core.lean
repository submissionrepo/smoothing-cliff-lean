/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Cooperative.Shapley
import Econlib.Math.Combinatorics.FiniteOrder
import Mathlib.Algebra.BigOperators.Field

/-!
# The core, imputations, and convex games

This file collects the cooperative-game payoff-vector predicates: Efficiency, individual
rationality, imputations, the **core**, and convexity (supermodularity of the characteristic
function). It also contains the single-game form of Shapley efficiency and the result that in
convex games the Shapley value lies in the core.

## Main definitions

* `TUGameOn.IsEfficient`: Efficiency for the grand coalition.
* `TUGameOn.IsIndividuallyRational`: Individual rationality.
* `TUGameOn.IsImputation`: Efficiency and individual rationality.
* `TUGameOn.IsCore`: Core membership.
* `TUGameOn.IsConvex`: Supermodularity of the characteristic function.

## Main statements

* `TUGameOn.shapleyValue_efficient`: Shapley value satisfies efficiency.
* `TUGameOn.shapleyValue_mem_core_of_convex`: In convex games, the Shapley value is in the core.

## References

* Gillies, Donald B. 1959. “Solutions to General Non-Zero-Sum Games.” In *Contributions to the
  Theory of Games, Volume IV*, edited by A. W. Tucker and R. D. Luce. Princeton University Press.

## Tags

cooperative game, core, convex game, Shapley value
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

namespace TUGameOn

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- The grand coalition. -/
-- `G` is unused in the body but required so `G.grandCoalition` dot notation resolves.
def grandCoalition (_G : TUGameOn Player) : Finset Player := Finset.univ

/-- Coalition payoff under a payoff vector. -/
-- `G` is unused in the body but required so `G.coalitionPayoff` dot notation resolves.
def coalitionPayoff (_G : TUGameOn Player) (x : Player → ℝ) (S : Finset Player) : ℝ :=
  ∑ i ∈ S, x i

/-- Efficiency for the grand coalition. -/
def IsEfficient (G : TUGameOn Player) (x : G.PayoffVector) : Prop :=
  G.coalitionPayoff x G.grandCoalition = G.value G.grandCoalition

@[simp] lemma isEfficient_iff_sum_univ (G : TUGameOn Player) (x : G.PayoffVector) :
    G.IsEfficient x ↔ ∑ i : Player, x i = G.value G.grandCoalition := by rfl

/-- Individual rationality. -/
def IsIndividuallyRational (G : TUGameOn Player) (x : G.PayoffVector) : Prop :=
  ∀ i, G.value {i} ≤ x i

/-- An imputation is efficient and individually rational. -/
structure IsImputation (G : TUGameOn Player) (x : G.PayoffVector) : Prop where
  /-- The payoff vector is efficient. -/
  efficient : G.IsEfficient x
  /-- The payoff vector is individually rational. -/
  individuallyRational : G.IsIndividuallyRational x

/-- A payoff vector is in the **core** (Gillies 1959) if every coalition receives at least its
characteristic value and the grand coalition receives exactly its value. -/
structure IsCore (G : TUGameOn Player) (x : G.PayoffVector) : Prop where
  /-- The payoff vector is efficient. -/
  efficient : G.IsEfficient x
  /-- Every coalition receives at least its characteristic value. -/
  coalitionRational : ∀ S : Finset Player, G.value S ≤ G.coalitionPayoff x S

/-- Convex cooperative games are supermodular over coalition union/intersection. -/
def IsConvex (G : TUGameOn Player) : Prop :=
  ∀ S T : Finset Player, G.value S + G.value T ≤ G.value (S ∪ T) + G.value (S ∩ T)

/-- In a convex game, marginal contributions are monotone in the coalition that the player joins. -/
theorem IsConvex.marginal_monotone {G : TUGameOn Player} (hG : G.IsConvex)
    {S T : Finset Player} {i : Player}
    (hST : S ⊆ T) (hiT : i ∉ T) :
    G.marginalContribution i S ≤ G.marginalContribution i T := by
  unfold marginalContribution
  have hconv := hG (insert i S) T
  have hunion : insert i S ∪ T = insert i T := by
    rw [Finset.insert_union, Finset.union_eq_right.mpr hST]
  have hinter : insert i S ∩ T = S := by
    rw [Finset.insert_inter_of_notMem hiT, Finset.inter_eq_left.mpr hST]
  rw [hunion, hinter] at hconv
  linarith

/-- Shapley value satisfies efficiency (single-game form). -/
theorem shapleyValue_efficient (G : TUGameOn Player) : G.IsEfficient G.shapleyValue :=
  ValueRule.shapley_satisfiesEfficiency G

/-- In a convex game, every coalition receives at least its worth under the Shapley payoff
vector. -/
theorem shapleyValue_coalitionPayoff_ge_of_convex {G : TUGameOn Player} (hG : G.IsConvex)
    (S : Finset Player) :
    G.value S ≤ G.coalitionPayoff G.shapleyValue S := by
  let nfac : ℝ := ((Fintype.card Player).factorial : ℝ)
  have hnfac_pos : 0 < nfac := by
    dsimp [nfac]
    exact_mod_cast Nat.factorial_pos (Fintype.card Player)
  have hcard_orders :
      Fintype.card (FiniteOrder Player) =
        (Fintype.card Player).factorial := by
    dsimp [FiniteOrder]
    exact Fintype.card_equiv (Fintype.equivFin Player)
  have hshapley : ∀ i : Player,
      G.shapleyValue i =
        (∑ ω : FiniteOrder Player,
          (G.value (insert i (ω.predecessors i)) - G.value (ω.predecessors i))) / nfac := by
    intro i
    unfold shapleyValue marginalContribution shapleyWeight nfac
    exact FiniteOrder.weighted_marginal_eq_order_sum_div_factorial G.value i
  have hcoalition :
      G.coalitionPayoff G.shapleyValue S =
        (∑ ω : FiniteOrder Player,
          ∑ i ∈ S,
            (G.value (insert i (ω.predecessors i)) - G.value (ω.predecessors i))) / nfac := by
    unfold coalitionPayoff
    calc
      ∑ i ∈ S, G.shapleyValue i = ∑ i ∈ S, (∑ ω : FiniteOrder Player,
              (G.value (insert i (ω.predecessors i)) - G.value (ω.predecessors i))) / nfac :=
            Finset.sum_congr rfl fun i _ => hshapley i
      _ = (∑ i ∈ S, ∑ ω : FiniteOrder Player,
            (G.value (insert i (ω.predecessors i)) - G.value (ω.predecessors i))) / nfac := by
          rw [Finset.sum_div]
      _ = (∑ ω : FiniteOrder Player, ∑ i ∈ S,
            (G.value (insert i (ω.predecessors i)) - G.value (ω.predecessors i))) / nfac := by
          rw [Finset.sum_comm]
  have hmono :
      ∀ {A B : Finset Player} {i : Player}, A ⊆ B → i ∉ B →
        G.value (insert i A) - G.value A ≤ G.value (insert i B) - G.value B := by
    intro A B i hAB hiB
    have h := IsConvex.marginal_monotone (G := G) hG hAB hiB
    simpa [marginalContribution] using h
  have horder_lower :
      ∀ ω : FiniteOrder Player, G.value S ≤ ∑ i ∈ S,
        (G.value (insert i (ω.predecessors i)) - G.value (ω.predecessors i)) := fun ω =>
    FiniteOrder.value_le_sum_marginal_predecessors_of_marginal_mono G.value G.value_empty hmono ω S
  have hsum_lower : nfac * G.value S ≤ ∑ ω : FiniteOrder Player, ∑ i ∈ S,
      (G.value (insert i (ω.predecessors i)) - G.value (ω.predecessors i)) := by
    have hsum_const :
        (∑ _ω : FiniteOrder Player, G.value S) = nfac * G.value S := by
      rw [Finset.sum_const, nsmul_eq_mul]
      simp [nfac, hcard_orders]
    rw [← hsum_const]
    exact Finset.sum_le_sum fun ω _ => horder_lower ω
  rw [hcoalition]
  exact (le_div_iff₀ hnfac_pos).2 (by rw [mul_comm]; exact hsum_lower)

/-- In convex games, the Shapley value belongs to the core. -/
theorem shapleyValue_mem_core_of_convex {G : TUGameOn Player} (hG : G.IsConvex) :
    G.IsCore G.shapleyValue :=
  ⟨G.shapleyValue_efficient, shapleyValue_coalitionPayoff_ge_of_convex hG⟩

end TUGameOn

end Econlib.GameTheory
