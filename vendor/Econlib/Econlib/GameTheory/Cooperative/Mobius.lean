/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Cooperative.Operations

/-!
# Möbius inversion for TU games

The unanimity games `{u_T : T ⊆ Player}` form a basis for the vector space of TU games; the
coordinates of a game `G` in this basis are the **Harsanyi dividends** `δ_T(G)` (Harsanyi 1963).
This file establishes the reconstruction identity `harsanyiExpansion G = G` and its corollary
`∑ T ⊆ S, δ_T(G) = G.value S` (Möbius inversion on the Boolean lattice).

## Main definitions

* `TUGameOn.harsanyiExpansion`: The unanimity-basis reconstruction from Harsanyi dividends.

## Main statements

* `TUGameOn.sum_harsanyiDividend_eq_value`: Boolean-lattice Möbius inversion.
* `TUGameOn.harsanyiExpansion_eq`: Harsanyi expansion reconstructs the game.

## References

* Harsanyi, John C. 1963. “A Simplified Bargaining Model for the n-Person Cooperative Game.”
  *International Economic Review* 4 (2): 194. [https://doi.org/10.2307/2525487](https://doi.org/10.2307/2525487).

## Tags

cooperative game, harsanyi dividend, möbius inversion
-/

@[expose] public noncomputable section

namespace Econlib.GameTheory

namespace TUGameOn

variable {Player : Type*} [Fintype Player] [DecidableEq Player]

/-- The unanimity-basis reconstruction from Harsanyi dividends. -/
def harsanyiExpansion (G : TUGameOn Player) : TUGameOn Player :=
  sum ((Finset.univ : Finset Player).powerset) (fun T => smul (G.harsanyiDividend T) (unanimity T))

/-- The value of the Harsanyi expansion at `S`, expanded as the dividend-weighted sum of unanimity
values over all coalitions. -/
lemma harsanyiExpansion_value (G : TUGameOn Player) (S : Finset Player) :
    G.harsanyiExpansion.value S = ∑ T ∈ (Finset.univ : Finset Player).powerset,
      G.harsanyiDividend T * (unanimity T).value S := rfl

/-- The value of the Harsanyi expansion at `S` equals the sum of dividends over subsets of `S`. -/
lemma harsanyiExpansion_value_eq_sum_subset (G : TUGameOn Player)
    (S : Finset Player) :
    G.harsanyiExpansion.value S =
      ∑ T ∈ S.powerset, G.harsanyiDividend T := by
  rw [harsanyiExpansion_value]
  -- Only subsets `T ⊆ S` contribute: `unanimity T` vanishes at `S` otherwise, so the sum over
  -- `univ.powerset` collapses to the sum over `S.powerset`.
  rw [← Finset.sum_subset (s₁ := S.powerset)
      (fun T hT => Finset.mem_powerset.mpr
          ((Finset.mem_powerset.mp hT).trans (Finset.subset_univ S)))
        (fun T _ hTS => by
          rw [unanimity_value_of_not_subset fun h => hTS (Finset.mem_powerset.mpr h), mul_zero])]
  -- On `S.powerset` every `T` is a subset of `S`, so `(unanimity T).value S` is `1` when `T` is
  -- nonempty (and `0` on the empty set, where the dividend also vanishes).
  refine Finset.sum_congr rfl fun T hT => ?_
  rcases T.eq_empty_or_nonempty with hTempty | hTnon
  · simp [hTempty]
  · rw [unanimity_value_of_nonempty_subset hTnon (Finset.mem_powerset.mp hT), mul_one]

/-- Boolean-lattice Möbius inversion for Harsanyi dividends. -/
theorem sum_harsanyiDividend_eq_value (G : TUGameOn Player) (S : Finset Player) :
    ∑ T ∈ S.powerset, G.harsanyiDividend T = G.value S :=
  Finset.sum_powerset_booleanMobiusCoeff G.value S

/-- The Harsanyi expansion reconstructs the original game from its dividends. -/
theorem harsanyiExpansion_eq (G : TUGameOn Player) :
    G.harsanyiExpansion = G := by
  ext S
  rw [harsanyiExpansion_value_eq_sum_subset, sum_harsanyiDividend_eq_value]

end TUGameOn

end Econlib.GameTheory
