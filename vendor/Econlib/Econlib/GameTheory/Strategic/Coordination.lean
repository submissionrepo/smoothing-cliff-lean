/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic

/-!
# Symmetric Coordination Games with Strategic Complementarities

This file defines a one-dimensional symmetric coordination game where the population action level
lies in `[0, 1]` and the payoff from acting is continuous and monotone on that interval. It proves
the boundary pure equilibria and interior equilibrium existence results used for coordination
models with strategic complementarities.

## Main definitions

* `SymCoordGame`: Continuous monotone payoff model on `[0, 1]`.
* `SymCoordGame.isSymmetricBNE`: Symmetric best-response condition on `[0, 1]`.
* `StrictSymCoordGame`: Symmetric coordination games with strictly increasing payoff.

## Main statements

* `SymCoordGame.reform_equilibrium`: `1` is a symmetric BNE when payoff at `1` is nonnegative.
* `SymCoordGame.no_reform_equilibrium`: `0` is a symmetric BNE when payoff at `0` is nonpositive.
* `SymCoordGame.multiple_equilibria`: Both boundary equilibria coexist under opposing signs.
* `SymCoordGame.mixed_equilibrium_exists`: The intermediate value theorem gives an interior zero.
* `StrictSymCoordGame.mixed_equilibrium_unique`: Strict monotonicity gives uniqueness of an
  interior zero.

## Tags

coordination games, strategic complementarities, symmetric equilibrium
-/

@[expose] public section

open Set

namespace Econlib.GameTheory

/-- A symmetric coordination game parameterized by a payoff function on `[0, 1]`. The payoff
represents the net benefit of acting when others act with probability `σ`. -/
structure SymCoordGame where
  /-- Net payoff from acting when others act with probability `σ`. -/
  payoff : ℝ → ℝ
  /-- The payoff is continuous on `[0, 1]`. -/
  continuous : ContinuousOn payoff (Icc 0 1)
  /-- Strategic complementarity: Payoff is monotone increasing. -/
  monotone : MonotoneOn payoff (Icc 0 1)

namespace SymCoordGame

variable (G : SymCoordGame)

/-- A symmetric BNE: `σ ∈ [0, 1]` is a best response to itself.

* If reforming is strictly profitable given others play `σ`, then `σ = 1`.
* If reforming is strictly unprofitable, then `σ = 0`.
* If indifferent, any `σ ∈ [0, 1]` is consistent. -/
def isSymmetricBNE (σ : ℝ) : Prop :=
  σ ∈ Icc 0 1 ∧
  (G.payoff σ > 0 → σ = 1) ∧
  (G.payoff σ < 0 → σ = 0)

/-- If `payoff σ = 0` and `σ ∈ [0, 1]`, then `σ` is a symmetric BNE. -/
theorem mixed_equilibrium_is_BNE {σ : ℝ} (hσ : σ ∈ Icc 0 1)
    (h : G.payoff σ = 0) : G.isSymmetricBNE σ :=
  ⟨hσ, fun hgt => absurd h (by linarith), fun hlt => absurd h (by linarith)⟩

/-- The full-action profile `1` is a symmetric BNE when payoff at full action is nonnegative. -/
theorem reform_equilibrium (h : G.payoff 1 ≥ 0) : G.isSymmetricBNE 1 :=
  ⟨⟨zero_le_one, le_rfl⟩, fun _ => rfl, fun hlt => absurd hlt (by linarith)⟩

/-- The no-action profile `0` is a symmetric BNE when payoff at no action is nonpositive. -/
theorem no_reform_equilibrium (h : G.payoff 0 ≤ 0) : G.isSymmetricBNE 0 :=
  ⟨⟨le_rfl, zero_le_one⟩, fun hgt => absurd hgt (by linarith), fun _ => rfl⟩

/-- Coordination failure: Both `0` and `1` are symmetric BNEs under opposing payoff signs. -/
theorem multiple_equilibria
    (h_low : G.payoff 0 < 0) (h_high : G.payoff 1 > 0) :
    G.isSymmetricBNE 0 ∧ G.isSymmetricBNE 1 :=
  ⟨no_reform_equilibrium G h_low.le, reform_equilibrium G h_high.le⟩

/-- In the multiplicity region, a mixed equilibrium exists by IVT. -/
theorem mixed_equilibrium_exists
    (h_low : G.payoff 0 < 0) (h_high : 0 < G.payoff 1) :
    ∃ σ ∈ Ioo 0 1, G.payoff σ = 0 :=
  intermediate_value_Ioo zero_le_one G.continuous ⟨h_low, h_high⟩

/-- The mixed equilibrium from IVT is a BNE. -/
theorem mixed_equilibrium_exists_BNE
    (h_low : G.payoff 0 < 0) (h_high : 0 < G.payoff 1) :
    ∃ σ ∈ Ioo 0 1, G.isSymmetricBNE σ := by
  obtain ⟨σ, hσ, hpσ⟩ := mixed_equilibrium_exists G h_low h_high
  exact ⟨σ, hσ, mixed_equilibrium_is_BNE G (Ioo_subset_Icc_self hσ) hpσ⟩

end SymCoordGame

/-- Strict strategic complementarity: Payoff is strictly increasing on `[0, 1]`. This ensures
uniqueness of the mixed equilibrium. -/
structure StrictSymCoordGame extends SymCoordGame where
  strictMono : StrictMonoOn payoff (Icc 0 1)

namespace StrictSymCoordGame

variable (G : StrictSymCoordGame)

/-- Under strict complementarity, the mixed equilibrium is unique. -/
theorem mixed_equilibrium_unique
    {σ₁ σ₂ : ℝ} (hσ₁ : σ₁ ∈ Ioo 0 1) (hσ₂ : σ₂ ∈ Ioo 0 1)
    (h₁ : G.payoff σ₁ = 0) (h₂ : G.payoff σ₂ = 0) :
    σ₁ = σ₂ := by
  rcases lt_trichotomy σ₁ σ₂ with h | h | h
  · linarith [G.strictMono (Ioo_subset_Icc_self hσ₁) (Ioo_subset_Icc_self hσ₂) h]
  · exact h
  · linarith [G.strictMono (Ioo_subset_Icc_self hσ₂) (Ioo_subset_Icc_self hσ₁) h]

end StrictSymCoordGame

end Econlib.GameTheory
