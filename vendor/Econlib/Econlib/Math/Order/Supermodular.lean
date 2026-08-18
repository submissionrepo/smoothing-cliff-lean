/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic

/-!
# Supermodular real-valued functions

This file defines supermodularity for a bivariate real-valued function on a product of linear
orders (the increasing-differences condition `u θ₂ x₂ + u θ₁ x₁ ≥ u θ₂ x₁ + u θ₁ x₂`) and for a
multivariate function on the product lattice `Fin n → ℝ` (`u (x ⊔ y) + u (x ⊓ y) ≥ u x + u y`), and
proves that the two agree on `Fin 2 → ℝ`.

## Main definitions

* `Supermodular` — bivariate supermodularity via increasing differences.
* `MultivariateSupermodular` — supermodularity over the product lattice `Fin n → ℝ`.

## Main results

* `multivariateSupermodular_iff_supermodular` — on `Fin 2 → ℝ`, multivariate supermodularity is
  equivalent to bivariate supermodularity.
* `Supermodular.iff_increasing_differences` — supermodularity restated as the
  increasing-differences inequality.

## Tags

supermodular, increasing differences, lattice, submodular
-/

@[expose] public section

/-- `u` is **supermodular** if for all `θ₁ ≤ θ₂` and `x₁ ≤ x₂`,
`u(θ₂, x₂) + u(θ₁, x₁) ≥ u(θ₂, x₁) + u(θ₁, x₂)` — the **increasing differences** condition. -/
def Supermodular [LinearOrder Θ] [LinearOrder X] (u : Θ → X → ℝ) : Prop :=
  ∀ (θ₁ θ₂ : Θ) (x₁ x₂ : X), θ₁ ≤ θ₂ → x₁ ≤ x₂ →
    u θ₂ x₂ + u θ₁ x₁ ≥ u θ₂ x₁ + u θ₁ x₂

/-- Multivariate supermodularity over the product lattice `Fin n → ℝ`:
`u (x ⊔ y) + u (x ⊓ y) ≥
u x + u y`, with `⊔`/`⊓` the pointwise max/min from Mathlib's Pi-lattice
instances. -/
def MultivariateSupermodular {n : ℕ} (u : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, u (x ⊔ y) + u (x ⊓ y) ≥ u x + u y

/-- Bridge between multivariate supermodularity on `Fin 2 → ℝ` and bivariate supermodularity. On
`Fin 2 → ℝ`, the lattice operations `⊔` and `⊓` are pointwise `max` and `min`. -/
lemma multivariateSupermodular_iff_supermodular (u : ℝ → ℝ → ℝ) :
    MultivariateSupermodular (fun v : Fin 2 → ℝ => u (v 0) (v 1)) ↔ Supermodular u := by
  constructor
  · -- MultivariateSupermodular → Supermodular
    intro h_multi θ₁ θ₂ x₁ x₂ hθ hx
    -- Instantiate at v = ![θ₁, x₂], w = ![θ₂, x₁] so sup = ![θ₂, x₂], inf = ![θ₁, x₁]; then the
    -- pointwise max/min reduce via the order hypotheses, beta-reducing the vector indices.
    have h := h_multi ![θ₁, x₂] ![θ₂, x₁]
    simp only [Pi.sup_apply, Pi.inf_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, max_eq_right hθ, max_eq_left hx, min_eq_left hθ,
      min_eq_right hx] at h
    linarith
  · -- Supermodular → MultivariateSupermodular
    intro h_super x y
    change u ((x ⊔ y) 0) ((x ⊔ y) 1) + u ((x ⊓ y) 0) ((x ⊓ y) 1) ≥
         u (x 0) (x 1) + u (y 0) (y 1)
    simp only [Pi.sup_apply, Pi.inf_apply]
    -- Case split on coordinate orderings
    rcases le_or_gt (x 0) (y 0) with h0 | h0 <;> rcases le_or_gt (x 1) (y 1) with h1 | h1
    · -- x 0 ≤ y 0, x 1 ≤ y 1: sup = y, inf = x, so equality
      simp [sup_eq_right.mpr h0, sup_eq_right.mpr h1, inf_eq_left.mpr h0, inf_eq_left.mpr h1,
            add_comm]
    · -- x 0 ≤ y 0, x 1 > y 1: sup = (y 0, x 1), inf = (x 0, y 1)
      simp [sup_eq_right.mpr h0, sup_eq_left.mpr h1.le, inf_eq_left.mpr h0, inf_eq_right.mpr h1.le]
      linarith [h_super (x 0) (y 0) (y 1) (x 1) h0 h1.le]
    · -- x 0 > y 0, x 1 ≤ y 1: sup = (x 0, y 1), inf = (y 0, x 1)
      simp [sup_eq_left.mpr h0.le, sup_eq_right.mpr h1, inf_eq_right.mpr h0.le, inf_eq_left.mpr h1]
      linarith [h_super (y 0) (x 0) (x 1) (y 1) h0.le h1]
    · -- x 0 > y 0, x 1 > y 1: sup = x, inf = y, so equality
      simp [sup_eq_left.mpr h0.le, sup_eq_left.mpr h1.le, inf_eq_right.mpr h0.le,
            inf_eq_right.mpr h1.le]

/-- `Supermodular u` is equivalent to the increasing-differences inequality
`u θ₂ x₂ - u θ₂ x₁ ≥ u θ₁ x₂ - u θ₁ x₁` for all `θ₁ ≤ θ₂` and `x₁ ≤ x₂`. -/
lemma Supermodular.iff_increasing_differences [LinearOrder Θ] [LinearOrder X] (u : Θ → X → ℝ) :
    Supermodular u ↔ ∀ (θ₁ θ₂ : Θ) (x₁ x₂ : X), θ₁ ≤ θ₂ → x₁ ≤ x₂ →
      u θ₂ x₂ - u θ₂ x₁ ≥ u θ₁ x₂ - u θ₁ x₁ := by
  constructor
  · intro h θ₁ θ₂ x₁ x₂ hθ hx
    linarith [h θ₁ θ₂ x₁ x₂ hθ hx]
  · intro h θ₁ θ₂ x₁ x₂ hθ hx
    linarith [h θ₁ θ₂ x₁ x₂ hθ hx]
