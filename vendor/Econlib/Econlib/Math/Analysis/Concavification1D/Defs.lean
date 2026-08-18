/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Affine functions and contact sets

This file defines the basic objects for one-dimensional concavification: The affine function
`x ↦ m * x + c`, and the **contact set** of a payoff `φ` with an affine majorant on `[a, b]` — the
set of points where `φ` touches its affine majorant.

## Main definitions

* `affineFun m c` — the affine function `x ↦ m * x + c`.
* `contactSet a b φ m c` — the set of `x ∈ [a, b]` where `φ x = affineFun m c x`.

## Main statements

* `affineFun_continuous` — affine functions are continuous.
* `convexOn_affineFun` — affine functions are convex on any interval.
* `contactSet_measurable`, `contactSet_closed` — for continuous `φ`, the contact set is measurable
  and closed.

## Tags

affine function, contact set, concavification
-/

@[expose] public section

open MeasureTheory Set

/-- Affine function `x ↦ m * x + c`. -/
def affineFun (m c : ℝ) (x : ℝ) : ℝ := m * x + c

/-- Contact set of a payoff with an affine majorant on `[a,b]`. -/
def contactSet (a b : ℝ) (φ : ℝ → ℝ) (m c : ℝ) : Set ℝ :=
  {x | x ∈ Icc a b ∧ φ x = affineFun m c x}

/-- An affine function is continuous. -/
lemma affineFun_continuous (m c : ℝ) : Continuous (affineFun m c) := by
  unfold affineFun
  exact (continuous_const.mul continuous_id).add continuous_const

/-- An affine function is convex on any interval (indeed on all of `ℝ`). -/
lemma convexOn_affineFun (a b m c : ℝ) : ConvexOn ℝ (Icc a b) (affineFun m c) := by
  refine ⟨convex_Icc a b, fun x _ y _ p q _ _ hpq => le_of_eq ?_⟩
  simp only [affineFun, smul_eq_mul]
  linear_combination (-c) * hpq

/-- For continuous `φ`, the contact set is measurable. -/
lemma contactSet_measurable (a b : ℝ) (φ : ℝ → ℝ) (hφ : Continuous φ) (m c : ℝ) :
    MeasurableSet (contactSet a b φ m c) := by
  unfold contactSet
  exact measurableSet_Icc.inter (measurableSet_eq_fun hφ.measurable
    (affineFun_continuous m c).measurable)

/-- For continuous `φ`, the contact set is closed. -/
lemma contactSet_closed (a b : ℝ) (φ : ℝ → ℝ) (hφ : Continuous φ) (m c : ℝ) :
    IsClosed (contactSet a b φ m c) := by
  unfold contactSet
  exact isClosed_Icc.inter (isClosed_eq hφ (affineFun_continuous m c))
