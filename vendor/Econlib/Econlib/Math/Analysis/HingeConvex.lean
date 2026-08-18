/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Real.StarOrdered

/-!
# Convexity of the positive-part hinge

The map `z ↦ max (z - a) 0`, i.e. the upper hinge with break at `a`, is convex on `ℝ`.

This is a building block for the discrete Hardy–Littlewood–Pólya majorization theorem (see
`Econlib.Math.LinearAlgebra.Majorization`), where hinge test functions are the dual cone separating
convex-order inequalities from top-`k` partial sums.

The symmetric lower hinge `z ↦ max (a - z) 0` is the upper hinge precomposed with `z ↦ -z`. It is
the test function of the integrated-CDF ("expected shortfall") characterization of mean-preserving
spreads (`Econlib.Probability.Order.Convex.MPSCharacterization`).

## Main statements

* `convexOn_hinge_right` — the upper hinge `z ↦ max (z - a) 0` is convex on `ℝ`.
* `convexOn_hinge_left` — the lower hinge `z ↦ max (a - z) 0` is convex on `ℝ`.

## Tags

convex, hinge, positive part, majorization
-/

@[expose] public section

open Set

/-- The upper hinge `z ↦ max (z - a) 0` is convex on `ℝ`. -/
lemma convexOn_hinge_right (a : ℝ) :
    ConvexOn ℝ Set.univ (fun z : ℝ => max (z - a) 0) := by
  have hlin : ConvexOn ℝ Set.univ (fun z : ℝ => z + (-a)) :=
    (convexOn_id convex_univ).add_const (-a)
  simpa [sub_eq_add_neg] using hlin.sup (convexOn_const 0 convex_univ)

/-- The lower hinge `z ↦ max (a - z) 0` is convex on `ℝ`. -/
lemma convexOn_hinge_left (a : ℝ) :
    ConvexOn ℝ Set.univ (fun z : ℝ => max (a - z) 0) := by
  have hlin : ConvexOn ℝ Set.univ (fun z : ℝ => -z + a) :=
    (concaveOn_id convex_univ).neg.add_const a
  simpa [sub_eq_neg_add] using hlin.sup (convexOn_const 0 convex_univ)
