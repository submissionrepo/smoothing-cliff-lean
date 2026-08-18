/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Data.Real.StarOrdered

/-!
# Concavity of negative even powers

For even `n`, the map `x ↦ -x^n` is concave on all of `ℝ`, the canonical instance being the
quadratic loss map `x ↦ -x²`. This is the concave dual of Mathlib's `Even.convexOn_pow` (convexity
of `x ↦ x^n` for even `n`), stated for the scalar field `ℝ`.

## Main statements

* `concaveOn_neg_pow_of_even` — `x ↦ -x^n` is concave on `ℝ` for even `n`.
* `concaveOn_neg_sq` — the special case `x ↦ -x²`.

## Tags

concave, convex, even power, quadratic
-/

@[expose] public section

open Set

/-- For even `n`, `x ↦ -x^n` is concave on all of `ℝ`. -/
lemma concaveOn_neg_pow_of_even {n : ℕ} (hn : Even n) :
    ConcaveOn ℝ Set.univ (fun x : ℝ => -x ^ n) :=
  (Even.convexOn_pow hn).neg

/-- The textbook risk-aversion / quadratic-loss utility `x ↦ -x²` is concave on `ℝ`. -/
lemma concaveOn_neg_sq : ConcaveOn ℝ Set.univ (fun x : ℝ => -x ^ 2) :=
  concaveOn_neg_pow_of_even (by norm_num)
