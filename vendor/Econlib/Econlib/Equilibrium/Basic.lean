/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.Instances.Matrix

/-!
# General Equilibrium: Basic Commodity-Space Conventions

This file defines the nonnegative orthant in the commodity space used by the equilibrium files and
records its basic convexity and closedness properties.

## Module conventions

* A commodity space with `L` goods is represented by `Fin L → ℝ`.
* Price vectors and commodity bundles use the same coordinate type. Their value pairing is
  `p ⬝ᵥ x`, Mathlib's `Matrix.dotProduct`.
* The canonical consumption set is the nonnegative orthant `nonnegOrthant L`.

The broader equilibrium API for budgets, demand, market clearing, welfare, and existence results is
defined in later files.

## Main definitions

* `nonnegOrthant`: The set of bundles with every coordinate nonnegative.

## Main statements

* `nonnegOrthant_eq_Ici`: The nonnegative orthant is `Set.Ici 0` for the pointwise order.
* `nonnegOrthant_convex`: The nonnegative orthant is convex.
* `nonnegOrthant_closed`: The nonnegative orthant is closed.

## Tags

general equilibrium, commodity space, consumption set, nonnegative orthant
-/

@[expose] public section

namespace Econlib.Equilibrium

variable {L : ℕ}

/-! ## Consumption set -/

/-- The **basic consumption set** — commodity bundles with a nonnegative quantity of every good.

For a finite commodity space `Fin L → ℝ`, membership in `nonnegOrthant L` says that the bundle
assigns no negative amount to any commodity. -/
def nonnegOrthant (L : ℕ) : Set (Fin L → ℝ) :=
  {x | ∀ l, 0 ≤ x l}

/-- The nonnegative orthant is exactly the set of bundles that weakly dominate the zero bundle
coordinatewise. -/
lemma nonnegOrthant_eq_Ici : nonnegOrthant L = Set.Ici (0 : Fin L → ℝ) := by
  ext x; simp [nonnegOrthant, Pi.le_def]

/-- The **consumption set is convex**: Any convex combination of two feasible nonnegative bundles
is again a feasible nonnegative bundle. -/
lemma nonnegOrthant_convex : Convex ℝ (nonnegOrthant L) :=
  nonnegOrthant_eq_Ici ▸ convex_Ici (0 : Fin L → ℝ)

/-- The **consumption set is closed**: Limits of feasible nonnegative bundles remain feasible,
including boundary bundles with zero quantities of some goods. -/
lemma nonnegOrthant_closed : IsClosed (nonnegOrthant L) :=
  nonnegOrthant_eq_Ici ▸ isClosed_Ici

end Econlib.Equilibrium
