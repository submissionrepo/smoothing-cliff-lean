/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Continuous linear functionals on `Fin L → ℝ` as dot products

A continuous linear functional on the finite-dimensional space `Fin L → ℝ` is determined by its
values on the standard basis vectors `Pi.single l 1`: It acts as the dot product
(`Matrix.dotProduct`, notation `⬝ᵥ`) with the vector of those values.

## Main results

* `ContinuousLinearMap.pi_eq_dotProduct_single` — `f y = (fun l => f (Pi.single l 1)) ⬝ᵥ y`.
* `ContinuousLinearMap.neg_dotProduct_single` — `(fun l => -(f (Pi.single l 1))) ⬝ᵥ y = -(f y)`.
-/

@[expose] public section

open Matrix

namespace ContinuousLinearMap

variable {L : ℕ}

/-- Any continuous linear functional on `Fin L → ℝ` equals the dot product with its values on the
standard basis vectors. -/
lemma pi_eq_dotProduct_single (f : (Fin L → ℝ) →L[ℝ] ℝ) (y : Fin L → ℝ) :
    f y = (fun l => f (Pi.single l 1)) ⬝ᵥ y := by
  unfold dotProduct
  conv_lhs => rw [pi_eq_sum_univ' y]
  simp [map_sum, map_smul, smul_eq_mul, mul_comm]

/-- The dot product with the negation of a CLM's basis values equals minus the CLM. -/
lemma neg_dotProduct_single (f : (Fin L → ℝ) →L[ℝ] ℝ) (y : Fin L → ℝ) :
    (fun l => -(f (Pi.single l 1))) ⬝ᵥ y = -(f y) := by
  rw [show (fun l => -(f (Pi.single l 1))) = -(fun l => f (Pi.single l 1)) from rfl,
    neg_dotProduct, ← pi_eq_dotProduct_single]

end ContinuousLinearMap
