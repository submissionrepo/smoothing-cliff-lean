/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Utility.Inada

open Filter Set Topology

/-!
# Positive-domain concave primitives

This module packages the reusable analytic assumptions used for utility, service-flow utility, and
production primitives in dynamic economic models: A real-valued function on `(0, ∞)` that is
strictly monotone, strictly concave, continuously differentiable, has strictly positive marginal
value, and satisfies the **Inada conditions** (Inada 1963) on its derivative. Concavity and
monotonicity facts are derived from the bundled fields.

## Main definitions

* `PositiveConcavePrimitive` — a strictly monotone, strictly concave, continuously differentiable
  function on `(0, ∞)` with positive marginal value and Inada boundary behavior.

## Main statements

* `PositiveConcavePrimitive.concaveOn_pos`, `PositiveConcavePrimitive.monotoneOn_pos` — the
  non-strict concavity and monotonicity facts derived from the strict fields.

## Notes

The object is a structure rather than a typeclass: Applications pass the primitive explicitly and
read derived regularity facts off the bundled fields.

## References

* Inada, Ken-Ichi. 1963. “On a Two-Sector Model of Economic Growth: Comments and a Generalization.”
  *The Review of Economic Studies* 30 (2): 119. [https://doi.org/10.2307/2295809](https://doi.org/10.2307/2295809).

## Tags

utility, concave, inada conditions, dynamic programing
-/

@[expose] public section

namespace Econlib.Preferences

/-- A real-valued primitive on `(0, ∞)` with the monotonicity, concavity, smoothness, positive
marginal value, and Inada boundary behavior usually needed in household and production dynamic
programs. -/
structure PositiveConcavePrimitive where
  /-- The primitive real-valued function. -/
  toFun : ℝ → ℝ
  /-- Strict monotonicity on positive inputs. -/
  strictMonoOn_pos : StrictMonoOn toFun (Ioi (0 : ℝ))
  /-- Strict concavity on positive inputs. -/
  strictConcaveOn_pos : StrictConcaveOn ℝ (Ioi (0 : ℝ)) toFun
  /-- Smoothness on positive inputs. -/
  contDiffOn_pos : ContDiffOn ℝ 1 toFun (Ioi (0 : ℝ))
  /-- Marginal utility or product is strictly positive on positive inputs. -/
  deriv_pos : ∀ x : ℝ, 0 < x → 0 < deriv toFun x
  /-- Inada condition at zero: The derivative diverges to infinity from the right. -/
  deriv_at_zero_atTop : Tendsto (deriv toFun) (𝓝[>] (0 : ℝ)) atTop
  /-- Inada condition at infinity: The derivative converges to zero. -/
  deriv_atTop_zero : Tendsto (deriv toFun) atTop (𝓝 (0 : ℝ))

namespace PositiveConcavePrimitive

/-- Coerce a `PositiveConcavePrimitive` to its underlying function. -/
instance : CoeFun PositiveConcavePrimitive (fun _ => ℝ → ℝ) where
  coe f := f.toFun

variable (f : PositiveConcavePrimitive)

/-- The primitive is concave on `(0,∞)`. -/
lemma concaveOn_pos : ConcaveOn ℝ (Ioi (0 : ℝ)) f.toFun :=
  f.strictConcaveOn_pos.concaveOn

/-- The primitive is monotone on positive inputs. -/
lemma monotoneOn_pos : MonotoneOn f.toFun (Ioi (0 : ℝ)) :=
  f.strictMonoOn_pos.monotoneOn

/-- The derivative of the primitive is strictly positive at any positive input. -/
lemma deriv_pos_of_mem {x : ℝ} (hx : x ∈ Ioi (0 : ℝ)) :
    0 < deriv f.toFun x :=
  f.deriv_pos x hx

/-- Coercion preserves the defining function. -/
@[simp] lemma coe_apply (x : ℝ) : (f : ℝ → ℝ) x = f.toFun x := rfl

end PositiveConcavePrimitive

end Econlib.Preferences
