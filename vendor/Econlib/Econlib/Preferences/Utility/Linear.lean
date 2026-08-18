/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Geometry.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.Instances.Matrix

/-!
# Linear (perfect-substitutes) utility

This file defines **linear**, or perfect-substitutes, utility `u(x) = c ⬝ᵥ x = ∑ l, c l · x l` on a
finite product domain, with constant marginal utilities `c`. It provides the preference-level
regularity facts consumed by the general-equilibrium bundle: Continuity, quasiconcavity (every
upper contour set is a half-space), and — with strictly positive coefficients — strict monotonicity
and the resulting strongly monotone preference.

## Main definitions

* `LinearUtility` — a linear utility, carrying the coefficient vector `c`.
* `LinearUtility.u` — the utility `u(x) = c ⬝ᵥ x`.

## Main statements

* `LinearUtility.continuous_u`, `LinearUtility.quasiconcaveOn_u` — continuity and quasiconcavity
  for arbitrary coefficients.
* `LinearUtility.strictMono_u`, `LinearUtility.strictMonotonePreference` — strict monotonicity and
  the strongly monotone preference under strictly positive coefficients.

## Tags

utility, linear, perfect substitutes, quasiconcave, monotone
-/

@[expose] public section

open Matrix

namespace Econlib.Preferences

/-- **Linear** (perfect-substitutes) utility over `L` goods. The utility function is
`u(x) = c ⬝ᵥ x = ∑ l, c l · x l`, with `c l` the constant marginal utility of good `l`. -/
structure LinearUtility (L : ℕ) where
  /-- The coefficient (constant marginal utility) of each good. -/
  c : Fin L → ℝ

namespace LinearUtility

variable {L : ℕ}

/-- The utility function `u(x) = c ⬝ᵥ x`. -/
def u (lu : LinearUtility L) (x : Fin L → ℝ) : ℝ := lu.c ⬝ᵥ x

variable (lu : LinearUtility L)

@[simp] lemma u_def (x : Fin L → ℝ) : lu.u x = lu.c ⬝ᵥ x := rfl

/-- Linear utility is continuous. -/
lemma continuous_u : Continuous lu.u :=
  continuous_const.dotProduct continuous_id

/-- Linear utility is quasiconcave: Every upper contour set is a (convex) half-space. -/
lemma quasiconcaveOn_u : QuasiconcaveOn ℝ Set.univ lu.u := by
  change QuasiconcaveOn ℝ Set.univ (fun x => lu.c ⬝ᵥ x)
  refine Convex.quasiconcaveOn_of_convex_ge convex_univ fun t => ?_
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have hcomb : lu.c ⬝ᵥ (a • x + b • y) = a * (lu.c ⬝ᵥ x) + b * (lu.c ⬝ᵥ y) := by
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  rw [hcomb]
  have hconvex_combo : a * t + b * t = t := by rw [← add_mul, hab, one_mul]
  linarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb, hconvex_combo]

/-- With strictly positive coefficients, linear utility is strictly monotone. -/
lemma strictMono_u (hc : ∀ l, 0 < lu.c l) :
    ∀ {x y : Fin L → ℝ}, x ≤ y → x ≠ y → lu.u x < lu.u y := by
  intro x y hxy hne
  simp only [u_def]
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
  refine Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hxy i) (hc i).le)
    ⟨k, Finset.mem_univ k, mul_lt_mul_of_pos_left (lt_of_le_of_ne (hxy k) hk) (hc k)⟩

/-- The linear preference with strictly positive coefficients is strongly monotone. -/
lemma strictMonotonePreference (hc : ∀ l, 0 < lu.c l) :
    StrictMonotonePreference (preferenceOfRealUtility lu.u) :=
  strictMonotonePreference_of_strictMono _ (lu.strictMono_u hc)

end LinearUtility

end Econlib.Preferences
