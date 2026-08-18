/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# A Two-Good Cobb–Douglas Consumer

Cobb–Douglas preferences `u(x₁, x₂) = x₁^α₁ · x₂^α₂` are the workhorse of consumer theory: They are
log-linear, homogeneous, continuous, quasiconcave, and strictly increasing toward the interior of
the consumption set, and their better-than ("strict upper contour") sets are convex. This file
instantiates the Econlib Cobb–Douglas API on the symmetric two-good case with exponents
`α = (1/2, 1/2)` and assembles each of these textbook properties from theorems that already exist
in the library.

## The model

Two goods, `Fin 2`. The consumer has Cobb–Douglas utility with equal exponents `α := ![1/2, 1/2]`,
so `∑ α = 1`: the utility is homogeneous of degree one (the consumer-theory analogue of constant
returns). The interior-only utility `cd.u x` is `∏ i, (x i)^(α i)`; the total utility
`cd.uTotal x = ∏ i, (max (x i) 0)^(α i)` extends it to the whole commodity space `Fin 2 → ℝ` by
truncating negative coordinates at `0`, and it is this total preference relation that carries the
geometric structure used by general-equilibrium arguments.

## The mathematics

* **Log-linearity.** Taking logs turns the product into a sum: `log (u x) = ∑ i, α i · log (x i)`.
* **Homogeneity of degree one.** Scaling the bundle by `t > 0` scales utility by `t^(∑ α) = t`.
* **Continuity** of the total utility on all of `Fin 2 → ℝ`.
* **Quasiconcavity:** every upper contour `{x | c ≤ uTotal x}` is convex — the Cobb–Douglas product
  is log-concave on the interior.
* **Strict monotonicity toward the interior** and **boundary avoidance:** more of every good is
  strictly better when the larger bundle is interior, and any bundle as good as an interior one is
  itself interior (boundary bundles have utility `0`).
* **Convex better-than sets:** quasiconcavity upgrades, via `QuasiconcaveOn.toConvexPreference` and
  `ConvexPreference.strictUpperContour_convex`, to convexity of every strict upper contour set.

## Main definitions and theorems

* `cd` — the symmetric two-good Cobb–Douglas utility with `α = (1/2, 1/2)`.
* `u_eval` — the numeric evaluation `u ![4, 9] = 6` (since `4^(1/2)·9^(1/2) = 2·3 = 6`).
* `log_form` — the log-linear form `log (u x) = ∑ i, α i · log (x i)`.
* `homogeneous_degree_one` — scaling the bundle by `t > 0` scales utility by `t`.
* `u_continuous` — continuity of the total utility.
* `u_quasiconcave` — quasiconcavity (convex upper contour sets).
* `u_strictMonoToInterior` — strict monotonicity toward interior bundles.
* `u_boundaryAvoiding` — boundary avoidance of interior upper contours.
* `upperContour_convex` — every strict better-than set is convex.
-/

noncomputable section

namespace EconlibExamples.Preferences.CobbDouglas

open Econlib.Preferences

/-! ## The symmetric two-good Cobb–Douglas consumer -/

/-- The symmetric two-good Cobb–Douglas utility with exponents `α = (1/2, 1/2)`. Both exponents are
strictly positive, which is the only field the structure requires. -/
def cd : CobbDouglasUtility 2 where
  α := ![1 / 2, 1 / 2]
  α_pos i := by fin_cases i <;> norm_num

@[simp] lemma cd_α_zero : cd.α 0 = 1 / 2 := rfl

@[simp] lemma cd_α_one : cd.α 1 = 1 / 2 := rfl

/-- The exponents sum to one. This is the hypothesis behind homogeneity of degree one, established
separately in `homogeneous_degree_one`. -/
lemma cd_α_sum_one : ∑ i, cd.α i = 1 := by
  simp only [Fin.sum_univ_two, cd_α_zero, cd_α_one]; norm_num

/-! ## A concrete numeric evaluation: `u ![4, 9] = 6` -/

/-- **Numeric evaluation.** With `α = (1/2, 1/2)`, the bundle `(4, 9)` has utility
`4^(1/2) · 9^(1/2) = √4 · √9 = 2 · 3 = 6`. -/
lemma u_eval : cd.u ![4, 9] (by intro i; fin_cases i <;> norm_num) = 6 := by
  -- Unfold the product over the two goods and identify each real power with a square root.
  rw [cd.u_def, Fin.prod_univ_two]
  have h4 : (![(4 : ℝ), 9] 0) ^ (cd.α 0) = 2 := by
    rw [cd_α_zero]
    change (4 : ℝ) ^ ((1 : ℝ) / 2) = 2
    rw [← Real.sqrt_eq_rpow]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h9 : (![(4 : ℝ), 9] 1) ^ (cd.α 1) = 3 := by
    rw [cd_α_one]
    change (9 : ℝ) ^ ((1 : ℝ) / 2) = 3
    rw [← Real.sqrt_eq_rpow]
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4, h9]; norm_num

/-! ## Log-linearity and homogeneity -/

/-- **Log-linear form.** Logs convert the Cobb–Douglas product into the additively-separable sum
`log (u x) = ∑ i, α i · log (x i)`. -/
lemma log_form (x : Fin 2 → ℝ) (hx : ∀ i, 0 < x i) :
    Real.log (cd.u x hx) = ∑ i, cd.α i * Real.log (x i) :=
  cd.log_u_eq_sum_mul_log x hx

/-- **Homogeneity of degree one.** Since `∑ α = 1`, scaling the bundle by `t > 0` scales utility by
`t^(∑ α) = t`. -/
lemma homogeneous_degree_one (x : Fin 2 → ℝ) (hx : ∀ i, 0 < x i) (t : ℝ) (ht : 0 < t) :
    cd.u (fun i => t * x i) (fun i => mul_pos ht (hx i)) = t * cd.u x hx := by
  rw [cd.u_homogeneous x hx t ht, cd_α_sum_one, Real.rpow_one]

/-! ## Topological and geometric structure -/

/-- **Continuity** of the total Cobb–Douglas utility on all of `Fin 2 → ℝ`. -/
lemma u_continuous : Continuous cd.uTotal :=
  cd.uTotal_continuous

/-- **Quasiconcavity:** every upper contour set `{x | c ≤ uTotal x}` is convex. -/
lemma u_quasiconcave : QuasiconcaveOn ℝ Set.univ cd.uTotal :=
  cd.uTotal_quasiconcave

/-- **Strict monotonicity toward the interior:** a coordinatewise-larger, strictly-positive bundle
is strictly preferred. -/
lemma u_strictMonoToInterior :
    StrictMonoToInterior (preferenceOfRealUtility cd.uTotal) :=
  cd.uTotal_strictMonoToInterior

/-- **Boundary avoidance:** any bundle at least as good as a strictly-positive bundle is itself
strictly positive. -/
lemma u_boundaryAvoiding :
    BoundaryAvoiding (preferenceOfRealUtility cd.uTotal) :=
  cd.uTotal_boundaryAvoiding

/-- **Convex better-than sets (the geometric punchline).** Quasiconcavity of the total utility
makes the induced preference relation convex, so every strict upper contour ("strictly better than
`x`") set is convex. -/
lemma upperContour_convex (x : Fin 2 → ℝ) :
    Convex ℝ ((preferenceOfRealUtility cd.uTotal).strictUpperContour x) :=
  cd.uTotal_quasiconcave.toConvexPreference.strictUpperContour_convex x

end EconlibExamples.Preferences.CobbDouglas
