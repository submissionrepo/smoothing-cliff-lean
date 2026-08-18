/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Strong Duality for a Concrete Convex Program (Slater's Condition)

A linear program in one variable:

Maximize  `f(x) = x`   subject to   `g(x) = x − 1 ≤ 0`,   `x ∈ [0, 2]`.

The feasible set is `[0, 1]`, so the **primal optimum is `1`**. Because the program admits a
*strictly feasible* point — one where the inequality is slack, e.g. `x = 0` gives `g(0) = −1 < 0`
(note `x = 0` is a *boundary* point of the box `X = [0, 2]`; Slater asks for slack in the
constraint, not topological interiority) — **Slater's condition** holds, and
the general convex-duality theorem `strongDuality_scalar_of_isSlater` gives **zero duality gap**:
The primal value equals the dual (Lagrangian) value.

## The mathematics

`strongDuality_scalar_of_isSlater` needs: A compact convex feasible set (`[0,2]` — `isCompact_Icc`,
`convex_Icc`), a continuous concave objective (`x ↦ x` — `concaveOn_id`), a continuous convex
constraint (`x ↦ x − 1`, affine hence convex), and a strictly feasible point (`x = 0`). With these
discharged, the theorem yields `primalValueScalar = dualValueScalar`. The primal value is then
computed directly: The feasible set `{x ∈ [0,2] | x − 1 ≤ 0}` is `[0,1]`, whose image under the
identity has supremum `1`.

Beyond the value equality, this instance also delivers **dual attainment**: The dual objective
computes in closed form to `φ(λ) = sup_{x ∈ [0,2]} (x − λ(x−1)) = max (2−λ) λ`, minimized over
`λ ≥ 0` exactly at the **optimal multiplier `λ* = 1`** with minimum value `1` — the dual infimum is
attained, not merely approached.

## Main definitions and theorems

* `X`, `obj`, `con` — the feasible box `[0,2]`, objective `x`, and constraint `x − 1`.
* `slater` — Slater's condition holds for this program.
* `strong_duality` — zero duality gap: `primalValueScalar X obj con = dualValueScalar X obj con`.
* `primal_eq_one` / `dual_eq_one` — the common optimal value is `1`.
* `dualObjective_eq` — the dual objective in closed form, `φ(λ) = max (2−λ) λ`.
* `dual_attained` / `dual_minimizer` — the dual infimum is attained, and the optimal multiplier
  `λ* = 1` minimizes the dual objective over `λ ≥ 0`.
-/

noncomputable section

namespace EconlibExamples.Optimization.SlaterDuality

open Econlib.Optimization Set

/-- The ambient feasible box `X = [0, 2]`. -/
def X : Set ℝ := Set.Icc 0 2

/-- The objective `f(x) = x` (to be maximized). -/
def obj : ℝ → ℝ := fun x => x

/-- The single inequality constraint `g(x) = x − 1 ≤ 0`. -/
def con : ℝ → ℝ := fun x => x - 1

lemma convex_X : Convex ℝ X := convex_Icc 0 2

/-- The objective `x ↦ x` is continuous on `X`. -/
lemma obj_continuousOn : ContinuousOn obj X := continuous_id.continuousOn

/-- The constraint `x ↦ x − 1` is continuous on `X`. -/
lemma con_continuousOn : ContinuousOn con X := (continuous_id.sub continuous_const).continuousOn

/-- The objective `x ↦ x` is concave on `X` (it is linear). -/
lemma obj_concave : ConcaveOn ℝ X obj := concaveOn_id convex_X

/-- The constraint `x ↦ x − 1` is convex on `X` (it is affine). -/
lemma con_convex : ConvexOn ℝ X con := by
  refine ⟨convex_X, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [con, smul_eq_mul]
  have h : a * (x - 1) + b * (y - 1) = a * x + b * y - (a + b) := by ring
  rw [h, hab]

/-- **Slater's condition holds**: The convexities above plus the strictly feasible point `x = 0`,
where the constraint `g(0) = −1` is strictly negative. -/
theorem slater : IsSlater X (fun _ : Unit => con) where
  convex_X := convex_X
  convex_g := fun _ => con_convex
  strict_feasible := ⟨0, by simp [X], fun _ => by simp [con]⟩

/-- **Strong duality (zero duality gap).** Slater's condition lets the general convex-duality
theorem close the gap: The primal value equals the dual value. -/
theorem strong_duality :
    primalValueScalar X obj con = dualValueScalar X obj con :=
  strongDuality_scalar_of_isSlater isCompact_Icc
    obj_continuousOn obj_concave con_continuousOn con_convex slater

/-- The feasible set `{x ∈ [0,2] | x − 1 ≤ 0}` is exactly `[0,1]`. -/
lemma scalarFeasible_eq : scalarFeasible X con = Set.Icc 0 1 := by
  ext x
  simp only [scalarFeasible, con, X, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · rintro ⟨⟨hx0, _⟩, hx1⟩; exact ⟨hx0, by linarith⟩
  · rintro ⟨hx0, hx1⟩; exact ⟨⟨hx0, by linarith⟩, by linarith⟩

/-- **The primal optimal value is `1`** (the constraint binds at `x = 1`); by `strong_duality` the
dual value is `1` as well. -/
theorem primal_eq_one : primalValueScalar X obj con = 1 := by
  rw [primalValueScalar, scalarFeasible_eq]
  have : obj '' Set.Icc 0 1 = Set.Icc 0 1 := by simp [obj, Set.image_id']
  rw [this, csSup_Icc (by norm_num : (0 : ℝ) ≤ 1)]

/-- **The dual optimal value is `1`** — the zero duality gap of `strong_duality`, made explicit. -/
theorem dual_eq_one : dualValueScalar X obj con = 1 :=
  strong_duality.symm.trans primal_eq_one

/-! ## Dual attainment: The optimal multiplier `λ* = 1`

Strong duality gives equality of *values*. On this instance we can go further and exhibit the
**optimal multiplier**: The dual objective computes in closed form to `φ(λ) = max (2 − λ) λ`, a
piecewise-affine V with kink at `λ* = 1`, where the dual infimum is *attained* at the common
optimal value `1`. -/

/-- The **dual objective in closed form**: `φ(λ) = sup_{x ∈ [0,2]} (x − λ·(x − 1)) = max (2−λ) λ`.
The Lagrangian `(1−λ)·x + λ` is affine in `x`, so its supremum over the box sits at an endpoint: At
`x = 2` when `λ ≤ 1` (value `2 − λ`), at `x = 0` when `λ ≥ 1` (value `λ`). -/
lemma dualObjective_eq (lam : ℝ) :
    dualObjectiveScalar X obj con lam = max (2 - lam) lam := by
  unfold dualObjectiveScalar
  apply IsGreatest.csSup_eq
  constructor
  · -- The max is attained at an endpoint of the box.
    rcases le_total lam 1 with hl | hl
    · rw [max_eq_left (by linarith)]
      exact ⟨2, Set.mem_Icc.mpr ⟨by norm_num, le_refl 2⟩,
        by simp only [lagrangianScalar, obj, con]; ring⟩
    · rw [max_eq_right (by linarith)]
      exact ⟨0, Set.mem_Icc.mpr ⟨le_refl 0, by norm_num⟩,
        by simp only [lagrangianScalar, obj, con]; ring⟩
  · -- Every Lagrangian value over the box is below the max.
    rintro v ⟨x, hx, rfl⟩
    obtain ⟨hx0, hx2⟩ := Set.mem_Icc.mp hx
    simp only [lagrangianScalar, obj, con]
    rcases le_total lam 1 with hl | hl
    · exact le_max_of_le_left (by nlinarith)
    · exact le_max_of_le_right (by nlinarith)

/-- **Dual attainment at the optimal multiplier `λ* = 1`.** The dual infimum over `λ ≥ 0` is a
*minimum*, attained at the common optimal value `1`. This is the general theorem
`dualAttainment_scalar_of_isSlater` — which guarantees *some* optimal multiplier under Slater — with
its least value fixed at `1` by `dual_eq_one`; the bare-hands lower bound is no longer needed. (The
closed form `dualObjective_eq` independently shows the minimizer is the kink `λ* = 1`, below.) -/
theorem dual_attained : IsLeast (dualObjectiveScalar X obj con '' Set.Ici 0) 1 := by
  -- The general attainment theorem exhibits an optimal multiplier `lam*`
  -- (determined by `obj`/`con`).
  obtain ⟨lamStar, _, hleast⟩ := dualAttainment_scalar_of_isSlater (X := X) (f := obj) (g := con)
    isCompact_Icc obj_continuousOn obj_concave con_continuousOn con_convex slater
  -- Its least value equals `dualValueScalar = 1`, so `1` is the least element too.
  have hval : dualObjectiveScalar X obj con lamStar = 1 := by
    rw [← dualValueScalar_eq_of_isLeast hleast, dual_eq_one]
  rwa [hval] at hleast

/-- The optimal multiplier as a first-class statement: **`λ* = 1` minimizes the dual objective**
over the nonnegative multipliers. Single-valued route via the general theorem: `dual_attained` makes
`1` the least *value* over `Ici 0`, and the closed form `dualObjective_eq` evaluates `φ(1) = 1`, so
the multiplier `1` attains it. -/
theorem dual_minimizer : IsMinOn (dualObjectiveScalar X obj con) (Set.Ici 0) 1 := by
  intro lam hlam
  simp only [Set.mem_setOf_eq]
  -- `φ(1) = max 1 1 = 1`, and `1` lower-bounds `φ` over `Ici 0` by `dual_attained`.
  rw [dualObjective_eq, show (2 : ℝ) - 1 = 1 by norm_num, max_self]
  exact dual_attained.2 ⟨lam, hlam, rfl⟩

end EconlibExamples.Optimization.SlaterDuality
