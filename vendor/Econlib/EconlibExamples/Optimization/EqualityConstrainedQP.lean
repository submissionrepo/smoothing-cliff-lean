/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# An Equality-Constrained Quadratic Program via KKT

A worked example of **full** Karush-Kuhn-Tucker sufficiency — the mixed equality-and-inequality
form `ConstrainedProblem.isMaxOn_of_kkt_eq` packaged as `MaxKKTEq.isMaxOn` — on a program whose
binding constraint is an equality, so the inequality-only certificate `MaxKKT` cannot reach it.

The program maximizes the strictly concave objective `f(x) = −(x₀ − a)² − (x₁ − d)²` over `ℝ²`
(modelled as `Fin 2 → ℝ`) subject to the single linear equality `h(x) = x₀ + x₁ − s = 0`.
Geometrically: project the bliss point `(a, d)` onto the line `x₀ + x₁ = s`. The projection is
`x* = ((a − d + s)/2, (d − a + s)/2)`, and the equality multiplier is `μ = a + d − s`.

## What distinguishes this from the inequality case

* The feasible set is the entire line `x₀ + x₁ = s` (`feasibleSet_eq`), a nontrivial set — so the
  optimality claim has content. (A one-dimensional equality would instead pin `x` to a single
  point.) The inequality-only conclusion of `MaxKKT.isMaxOn` would range over `feasibleSetIneq`,
  which here is all of `ℝ²` and ignores the constraint entirely.
* The equality multiplier `μ = a + d − s` is sign-unrestricted (`multiplier_neg`): it is
  negative exactly when `s > a + d`. An inequality multiplier `λ ≥ 0` can never be negative.

## The mathematics

The Lagrangian is `L(y) = −(y₀ − a)² − (y₁ − d)² − μ(y₀ + y₁ − s)`. With `μ = a + d − s` the
gradient vanishes at `x*`. The certificate is assembled by the first-order constructor
`MaxKKTEq.ofFOC`: `L` is concave (`lagrangian_concaveOn`) and Fréchet-stationary at `x*`
(`lagrangian_hasFDerivAt_zero`), so `x*` maximizes `L`. Equality feasibility `x₀* + x₁* = s` is
immediate, and there are no inequalities, so `MaxKKTEq.isMaxOn` turns the certificate into global
constrained optimality (`qp_isMaxOn`). The same maximality also follows elementarily, with no
calculus, by completing the square — `lagrangian_isMaxOn` records that route, since the exact gap is
`L(x*) − L(y) = (y₀ − x₀*)² + (y₁ − x₁*)² ≥ 0`.

## Main definitions and theorems

* `qp a d s` — the constrained problem (`f = −(x₀−a)²−(x₁−d)²`, one equality `h = x₀+x₁−s`, no
  inequalities).
* `multiplier a d s` — the equality multiplier `μ = a + d − s`; `multiplier_neg` records that it can
  be negative.
* `xStar a d s` — the projection `x* = ((a−d+s)/2, (d−a+s)/2)`.
* `lagrangian_concaveOn`, `lagrangian_hasFDerivAt_zero` — the first-order data (concavity and
  vanishing derivative) feeding the certificate.
* `lagrangian_isMaxOn` — the elementary alternative: `x*` globally maximizes the Lagrangian by
  completing the square.
* `kkt a d s` — the `MaxKKTEq` certificate at `x*`, built via `MaxKKTEq.ofFOC`.
* `qp_isMaxOn` — `x*` globally maximizes the objective over the feasible line `feasibleSet_eq`.
-/

noncomputable section

namespace EconlibExamples.Optimization.EqualityConstrainedQP

open Econlib.Optimization

variable (a d s : ℝ)

/-- The equality-constrained quadratic program: maximize `−(x₀−a)² − (x₁−d)²` subject to
`x₀ + x₁ − s = 0`. There are no inequality constraints, so the inequality index type is `Empty`;
the single equality is `Unit`-indexed. -/
def qp : ConstrainedProblem (Fin 2 → ℝ) Empty Unit where
  f := fun x => -(x 0 - a) ^ 2 - (x 1 - d) ^ 2
  g := fun e => e.elim
  h := fun _ x => x 0 + x 1 - s

@[simp] lemma qp_f_apply (x : Fin 2 → ℝ) :
    (qp a d s).f x = -(x 0 - a) ^ 2 - (x 1 - d) ^ 2 := rfl

@[simp] lemma qp_h_apply (j : Unit) (x : Fin 2 → ℝ) :
    (qp a d s).h j x = x 0 + x 1 - s := rfl

/-- The KKT equality multiplier `μ = a + d − s`. Unlike an inequality multiplier it carries no sign
restriction (`multiplier_neg`). -/
def multiplier : ℝ := a + d - s

/-- The constrained optimum: the projection of the bliss point `(a, d)` onto the line
`x₀ + x₁ = s`. -/
def xStar : Fin 2 → ℝ := ![(a - d + s) / 2, (d - a + s) / 2]

@[simp] lemma xStar_zero : xStar a d s 0 = (a - d + s) / 2 := by simp [xStar]

@[simp] lemma xStar_one : xStar a d s 1 = (d - a + s) / 2 := by simp [xStar]

/-! ## The Lagrangian, maximized at `x*` by completing the square -/

/-- The full Lagrangian `L(y) = f(y) − μ(y₀ + y₁ − s)` at the derived multiplier, in explicit form.
The inequality sum (over `Empty`) vanishes and the equality sum (over `Unit`) is a single term —
both collapses come straight from the library `simp` lemmas `lagrangian_of_isEmpty_ineq` and
`lagrangian_unique_eq`. -/
lemma lagrangian_eq (y : Fin 2 → ℝ) :
    lagrangian (qp a d s) y Empty.elim (fun _ => multiplier a d s)
      = -(y 0 - a) ^ 2 - (y 1 - d) ^ 2 - multiplier a d s * (y 0 + y 1 - s) := by
  simp [qp]

/-- **Global Lagrangian maximality, by hand.** Completing the square exhibits the exact gap
`L(x*) − L(y) = (y₀ − x₀*)² + (y₁ − x₁*)² ≥ 0`, so the stationary point `x*` globally maximizes the
Lagrangian — no calculus required. The KKT certificate `kkt` below instead obtains this same
maximality through the first-order route `MaxKKTEq.ofFOC` (concavity plus a vanishing derivative);
this lemma records the elementary alternative. -/
theorem lagrangian_isMaxOn :
    IsMaxOn (fun y => lagrangian (qp a d s) y Empty.elim (fun _ => multiplier a d s))
      Set.univ (xStar a d s) := by
  intro y _
  simp only [Set.mem_setOf_eq, lagrangian_eq, xStar_zero, xStar_one]
  simp only [multiplier]
  nlinarith [sq_nonneg (y 0 - (a - d + s) / 2), sq_nonneg (y 1 - (d - a + s) / 2)]

/-! ## The first-order route to the certificate: concavity and stationarity of the Lagrangian -/

/-- The one-variable building block `t ↦ −t²` is concave on `ℝ`. -/
lemma negsq_concaveOn : ConcaveOn ℝ (Set.univ : Set ℝ) (fun t : ℝ => -t ^ 2) := by
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => t ^ 2) := Even.convexOn_pow (by norm_num)
  have hneg := hconv.neg
  have heq : (-fun t : ℝ => t ^ 2) = fun t : ℝ => -t ^ 2 := by funext t; simp
  rwa [heq] at hneg

/-- The coordinate-shift affine map `y ↦ yᵢ − c` on `ℝ²`. -/
def coordAff (i : Fin 2) (c : ℝ) : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ :=
  (LinearMap.proj i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).toAffineMap - AffineMap.const ℝ _ c

/-- The one-variable building block `t ↦ μ·t` is convex on `ℝ`. -/
lemma scaledId_convexOn :
    ConvexOn ℝ (Set.univ : Set ℝ) (fun t : ℝ => multiplier a d s * t) := by
  have h := (multiplier a d s • LinearMap.id : ℝ →ₗ[ℝ] ℝ).convexOn convex_univ
  have heq : (⇑(multiplier a d s • LinearMap.id : ℝ →ₗ[ℝ] ℝ))
      = fun t : ℝ => multiplier a d s * t := by funext t; simp
  rwa [heq] at h

/-- The affine constraint map `y ↦ y₀ + y₁ − s` on `ℝ²`. -/
def sumAff : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ :=
  (LinearMap.proj (0 : Fin 2) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).toAffineMap
    + (LinearMap.proj (1 : Fin 2) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ).toAffineMap
    - AffineMap.const ℝ _ s

/-- **The full Lagrangian is concave.** Each quadratic penalty `−(yᵢ − cᵢ)²` is `−t²` precomposed
with a coordinate-shift affine map, hence concave; the linear equality term `μ(y₀ + y₁ − s)` is
affine, hence convex. Their concave-minus-convex combination is concave. -/
lemma lagrangian_concaveOn : ConcaveOn ℝ Set.univ
    (fun y => lagrangian (qp a d s) y Empty.elim (fun _ => multiplier a d s)) := by
  have hfun : (fun y => lagrangian (qp a d s) y Empty.elim (fun _ => multiplier a d s))
      = fun y : Fin 2 → ℝ =>
        -(y 0 - a) ^ 2 - (y 1 - d) ^ 2 - multiplier a d s * (y 0 + y 1 - s) :=
    funext (lagrangian_eq a d s)
  rw [hfun]
  have c0 : ConcaveOn ℝ Set.univ (fun y : Fin 2 → ℝ => -(y 0 - a) ^ 2) := by
    have h := (negsq_concaveOn).comp_affineMap (coordAff 0 a)
    have heq : ((fun t : ℝ => -t ^ 2) ∘ coordAff 0 a)
        = fun y : Fin 2 → ℝ => -(y 0 - a) ^ 2 := by funext y; simp [Function.comp, coordAff]
    rw [heq] at h; simpa using h
  have c1 : ConcaveOn ℝ Set.univ (fun y : Fin 2 → ℝ => -(y 1 - d) ^ 2) := by
    have h := (negsq_concaveOn).comp_affineMap (coordAff 1 d)
    have heq : ((fun t : ℝ => -t ^ 2) ∘ coordAff 1 d)
        = fun y : Fin 2 → ℝ => -(y 1 - d) ^ 2 := by funext y; simp [Function.comp, coordAff]
    rw [heq] at h; simpa using h
  have caff : ConvexOn ℝ Set.univ
      (fun y : Fin 2 → ℝ => multiplier a d s * (y 0 + y 1 - s)) := by
    have h := (scaledId_convexOn a d s).comp_affineMap (sumAff s)
    have heq : ((fun t : ℝ => multiplier a d s * t) ∘ sumAff s)
        = fun y : Fin 2 → ℝ => multiplier a d s * (y 0 + y 1 - s) := by
      funext y; simp [Function.comp, sumAff]
    rw [heq] at h; simpa using h
  have hgoal : (fun y : Fin 2 → ℝ => -(y 0 - a) ^ 2 - (y 1 - d) ^ 2
      - multiplier a d s * (y 0 + y 1 - s))
      = (fun y : Fin 2 → ℝ => -(y 0 - a) ^ 2) + (fun y => -(y 1 - d) ^ 2)
        - (fun y => multiplier a d s * (y 0 + y 1 - s)) := by
    funext y; simp; ring
  rw [hgoal]
  exact (c0.add c1).sub caff

/-- **The full Lagrangian is stationary at `x*`** (Fréchet derivative `0`). Assembling the
coordinate derivatives, the resulting continuous linear map evaluates to the zero map at `x*`,
because `μ = a + d − s` exactly cancels the gradient of the quadratic penalty there. -/
lemma lagrangian_hasFDerivAt_zero : HasFDerivAt
    (fun y => lagrangian (qp a d s) y Empty.elim (fun _ => multiplier a d s))
    (0 : (Fin 2 → ℝ) →L[ℝ] ℝ) (xStar a d s) := by
  have hfun : (fun y => lagrangian (qp a d s) y Empty.elim (fun _ => multiplier a d s))
      = fun y : Fin 2 → ℝ =>
        -(y 0 - a) ^ 2 - (y 1 - d) ^ 2 - multiplier a d s * (y 0 + y 1 - s) :=
    funext (lagrangian_eq a d s)
  rw [hfun]
  have e0 : HasFDerivAt (fun y : Fin 2 → ℝ => y 0)
      (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) (xStar a d s) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).hasFDerivAt
  have e1 : HasFDerivAt (fun y : Fin 2 → ℝ => y 1)
      (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ) (xStar a d s) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1).hasFDerivAt
  have hcomb := (((e0.sub_const a).pow 2).neg.sub (((e1.sub_const d).pow 2))) |>.sub
    ((e0.add e1).sub_const s |>.const_mul (multiplier a d s))
  -- The assembled derivative is the zero map: evaluate at an arbitrary direction and `ring`.
  convert hcomb using 1
  ext v
  simp only [xStar_zero, xStar_one, multiplier, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.coe_sub', Pi.sub_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply]
  ring

/-! ## The KKT certificate and global optimality -/

/-- The **full KKT certificate** at the projection `x*`, assembled by the first-order constructor
`MaxKKTEq.ofFOC`: there are no inequalities (so dual feasibility and complementary slackness are
vacuous), the equality binds at `x*` (`x₀* + x₁* = s`), and the sign-unrestricted multiplier
`μ = a + d − s` makes the Lagrangian concave with a vanishing derivative at `x*`, hence globally
maximized there. (The elementary completing-the-square route to the same maximality is recorded in
`lagrangian_isMaxOn`.) -/
def kkt : MaxKKTEq (qp a d s) (xStar a d s) :=
  MaxKKTEq.ofFOC (qp a d s) (xStar a d s) Empty.elim (fun _ => multiplier a d s)
    (fun e => e.elim)
    (fun _ => by simp only [qp_h_apply, xStar_zero, xStar_one]; ring)
    (fun e => e.elim)
    (fun e => e.elim)
    (lagrangian_concaveOn a d s)
    (lagrangian_hasFDerivAt_zero a d s)

/-- **Full KKT sufficiency.** The projection `x*` globally maximizes the objective over the whole
feasible line `feasibleSet`. -/
theorem qp_isMaxOn : IsMaxOn (qp a d s).f (qp a d s).feasibleSet (xStar a d s) :=
  (kkt a d s).isMaxOn

/-- The feasible set is the line `x₀ + x₁ = s` — a nontrivial set on which the optimality claim has
content. -/
lemma feasibleSet_eq :
    (qp a d s).feasibleSet = {x : Fin 2 → ℝ | x 0 + x 1 = s} := by
  ext x
  simp only [ConstrainedProblem.feasibleSet, Set.mem_setOf_eq, qp_h_apply]
  constructor
  · rintro ⟨-, heq⟩
    have := heq ()
    linarith
  · intro hx
    exact ⟨fun e => e.elim, fun _ => by linarith⟩

/-- The equality multiplier is sign-unrestricted: it is negative exactly when the constraint
level `s` exceeds the unconstrained bliss sum `a + d`. (An inequality multiplier could never be
negative — this is the qualitative gap that `isMaxOn_of_kkt_eq` accommodates and `isMaxOn_of_kkt`
does not.) -/
theorem multiplier_neg (h : a + d < s) : multiplier a d s < 0 := by
  rw [multiplier]; linarith

end EconlibExamples.Optimization.EqualityConstrainedQP
