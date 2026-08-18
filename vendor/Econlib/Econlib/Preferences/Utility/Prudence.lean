/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.SpecialFunctions.Rpow
public import Econlib.Preferences.Utility.Positive
public import Econlib.Preferences.Utility.RiskFamilies

/-!
# Prudence

A utility function is **prudent** (Kimball 1990) when its marginal utility is convex on `(0, ∞)`.
For sufficiently differentiable `u` this is equivalent to nonnegativity of the third derivative
`u''' = iteratedDeriv 3 u` on `(0, ∞)`. Prudence is the utility-curvature condition underlying
precautionary saving.

## Main definitions

* `Prudent` — the marginal-utility-convex predicate.
* `crraMarginal` — the CRRA marginal utility `crraMarginal γ x = x^(-γ)`, a uniform interface
  coinciding with the derivative of both log utility (`γ = 1`) and the CRRA utility `c^(1-γ)/(1-γ)`
  (`γ ≠ 1`).

## Main statements

* `prudent_iff_iteratedDeriv3_nonneg` — for thrice-differentiable `u`, prudence is equivalent to
  nonnegativity of the third derivative on `(0, ∞)`, with directions
  `prudent_of_iteratedDeriv3_nonneg` and `Prudent.iteratedDeriv3_nonneg`.
* `prudent_log` — logarithmic utility is prudent.
* `ConstantRelativeRiskAversionUtility.prudent` — CRRA utility is prudent.

## References

* Kimball, Miles S. 1990. “Precautionary Saving in the Small and in the Large.” *Econometrica* 58
  (1): 53. [https://doi.org/10.2307/2938334](https://doi.org/10.2307/2938334).

## Tags

prudence, precautionary saving, third derivative, crra, marginal utility
-/

@[expose] public section

open Real Set Filter Topology

namespace Econlib.Preferences

/-! ## Marginal utility helper -/

/-- Marginal utility for the CRRA family: `u'(c) = c^(-γ)`.

This formula coincides with the derivative of both the log utility (`γ = 1`) and the CRRA utility
`c^(1-γ)/(1-γ)` (`γ ≠ 1`), giving a uniform interface for Bellman characterizations parametrised by
the elasticity coefficient `γ`. -/
noncomputable def crraMarginal (γ : ℝ) (x : ℝ) : ℝ := x ^ (-γ)

@[simp] theorem crraMarginal_apply (γ x : ℝ) : crraMarginal γ x = x ^ (-γ) := rfl

theorem crraMarginal_pos {γ x : ℝ} (hx : 0 < x) : 0 < crraMarginal γ x :=
  Real.rpow_pos_of_pos hx _

/-! ## Prudence -/

/-- A utility function `u : ℝ → ℝ` is **prudent** on `(0, ∞)` when its marginal utility is convex
there.  Equivalently, for thrice-differentiable `u`, the third derivative `u'''` is nonnegative on
`(0, ∞)` — this equivalence is `prudent_iff_iteratedDeriv3_nonneg`, with the two directions
`prudent_of_iteratedDeriv3_nonneg` and `Prudent.iteratedDeriv3_nonneg`. -/
def Prudent (u : ℝ → ℝ) : Prop :=
  ConvexOn ℝ (Ioi 0) (deriv u)

/-! ## Prudence and the third derivative

The marginal-utility-convexity definition of prudence is equivalent, for sufficiently
differentiable `u`, to nonnegativity of the third derivative `u''' = iteratedDeriv 3 u` on
`(0, ∞)`. -/

/-- If the marginal utility `deriv u` and second derivative `deriv (deriv u)` are differentiable on
`(0, ∞)` and the third derivative `u''' = iteratedDeriv 3 u` is nonnegative there, then `u` is
prudent. -/
theorem prudent_of_iteratedDeriv3_nonneg {u : ℝ → ℝ}
    (hu' : DifferentiableOn ℝ (deriv u) (Ioi 0))
    (hu'' : DifferentiableOn ℝ (deriv (deriv u)) (Ioi 0))
    (hu''' : ∀ x ∈ Ioi 0, 0 ≤ iteratedDeriv 3 u x) :
    Prudent u := by
  refine convexOn_of_deriv2_nonneg' (convex_Ioi 0) hu' hu'' ?_
  intro x hx
  have h3 : deriv^[2] (deriv u) x = iteratedDeriv 3 u x := by
    rw [iteratedDeriv_eq_iterate]; rfl
  rw [h3]
  exact hu''' x hx

/-- If `u` is prudent and its marginal utility `deriv u` is differentiable on `(0, ∞)`, then the
third derivative `u''' = iteratedDeriv 3 u` is nonnegative there. -/
theorem Prudent.iteratedDeriv3_nonneg {u : ℝ → ℝ} (h : Prudent u)
    (hu' : ∀ x ∈ Ioi 0, DifferentiableAt ℝ (deriv u) x) :
    ∀ x ∈ Ioi 0, 0 ≤ iteratedDeriv 3 u x := by
  -- Convexity of marginal utility implies the second derivative is monotone on `(0, ∞)`.
  have hmono : MonotoneOn (deriv (deriv u)) (Ioi 0) := ConvexOn.monotoneOn_deriv h hu'
  intro x hx
  have h3 : iteratedDeriv 3 u x = deriv (deriv (deriv u)) x := by
    rw [iteratedDeriv_eq_iterate]; rfl
  rw [h3, ← derivWithin_of_isOpen isOpen_Ioi hx]
  exact hmono.derivWithin_nonneg

/-- For a utility whose marginal utility and second derivative are differentiable on `(0, ∞)`,
prudence is equivalent to nonnegativity of the third derivative `u''' = iteratedDeriv 3 u` there,
i.e., the `u''' ≥ 0` condition from Kimball (1990). -/
theorem prudent_iff_iteratedDeriv3_nonneg {u : ℝ → ℝ}
    (hu' : DifferentiableOn ℝ (deriv u) (Ioi 0))
    (hu'' : DifferentiableOn ℝ (deriv (deriv u)) (Ioi 0)) :
    Prudent u ↔ ∀ x ∈ Ioi 0, 0 ≤ iteratedDeriv 3 u x :=
  ⟨fun h => h.iteratedDeriv3_nonneg (fun x hx => (hu' x hx).differentiableAt
      (isOpen_Ioi.mem_nhds hx)),
   prudent_of_iteratedDeriv3_nonneg hu' hu''⟩

/-! ## Log utility is prudent -/

/-- The derivative of `Real.log` on `(0, ∞)` equals the CRRA marginal at `γ = 1`. -/
theorem deriv_log_eq_crraMarginal_one_on_Ioi :
    Set.EqOn (deriv Real.log) (crraMarginal 1) (Ioi 0) := by
  intro x hx
  have hx' : (0 : ℝ) < x := mem_Ioi.mp hx
  rw [Real.deriv_log, crraMarginal_apply, Real.rpow_neg_one]

/-- Logarithmic utility is prudent: Its marginal `1/c` is convex on `(0, ∞)`. -/
theorem prudent_log : Prudent Real.log := by
  unfold Prudent
  have h_eq : Set.EqOn (deriv Real.log) (fun x : ℝ => x ^ (-(1 : ℝ))) (Ioi 0) := by
    intro x hx
    have := deriv_log_eq_crraMarginal_one_on_Ioi hx
    simpa [crraMarginal] using this
  have hconv : ConvexOn ℝ (Ioi 0) (fun x : ℝ => x ^ (-(1 : ℝ))) :=
    convexOn_rpow_of_nonpos (by norm_num)
  exact hconv.congr h_eq.symm

/-! ## CRRA utility is prudent -/

namespace ConstantRelativeRiskAversionUtility

/-- The derivative of CRRA utility `c^(1-γ)/(1-γ)` on `(0, ∞)` equals `crraMarginal γ`. -/
theorem deriv_eq_crraMarginal_on_Ioi (c : ConstantRelativeRiskAversionUtility) :
    Set.EqOn (deriv (fun x : ℝ => x ^ (1 - c.γ) / (1 - c.γ))) (crraMarginal c.γ) (Ioi 0) := by
  intro x hx
  have hx' : (0 : ℝ) < x := mem_Ioi.mp hx
  have h1γ : (1 - c.γ) ≠ 0 := sub_ne_zero.mpr c.γ_ne_one.symm
  have hd := (Real.hasDerivAt_rpow_const (x := x) (p := 1 - c.γ)
    (Or.inl hx'.ne')).div_const (1 - c.γ)
  rw [hd.deriv, crraMarginal_apply,
    show (1 - c.γ - 1) = -c.γ from by ring]
  field_simp

/-- CRRA utility is prudent: Its marginal `c^(-γ)` is convex on `(0, ∞)`. -/
theorem prudent (c : ConstantRelativeRiskAversionUtility) :
    Prudent (fun x : ℝ => x ^ (1 - c.γ) / (1 - c.γ)) := by
  unfold Prudent
  have h_eq : Set.EqOn (deriv (fun x : ℝ => x ^ (1 - c.γ) / (1 - c.γ)))
      (fun x : ℝ => x ^ (-c.γ)) (Ioi 0) := by
    intro x hx
    have := c.deriv_eq_crraMarginal_on_Ioi hx
    simpa [crraMarginal] using this
  have hconv : ConvexOn ℝ (Ioi 0) (fun x : ℝ => x ^ (-c.γ)) :=
    convexOn_rpow_of_nonpos (neg_nonpos_of_nonneg c.γ_pos.le)
  exact hconv.congr h_eq.symm

end ConstantRelativeRiskAversionUtility

end Econlib.Preferences
