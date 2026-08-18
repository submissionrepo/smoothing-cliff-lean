/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Extrema

/-!
# First-Order Conditions

Calculus-based necessary and sufficient conditions for unconstrained interior maxima of real-valued
functions on `ℝ`. These are stated as lemmas in the `IsMaxOn`, `StrictConcaveOn`, and `ConcaveOn`
namespaces so they apply directly to optimization certificates.

## Main statements

* `IsMaxOn.deriv_eq_zero`: An interior maximizer of a differentiable function is stationary.
* `IsMaxOn.deriv_deriv_nonpos`: The second-order necessary condition `f''(x*) ≤ 0` at an interior
  maximizer.
* `StrictConcaveOn.isLocalMax_of_deriv_eq_zero`, `ConcaveOn.isLocalMax_of_deriv_eq_zero`: A
  stationary point of a (strictly) concave function on an open set is a local maximizer.
* `StrictConcaveOn.isMaxOn_of_deriv_eq_zero`, `ConcaveOn.isMaxOn_of_deriv_eq_zero`: A stationary
  point of a (strictly) concave function on an open set is a global maximizer on that set.

## Notes

`ConcaveOn` already suffices for global maximality; strict concavity is needed only for uniqueness
of the maximizer.

## Tags

first-order conditions, stationary point, concave, local maximum, optimization
-/

@[expose] public section

namespace Econlib.Optimization

/-- Interior first-order necessary condition: If `x*` is an interior maximizer and `f` is
differentiable at `x*`, then `f'(x*) = 0`. -/
lemma _root_.IsMaxOn.deriv_eq_zero {f : ℝ → ℝ} {x : ℝ} {X : Set ℝ}
    (h_max : IsMaxOn f X x)
    (h_interior : x ∈ interior X)
    -- kept for the statement's usual differentiability hypothesis; `IsLocalMax.deriv_eq_zero`
    -- holds unconditionally since `deriv` is junk-valued `0` off differentiability points
    (_h_diff : DifferentiableAt ℝ f x) :
    deriv f x = 0 :=
  (h_max.isLocalMax (interior_mem_nhds.mp (isOpen_interior.mem_nhds h_interior))).deriv_eq_zero

/-- Second-order necessary condition: If `x*` is an interior maximizer and `f` is twice
differentiable at `x*`, then `f''(x*) ≤ 0`. -/
lemma _root_.IsMaxOn.deriv_deriv_nonpos {f : ℝ → ℝ} {x : ℝ} {X : Set ℝ}
    (h_max : IsMaxOn f X x)
    (h_interior : x ∈ interior X)
    (h_diff : DifferentiableAt ℝ f x)
    -- kept for the statement's usual twice-differentiability hypothesis; the proof goes through
    -- unconditionally since `deriv (deriv f) x` is junk-valued `0` off differentiability points
    (_h_diff2 : DifferentiableAt ℝ (deriv f) x) :
    deriv (deriv f) x ≤ 0 := by
  have hloc : IsLocalMax f x :=
    h_max.isLocalMax (interior_mem_nhds.mp (isOpen_interior.mem_nhds h_interior))
  have hderiv_eq_zero : deriv f x = 0 := hloc.deriv_eq_zero
  by_contra h
  push Not at h
  have hmin : IsLocalMin f x :=
    isLocalMin_of_deriv_deriv_pos h hderiv_eq_zero h_diff.continuousAt
  have hf_const_nhds : ∀ᶠ y in nhds x, f y = f x :=
    hloc.mp (hmin.mono fun y hle hge => le_antisymm hge hle)
  have hderiv_zero_nhds : ∀ᶠ y in nhds x, deriv f y = 0 :=
    hf_const_nhds.eventually_nhds.mono fun y hy =>
      (Filter.EventuallyEq.deriv_eq hy).trans (deriv_const y (f x))
  have hderiv2_eq_zero : deriv (deriv f) x = 0 :=
    (Filter.EventuallyEq.deriv_eq hderiv_zero_nhds).trans (deriv_const x (0 : ℝ))
  linarith

/-- Second-order sufficient condition: If `f` is differentiable at `x*` with `f'(x*) = 0` and `f`
is strictly concave on an open set containing `x*`, then `x*` is a local maximizer. -/
lemma _root_.StrictConcaveOn.isLocalMax_of_deriv_eq_zero {f : ℝ → ℝ} {x : ℝ} {S : Set ℝ}
    (h_open : IsOpen S) (hx : x ∈ S)
    (h_diff : DifferentiableAt ℝ f x)
    (h_foc : deriv f x = 0)
    (h_concave : StrictConcaveOn ℝ S f) :
    IsLocalMax f x := by
  apply Filter.mem_of_superset (h_open.mem_nhds hx)
  intro y hy
  change f y ≤ f x
  by_cases hxy : y = x
  · rw [hxy]
  · rcases ne_iff_lt_or_gt.mp hxy with hlt | hgt
    · have hslope := h_concave.concaveOn.deriv_le_slope hy hx hlt h_diff
      rw [h_foc, slope_def_field] at hslope
      have hpos : (0 : ℝ) < x - y := sub_pos.mpr hlt
      rcases div_nonneg_iff.mp hslope with ⟨hnum, _⟩ | ⟨_, hden⟩ <;> linarith
    · have hslope := h_concave.concaveOn.slope_le_deriv hx hy hgt h_diff
      rw [h_foc, slope_def_field] at hslope
      have hpos : (0 : ℝ) < y - x := sub_pos.mpr hgt
      rcases div_nonpos_iff.mp hslope with ⟨hnum, _⟩ | ⟨_, hden⟩ <;> linarith

/-- First-order sufficient condition: A stationary point of a function that is strictly concave on
an open set is a global maximizer on that set. -/
lemma _root_.StrictConcaveOn.isMaxOn_of_deriv_eq_zero {f : ℝ → ℝ} {x : ℝ} {S : Set ℝ}
    (h_open : IsOpen S) (hx : x ∈ S)
    (h_diff : DifferentiableAt ℝ f x)
    (h_foc : deriv f x = 0)
    (h_concave : StrictConcaveOn ℝ S f) :
    IsMaxOn f S x :=
  IsMaxOn.of_isLocalMaxOn_of_concaveOn hx
    ((h_concave.isLocalMax_of_deriv_eq_zero h_open hx h_diff h_foc).on S)
    h_concave.concaveOn

/-- Second-order sufficient condition (non-strict): If `f` is differentiable at `x*` with
`f′(x*) = 0` and `f` is concave on an open set containing `x*`, then `x*` is a local maximizer.
Strictness is needed only to make the maximizer unique, not to make it a maximizer. -/
lemma _root_.ConcaveOn.isLocalMax_of_deriv_eq_zero {f : ℝ → ℝ} {x : ℝ} {S : Set ℝ}
    (h_open : IsOpen S) (hx : x ∈ S)
    (h_diff : DifferentiableAt ℝ f x)
    (h_foc : deriv f x = 0)
    (h_concave : ConcaveOn ℝ S f) :
    IsLocalMax f x := by
  apply Filter.mem_of_superset (h_open.mem_nhds hx)
  intro y hy
  change f y ≤ f x
  by_cases hxy : y = x
  · rw [hxy]
  · rcases ne_iff_lt_or_gt.mp hxy with hlt | hgt
    · have hslope := h_concave.deriv_le_slope hy hx hlt h_diff
      rw [h_foc, slope_def_field] at hslope
      have hpos : (0 : ℝ) < x - y := sub_pos.mpr hlt
      rcases div_nonneg_iff.mp hslope with ⟨hnum, _⟩ | ⟨_, hden⟩ <;> linarith
    · have hslope := h_concave.slope_le_deriv hx hy hgt h_diff
      rw [h_foc, slope_def_field] at hslope
      have hpos : (0 : ℝ) < y - x := sub_pos.mpr hgt
      rcases div_nonpos_iff.mp hslope with ⟨hnum, _⟩ | ⟨_, hden⟩ <;> linarith

/-- First-order sufficient condition (non-strict): A stationary point of a function concave on an
open set is a global maximizer on that set. `ConcaveOn` suffices for global maximality; strict
concavity is only needed for uniqueness of the maximizer. -/
lemma _root_.ConcaveOn.isMaxOn_of_deriv_eq_zero {f : ℝ → ℝ} {x : ℝ} {S : Set ℝ}
    (h_open : IsOpen S) (hx : x ∈ S)
    (h_diff : DifferentiableAt ℝ f x)
    (h_foc : deriv f x = 0)
    (h_concave : ConcaveOn ℝ S f) :
    IsMaxOn f S x :=
  IsMaxOn.of_isLocalMaxOn_of_concaveOn hx
    ((h_concave.isLocalMax_of_deriv_eq_zero h_open hx h_diff h_foc).on S)
    h_concave

end Econlib.Optimization
