/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Convexity of negative-exponent power functions

Mathlib's `convexOn_rpow` covers the real power `x ↦ x ^ p` only for `1 ≤ p`. This file supplies
the complementary convexity for nonpositive exponents `p ≤ 0` on `(0, ∞)`, via the nonnegative
second derivative `p (p - 1) x ^ (p - 2)`.

## Main results

* `convexOn_rpow_of_nonpos` — `x ↦ x ^ p` is convex on `(0, ∞)` for `p ≤ 0`.
-/

@[expose] public section

open Set Topology

/-- `x ↦ x^p` is convex on `(0, ∞)` for `p ≤ 0`. Complements Mathlib's `convexOn_rpow`, which
covers only `1 ≤ p`. -/
theorem convexOn_rpow_of_nonpos {p : ℝ} (hp : p ≤ 0) :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ => x ^ p) := by
  set f : ℝ → ℝ := fun x => x ^ p
  set f' : ℝ → ℝ := fun x => p * x ^ (p - 1)
  have hderiv_eq_nhds : ∀ x ∈ Ioi 0, deriv f =ᶠ[𝓝 x] f' := by
    intro x hx
    filter_upwards [isOpen_Ioi.mem_nhds (mem_Ioi.mp hx)] with y hy
    exact (Real.hasDerivAt_rpow_const (Or.inl (mem_Ioi.mp hy).ne')).deriv
  refine convexOn_of_deriv2_nonneg (convex_Ioi 0) ?cont ?diff ?diff2 ?nn
  case cont =>
    intro x hx
    have hx' : (0 : ℝ) < x := mem_Ioi.mp hx
    exact (Real.continuousAt_rpow_const x p (Or.inl hx'.ne')).continuousWithinAt
  case diff =>
    rw [interior_Ioi]
    intro x hx
    have hx' : (0 : ℝ) < x := mem_Ioi.mp hx
    exact (Real.hasDerivAt_rpow_const
      (Or.inl hx'.ne')).differentiableAt.differentiableWithinAt
  case diff2 =>
    rw [interior_Ioi]
    intro x hx
    have hx' : (0 : ℝ) < x := mem_Ioi.mp hx
    have hf'_diff : DifferentiableAt ℝ f' x :=
      ((Real.hasDerivAt_rpow_const (x := x) (p := p - 1)
        (Or.inl hx'.ne')).const_mul p).differentiableAt
    exact (hf'_diff.congr_of_eventuallyEq
      (hderiv_eq_nhds x hx)).differentiableWithinAt
  case nn =>
    rw [interior_Ioi]
    intro x hx
    have hx' : (0 : ℝ) < x := mem_Ioi.mp hx
    change 0 ≤ deriv (deriv f) x
    rw [(hderiv_eq_nhds x hx).deriv_eq]
    have hd := (Real.hasDerivAt_rpow_const (x := x) (p := p - 1)
      (Or.inl hx'.ne')).const_mul p
    rw [hd.deriv]
    have hpp1 : 0 ≤ p * (p - 1) := by nlinarith
    have hxpow : 0 < x ^ (p - 1 - 1) := Real.rpow_pos_of_pos hx' _
    nlinarith
