/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Topology.StrictMonoOn
public import Econlib.Preferences.Utility.RiskFamilies
public import Mathlib.Algebra.EuclideanDomain.Basic
public import Mathlib.Algebra.EuclideanDomain.Field
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Twice-differentiable utility

This file defines `TwiceDiffUtility`, the central analytic utility object for risk and dynamic
choice: A twice-differentiable, strictly increasing utility on an open convex domain with its first
and second derivatives bundled as fields. It develops continuity and strict-monotonicity facts,
openness and convexity of the image, and the differentiable-inverse API, and instantiates the
structure from the constant-risk-aversion families.

## Main definitions

* `TwiceDiffUtility` — a twice-differentiable, strictly increasing utility on an open convex domain.
* `ConstantAbsoluteRiskAversionUtility.toTwiceDiffUtility`,
  `ConstantRelativeRiskAversionUtility.toTwiceDiffUtility` — CARA and CRRA instances.

## Main statements

* `TwiceDiffUtility.exists_inverse` — `u` admits a differentiable inverse on its image, with
  derivative `1 / u'(u_inv y)`.
* `TwiceDiffUtility.exists_inverse_twice_diff` — that inverse is twice differentiable on the image.

## Tags

utility, differentiable, inverse function, risk aversion
-/

@[expose] public section

open Set Filter

open Topology

namespace Econlib.Preferences

/-- A twice-differentiable, strictly increasing utility on an open convex domain. The first and
second derivatives are carried as fields `u'` and `u''`. -/
structure TwiceDiffUtility where
  /-- The utility function. -/
  u : ℝ → ℝ
  /-- The first derivative. -/
  u' : ℝ → ℝ
  /-- The second derivative. -/
  u'' : ℝ → ℝ
  /-- The domain on which the function is defined and twice differentiable. -/
  domain : Set ℝ
  /-- `domain` is open. -/
  domain_open : IsOpen domain
  /-- `domain` is convex. -/
  domain_convex : Convex ℝ domain
  /-- `domain` is nonempty. -/
  domain_nonempty : domain.Nonempty
  /-- `u` has derivative `u'` at every point in the domain. -/
  has_deriv : ∀ x ∈ domain, HasDerivAt u (u' x) x
  /-- `u'` has derivative `u''` at every point in the domain. -/
  has_second_deriv : ∀ x ∈ domain, HasDerivAt u' (u'' x) x
  /-- The agent is non-satiated: `u' > 0` on the domain. -/
  u'_pos : ∀ x ∈ domain, 0 < u' x

namespace TwiceDiffUtility

variable (f : TwiceDiffUtility)

/-- `u` is continuous on its domain. -/
lemma continuousOn_u : ContinuousOn f.u f.domain := fun x hx =>
  (f.has_deriv x hx).continuousAt.continuousWithinAt

/-- `u` is strictly monotone on its domain. -/
lemma strictMonoOn_u : StrictMonoOn f.u f.domain := by
  refine strictMonoOn_of_deriv_pos f.domain_convex f.continuousOn_u ?_
  intro x hx
  have hx' : x ∈ f.domain := interior_subset hx
  have hu : 0 < f.u' x := f.u'_pos x hx'
  have hderiv : deriv f.u x = f.u' x :=
    (f.has_deriv x hx').deriv
  simpa [hderiv] using hu

/-- The image of the domain under `u` is open. -/
lemma image_domain_open : IsOpen (f.u '' f.domain) :=
  StrictMonoOn.isOpen_image
    f.domain_open f.continuousOn_u f.strictMonoOn_u

/-- The image of the domain under `u` is convex. -/
lemma image_domain_convex : Convex ℝ (f.u '' f.domain) :=
  (f.domain_convex.isPreconnected.image f.u f.continuousOn_u).convex

/-- The image of the domain under `u` is nonempty. -/
lemma image_domain_nonempty : (f.u '' f.domain).Nonempty :=
  Set.Nonempty.image f.u f.domain_nonempty

/-- `u` admits an inverse on its image that is differentiable with derivative `1 / u'(u_inv y)`:
There is a function `u_inv` that is a two-sided inverse of `u` between the domain and its image and
satisfies `HasDerivAt u_inv (1 / u' (u_inv y)) y` at every image point `y`. -/
lemma exists_inverse :
    ∃ u_inv : ℝ → ℝ,
      (∀ x ∈ f.domain, u_inv (f.u x) = x) ∧
      (∀ y ∈ f.u '' f.domain, f.u (u_inv y) = y) ∧
      (∀ y ∈ f.u '' f.domain,
        HasDerivAt u_inv (1 / f.u' (u_inv y)) y) := by
  set u_inv := Function.invFunOn f.u f.domain
  have hinj := f.strictMonoOn_u.injOn
  refine ⟨u_inv, ?_, ?_, ?_⟩
  · intro x hx
    exact hinj (Function.invFunOn_mem ⟨x, hx, rfl⟩) hx
      (Function.invFunOn_eq ⟨x, hx, rfl⟩)
  · intro y hy
    exact Function.invFunOn_eq hy
  · intro y hy
    have h_cont : ContinuousAt u_inv y :=
      StrictMonoOn.continuousAt_invFunOn f.domain_open f.continuousOn_u f.strictMonoOn_u hy
    have h_mem : u_inv y ∈ f.domain := Function.invFunOn_mem hy
    have h_deriv : HasDerivAt f.u (f.u' (u_inv y)) (u_inv y) := f.has_deriv _ h_mem
    have h_ne : f.u' (u_inv y) ≠ 0 := ne_of_gt (f.u'_pos _ h_mem)
    have h_right_inv : ∀ᶠ z in nhds y, f.u (u_inv z) = z := f.image_domain_open.eventually_mem hy
      |>.mono (fun z hz => Function.invFunOn_eq hz)
    rw [one_div]
    exact HasDerivAt.of_local_left_inverse h_cont h_deriv h_ne h_right_inv

/-- The inverse of `u` is twice differentiable on the image of the domain: There are functions
`u_inv`, `u_inv'`, `u_inv''` with `u_inv` a two-sided inverse of `u`, and
`HasDerivAt u_inv (u_inv' y) y` and `HasDerivAt u_inv' (u_inv'' y) y` at every image point `y`. -/
lemma exists_inverse_twice_diff :
    ∃ u_inv u_inv' u_inv'' : ℝ → ℝ,
      (∀ x ∈ f.domain, u_inv (f.u x) = x) ∧
      (∀ y ∈ f.u '' f.domain, f.u (u_inv y) = y) ∧
      (∀ y ∈ f.u '' f.domain, HasDerivAt u_inv (u_inv' y) y) ∧
      (∀ y ∈ f.u '' f.domain, HasDerivAt u_inv' (u_inv'' y) y) := by
  obtain ⟨u_inv, h_left, h_right, h_deriv₁⟩ := f.exists_inverse
  set u_inv' := fun y => 1 / f.u' (u_inv y)
  set u_inv'' := fun y =>
    -(f.u'' (u_inv y) * (1 / f.u' (u_inv y))) / (f.u' (u_inv y)) ^ 2
  refine ⟨u_inv, u_inv', u_inv'', h_left, h_right, fun y hy => h_deriv₁ y hy, ?_⟩
  intro y hy
  have h_mem : u_inv y ∈ f.domain := by
    obtain ⟨x, hx, hfx⟩ := hy
    have : u_inv (f.u x) = x := h_left x hx
    rw [← hfx, this]; exact hx
  have h_u'_ne : f.u' (u_inv y) ≠ 0 := ne_of_gt (f.u'_pos _ h_mem)
  have h_chain : HasDerivAt (fun y => f.u' (u_inv y))
      (f.u'' (u_inv y) * (1 / f.u' (u_inv y))) y :=
    (f.has_second_deriv _ h_mem).comp y (h_deriv₁ y hy)
  -- `u_inv' = (f.u' (u_inv ·))⁻¹` definitionally (via `one_div`), so the reciprocal rule applies.
  simpa only [u_inv', u_inv'', one_div] using h_chain.inv h_u'_ne

end TwiceDiffUtility

/-- Construct a `TwiceDiffUtility` from a `ConstantAbsoluteRiskAversionUtility`. -/
noncomputable def ConstantAbsoluteRiskAversionUtility.toTwiceDiffUtility
    (c : ConstantAbsoluteRiskAversionUtility) : TwiceDiffUtility where
  u := c.u
  u' x := c.α * Real.exp (-c.α * x)
  u'' x := -(c.α ^ 2) * Real.exp (-c.α * x)
  domain := Set.univ
  domain_open := isOpen_univ
  domain_convex := convex_univ
  domain_nonempty := univ_nonempty
  has_deriv := by
    simpa using c.hasDerivAt_u
  has_second_deriv := by
    simpa using c.hasDerivAt_deriv_u
  u'_pos := by
    intro x _
    exact mul_pos c.α_pos (Real.exp_pos _)

/-- Construct a `TwiceDiffUtility` on `(0, ∞)` from a `ConstantRelativeRiskAversionUtility`. -/
noncomputable def ConstantRelativeRiskAversionUtility.toTwiceDiffUtility
    (c : ConstantRelativeRiskAversionUtility) : TwiceDiffUtility where
  u x := if hx : 0 < x then c.u x hx else 0
  u' x := if _hx : 0 < x then x ^ (-c.γ) else 0
  u'' x := if _hx : 0 < x then -c.γ * x ^ (-c.γ - 1) else 0
  domain := Set.Ioi 0
  domain_open := isOpen_Ioi
  domain_convex := convex_Ioi 0
  domain_nonempty := nonempty_Ioi
  has_deriv := by
    intro x hx
    have hx_pos : 0 < x := Set.mem_Ioi.mp hx
    have h1 : HasDerivAt (fun x' => x' ^ (1 - c.γ) / (1 - c.γ)) (x ^ (-c.γ)) x := by
      -- `(x'^(1-γ))/(1-γ)` differentiates to `(1-γ)·x^(1-γ-1)/(1-γ) = x^(-γ)`.
      have h1γ : (1 : ℝ) - c.γ ≠ 0 := sub_ne_zero.mpr (Ne.symm c.γ_ne_one)
      have hd := (Real.hasDerivAt_rpow_const (p := (1 - c.γ))
        (Or.inl (ne_of_gt hx_pos))).div_const (1 - c.γ)
      have h_pow_eq : (1 - c.γ) * x ^ (1 - c.γ - 1) = (1 - c.γ) * x ^ (-c.γ) := by congr 2; ring
      rwa [h_pow_eq, mul_div_cancel_left₀ _ h1γ] at hd
    have h_nhds : (fun x' => if hx' : 0 < x' then c.u x' hx' else 0) =ᶠ[𝓝 x]
      (fun x' => x' ^ (1 - c.γ) / (1 - c.γ)) := by
        apply Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hx_pos)
        intro y hy
        dsimp [ConstantRelativeRiskAversionUtility.u]
        exact if_pos hy
    simp only [hx_pos, u_def, dite_eq_ite]
    exact HasDerivAt.congr_of_eventuallyEq h1 h_nhds
  has_second_deriv := by
    intro x hx
    have hx_pos : 0 < x := hx -- We explicitly type this so `rw` can find the exact match later
    have hd := Real.hasDerivAt_rpow_const (p := -c.γ) (Or.inl (ne_of_gt hx_pos))
    have h_nhds :
      (fun x' => if hx' : 0 < x' then x' ^ (-c.γ) else 0) =ᶠ[𝓝 x] fun x' => x' ^ (-c.γ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact dif_pos hy
    rw [dif_pos hx_pos]
    exact hd.congr_of_eventuallyEq h_nhds
  u'_pos := by
    intro x hx
    have hx_pos : 0 < x := Set.mem_Ioi.mp hx
    rw [dif_pos hx_pos]
    exact Real.rpow_pos_of_pos hx_pos _

end Econlib.Preferences
