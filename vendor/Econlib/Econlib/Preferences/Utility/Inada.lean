/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Utility.Differentiable
public import Mathlib.Analysis.Convex.Deriv

/-!
# Inada conditions

This file extends `TwiceDiffUtility` with the **Inada conditions** (Inada 1963) used in
macroeconomic and dynamic-choice models:

* `u''(x) < 0` for all `x ∈ (0, ∞)` (strict concavity),
* `u'(x) → +∞` as `x → 0⁺`,
* `u'(x) → 0` as `x → +∞`.

It derives strict concavity, the tangent-line bound, strict monotonicity and surjectivity of
marginal utility onto `(0, ∞)`, the unique solution of the marginal-utility equation, and the
inverse-marginal function, and exhibits the natural logarithm as the canonical witness.

## Main definitions

* `InadaUtility` — a `TwiceDiffUtility` whose domain is `(0, ∞)` and which satisfies the Inada
  conditions.
* `InadaUtility.inverseMarginal` — the inverse marginal utility `μ ↦ c` solving `u'(c) = μ`.
* `InadaUtility.log` — the natural logarithm as a canonical Inada utility.

## Main statements

* `InadaUtility.strictConcaveOn` — `u` is strictly concave on `(0, ∞)`.
* `InadaUtility.u_le_tangent` — the concave tangent-line bound `u(y) ≤ u(x) + u'(x)·(y − x)`.
* `InadaUtility.strictAntiOn_u'` — `u'` is strictly decreasing.
* `InadaUtility.u'_surjOn` — `u'` surjects onto `(0, ∞)`.
* `InadaUtility.unique_marginal_solution` — `u'(c) = μ` has a unique solution `c > 0` for any
  `μ > 0`.

## References

* Inada, Ken-Ichi. 1963. “On a Two-Sector Model of Economic Growth: Comments and a Generalization.”
  *The Review of Economic Studies* 30 (2): 119. [https://doi.org/10.2307/2295809](https://doi.org/10.2307/2295809).

## Tags

utility, inada conditions, concave, marginal utility, logarithm
-/

@[expose] public section

namespace Econlib.Preferences

open Set Filter Topology

/-- A utility function satisfying the Inada conditions. -/
structure InadaUtility extends TwiceDiffUtility where
  /-- The domain is `(0, ∞)`. -/
  domain_eq : toTwiceDiffUtility.domain = Ioi 0
  /-- Strict concavity: `u'' < 0` on the domain. -/
  u''_neg : ∀ x ∈ toTwiceDiffUtility.domain, toTwiceDiffUtility.u'' x < 0
  /-- Inada condition at zero: `u'(x) → +∞` as `x → 0⁺`. -/
  inada_zero : Tendsto toTwiceDiffUtility.u' (𝓝[>] 0) atTop
  /-- Inada condition at infinity: `u'(x) → 0` as `x → +∞`. -/
  inada_infty : Tendsto toTwiceDiffUtility.u' atTop (𝓝 0)

namespace InadaUtility

variable (f : InadaUtility)

/-- A point lies in the domain iff it is strictly positive. -/
lemma mem_domain_iff {x : ℝ} :
    x ∈ f.toTwiceDiffUtility.domain ↔ 0 < x := by
  rw [f.domain_eq]; exact Set.mem_Ioi

/-- `u'` is positive on `(0, ∞)`. -/
lemma u'_pos_on (x : ℝ) (hx : 0 < x) :
    0 < f.u' x :=
  f.u'_pos x (f.mem_domain_iff.mpr hx)

/-- `u'` is continuous on `(0, ∞)`. -/
lemma continuousOn_u' :
    ContinuousOn f.u' (Ioi 0) := by
  rw [← f.domain_eq]
  exact fun x hx =>
    (f.has_second_deriv x hx).continuousAt.continuousWithinAt

/-- `deriv u = u'` on the domain. -/
lemma deriv_eq (x : ℝ) (hx : x ∈ f.domain) :
    deriv f.u x = f.u' x :=
  (f.has_deriv x hx).deriv

/-- `deriv u' = u''` on the domain. -/
lemma deriv_u'_eq (x : ℝ) (hx : x ∈ f.domain) :
    deriv f.u' x = f.u'' x :=
  (f.has_second_deriv x hx).deriv

/-- **Strict concavity.** `u` is strictly concave on `(0, ∞)`. -/
theorem strictConcaveOn :
    StrictConcaveOn ℝ (Ioi (0 : ℝ)) f.u := by
  rw [← f.domain_eq]
  apply strictConcaveOn_of_deriv2_neg f.domain_convex
    f.continuousOn_u
  intro x hx
  rw [f.toTwiceDiffUtility.domain_open.interior_eq] at hx
  change deriv (deriv f.u) x < 0
  have hderiv_eq_u' : deriv f.u =ᶠ[𝓝 x] f.u' :=
    Filter.eventually_of_mem (f.toTwiceDiffUtility.domain_open.mem_nhds hx)
      fun y hy => (f.has_deriv y hy).deriv
  rw [hderiv_eq_u'.deriv_eq, f.deriv_u'_eq x hx]
  exact f.u''_neg x hx

/-- `u` is concave on `(0, ∞)`. -/
theorem concaveOn : ConcaveOn ℝ (Ioi (0 : ℝ)) f.u :=
  f.strictConcaveOn.concaveOn

/-- **Concave tangent-line (gradient) bound.** `u` lies weakly below its tangent at any interior
point: `u(y) ≤ u(x) + u'(x)·(y − x)` for all `x, y > 0`. -/
theorem u_le_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    f.u y ≤ f.u x + f.u' x * (y - x) := by
  have hxd : x ∈ Ioi (0 : ℝ) := hx
  have hyd : y ∈ Ioi (0 : ℝ) := hy
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have hslope : f.u' x ≤ slope f.u y x :=
      f.concaveOn.le_slope_of_hasDerivAt hyd hxd hyx (f.has_deriv x (f.mem_domain_iff.mpr hx))
    rw [slope_def_field] at hslope
    have hdpos : 0 < x - y := sub_pos.mpr hyx
    have := (le_div_iff₀ hdpos).mp hslope
    nlinarith [this]
  · simp
  · have hslope : slope f.u x y ≤ f.u' x :=
      f.concaveOn.slope_le_of_hasDerivAt hxd hyd hxy (f.has_deriv x (f.mem_domain_iff.mpr hx))
    rw [slope_def_field] at hslope
    have hdpos : 0 < y - x := sub_pos.mpr hxy
    have := (div_le_iff₀ hdpos).mp hslope
    nlinarith [this]

/-- **`u'` is strictly decreasing** on `(0, ∞)`. -/
theorem strictAntiOn_u' :
    StrictAntiOn f.u' (Ioi (0 : ℝ)) := by
  rw [← f.domain_eq]
  apply strictAntiOn_of_deriv_neg f.domain_convex
  · rw [f.domain_eq]; exact f.continuousOn_u'
  · intro x hx
    rw [f.domain_open.interior_eq] at hx
    rw [f.deriv_u'_eq x hx]
    exact f.u''_neg x hx

/-- `u'` surjects onto `(0, ∞)`: For any `μ > 0`, there exists `c > 0` with `u'(c) = μ`. -/
theorem u'_surjOn :
    SurjOn f.u' (Ioi 0) (Ioi 0) := by
  intro μ hμ
  rw [Set.mem_Ioi] at hμ
  -- u' → 0 at +∞ with μ > 0 gives x₂ with u'(x₂) < μ.
  obtain ⟨x₂, hx₂, hx₂_pos⟩ :=
    ((f.inada_infty.eventually_lt_const hμ).and (eventually_gt_atTop 0)).exists
  -- u' → +∞ at 0⁺ gives x₁ ∈ (0, x₂) with u'(x₁) > μ.
  have h_eventually_large : ∀ᶠ x in 𝓝[>] (0 : ℝ), μ < f.u' x :=
    f.inada_zero.eventually_gt_atTop μ
  obtain ⟨x₁, hx₁, hx₁_pos, hx₁_lt⟩ :=
    ((h_eventually_large.and
      (Filter.eventually_of_mem (Ioo_mem_nhdsGT hx₂_pos) fun _ h => h)).exists)
  have hle : x₁ ≤ x₂ := le_of_lt hx₁_lt
  have hcont : ContinuousOn f.u' (Set.Icc x₁ x₂) :=
    f.continuousOn_u'.mono (fun x ⟨h1, _⟩ =>
      Set.mem_Ioi.mpr (lt_of_lt_of_le hx₁_pos h1))
  have hμ_mem : μ ∈ Set.Icc (f.u' x₂) (f.u' x₁) :=
    ⟨le_of_lt hx₂, le_of_lt hx₁⟩
  -- Apply IVT on [x₁, x₂] with endpoints swapped (u' is decreasing so u'(x₂) ≤ u'(x₁)).
  have hivt := isPreconnected_Icc.intermediate_value
    (Set.right_mem_Icc.mpr hle) (Set.left_mem_Icc.mpr hle)
    hcont
  obtain ⟨c, hc_mem, hc_eq⟩ := hivt hμ_mem
  exact ⟨c, Set.mem_Ioi.mpr (lt_of_lt_of_le hx₁_pos hc_mem.1),
    hc_eq⟩

/-- **Unique marginal solution.** For `μ > 0`, `u'(c) = μ` has a unique solution `c ∈ (0, ∞)`. -/
theorem unique_marginal_solution (μ : ℝ) (hμ : 0 < μ) :
    ∃! c : ℝ, c ∈ Ioi (0 : ℝ) ∧ f.u' c = μ := by
  obtain ⟨c, hc_pos, hc_eq⟩ := f.u'_surjOn (Set.mem_Ioi.mpr hμ)
  refine ⟨c, ⟨hc_pos, hc_eq⟩, fun d ⟨hd_pos, hd_eq⟩ => ?_⟩
  exact f.strictAntiOn_u'.injOn hd_pos hc_pos (hd_eq.trans hc_eq.symm)

/-- The inverse marginal utility function. -/
noncomputable def inverseMarginal (μ : ℝ) : ℝ :=
  if hμ : 0 < μ then
    (f.unique_marginal_solution μ hμ).choose
  else 0

/-- The inverse marginal utility is strictly positive at any positive marginal value. -/
lemma inverseMarginal_pos {μ : ℝ} (hμ : 0 < μ) :
    0 < f.inverseMarginal μ := by
  simp only [inverseMarginal, dif_pos hμ]
  exact (f.unique_marginal_solution μ hμ).choose_spec.1.1

/-- The inverse marginal utility inverts `u'`: `u'(inverseMarginal μ) = μ` for `μ > 0`. -/
lemma inverseMarginal_spec {μ : ℝ} (hμ : 0 < μ) :
    f.u' (f.inverseMarginal μ) = μ := by
  simp only [inverseMarginal, dif_pos hμ]
  exact (f.unique_marginal_solution μ hμ).choose_spec.1.2

end InadaUtility

/-- **The canonical Inada utility: Natural logarithm** `u(x) = log x` on `(0, ∞)`. The marginal
utility `u' = x⁻¹` is positive and strictly decreasing, `u'' = -(x²)⁻¹ < 0`, and `x⁻¹ → ∞` as
`x → 0⁺` while `x⁻¹ → 0` as `x → ∞`. -/
noncomputable def InadaUtility.log : InadaUtility where
  toTwiceDiffUtility :=
    { u := Real.log
      u' := fun x => x⁻¹
      u'' := fun x => -(x ^ 2)⁻¹
      domain := Set.Ioi 0
      domain_open := isOpen_Ioi
      domain_convex := convex_Ioi 0
      domain_nonempty := Set.nonempty_Ioi
      has_deriv := fun _ hx => Real.hasDerivAt_log (ne_of_gt (Set.mem_Ioi.mp hx))
      has_second_deriv := fun _ hx => hasDerivAt_inv (ne_of_gt (Set.mem_Ioi.mp hx))
      u'_pos := fun _ hx => inv_pos.mpr (Set.mem_Ioi.mp hx) }
  domain_eq := rfl
  u''_neg := fun x hx => by
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    exact neg_lt_zero.mpr (inv_pos.mpr (pow_pos hx0 2))
  inada_zero := tendsto_inv_nhdsGT_zero
  inada_infty := tendsto_inv_atTop_zero

/-- The utility of `InadaUtility.log` is `Real.log`. -/
@[simp] lemma InadaUtility.log_u : InadaUtility.log.u = Real.log := rfl

/-- The marginal utility of `InadaUtility.log` is `x⁻¹`. -/
@[simp] lemma InadaUtility.log_u'_apply (x : ℝ) : InadaUtility.log.u' x = x⁻¹ := rfl

end Econlib.Preferences
