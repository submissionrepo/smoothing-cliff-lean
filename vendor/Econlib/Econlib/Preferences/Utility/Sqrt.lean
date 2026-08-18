/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Utility.Inada
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The square-root Inada utility

The concrete `InadaUtility` witness `u(c) = √c` (CRRA with `γ = 1/2`, up to a positive scalar) on
the domain `(0, ∞)`.

Unlike `InadaUtility.log`, the square-root utility is concave on the closed ray `[0, ∞)`: Its junk
value `Real.sqrt 0 = 0` is exactly the boundary value of `√`, so concavity extends to the boundary.
This is the canonical witness when concavity is needed on `[0, ∞)` rather than only on the open
domain `(0, ∞)`.

## Main definitions

* `InadaUtility.sqrt` — the square-root utility as an `InadaUtility`.

## Main statements

* `InadaUtility.sqrt_concaveOn_Ici` — `√` is concave on the closed ray `[0, ∞)`.
* `InadaUtility.sqrt_slowlyVarying` — the marginal utility is slowly varying:
  `u'(c + Δ) / u'(c) → 1` as `c → ∞`.

## Tags

square-root utility, inada utility, crra, concavity, slowly varying
-/

@[expose] public section

namespace Econlib.Preferences

open Set Filter Topology

/-- **The square-root Inada utility** `u(x) = √x` on `(0, ∞)`.

This is the canonical witness with marginal utility `u'(x) = (2√x)⁻¹ = (1/2)·x^(-1/2)` and
curvature `u''(x) = -(4·x·√x)⁻¹ = -(1/4)·x^(-3/2)`. It is the CRRA utility with relative risk
aversion `1/2` (up to a positive scalar). Unlike `log`, `√` is concave on the closed ray `[0, ∞)`,
since `Real.sqrt 0 = 0` agrees with the boundary value. -/
noncomputable def InadaUtility.sqrt : InadaUtility where
  toTwiceDiffUtility :=
    { u := Real.sqrt
      u' := fun x => (2 * Real.sqrt x)⁻¹
      u'' := fun x => -(4 * x * Real.sqrt x)⁻¹
      domain := Set.Ioi 0
      domain_open := isOpen_Ioi
      domain_convex := convex_Ioi 0
      domain_nonempty := Set.nonempty_Ioi
      has_deriv := fun x hx => by
        have hx0 : x ≠ 0 := ne_of_gt (Set.mem_Ioi.mp hx)
        simpa only [one_div] using Real.hasDerivAt_sqrt hx0
      has_second_deriv := fun x hx => by
        have hx0 : 0 < x := Set.mem_Ioi.mp hx
        have hx0' : x ≠ 0 := ne_of_gt hx0
        have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
        have hg : HasDerivAt (fun x => 2 * Real.sqrt x)
            (2 * (1 / (2 * Real.sqrt x))) x :=
          (Real.hasDerivAt_sqrt hx0').const_mul 2
        have hg_ne : (2 * Real.sqrt x) ≠ 0 := ne_of_gt (mul_pos two_pos hsqrt_pos)
        -- Reciprocal rule: `(g⁻¹)' = -g' / (g x)²`.
        have hinv := hg.inv hg_ne
        have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
        convert hinv using 1
        change -(4 * x * Real.sqrt x)⁻¹
            = -(2 * (1 / (2 * Real.sqrt x))) / (2 * Real.sqrt x) ^ 2
        set s := Real.sqrt x
        have hs_ne : s ≠ 0 := ne_of_gt hsqrt_pos
        rw [← hsx]
        field_simp
        ring
      u'_pos := fun x hx => by
        have hx0 : 0 < x := Set.mem_Ioi.mp hx
        have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
        exact inv_pos.mpr (mul_pos two_pos hsqrt_pos) }
  domain_eq := rfl
  u''_neg := fun x hx => by
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have hpos : 0 < 4 * x * Real.sqrt x :=
      mul_pos (mul_pos (by norm_num) hx0) hsqrt_pos
    exact neg_lt_zero.mpr (inv_pos.mpr hpos)
  inada_zero := by
    -- `(2√x)⁻¹ → +∞` as `x → 0⁺`: `2√x → 0⁺`, so the inverse diverges.
    have h2sqrt : Tendsto (fun x : ℝ => 2 * Real.sqrt x) (𝓝[>] 0) (𝓝[>] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun x : ℝ => 2 * Real.sqrt x) (𝓝[>] 0) (𝓝 (2 * Real.sqrt 0)) :=
          ((continuous_const.mul Real.continuous_sqrt).tendsto 0).mono_left nhdsWithin_le_nhds
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        have hx0 : 0 < x := Set.mem_Ioi.mp hx
        exact Set.mem_Ioi.mpr (mul_pos two_pos (Real.sqrt_pos.mpr hx0))
    exact tendsto_inv_nhdsGT_zero.comp h2sqrt
  inada_infty := by
    -- `(2√x)⁻¹ → 0` as `x → ∞`: `2√x → ∞`, so the inverse vanishes.
    have h2sqrt : Tendsto (fun x : ℝ => 2 * Real.sqrt x) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) Real.tendsto_sqrt_atTop
    exact tendsto_inv_atTop_zero.comp h2sqrt

/-- `InadaUtility.sqrt.u` is definitionally `Real.sqrt`. -/
@[simp] lemma InadaUtility.sqrt_u : InadaUtility.sqrt.u = Real.sqrt := rfl

/-- `InadaUtility.sqrt.u' x = (2√x)⁻¹`. -/
@[simp] lemma InadaUtility.sqrt_u'_apply (x : ℝ) :
    InadaUtility.sqrt.u' x = (2 * Real.sqrt x)⁻¹ := rfl

/-- `√` is concave on the closed ray `[0, ∞)`.

Its boundary junk value `Real.sqrt 0 = 0` agrees with the boundary value of the concave function,
so concavity holds on `[0, ∞)`, not merely on the open domain `(0, ∞)`. -/
theorem InadaUtility.sqrt_concaveOn_Ici :
    ConcaveOn ℝ (Set.Ici (0 : ℝ)) InadaUtility.sqrt.u :=
  Real.strictConcaveOn_sqrt.concaveOn

/-- **Slowly varying marginal utility.** For any shift `Δ`, the ratio of marginal utilities
`u'(c + Δ) / u'(c) → 1` as `c → ∞`. -/
theorem InadaUtility.sqrt_slowlyVarying (Δ : ℝ) :
    Tendsto (fun c => InadaUtility.sqrt.u' (c + Δ) / InadaUtility.sqrt.u' c) atTop (𝓝 1) := by
  have hadd : Tendsto (fun c : ℝ => c + Δ) atTop atTop :=
    tendsto_atTop_add_const_right atTop Δ tendsto_id
  -- `Δ / (c + Δ) → 0`, so `c / (c + Δ) = 1 - Δ / (c + Δ) → 1`.
  have hfrac : Tendsto (fun c : ℝ => Δ / (c + Δ)) atTop (𝓝 0) :=
    hadd.const_div_atTop Δ
  have hratio1 : Tendsto (fun c : ℝ => 1 - Δ / (c + Δ)) atTop (𝓝 (1 - 0)) :=
    tendsto_const_nhds.sub hfrac
  -- `c / (c + Δ) → 1`, via eventual equality `c / (c + Δ) = 1 - Δ / (c + Δ)` once `c + Δ ≠ 0`.
  have hratio : Tendsto (fun c : ℝ => c / (c + Δ)) atTop (𝓝 1) := by
    have heq : (fun c : ℝ => c / (c + Δ)) =ᶠ[atTop] (fun c : ℝ => 1 - Δ / (c + Δ)) := by
      filter_upwards [eventually_gt_atTop (max 0 (-Δ))] with c hc
      have hcΔ : c + Δ ≠ 0 := by
        have : -Δ < c := lt_of_le_of_lt (le_max_right 0 (-Δ)) hc
        linarith
      rw [eq_sub_iff_add_eq, ← add_div, div_self hcΔ]
    rw [sub_zero] at hratio1
    exact hratio1.congr' heq.symm
  have hsqrt_ratio : Tendsto (fun c : ℝ => Real.sqrt (c / (c + Δ))) atTop (𝓝 1) := by
    have := hratio.sqrt
    simpa using this
  refine hsqrt_ratio.congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 (-Δ))] with c hc
  have hc0 : 0 < c := lt_of_le_of_lt (le_max_left 0 (-Δ)) hc
  have hcΔ : 0 < c + Δ := by
    have : -Δ < c := lt_of_le_of_lt (le_max_right 0 (-Δ)) hc
    linarith
  have hsc : Real.sqrt c ≠ 0 := Real.sqrt_ne_zero'.mpr hc0
  have hscΔ : Real.sqrt (c + Δ) ≠ 0 := Real.sqrt_ne_zero'.mpr hcΔ
  -- `√(c / (c + Δ)) = √c / √(c + Δ) = (2√(c + Δ))⁻¹ / (2√c)⁻¹`.
  simp only [InadaUtility.sqrt_u'_apply]
  rw [Real.sqrt_div hc0.le]
  field_simp

end Econlib.Preferences
