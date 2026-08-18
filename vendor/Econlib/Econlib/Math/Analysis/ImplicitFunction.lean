/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Parameterized implicit function theorem for contraction fixed points

Convenience wrappers on top of Mathlib's `ContDiffAt.implicitFunction` specialized to fixed-point
equations `F = T(μ, F)`, i.e. `Γ(μ, F) := F - T(μ, F) = 0`. When the partial derivative `D_F T` is
a contraction (`‖D_F T‖ < 1`), the partial derivative `D_F Γ = I - D_F T` is invertible by the
Neumann series, so the implicit function theorem applies. The resulting implicit function `s` with
`s(μ) = T(μ, s(μ))` is packaged together with its evaluation at the base point, the local
fixed-point equation, `C^n` smoothness, local uniqueness, and the derivative formula
`D s(μ₀) = (I - D_F T)⁻¹ ∘ D_μ T`.

The final section specializes the type parameters to `ι → ℝ` (with `ι` finite) for coordinate-based
applications.

## Main definitions

* `ContDiffAt.fixedPointImplicitFunction` — the implicit function for `F = T(μ, F)`.
* `ContDiffAt.fixedPointCoord` — its coordinate specialization to `ι → ℝ`.

## Main statements

* `ContinuousLinearMap.IsInvertible.id_sub_of_norm_lt_one` — `‖A‖ < 1 → (id - A).IsInvertible`.
* `ContDiffAt.contDiffAt_fixedPointImplicitFunction` — the implicit function is `C^n`.
* `ContDiffAt.eventually_eq_fixedPointImplicitFunction` — local uniqueness.
* `ContDiffAt.hasStrictFDerivAt_fixedPointImplicitFunction` — the derivative formula for the
  fixed-point case.
-/

@[expose] public section

open ContinuousLinearMap Filter
open scoped Topology

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Contraction bridge: `‖A‖ < 1 → (id - A).IsInvertible` -/

section ContractionBridge

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- If `A : F →L[𝕜] F` has operator norm `< 1`, then `id - A` is invertible as a continuous linear
map. This is the bridge from contraction conditions to the IFT hypothesis. -/
theorem ContinuousLinearMap.IsInvertible.id_sub_of_norm_lt_one
    (A : F →L[𝕜] F) (hA : ‖A‖ < 1) : (ContinuousLinearMap.id 𝕜 F - A).IsInvertible := by
  -- `1 - A` is a unit in the normed ring `F →L[𝕜] F` by Neumann series
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hA
  -- Build ContinuousLinearEquiv from the unit
  refine ⟨ContinuousLinearEquiv.ofUnit u, ?_⟩
  ext x
  -- `ofUnit u` applies as `u.val`, which equals `1 - A`
  change (u : F →L[𝕜] F) x = (ContinuousLinearMap.id 𝕜 F - A) x
  rw [hu, ContinuousLinearMap.one_def]

end ContractionBridge

/-! ### Fixed-point implicit function theorem -/

section FixedPointIFT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

omit [CompleteSpace E] in
/-- Given a C^n operator `T : E × F → F` and a fixed point `(μ₀, F₀)` with `F₀ = T(μ₀, F₀)`, if the
partial derivative `D_F T` has norm `< 1` (contraction), then the equation
`Γ(μ, F) := F - T(μ, F) = 0` satisfies the implicit function theorem hypothesis.

The partial derivative of `Γ` in `F` is `I - D_F T`, which is invertible by the Neumann series when
`‖D_F T‖ < 1`. -/
theorem isInvertible_fderiv_sub_of_contraction
    {T : E × F → F} {u : E × F}
    (hT : DifferentiableAt 𝕜 T u)
    (hcontr : ‖(fderiv 𝕜 T u).comp (.inr 𝕜 E F)‖ < 1) :
    (fderiv 𝕜 (fun p : E × F => p.2 - T p) u |>.comp (.inr 𝕜 E F)).IsInvertible := by
  -- D_F (F - T(μ,F)) = id - D_F T
  have hΓ : fderiv 𝕜 (fun p : E × F => p.2 - T p) u =
      .snd 𝕜 E F - fderiv 𝕜 T u :=
    (hasFDerivAt_snd.sub hT.hasFDerivAt).fderiv
  rw [hΓ, sub_comp, snd_comp_inr]
  exact ContinuousLinearMap.IsInvertible.id_sub_of_norm_lt_one _ hcontr

variable {n : WithTop ℕ∞}

/-- **Fixed-point implicit function theorem.** Given `T : E × F → F` that is C^n at a fixed point
`(μ₀, F₀)` with `F₀ = T(μ₀, F₀)`, if `‖D_F T(μ₀, F₀)‖ < 1`, then there exists a C^n implicit
function `s` with `s(μ) = T(μ, s(μ))` locally.

Returns the implicit function defined by `ContDiffAt.implicitFunction` applied to
`Γ(μ, F) := F - T(μ, F)`. -/
noncomputable def ContDiffAt.fixedPointImplicitFunction
    {T : E × F → F} {u : E × F}
    (hT : ContDiffAt 𝕜 n T u)
    (hn : n ≠ 0)
    (hcontr : ‖(fderiv 𝕜 T u).comp (.inr 𝕜 E F)‖ < 1) :
    E → F :=
  let Γ : E × F → F := fun p => p.2 - T p
  let hΓ : ContDiffAt 𝕜 n Γ u := contDiffAt_snd.sub hT
  let hinv := isInvertible_fderiv_sub_of_contraction (hT.differentiableAt hn) hcontr
  hΓ.implicitFunction hn hinv

/-- The fixed-point implicit function evaluates to the original fixed point at the base. -/
theorem ContDiffAt.fixedPointImplicitFunction_apply_self
    {T : E × F → F} {u : E × F}
    (hT : ContDiffAt 𝕜 n T u)
    (hn : n ≠ 0)
    -- kept for API symmetry with the other fixed-point lemmas; this apply-self fact
    -- holds for any base point, independent of the fixed-point equation
    (_hfp : u.2 = T u)
    (hcontr : ‖(fderiv 𝕜 T u).comp (.inr 𝕜 E F)‖ < 1) :
    hT.fixedPointImplicitFunction hn hcontr u.1 = u.2 :=
  (contDiffAt_snd.sub hT).implicitFunction_apply_self hn _

/-- The fixed-point implicit function satisfies `s(μ) = T(μ, s(μ))` in a neighborhood. -/
theorem ContDiffAt.eventually_fixedPointImplicitFunction_eq
    {T : E × F → F} {u : E × F}
    (hT : ContDiffAt 𝕜 n T u)
    (hn : n ≠ 0)
    (hfp : u.2 = T u)
    (hcontr : ‖(fderiv 𝕜 T u).comp (.inr 𝕜 E F)‖ < 1) :
    ∀ᶠ μ in 𝓝 u.1, hT.fixedPointImplicitFunction hn hcontr μ =
      T (μ, hT.fixedPointImplicitFunction hn hcontr μ) := by
  -- Mathlib gives: Γ(μ, s(μ)) = Γ(u), i.e. s(μ) - T(μ, s(μ)) = u.2 - T(u)
  -- With hfp: u.2 = T u, this becomes s(μ) - T(μ, s(μ)) = 0
  have hΓ := (contDiffAt_snd.sub hT).eventually_apply_implicitFunction hn
      (isInvertible_fderiv_sub_of_contraction (hT.differentiableAt hn) hcontr)
  -- hΓ : ∀ᶠ x, (x, s x).2 - T(x, s x) = u.2 - T u
  filter_upwards [hΓ] with μ hμ
  exact sub_eq_zero.mp (hμ.trans (sub_eq_zero.mpr hfp))

/-- The fixed-point implicit function is C^n. -/
theorem ContDiffAt.contDiffAt_fixedPointImplicitFunction
    {T : E × F → F} {u : E × F}
    (hT : ContDiffAt 𝕜 n T u)
    (hn : n ≠ 0)
    (hcontr : ‖(fderiv 𝕜 T u).comp (.inr 𝕜 E F)‖ < 1) :
    ContDiffAt 𝕜 n (hT.fixedPointImplicitFunction hn hcontr) u.1 :=
  (contDiffAt_snd.sub hT).contDiffAt_implicitFunction hn _

/-- Local uniqueness of the fixed-point implicit function: Near `u`, any point `(μ, y)` with
`y = T(μ, y)` must have `y = s(μ)`. -/
theorem ContDiffAt.eventually_eq_fixedPointImplicitFunction
    {T : E × F → F} {u : E × F}
    (hT : ContDiffAt 𝕜 n T u)
    (hn : n ≠ 0)
    (hfp : u.2 = T u)
    (hcontr : ‖(fderiv 𝕜 T u).comp (.inr 𝕜 E F)‖ < 1) :
    ∀ᶠ v in 𝓝 u,
      v.2 = T v ↔ hT.fixedPointImplicitFunction hn hcontr v.1 = v.2 := by
  -- Mathlib gives: Γ(v) = Γ(u) ↔ s(v.1) = v.2
  have hΓ := (contDiffAt_snd.sub hT).eventually_apply_eq_iff_implicitFunction hn
      (isInvertible_fderiv_sub_of_contraction (hT.differentiableAt hn) hcontr)
  -- hΓ : ∀ᶠ v, v.2 - T v = u.2 - T u ↔ s(v.1) = v.2
  have hzero : u.2 - T u = 0 := sub_eq_zero.mpr hfp
  filter_upwards [hΓ] with v hv
  constructor
  · intro h; exact hv.mp ((sub_eq_zero.mpr h).trans hzero.symm)
  · intro h; exact sub_eq_zero.mp ((hv.mpr h).trans hzero)

/-- **Derivative formula for the fixed-point implicit function.** If `s(μ) = T(μ, s(μ))` is the
implicit function from the contraction fixed-point theorem, then `D s(μ₀) = (I - D_F T)⁻¹ ∘ D_μ T`,
where all derivatives are evaluated at `(μ₀, F₀)`. -/
theorem ContDiffAt.hasStrictFDerivAt_fixedPointImplicitFunction
    {T : E × F → F} {u : E × F}
    (hT : ContDiffAt 𝕜 n T u)
    (hn : n ≠ 0)
    (hcontr : ‖(fderiv 𝕜 T u).comp (.inr 𝕜 E F)‖ < 1) :
    HasStrictFDerivAt (hT.fixedPointImplicitFunction hn hcontr)
      ((ContinuousLinearMap.id 𝕜 F - (fderiv 𝕜 T u).comp (.inr 𝕜 E F)).inverse.comp
        ((fderiv 𝕜 T u).comp (.inl 𝕜 E F))) u.1 := by
  -- Mathlib gives: Ds = -(D_F Γ)⁻¹ ∘ D_μ Γ for Γ(μ,F) = F - T(μ,F)
  -- D_F Γ = I - D_F T, D_μ Γ = -D_μ T, so the double negative cancels
  set Γ : E × F → F := fun p => p.2 - T p
  set hΓ : ContDiffAt 𝕜 n Γ u := contDiffAt_snd.sub hT
  set hinv := isInvertible_fderiv_sub_of_contraction (hT.differentiableAt hn) hcontr
  -- Get Mathlib's formula
  have hmathlib := hΓ.hasStrictFDerivAt_implicitFunction hn hinv
  -- Show the two derivative expressions are equal
  -- fderiv Γ u = snd - fderiv T u (proven in isInvertible_fderiv_sub_of_contraction)
  have hΓ_deriv : fderiv 𝕜 Γ u = .snd 𝕜 E F - fderiv 𝕜 T u :=
    (hasFDerivAt_snd.sub (hT.differentiableAt hn).hasFDerivAt).fderiv
  -- Partial derivatives:
  -- D_F Γ = (snd - fderiv T u) ∘ inr = id - D_F T
  have h_dF : fderiv 𝕜 Γ u ∘L .inr 𝕜 E F = .id 𝕜 F - (fderiv 𝕜 T u).comp (.inr 𝕜 E F) := by
    rw [hΓ_deriv, sub_comp, snd_comp_inr]
  -- D_μ Γ = (snd - fderiv T u) ∘ inl = 0 - D_μ T = -D_μ T
  have h_dE : fderiv 𝕜 Γ u ∘L .inl 𝕜 E F = -(fderiv 𝕜 T u).comp (.inl 𝕜 E F) := by
    rw [hΓ_deriv, sub_comp, snd_comp_inl, zero_sub]
  -- Rewrite Mathlib's formula using these identities
  rw [h_dF, h_dE] at hmathlib
  -- -(id - D_F T)⁻¹ ∘ (-D_μ T) = (id - D_F T)⁻¹ ∘ D_μ T
  rwa [comp_neg, neg_neg] at hmathlib

end FixedPointIFT

/-! ### Coordinate specialization for `ι → ℝ` -/

section Coordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Fixed-point IFT in coordinates.** For `T : (ι → ℝ) × (ι → ℝ) → (ι → ℝ)` that is C^n at a
fixed point, if the partial Jacobian `D_F T` has operator norm `< 1`, then the fixed-point map
`μ ↦ s(μ)` is C^n with derivative `(I - D_F T)⁻¹ ∘ D_μ T`.

This is the same as `fixedPointImplicitFunction` but with all type parameters set to `ι → ℝ`,
eliminating Banach-space ceremony for coordinate-based applications. -/
noncomputable def ContDiffAt.fixedPointCoord
    {n : WithTop ℕ∞}
    {T : (ι → ℝ) × (ι → ℝ) → ι → ℝ}
    {u : (ι → ℝ) × (ι → ℝ)}
    (hT : ContDiffAt ℝ n T u)
    (hn : n ≠ 0)
    (hcontr : ‖(fderiv ℝ T u).comp (.inr ℝ (ι → ℝ) (ι → ℝ))‖ < 1) :
    (ι → ℝ) → ι → ℝ :=
  hT.fixedPointImplicitFunction hn hcontr

omit [DecidableEq ι] in
/-- The coordinate fixed-point implicit function is `C^n`. -/
theorem ContDiffAt.contDiffAt_fixedPointCoord
    {n : WithTop ℕ∞}
    {T : (ι → ℝ) × (ι → ℝ) → ι → ℝ}
    {u : (ι → ℝ) × (ι → ℝ)}
    (hT : ContDiffAt ℝ n T u)
    (hn : n ≠ 0)
    (hcontr : ‖(fderiv ℝ T u).comp (.inr ℝ (ι → ℝ) (ι → ℝ))‖ < 1) :
    ContDiffAt ℝ n (hT.fixedPointCoord hn hcontr) u.1 :=
  hT.contDiffAt_fixedPointImplicitFunction hn hcontr

omit [DecidableEq ι] in
/-- Derivative formula for the coordinate fixed-point implicit function:
`D s(μ₀) = (I - D_F T)⁻¹ ∘ D_μ T`. -/
theorem ContDiffAt.hasStrictFDerivAt_fixedPointCoord
    {n : WithTop ℕ∞}
    {T : (ι → ℝ) × (ι → ℝ) → ι → ℝ}
    {u : (ι → ℝ) × (ι → ℝ)}
    (hT : ContDiffAt ℝ n T u)
    (hn : n ≠ 0)
    (hcontr : ‖(fderiv ℝ T u).comp (.inr ℝ (ι → ℝ) (ι → ℝ))‖ < 1) :
    HasStrictFDerivAt (hT.fixedPointCoord hn hcontr)
      ((ContinuousLinearMap.id ℝ (ι → ℝ) -
        (fderiv ℝ T u).comp (.inr ℝ (ι → ℝ) (ι → ℝ))).inverse.comp
        ((fderiv ℝ T u).comp (.inl ℝ (ι → ℝ) (ι → ℝ)))) u.1 :=
  hT.hasStrictFDerivAt_fixedPointImplicitFunction hn hcontr

end Coordinates
