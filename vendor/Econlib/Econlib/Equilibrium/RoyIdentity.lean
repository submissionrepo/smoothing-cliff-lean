/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.Constrained.Sensitivity
public import Mathlib

/-!
# Roy's Identity

This file states Roy's identity for a smooth Marshallian demand selection. For utility `u`, demand
selection `xstar`, prices `p`, and wealth `w`, the conclusion recovers each demand coordinate as

`xstar (p, w) l = - (∂v/∂w)⁻¹ * (∂v/∂p_l)`,

where `v q w' := u (xstar (q, w'))` is the utility of the selection. The statement is formulated
for the utility of the demand selection. The corresponding value-function statement for
`indirectUtility` is `roy_identity_indirectUtility` in `Econlib.Equilibrium.IndirectUtility`, which
adds the local hypothesis that the selection's utility agrees with the indirect-utility value.

The file also defines the parameter and constraint objects for the utility-maximization problem,
including the budget constraint, nonnegativity constraints, and their derivatives.

## Main definitions

* `obj` — the UMP objective, uncurried for the envelope theorem.
* `con` — the UMP inequality constraints (`≤ 0` convention).
* `dotL` — dot product with a fixed price vector, as a continuous linear functional on `Fin L → ℝ`.
* `objFDeriv`, `conFDeriv` — joint derivatives of the objective and constraints.

## Main statements

* `hasFDerivAt_obj`, `hasFDerivAt_budget`, `hasFDerivAt_con` — differentiability of the objective
  and constraint functions.
* `roy_identity` — Roy's identity for the utility of a smooth demand selection, given multiplier
  and active-constraint data. The value-function version for `indirectUtility` is
  `roy_identity_indirectUtility` in `Econlib.Equilibrium.IndirectUtility`.

## References

* Roy, Rene. 1947. “La Distribution Du Revenu Entre Les Divers Biens.” *Econometrica* 15 (3): 205.
  [https://doi.org/10.2307/1905479](https://doi.org/10.2307/1905479).

## Tags

roy's identity, marshallian demand, indirect utility, envelope theorem
-/

@[expose] public section

open ContinuousLinearMap Matrix Econlib.Optimization

namespace Econlib.Equilibrium.Roy

variable {L : ℕ}

/-- Parameter space for the UMP: Prices and wealth. -/
abbrev Param (L : ℕ) := (Fin L → ℝ) × ℝ

/-- Inequality-constraint index: `none` is the budget `p ⬝ᵥ x − w ≤ 0`; `some l` is the
nonnegativity constraint `−x_l ≤ 0`. -/
abbrev CIdx (L : ℕ) := Option (Fin L)

/-- The UMP objective, uncurried for the envelope theorem: It ignores the parameter. -/
def obj (u : (Fin L → ℝ) → ℝ) : (Fin L → ℝ) → Param L → ℝ := fun x _ => u x

/-- The UMP inequality constraints (`≤ 0` convention). -/
def con : CIdx L → (Fin L → ℝ) → Param L → ℝ
  | none,   x, θ => θ.1 ⬝ᵥ x - θ.2
  | some l, x, _ => - x l

/-- Dot product with a fixed vector `v`, packaged as a continuous linear functional on `Fin L → ℝ`.
Built from coordinate projections — no inner-product structure, so it lives on `Fin L → ℝ` directly
and keeps the function-space topology. -/
noncomputable def dotL (v : Fin L → ℝ) : (Fin L → ℝ) →L[ℝ] ℝ :=
  ∑ i, v i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i

@[simp] lemma dotL_apply (v y : Fin L → ℝ) : dotL v y = v ⬝ᵥ y := by
  simp [dotL, ContinuousLinearMap.sum_apply, dotProduct]

/-- Joint derivative of the UMP objective `(x, θ) ↦ u x` at the optimum: It factors through the
`x`-coordinate, so its derivative is `∇u ∘ fst`. -/
noncomputable def objFDeriv (Du : (Fin L → ℝ) →L[ℝ] ℝ) :
    ((Fin L → ℝ) × Param L) →L[ℝ] ℝ :=
  Du.comp (fst ℝ (Fin L → ℝ) (Param L))

/-- Joint derivative of the UMP inequality constraints at `(x₀, (p, w))` (the optimum). For
`some l` (nonnegativity `−x_l`) it is `−proj_l ∘ fst`, independent of the parameter. For `none`
(the budget `p ⬝ᵥ x − w`) it is `(dp, dw, dx) ↦ p ⬝ᵥ dx + dp ⬝ᵥ x₀ − dw`, the differential of the
bilinear budget form. -/
noncomputable def conFDeriv (x₀ p : Fin L → ℝ) :
    CIdx L → ((Fin L → ℝ) × Param L) →L[ℝ] ℝ
  | none =>
      (dotL p).comp (fst ℝ (Fin L → ℝ) (Param L))
        + (dotL x₀).comp ((fst ℝ (Fin L → ℝ) ℝ).comp (snd ℝ (Fin L → ℝ) (Param L)))
        - (snd ℝ (Fin L → ℝ) ℝ).comp (snd ℝ (Fin L → ℝ) (Param L))
  | some l =>
      -(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) l).comp
        (fst ℝ (Fin L → ℝ) (Param L))

/-- The UMP objective is jointly differentiable: It depends only on `x`, so its derivative is `∇u`
precomposed with the `x`-projection. -/
lemma hasFDerivAt_obj {u : (Fin L → ℝ) → ℝ} {Du : (Fin L → ℝ) →L[ℝ] ℝ} {x₀ : Fin L → ℝ}
    (hu : HasFDerivAt u Du x₀) (θ : Param L) :
    HasFDerivAt (fun pr : (Fin L → ℝ) × Param L => obj u pr.1 pr.2) (objFDeriv Du) (x₀, θ) :=
  hu.comp (x₀, θ) (hasFDerivAt_fst)

/-- The budget constraint `(x, (p, w)) ↦ p ⬝ᵥ x − w` is jointly differentiable at the optimum, with
derivative the bilinear-form differential `(dx, dp, dw) ↦ p ⬝ᵥ dx + dp ⬝ᵥ x₀ − dw`. -/
lemma hasFDerivAt_budget (x₀ p : Fin L → ℝ) (w : ℝ) :
    HasFDerivAt (fun pr : (Fin L → ℝ) × Param L => con none pr.1 pr.2)
      (conFDeriv x₀ p none) (x₀, (p, w)) := by
  have hx : ∀ i, HasFDerivAt (fun pr : (Fin L → ℝ) × Param L => pr.1 i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).comp
        (fst ℝ (Fin L → ℝ) (Param L))) (x₀, (p, w)) := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).hasFDerivAt.comp _ hasFDerivAt_fst
  have hp : ∀ i, HasFDerivAt (fun pr : (Fin L → ℝ) × Param L => pr.2.1 i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).comp
        ((fst ℝ (Fin L → ℝ) ℝ).comp (snd ℝ (Fin L → ℝ) (Param L)))) (x₀, (p, w)) := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).hasFDerivAt.comp _
      ((fst ℝ (Fin L → ℝ) ℝ).comp (snd ℝ (Fin L → ℝ) (Param L))).hasFDerivAt
  have hprod : ∀ i, HasFDerivAt (fun pr : (Fin L → ℝ) × Param L => pr.2.1 i * pr.1 i)
      (p i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).comp
          (fst ℝ (Fin L → ℝ) (Param L))
        + x₀ i • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).comp
          ((fst ℝ (Fin L → ℝ) ℝ).comp (snd ℝ (Fin L → ℝ) (Param L)))) (x₀, (p, w)) := by
    intro i
    simpa using (hp i).mul (hx i)
  have hw : HasFDerivAt (fun pr : (Fin L → ℝ) × Param L => pr.2.2)
      ((snd ℝ (Fin L → ℝ) ℝ).comp (snd ℝ (Fin L → ℝ) (Param L))) (x₀, (p, w)) :=
    hasFDerivAt_snd.comp _ hasFDerivAt_snd
  have hsum := (HasFDerivAt.sum (fun i (_ : i ∈ Finset.univ) => hprod i)).sub hw
  refine hsum.congr_fderiv ?_ |>.congr_of_eventuallyEq ?_
  · rw [conFDeriv, dotL, dotL, ContinuousLinearMap.finset_sum_comp,
      ContinuousLinearMap.finset_sum_comp, ← Finset.sum_add_distrib]
    simp only [ContinuousLinearMap.smul_comp]
  · filter_upwards with pr; simp [con, dotProduct]

/-- All UMP constraints are jointly differentiable at the optimum `(x₀, (p, w))`, with derivatives
given by `conFDeriv x₀ p`. -/
lemma hasFDerivAt_con (x₀ p : Fin L → ℝ) (w : ℝ) (i : CIdx L) :
    HasFDerivAt (fun pr : (Fin L → ℝ) × Param L => con i pr.1 pr.2)
      (conFDeriv x₀ p i) (x₀, (p, w)) := by
  cases i with
  | none => exact hasFDerivAt_budget x₀ p w
  | some l =>
      have hxl : HasFDerivAt (fun pr : (Fin L → ℝ) × Param L => pr.1 l)
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) l).comp
            (fst ℝ (Fin L → ℝ) (Param L))) (x₀, (p, w)) :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) l).hasFDerivAt.comp _
          hasFDerivAt_fst
      simpa [con, conFDeriv] using hxl.neg

/-- **Roy's Identity along the KKT path (componentwise)** (Roy 1947). At prices `p`, wealth `w`,
with `xstar` the Marshallian demand and `lam none > 0` the budget multiplier, each demand component
satisfies `x*_l(p,w) = −(∂v/∂p_l) / (∂v/∂w)`, where `v q w' := u (xstar (q, w'))` is the utility
*of the demand selection*.

This is the analytic core: It differentiates `u ∘ xstar`, which coincides with the indirect-utility
value function only when `xstar` is a budget-feasible maximizer in a neighborhood of `(p, w)`. For
the statement in terms of `indirectUtility` itself, see `roy_identity_indirectUtility`.

The hypotheses are: `hu` (differentiability of `u` at the optimum), `hxs` (smooth demand
selection), `h_stat` (Lagrangian stationarity `∇u = lam none • p − Σ_l lam (some l) • e_l`), and
`h_bind` (complementary slackness / active-set persistence). -/
theorem roy_identity
    (u : (Fin L → ℝ) → ℝ)
    (xstar : Param L → (Fin L → ℝ)) (lam : CIdx L → ℝ)
    (p : Fin L → ℝ) (w : ℝ)
    (hlamB : 0 < lam none)
    (Du : (Fin L → ℝ) →L[ℝ] ℝ)
    (hu : HasFDerivAt u Du (xstar (p, w)))
    (Dxs : Param L →L[ℝ] (Fin L → ℝ))
    (hxs : HasFDerivAt xstar Dxs (p, w))
    (h_stat : (objFDeriv Du).comp (inl ℝ (Fin L → ℝ) (Param L))
      = ∑ i, lam i • (conFDeriv (xstar (p, w)) p i).comp (inl ℝ (Fin L → ℝ) (Param L)))
    (h_bind : ∀ i, lam i = 0 ∨
      (∀ᶠ θ in nhds (p, w), con i (xstar θ) θ = 0)) :
    ∀ l, xstar (p, w) l
      = - (deriv (fun w' => u (xstar (p, w'))) w)⁻¹ *
          (fderiv ℝ (fun q => u (xstar (q, w))) p (Pi.single l 1)) := by
  set x₀ := xstar (p, w) with hx₀
  set Df := objFDeriv Du with hDf
  set Dg := conFDeriv x₀ p with hDg
  have hf : HasFDerivAt (fun pr : (Fin L → ℝ) × Param L => obj u pr.1 pr.2) Df (x₀, (p, w)) :=
    hasFDerivAt_obj hu (p, w)
  have hg : ∀ i, HasFDerivAt (fun pr : (Fin L → ℝ) × Param L => con i pr.1 pr.2) (Dg i)
      (x₀, (p, w)) := fun i => hasFDerivAt_con x₀ p w i
  have hV := hasFDerivAt_constrainedValue (obj u) con xstar lam (p, w) Df Dg Dxs hf hg hxs
    h_stat h_bind
  set D := Df.comp (inr ℝ (Fin L → ℝ) (Param L))
    - ∑ i, lam i • (Dg i).comp (inr ℝ (Fin L → ℝ) (Param L)) with hD
  -- The objective ignores `θ` and the nonnegativity constraints ignore `θ`, so only the budget
  -- constraint contributes to the parameter-partial: `D (dp, dw) = −lam none • (dp ⬝ᵥ x₀ − dw)`.
  have hDeval : ∀ dp : Fin L → ℝ, ∀ dw : ℝ, D (dp, dw) = - lam none * (dp ⬝ᵥ x₀ - dw) := by
    intro dp dw
    simp only [hD, hDf, hDg, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, objFDeriv, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd', ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, Fintype.sum_option, conFDeriv,
      ContinuousLinearMap.neg_apply, dotL_apply, ContinuousLinearMap.add_apply,
      smul_eq_mul, map_zero, mul_zero, neg_zero, Finset.sum_const_zero,
      dotProduct_comm dp x₀]
    ring
  have hDw : D (0, 1) = lam none := by
    rw [hDeval 0 1, zero_dotProduct, zero_sub, mul_neg, mul_one, neg_neg]
  have hDp : ∀ l, D (Pi.single l 1, 0) = - lam none * x₀ l := by
    intro l
    rw [hDeval (Pi.single l 1) 0, single_dotProduct, one_mul, sub_zero]
  -- Compose the envelope derivative with the wealth and price curves to extract `∂v/∂w` and
  -- `∂v/∂p_l`, then divide.
  have hwealth : HasDerivAt (fun w' => u (xstar (p, w'))) (lam none) w := by
    have hcurve : HasFDerivAt (fun w' : ℝ => ((p, w') : Param L))
        ((inr ℝ (Fin L → ℝ) ℝ)) w := by
      simpa using (hasFDerivAt_const p w).prodMk (hasFDerivAt_id w)
    have hcomp := hV.comp_hasDerivAt w (by simpa using hcurve.hasDerivAt)
    rw [hDw] at hcomp
    simpa [Function.comp, obj] using hcomp
  have hprice : ∀ l, fderiv ℝ (fun q => u (xstar (q, w))) p (Pi.single l 1)
      = - lam none * x₀ l := by
    intro l
    have hcurve : HasFDerivAt (fun q : Fin L → ℝ => ((q, w) : Param L))
        (inl ℝ (Fin L → ℝ) ℝ) p := by
      simpa using (hasFDerivAt_id p).prodMk (hasFDerivAt_const w p)
    have hcomp : HasFDerivAt (fun q : Fin L → ℝ => u (xstar (q, w)))
        (D.comp (inl ℝ (Fin L → ℝ) ℝ)) p := by
      have := hV.comp p hcurve
      simpa [Function.comp, obj] using this
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, hDp l]
  intro l
  rw [hprice l, hwealth.deriv]
  field_simp

end Econlib.Equilibrium.Roy
