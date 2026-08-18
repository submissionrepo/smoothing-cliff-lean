/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Topology

/-!
# Closed-form risk utility families

Standard one-dimensional real-valued utility families used in risk and intertemporal-choice models:
**constant absolute risk aversion** (CARA), **constant relative risk aversion** (CRRA), and
logarithmic utility. Each carries its defining parameters, the closed-form utility, monotonicity,
concavity, and the relevant Arrow–Pratt risk-aversion measure (Pratt 1964; Arrow 1971).

## Main definitions

* `ConstantAbsoluteRiskAversionUtility` — CARA (exponential) utility `u(x) = -exp(-α·x)`, `α > 0`.
* `ConstantRelativeRiskAversionUtility` — CRRA (isoelastic) utility `u(x) = x^(1-γ)/(1-γ)`,
  `γ > 0`, `γ ≠ 1`, on the positive reals.
* `LogUtility` — logarithmic utility `u(x) = log x`, the `γ = 1` case of CRRA.

## Main statements

* `ConstantAbsoluteRiskAversionUtility.continuous_u` — CARA utility is continuous on all of `ℝ`.
* `ConstantAbsoluteRiskAversionUtility.concaveOn_u`,
  `ConstantRelativeRiskAversionUtility.concaveOn_u`, `LogUtility.log_concave` — each utility is
  concave on its domain.
* `ConstantAbsoluteRiskAversionUtility.arrow_pratt` — the Arrow–Pratt measure of absolute risk
  aversion is the constant `α`.
* `ConstantRelativeRiskAversionUtility.relativeRiskAversion` — the coefficient of relative risk
  aversion is the constant `γ`.

## References

* Pratt, John W. 1964. “Risk Aversion in the Small and in the Large.” *Econometrica* 32 (1/2): 122.
  [https://doi.org/10.2307/1913738](https://doi.org/10.2307/1913738).
* Arrow, Kenneth J. 1971. *Essays in the Theory of Risk-Bearing*. Markham.

## Tags

cara, crra, isoelastic, exponential utility, logarithmic utility, risk aversion, arrow-pratt
-/

@[expose] public section

namespace Econlib.Preferences

/-- **Constant absolute risk aversion utility**, also known as exponential utility. The utility
function is `u(x) = -exp(-α·x)` where `α > 0` is the coefficient of absolute risk aversion. Its
Arrow-Pratt measure of absolute risk aversion is constant: `A(x) = α` for all `x`. -/
structure ConstantAbsoluteRiskAversionUtility where
  /-- The coefficient of absolute risk aversion. -/
  α : ℝ
  /-- Positivity of the risk aversion coefficient. -/
  α_pos : 0 < α

namespace ConstantAbsoluteRiskAversionUtility

/-- The utility function. -/
noncomputable def u (c : ConstantAbsoluteRiskAversionUtility) (x : ℝ) : ℝ :=
  -Real.exp (-c.α * x)

variable (c : ConstantAbsoluteRiskAversionUtility)

@[simp] lemma u_def (x : ℝ) :
    c.u x = -Real.exp (-c.α * x) := rfl

/-- CARA utility `u(x) = -exp(-α·x)` is continuous on all of `ℝ`. -/
lemma continuous_u : Continuous c.u := by
  unfold ConstantAbsoluteRiskAversionUtility.u
  fun_prop

/-- CARA utility is strictly increasing. -/
lemma u_strictMono : StrictMono c.u := by
  intro x y hxy
  unfold u
  apply neg_lt_neg
  simp only [neg_mul, Real.exp_lt_exp, neg_lt_neg_iff]
  exact (mul_lt_mul_iff_of_pos_left c.α_pos).mpr hxy

/-- The marginal utility of CARA utility: `u'(x) = α·exp(-α·x)`. -/
lemma hasDerivAt_u (x : ℝ) :
    HasDerivAt c.u (c.α * Real.exp (-c.α * x)) x := by
  unfold u
  have h_lin : HasDerivAt (fun y => -c.α * y) (-c.α) x := hasDerivAt_const_mul (-c.α)
  convert (h_lin.exp).neg using 1
  ring

/-- The second derivative of CARA utility: `u''(x) = -α²·exp(-α·x)`. -/
lemma hasDerivAt_deriv_u (x : ℝ) :
    HasDerivAt (fun x' => c.α * Real.exp (-c.α * x'))
      (-(c.α ^ 2) * Real.exp (-c.α * x)) x := by
  have h_lin : HasDerivAt (fun y => -c.α * y) (-c.α) x := hasDerivAt_const_mul (-c.α)
  convert h_lin.exp.const_mul c.α using 1
  ring

/-- CARA utility is concave on all of `ℝ`. -/
lemma concaveOn_u : ConcaveOn ℝ Set.univ c.u := by
  have hderiv : deriv c.u = fun x => c.α * Real.exp (-c.α * x) :=
    funext fun x => (c.hasDerivAt_u x).deriv
  refine concaveOn_univ_of_deriv2_nonpos ?h₁ ?h₂ ?h₃
  · exact fun x => (c.hasDerivAt_u x).differentiableAt
  · rw [hderiv]
    exact fun x => (c.hasDerivAt_deriv_u x).differentiableAt
  · intro x
    simp only [Function.iterate_succ, Function.comp_apply, Function.iterate_zero, id_eq]
    rw [hderiv, (c.hasDerivAt_deriv_u x).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg _))
      (Real.exp_pos _).le

/-- The Arrow–Pratt measure of absolute risk aversion `-u''/u'` is the constant `α`. -/
lemma arrow_pratt (x : ℝ) :
    -( -(c.α ^ 2) * Real.exp (-c.α * x) ) / (c.α * Real.exp (-c.α * x)) = c.α := by
  have he : Real.exp (-c.α * x) ≠ 0 := (Real.exp_pos _).ne'
  have hc : c.α ≠ 0 := ne_of_gt c.α_pos
  have : -( -(c.α ^ 2) * Real.exp (-c.α * x) ) = c.α * (c.α * Real.exp (-c.α * x)) := by ring
  rw [this, mul_div_cancel_right₀ _ (mul_ne_zero hc he)]

end ConstantAbsoluteRiskAversionUtility

/-- **Constant relative risk aversion utility**, also called isoelastic or power utility. The
utility function is `u(x) = x^(1-γ) / (1-γ)` on the positive reals, with `γ > 0` the coefficient of
relative risk aversion and `γ ≠ 1` (the `γ = 1` case is `LogUtility`). -/
structure ConstantRelativeRiskAversionUtility where
  /-- The coefficient of relative risk aversion. -/
  γ : ℝ
  /-- Positivity of the coefficient. -/
  γ_pos : 0 < γ
  /-- The coefficient is not equal to 1; the log case is handled separately. -/
  γ_ne_one : γ ≠ 1

namespace ConstantRelativeRiskAversionUtility

/-- The utility function, defined on strictly positive reals. -/
-- `_hx` restricts the domain to `(0, ∞)`; `Real.rpow` extends to all of `ℝ` by convention.
noncomputable def u (c : ConstantRelativeRiskAversionUtility) (x : ℝ) (_hx : 0 < x) :
    ℝ :=
  x ^ (1 - c.γ) / (1 - c.γ)

variable (c : ConstantRelativeRiskAversionUtility)

@[simp] lemma u_def (x : ℝ) (hx : 0 < x) :
    c.u x hx = x ^ (1 - c.γ) / (1 - c.γ) := rfl

/-- CRRA utility is strictly increasing on the positive reals. -/
lemma u_strictMono {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x < y) :
    c.u x hx < c.u y hy := by
  unfold u
  rcases lt_trichotomy (1 - c.γ) 0 with hneg | hzero | hpos
  · have hpow : y ^ (1 - c.γ) < x ^ (1 - c.γ) := Real.rpow_lt_rpow_of_neg hx hxy hneg
    exact div_lt_div_of_neg_of_lt hneg hpow
  · exact absurd (by linarith : c.γ = 1) c.γ_ne_one
  · have hpow : x ^ (1 - c.γ) < y ^ (1 - c.γ) := Real.rpow_lt_rpow hx.le hxy hpos
    exact div_lt_div_of_pos_right hpow hpos

/-- CRRA utility is concave on the positive reals `(0, ∞)`. -/
lemma concaveOn_u :
    ConcaveOn ℝ (Set.Ioi 0) (fun x => if hx : 0 < x then c.u x hx else 0) := by
  set g := fun x : ℝ => x ^ (1 - c.γ) / (1 - c.γ) with hg_def
  have heq : Set.EqOn (fun x => if hx : 0 < x then c.u x hx else 0) g (Set.Ioi 0) :=
    fun x hx => by simp [u, dif_pos (Set.mem_Ioi.mp hx)]; rfl
  suffices ConcaveOn ℝ (Set.Ioi 0) g from this.congr heq.symm
  have h1γ : 1 - c.γ ≠ 0 := sub_ne_zero.mpr c.γ_ne_one.symm
  have hderiv : ∀ x ∈ Set.Ioi 0, HasDerivAt g (x ^ (-c.γ)) x := by
    intro x hx
    have hx' := Set.mem_Ioi.mp hx
    have hd := (Real.hasDerivAt_rpow_const (p := (1 - c.γ)) (by left; linarith))
      |>.div_const (1 - c.γ)
    convert hd using 1
    rw [mul_div_cancel_left₀ _ h1γ]
    congr 1
    ring
  have hderiv2 : ∀ x ∈ Set.Ioi 0, HasDerivAt (fun x' => x' ^ (-c.γ)) ((-c.γ) * x ^ (-c.γ - 1)) x :=
    fun x hx => Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (Set.mem_Ioi.mp hx)))
  have h_deriv_eq : ∀ y ∈ interior (Set.Ioi 0), deriv g y = y ^ (-c.γ) :=
    fun y hy => (hderiv y (interior_subset hy)).deriv
  apply concaveOn_of_deriv2_nonpos (convex_Ioi 0)
  · exact fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hderiv x (interior_subset hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    exact DifferentiableWithinAt.congr
      (hderiv2 x (interior_subset hx)).differentiableAt.differentiableWithinAt
      h_deriv_eq (h_deriv_eq x hx)
  · intro x hx
    have hx' := Set.mem_Ioi.mp (interior_subset hx)
    change deriv (deriv g) x ≤ 0
    have heq_nhds : deriv g =ᶠ[𝓝 x] fun y => y ^ (-c.γ) :=
      Filter.eventuallyEq_of_mem (isOpen_interior.mem_nhds hx) h_deriv_eq
    rw [heq_nhds.deriv_eq, (hderiv2 x (interior_subset hx)).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt c.γ_pos))
      (Real.rpow_nonneg (le_of_lt hx') _)

/-- The coefficient of relative risk aversion `-x·u''/u'` is the constant `γ`. -/
lemma relativeRiskAversion (x : ℝ) (hx : 0 < x) :
    let u' := x ^ (-c.γ)
    let u'' := -c.γ * x ^ (-c.γ - 1);
    -(x * u'') / u' = c.γ := by
  intro u' u''
  have h_pow : x * x ^ (-c.γ - 1) = x ^ (-c.γ) := by
    nth_rewrite 1 [← Real.rpow_one x]
    rw [← Real.rpow_add hx]
    ring_nf
  have h_num : -(x * (-c.γ * x ^ (-c.γ - 1))) = c.γ * (x * x ^ (-c.γ - 1)) := by ring
  rw [h_num, h_pow]
  have : x ^ (-c.γ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  rw [mul_div_cancel_right₀ c.γ this]

end ConstantRelativeRiskAversionUtility

/-- **Logarithmic utility**, the `γ = 1` case of constant relative risk aversion utility. The
utility function is `u(x) = log(x)` for `x > 0`. -/
structure LogUtility where

namespace LogUtility

/-- The utility function. -/
-- `_l` is the `LogUtility` carrier (no data; present for dot-notation uniformity).
-- `_hx` restricts the domain to `(0, ∞)`; `Real.log` handles the extension to `ℝ` by convention.
noncomputable def u (_l : LogUtility) (x : ℝ) (_hx : 0 < x) : ℝ := Real.log x

variable (l : LogUtility)

@[simp] lemma log_u_def (x : ℝ) (hx : 0 < x) : l.u x hx = Real.log x := rfl

/-- Logarithmic utility is strictly increasing on the positive reals. -/
lemma log_strictly_increasing {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x < y) :
    l.u x hx < l.u y hy := by
  dsimp [u]
  exact Real.log_lt_log hx hxy

/-- Logarithmic utility is concave on the positive reals `(0, ∞)`. -/
lemma log_concave :
    ConcaveOn ℝ (Set.Ioi 0) (fun x => if hx : 0 < x then l.u x hx else 0) := by
  have heq : Set.EqOn (fun x => if hx : 0 < x then l.u x hx else 0) Real.log
      (Set.Ioi 0) := by
    intro x hx
    simp [u, dif_pos (Set.mem_Ioi.mp hx)]
  suffices ConcaveOn ℝ (Set.Ioi 0) Real.log from this.congr heq.symm
  exact strictConcaveOn_log_Ioi.concaveOn

end LogUtility

end Econlib.Preferences
