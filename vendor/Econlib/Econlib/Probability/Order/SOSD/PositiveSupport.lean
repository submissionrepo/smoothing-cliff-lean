/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Utility.RiskFamilies
public import Econlib.Probability.Order.SOSD.CompactSupport

/-!
# SOSD for `log` and CRRA agents under positive bounded support

The canonical risk-averse utilities `Real.log` and CRRA `x ↦ x^(1-γ)/(1-γ)` are superlinear in
`|·|` as `x ↓ 0` and are not real-valued on all of `ℝ`, so a global-domain SOSD theorem does not
apply to them directly.

This file recovers those two cases under the natural domain restriction that makes them well-posed:
The distributions are supported on a positive bounded interval `[a, b]` with `0 < a`. On `[a, b]`
both `log` and CRRA are concave, monotone, continuous, and differentiable with bounded derivative,
so `CDF.SOSD.expect_concave_compactSupport_of_hasDerivAt` — which sees the support only and needs
no mean or linear-growth hypotheses — applies directly.

## Main statements

* `CDF.SOSD.expect_log` — SOSD implies the `log`-expectation ordering for positively supported laws.
* `CDF.SOSD.expect_crra` — SOSD implies the CRRA-expectation ordering for positively supported laws.
-/

@[expose] public section

open MeasureTheory Set Filter Function
open scoped Topology Real

namespace Econlib.Probability

open Econlib.Preferences

/-! ## SOSD for `Real.log` -/

/-- A positive bounded support forces a nondegenerate interval: If `b ≤ a`, the density
(nonnegative, supported on `Icc a b`) would have total interval mass `≤ 0`, contradicting the unit
mass `∫ s in a..b, density = 1`. -/
lemma contDist_lt_of_support (d : ContDist) {a b : ℝ}
    (h_supp : ∀ x ∉ Icc a b, d.density x = 0) : a < b := by
  by_contra hba
  rw [not_lt] at hba
  have hmass : ∫ s in a..b, d.density s = 1 := contDist_mass_intervalIntegral d h_supp
  have hle : ∫ s in a..b, d.density s ≤ 0 := by
    rw [intervalIntegral.integral_of_ge hba]
    have : 0 ≤ ∫ s in Ioc b a, d.density s :=
      setIntegral_nonneg measurableSet_Ioc (fun x _ => d.nonneg x)
    linarith
  rw [hmass] at hle
  norm_num at hle

/-- **SOSD for log utility under positive bounded support.** If `dF` second-order stochastically
dominates `dG`, and both densities are supported on a positive bounded interval `[a, b]` with
`0 < a`, then the log-expected utility is ordered: `E_G[log] ≤ E_F[log]`.

On `[a, b] ⊆ (0, ∞)` the log utility is concave, monotone, continuous, and differentiable with
derivative `x⁻¹` bounded between `b⁻¹` and `a⁻¹`, so the ordering follows directly from
`CDF.SOSD.expect_concave_compactSupport_of_hasDerivAt`. The nondegeneracy `a < b` is derived from
the unit mass of the densities on the support. -/
theorem CDF.SOSD.expect_log (dF dG : ContDist) {a b : ℝ} (ha : 0 < a)
    (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (h_suppF : ∀ x ∉ Icc a b, dF.density x = 0)
    (h_suppG : ∀ x ∉ Icc a b, dG.density x = 0)
    (h_intF : Integrable (fun x => dF.density x * Real.log x))
    (h_intG : Integrable (fun x => dG.density x * Real.log x)) :
    dG.expect Real.log ≤ dF.expect Real.log := by
  have hab : a < b := contDist_lt_of_support dF h_suppF
  -- `Icc a b ⊆ (0, ∞)` since `a > 0`; log is concave/monotone/continuous there.
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hsub' : Icc a b ⊆ {(0 : ℝ)}ᶜ := fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1)
  refine CDF.SOSD.expect_concave_compactSupport_of_hasDerivAt dF dG Real.log (fun x => x⁻¹) hab
    h_sosd h_suppF h_suppG
    (strictConcaveOn_log_Ioi.concaveOn.subset hsub (convex_Icc a b))
    (Real.strictMonoOn_log.monotoneOn.mono hsub)
    (Real.continuousOn_log.mono hsub')
    (fun x hx => Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le ha hx.1.le)))
    ?_ ?_ h_intF h_intG
  · refine ⟨0, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact inv_nonneg.mpr (lt_of_lt_of_le ha hx.1.le).le
  · refine ⟨a⁻¹, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact (inv_le_inv₀ (lt_of_lt_of_le ha hx.1.le) ha).mpr hx.1.le

/-! ## SOSD for CRRA utility -/

/-- The CRRA utility piece `y ↦ y^(1-γ)/(1-γ)` has derivative `x^(-γ)` at any `x > 0`. -/
lemma crra_hasDerivAt {γ x : ℝ} (hγ1 : γ ≠ 1) (hx : 0 < x) :
    HasDerivAt (fun y => y ^ (1 - γ) / (1 - γ)) (x ^ (-γ)) x := by
  have h1γ : 1 - γ ≠ 0 := sub_ne_zero.mpr (fun h => hγ1 h.symm)
  have hd := (Real.hasDerivAt_rpow_const (x := x) (p := 1 - γ) (Or.inl hx.ne')).div_const (1 - γ)
  convert hd using 1
  rw [show (1 : ℝ) - γ - 1 = -γ by ring]
  field_simp

/-- **SOSD for CRRA utility under positive bounded support.** If `dF` second-order stochastically
dominates `dG`, and both densities are supported on a positive bounded interval `[a, b]` with
`0 < a`, then the CRRA-expected utility is ordered: `E_G[u] ≤ E_F[u]` for `u x = x^(1-γ)/(1-γ)`
with `γ = c.γ` from `c : ConstantRelativeRiskAversionUtility`. This integrand coincides with
`c.u x` for `x > 0`, hence on the positive support `[a, b]`.

On `[a, b] ⊆ (0, ∞)` the CRRA utility is concave, monotone, continuous, and differentiable with
derivative `x^(-γ)` bounded between `b^(-γ)` and `a^(-γ)`, so the ordering follows directly from
`CDF.SOSD.expect_concave_compactSupport_of_hasDerivAt`. The nondegeneracy `a < b` is derived from
the unit mass of the densities on the support. -/
theorem CDF.SOSD.expect_crra (dF dG : ContDist) (c : ConstantRelativeRiskAversionUtility)
    {a b : ℝ} (ha : 0 < a)
    (h_sosd : CDF.SOSD dF.cdf dG.cdf)
    (h_suppF : ∀ x ∉ Icc a b, dF.density x = 0)
    (h_suppG : ∀ x ∉ Icc a b, dG.density x = 0)
    (h_intF : Integrable (fun x => dF.density x * (x ^ (1 - c.γ) / (1 - c.γ))))
    (h_intG : Integrable (fun x => dG.density x * (x ^ (1 - c.γ) / (1 - c.γ)))) :
    dG.expect (fun x => x ^ (1 - c.γ) / (1 - c.γ)) ≤
      dF.expect (fun x => x ^ (1 - c.γ) / (1 - c.γ)) := by
  have hab : a < b := contDist_lt_of_support dF h_suppF
  set u : ℝ → ℝ := fun x => x ^ (1 - c.γ) / (1 - c.γ) with hu_def
  set u' : ℝ → ℝ := fun x => x ^ (-c.γ) with hu'_def
  have hf'_deriv : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x :=
    fun x hx => crra_hasDerivAt c.γ_ne_one (lt_of_lt_of_le ha hx.1.le)
  have hf'_diff : DifferentiableOn ℝ u (Ioo a b) :=
    fun x hx => (hf'_deriv x hx).differentiableAt.differentiableWithinAt
  -- `u` is continuous on `[a, b]`: positivity of `a` keeps `x ≠ 0` throughout.
  have hu_cont : ContinuousOn u (Icc a b) := by
    refine (continuousOn_id.rpow_const ?_).div_const _
    intro x hx
    left
    exact ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hint : interior (Icc a b) = Ioo a b := interior_Icc
  have hderiv_eq : ∀ x ∈ Ioo a b, deriv u x = u' x := fun x hx => (hf'_deriv x hx).deriv
  -- `u' x = x^(-γ)` is antitone on `(a, b)` (positive base, nonpositive exponent),
  -- so `u` is concave on `[a, b]`.
  have h_anti : AntitoneOn (deriv u) (Ioo a b) := by
    intro x hx y hy hxy
    rw [hderiv_eq x hx, hderiv_eq y hy]
    exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le ha hx.1.le) hxy (neg_nonpos.mpr c.γ_pos.le)
  have hu_conc : ConcaveOn ℝ (Icc a b) u :=
    AntitoneOn.concaveOn_of_deriv (convex_Icc a b) hu_cont (hint ▸ hf'_diff) (hint ▸ h_anti)
  have hu_mono : MonotoneOn u (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) hu_cont (hint ▸ hf'_diff) ?_
    rw [hint]
    intro x hx
    rw [hderiv_eq x hx]
    exact (Real.rpow_pos_of_pos (lt_of_lt_of_le ha hx.1.le) _).le
  refine CDF.SOSD.expect_concave_compactSupport_of_hasDerivAt dF dG u u' hab
    h_sosd h_suppF h_suppG hu_conc hu_mono hu_cont hf'_deriv ?_ ?_ h_intF h_intG
  · refine ⟨0, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact (Real.rpow_pos_of_pos (lt_of_lt_of_le ha hx.1.le) _).le
  · refine ⟨a ^ (-c.γ), ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact Real.rpow_le_rpow_of_nonpos ha hx.1.le (neg_nonpos.mpr c.γ_pos.le)

end Econlib.Probability
