/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Econlib.Math.Analysis.ConvexRightDeriv
public import Econlib.Math.MeasureTheory.StieltjesIBP
public import Econlib.Math.MeasureTheory.TriangleFubini
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Integral representation of convex functions

A convex function `φ` on `[a, b]` whose right derivative is bounded on `(a, b)` and which is
continuous on `[a, b]` admits the representation

`φ(t) = φ(a) + c · (t - a) + ∫ s in Ioc a t, (t - s) ∂μ(s)`

where `c` is the right derivative of `φ` at `a⁺` and `μ` is the positive second-derivative
Stieltjes measure of `φ` (the Stieltjes measure of the monotone right derivative).

## Main definitions

* `MeasureTheory.convexSecondDerivMeasure` — the Stieltjes measure `μ_φ''` of the extended right
  derivative.
* `MeasureTheory.convexRightDerivStieltjes` — the Stieltjes function of the extended right
  derivative.

## Main statements

* `MeasureTheory.convex_integral_repr` — the integral representation over `Ioc a t`.
* `MeasureTheory.convex_integral_repr_max` — the representation in `max (t - s) 0` form over
  `Ioc a b`.
* `MeasureTheory.fubini_triangle_lebesgue_stieltjes` — the Fubini swap
  `∫_a^t μ((a, s]) ds = ∫ s in Ioc a t, (t - s) ∂μ(s)`.

## Notes

This representation drives the SOSD ⇒ convex-order equivalence in `Econlib.Probability.Order.SOSD`.

## Tags

convex, integral representation, stieltjes measure, right derivative
-/

@[expose] public section

open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology ENNReal

variable {φ : ℝ → ℝ} {a b : ℝ}

namespace MeasureTheory

/-! ### The second-derivative measure -/

/-- The Stieltjes measure of the extended right derivative of a convex function. This is the
"second-derivative measure" `μ_φ''`. -/
noncomputable def convexSecondDerivMeasure (hφ : ConvexOn ℝ (Icc a b) φ)
    (hab : a < b)
    (hbb : BddBelow ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b))
    (hba : BddAbove ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b)) : Measure ℝ :=
  (hφ.rightDerivExtend_monotone hab hbb hba).stieltjesMeasure

/-- The Stieltjes function of the extended right derivative. -/
noncomputable def convexRightDerivStieltjes (hφ : ConvexOn ℝ (Icc a b) φ)
    (hab : a < b)
    (hbb : BddBelow ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b))
    (hba : BddAbove ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b)) : StieltjesFunction ℝ :=
  (hφ.rightDerivExtend_monotone hab hbb hba).stieltjes

/-! ### The Fubini triangle swap -/

/-- **Fubini triangle swap** (Lebesgue × Stieltjes):

`∫_a^t μ((a, s]) ds = ∫ s in Ioc a t, (t - s) ∂μ(s)`

where the left side is a Lebesgue integral of the measure function `s ↦ μ((a, s])`, and the right
side is a Stieltjes integral of `s ↦ (t - s)`.

This swaps integration order on the triangle `{(u, s) : a < s ≤ u, a < u ≤ t}`:

* Outer Lebesgue in `u`, inner Stieltjes in `s` → left side
* Outer Stieltjes in `s`, inner Lebesgue in `u` → right side

This is the weight-`1` case of the general Lebesgue × Stieltjes triangle swap
`MeasureTheory.integral_triangle_swap_stieltjes`: The inner Lebesgue integral `∫ u in s..t, 1`
collapses to the interval length `t - s`. -/
theorem fubini_triangle_lebesgue_stieltjes {g : ℝ → ℝ} (hg : Monotone g) (hat : a < t) :
    let μ := hg.stieltjesMeasure
    let g_sf := hg.stieltjes
    ∫ u in a..t, (g_sf u - g_sf a) =
    ∫ s in Ioc a t, (t - s) ∂μ := by
  intro μ g_sf
  simpa using integral_triangle_swap_stieltjes hg hat
    (_root_.intervalIntegrable_const (c := (1 : ℝ)))

/-! ### The integral representation theorem -/

/-- **Integral representation of convex functions.**

For `φ` convex and continuous on `[a, b]` with right derivative bounded on `(a, b)` (hypotheses
`hbb`, `hba`), and `t ∈ [a, b]`,

`φ(t) = φ(a) + c · (t - a) + ∫ s in Ioc a t, (t - s) ∂μ(s)`

where `c = sInf {rightDeriv(x) : x ∈ (a, b)}` (the right derivative at `a⁺`) and `μ` is the
second-derivative Stieltjes measure. -/
theorem convex_integral_repr (hφ : ConvexOn ℝ (Icc a b) φ) (hab : a < b)
    (hcont : ContinuousOn φ (Icc a b))
    (hbb : BddBelow ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b))
    (hba : BddAbove ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b))
    {t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    let μ := convexSecondDerivMeasure hφ hab hbb hba
    let c := sInf ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b)
    φ t = φ a + c * (t - a) + ∫ s in Ioc a t, (t - s) ∂μ := by
  intro μ c
  -- Handle the degenerate case a = t
  rcases eq_or_lt_of_le hat with rfl | hat_lt
  · simp
  -- FTC gives φ(t) - φ(a) = ∫_a^t rightDeriv(s) ds
  have h_ftc : ∫ s in a..t, derivWithin φ (Ioi s) s = φ t - φ a :=
    hφ.ftc_rightDeriv hab hcont hbb hba hat htb
  -- The Stieltjes function g_sf of rightDerivExtend satisfies
  -- g_sf(s) = rightDerivExtend(s) on (a, b) (right-continuity of right-derivative)
  -- and g_sf(a) = c = sInf(rightDeriv '' (a,b)) (right limit at a)
  set g := hφ.rightDerivExtend hab
  set hg_mono := hφ.rightDerivExtend_monotone hab hbb hba
  set g_sf := hg_mono.stieltjes
  -- Key bridge: g_sf = rightLim(g) agrees with g a.e. (Lebesgue) on (a, t).
  -- Monotone functions have at most countably many discontinuities; at continuity
  -- points, rightLim = value. On (a,b), g = derivWithin φ (Ioi ·) ·.
  have h_gsf_eq_ae : ∀ᵐ s, s ∈ Ioo a t →
      (g_sf : ℝ → ℝ) s = derivWithin φ (Ioi s) s := by
    -- The discontinuity set of the monotone function g is countable, hence measure zero.
    have hD := hg_mono.countable_not_continuousAt
    have hD_zero : volume {x | ¬ContinuousAt g x} = 0 := hD.measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hD_zero] with s hs_cont hs_mem
    -- At a continuity point, rightLim g = g
    have hcont : ContinuousAt g s := by simpa using hs_cont
    rw [show (g_sf : ℝ → ℝ) s = rightLim g s from hg_mono.stieltjesFunction_eq s]
    rw [hcont.continuousWithinAt.rightLim_eq]
    -- On (a, b), g = derivWithin by definition of rightDerivExtend
    exact hφ.rightDerivExtend_eq_of_mem_Ioo hab ⟨hs_mem.1, lt_of_lt_of_le hs_mem.2 htb⟩
  have h_gsf_a : (g_sf : ℝ → ℝ) a = c := by
    -- g_sf(a) = rightLim(g)(a) = sInf(g '' Ioi a) = c
    have h_sf_eq : (g_sf : ℝ → ℝ) a = rightLim g a := hg_mono.stieltjesFunction_eq a
    have h_nhds : nhdsWithin a (Ioi a) ≠ ⊥ := (nhdsWithin_Ioi_neBot (le_refl a)).ne
    have h_rl_eq : rightLim g a = sInf (g '' Ioi a) := hg_mono.rightLim_eq_sInf h_nhds
    rw [h_sf_eq, h_rl_eq]
    -- g(a) = c by rightDerivExtend_of_le_left
    have hga : g a = c := hφ.rightDerivExtend_of_le_left hab le_rfl
    -- Show sInf(g '' Ioi a) = c
    apply le_antisymm
    · -- sInf(g '' Ioi a) ≤ c: derivWithin '' Ioo a b ⊆ g '' Ioi a
      apply csInf_le_csInf
      · -- g '' Ioi a is bdd below: g(x) ≥ g(a) = c for x > a
        exact ⟨c, fun y hy => by
          obtain ⟨x, hx, rfl⟩ := hy
          rw [← hga]; exact hg_mono (le_of_lt hx)⟩
      · exact (nonempty_Ioo.mpr hab).image _
      · -- derivWithin '' Ioo a b ⊆ g '' Ioi a
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact ⟨x, hx.1, hφ.rightDerivExtend_eq_of_mem_Ioo hab hx⟩
    · -- c ≤ sInf(g '' Ioi a): g(x) ≥ g(a) = c for x > a by monotonicity
      apply le_csInf (nonempty_Ioi.image g)
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [← hga]; exact hg_mono (le_of_lt hx)
  -- The integrands agree a.e. on (a, t): derivWithin(s) = c + (g_sf(s) - g_sf(a)),
  -- so the FTC integral splits along this a.e. decomposition.
  have h_gsf_int : IntervalIntegrable (fun s => (g_sf : ℝ → ℝ) s - g_sf a) volume a t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hat_lt.le]
    have hmono : MonotoneOn (fun s => (g_sf : ℝ → ℝ) s - g_sf a) (Icc a t) :=
      fun x hx y hy hxy => sub_le_sub_right (g_sf.mono hxy) _
    exact (hmono.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have h_split : ∫ s in a..t, derivWithin φ (Ioi s) s =
      c * (t - a) + ∫ s in a..t, (g_sf s - g_sf a) := by
    -- The integrands agree a.e. on (a, t)
    have h_ae_eq : ∀ᵐ s, s ∈ Ioc a t →
        derivWithin φ (Ioi s) s = c + (g_sf s - g_sf a) := by
      filter_upwards [h_gsf_eq_ae, compl_mem_ae_iff.mpr (measure_singleton t)] with s h_eq hst hs
      have hsoo : s ∈ Ioo a t :=
        ⟨hs.1, lt_of_le_of_ne hs.2 (fun heq => hst (mem_singleton_iff.mpr heq))⟩
      rw [← h_eq hsoo, h_gsf_a]; ring
    rw [integral_of_le hat_lt.le, setIntegral_congr_ae measurableSet_Ioc h_ae_eq,
        ← integral_of_le hat_lt.le]
    rw [intervalIntegral.integral_add intervalIntegral.intervalIntegrable_const h_gsf_int]
    simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  -- Fubini triangle swap: μ = stieltjesMeasure hg_mono and g_sf = stieltjes hg_mono.
  have h_fubini : ∫ u in a..t, (g_sf u - g_sf a) = ∫ s in Ioc a t, (t - s) ∂μ :=
    fubini_triangle_lebesgue_stieltjes hg_mono hat_lt
  linarith [h_ftc, h_split, h_fubini]

/-! ### The `max(t-s, 0)` form for use with call payoffs -/

/-- **Integral representation of convex functions**, in `max (t - s) 0` form over `[a, b]`.

Under the same hypotheses as `convex_integral_repr` (φ convex and continuous on `[a, b]`, right
derivative bounded on `(a, b)`), for `t ∈ [a, b]`,

`φ(t) = φ(a) + c · (t - a) + ∫ s in Ioc a b, max (t - s) 0 ∂μ(s)`.

Since `max (t - s) 0 = t - s` for `s ≤ t` and `0` for `s > t`, the integral over `Ioc a b` reduces
to the integral over `Ioc a t`. This form is usable with
`expect_callPayoff_le_of_sosd_of_mean_eq`. -/
theorem convex_integral_repr_max (hφ : ConvexOn ℝ (Icc a b) φ) (hab : a < b)
    (hcont : ContinuousOn φ (Icc a b))
    (hbb : BddBelow ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b))
    (hba : BddAbove ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b))
    {t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    let μ := convexSecondDerivMeasure hφ hab hbb hba
    let c := sInf ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b)
    φ t = φ a + c * (t - a) + ∫ s in Ioc a b, max (t - s) 0 ∂μ := by
  -- The integral over Ioc a b of max(t-s, 0) splits into:
  -- Ioc a t (where max = t - s) + Ioc t b (where max = 0).
  -- The second integral is 0, so this equals the Ioc a t integral.
  intro μ c
  -- Reduce to convex_integral_repr by showing the integrals match
  have h_repr := convex_integral_repr hφ hab hcont hbb hba hat htb
  simp only at h_repr
  -- It suffices to show the max integral equals the Ioc a t integral
  suffices h_eq : ∫ s in Ioc a b, max (t - s) 0 ∂μ = ∫ s in Ioc a t, (t - s) ∂μ by
    rw [h_eq]; exact h_repr
  -- Split Ioc a b = Ioc a t ∪ Ioc t b
  rw [show Ioc a b = Ioc a t ∪ Ioc t b from (Ioc_union_Ioc_eq_Ioc hat htb).symm]
  -- Finiteness of the Stieltjes measure on bounded intervals
  have h_fin : ∀ p q : ℝ, μ (Ioc p q) ≠ ⊤ := fun p q => by
    simp only [μ, convexSecondDerivMeasure, Monotone.stieltjesMeasure,
      StieltjesFunction.measure_Ioc, ne_eq, ENNReal.ofReal_ne_top, not_false_eq_true]
  -- Integrability of max(t-s,0) on both pieces (bounded on finite measure sets)
  have h_meas_max : AEStronglyMeasurable (fun s => max (t - s) 0) μ :=
    ((measurable_const.sub measurable_id).max measurable_const).aestronglyMeasurable
  have h_int_at : IntegrableOn (fun s => max (t - s) 0) (Ioc a t) μ :=
    Measure.integrableOn_of_bounded (M := t - a) (h_fin a t) h_meas_max
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (le_max_right (t - s) 0)]
        exact max_le (by linarith [hs.1]) (by linarith [hs.1])))
  have h_int_tb : IntegrableOn (fun s => max (t - s) 0) (Ioc t b) μ :=
    Measure.integrableOn_of_bounded (M := 0) (h_fin t b) h_meas_max
      ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun s hs => by
        simp only [Real.norm_eq_abs, abs_of_nonneg (le_max_right (t - s) 0)]
        exact le_of_eq (max_eq_right (sub_nonpos.mpr (le_of_lt hs.1)))))
  rw [setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc h_int_at h_int_tb]
  -- On Ioc t b: max(t - s, 0) = 0 since s > t
  have h_zero : ∫ s in Ioc t b, max (t - s) 0 ∂μ = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun s hs =>
      max_eq_right (sub_nonpos.mpr (le_of_lt hs.1))
  rw [h_zero, add_zero]
  -- On Ioc a t: max(t - s, 0) = t - s since s ≤ t
  exact setIntegral_congr_fun measurableSet_Ioc fun s hs =>
    max_eq_left (sub_nonneg.mpr hs.2)

end MeasureTheory
