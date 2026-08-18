/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Stieltjes

open Set Filter MeasureTheory Function
open scoped Topology

/-!
# Integration by parts for Stieltjes measures

This file proves an integration-by-parts formula for the Stieltjes measures of two monotone
functions `F` and `u`. Writing `F_sf`, `u_sf` for their right-continuous regularizations and `μ_F`,
`μ_u` for the associated Stieltjes measures, the local identity on `(a, b]` is

`∫ F_sf dμ_u + ∫ leftLim u_sf dμ_F = F_sf(b)·u_sf(b) − F_sf(a)·u_sf(a)`,

with the left integrand against `μ_u` evaluated at the right-continuous representative and the
integrand against `μ_F` at the left limit. Under a boundary-decay assumption the identity extends
to all of `ℝ`. The convenience abbreviations `Monotone.stieltjes` and `Monotone.stieltjesMeasure`
wrap Mathlib's `Monotone.stieltjesFunction`.

## Main definitions

* `Monotone.stieltjes` — the Stieltjes function of a monotone function (Mathlib's right-continuous
  regularization).
* `Monotone.stieltjesMeasure` — the associated Stieltjes measure.
* `MeasureTheory.DecayAtInfinity` — the boundary condition `lim_{x→±∞} F(x)·u(x) = 0`.

## Main statements

* `MeasureTheory.stieltjes_ibp_local` — the integration-by-parts identity on a bounded interval
  `(a, b]`.
* `MeasureTheory.stieltjes_ibp` — the global identity on `ℝ` under boundary decay and integrability.

## Tags

integration by parts, stieltjes measure, fubini, monotone function
-/

@[expose] public section

namespace Monotone

section Wrappers

/-- The Stieltjes function induced by a monotone function (via Mathlib's right-continuous
regularization `rightLim f`). -/
noncomputable abbrev stieltjes {f : ℝ → ℝ} (hf : Monotone f) : StieltjesFunction ℝ :=
  hf.stieltjesFunction

/-- The Stieltjes measure induced by a monotone function. -/
noncomputable abbrev stieltjesMeasure {f : ℝ → ℝ} (hf : Monotone f) : Measure ℝ :=
  hf.stieltjesFunction.measure

end Wrappers

end Monotone

namespace MeasureTheory

section LocalIBP

variable {F u : ℝ → ℝ} (hF : Monotone F) (hu : Monotone u) (a b : ℝ)

/-- **Integration by parts** for Stieltjes measures on a bounded interval `(a, b]`: The integral of
`F_sf` against `μ_u` plus the integral of the left limit of `u_sf` against `μ_F` equals the
boundary term `F_sf(b)·u_sf(b) − F_sf(a)·u_sf(a)`. -/
theorem stieltjes_ibp_local (hab : a < b) :
    let F_sf := hF.stieltjes
    let u_sf := hu.stieltjes
    let μ_F := hF.stieltjesMeasure
    let μ_u := hu.stieltjesMeasure
    ∫ y in Ioc a b, F_sf y ∂μ_u + ∫ x in Ioc a b, leftLim (⇑u_sf) x ∂μ_F =
    F_sf b * u_sf b - F_sf a * u_sf a := by
  intro F_sf u_sf μ_F μ_u
  -- Fubini swap on the triangular indicator ∫∫_{x≤y} 1 dμ_F dμ_u
  -- Both sides compute (μ_F ⊗ μ_u)(T) where T = {(x,y) | a < x ≤ y ≤ b},
  -- sectioned in opposite orders via Tonelli's theorem.
  have h_fubini_swap : ∫ y in Ioc a b, ∫ x in Ioc a y, (1 : ℝ) ∂μ_F ∂μ_u =
                       ∫ x in Ioc a b, ∫ y in Icc x b, (1 : ℝ) ∂μ_u ∂μ_F := by
    -- Reduce inner Bochner integrals to (μ S).toReal
    simp_rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def]
    -- Convert outer Bochner integrals to lintegrals via integral_toReal
    have h_meas_F : AEMeasurable (fun y => μ_F (Ioc a y)) (μ_u.restrict (Ioc a b)) := by
      rw [show (fun y => μ_F (Ioc a y)) = fun y => ENNReal.ofReal (F_sf y - F_sf a) from
        funext (fun y => F_sf.measure_Ioc a y)]
      exact (F_sf.mono.measurable.sub measurable_const).ennreal_ofReal.aemeasurable
    have h_meas_u : AEMeasurable (fun x => μ_u (Icc x b)) (μ_F.restrict (Ioc a b)) := by
      rw [show (fun x => μ_u (Icc x b)) = fun x => ENNReal.ofReal (u_sf b - leftLim (⇑u_sf) x)
        from funext (fun x => u_sf.measure_Icc x b)]
      exact (measurable_const.sub u_sf.mono.leftLim.measurable).ennreal_ofReal.aemeasurable
    rw [integral_toReal h_meas_F
          (ae_of_all _ fun y => by rw [F_sf.measure_Ioc]; exact ENNReal.ofReal_lt_top),
        integral_toReal h_meas_u
          (ae_of_all _ fun x => by rw [u_sf.measure_Icc]; exact ENNReal.ofReal_lt_top)]
    congr 1
    -- Prove the lintegral equality via product measure of the triangle
    set T : Set (ℝ × ℝ) := {p | a < p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ b}
    have hT : MeasurableSet T :=
      (measurableSet_lt measurable_const measurable_fst).inter
        ((measurableSet_le measurable_fst measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const))
    -- Compute sections of T: x-section = Icc x b, y-section = Ioc a y
    have sect_x : ∀ x, Prod.mk x ⁻¹' T = if x ∈ Ioc a b then Icc x b else ∅ := by
      intro x; ext y; simp only [T, mem_preimage, mem_setOf_eq, mem_Ioc]
      split
      · next h => exact ⟨fun ⟨_, hxy, hyb⟩ => ⟨hxy, hyb⟩, fun ⟨hxy, hyb⟩ => ⟨h.1, hxy, hyb⟩⟩
      · next h => exact ⟨fun ⟨hax, hxy, hyb⟩ => absurd ⟨hax, le_trans hxy hyb⟩ h, False.elim⟩
    have sect_y : ∀ y, Prod.mk y ⁻¹' (Prod.swap ⁻¹' T) =
        if y ∈ Ioc a b then Ioc a y else ∅ := by
      intro y; ext x; simp only [T, mem_preimage, Prod.swap, mem_setOf_eq, mem_Ioc]
      split
      · next h => exact ⟨fun ⟨hax, hxy, _⟩ => ⟨hax, hxy⟩, fun ⟨hax, hxy⟩ => ⟨hax, hxy, h.2⟩⟩
      · next h => exact ⟨fun ⟨hax, hxy, hyb⟩ =>
          absurd ⟨lt_of_lt_of_le hax hxy, hyb⟩ h, False.elim⟩
    -- RHS = (μ_F ⊗ μ_u)(T) by sectioning at first coordinate
    have hRHS : (μ_F.prod μ_u) T = ∫⁻ x in Ioc a b, μ_u (Icc x b) ∂μ_F := by
      rw [Measure.prod_apply hT, ← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr; intro x; simp only [sect_x]
      split <;> simp [indicator_of_mem, indicator_of_notMem, *]
    -- LHS = (μ_u ⊗ μ_F)(swap ⁻¹' T) by sectioning at first coordinate
    have hLHS : (μ_u.prod μ_F) (Prod.swap ⁻¹' T) =
        ∫⁻ y in Ioc a b, μ_F (Ioc a y) ∂μ_u := by
      rw [Measure.prod_apply (hT.preimage measurable_swap),
          ← lintegral_indicator measurableSet_Ioc]
      apply lintegral_congr; intro y; simp only [sect_y]
      split <;> simp [indicator_of_mem, indicator_of_notMem, *]
    -- Connect via Measure.prod_swap
    have hSwap : (μ_u.prod μ_F) (Prod.swap ⁻¹' T) = (μ_F.prod μ_u) T := by
      rw [show μ_u.prod μ_F = (μ_F.prod μ_u).map Prod.swap from Measure.prod_swap.symm,
          Measure.map_apply measurable_swap (hT.preimage measurable_swap)]
      congr 1
    rw [← hLHS, hSwap, hRHS]
  -- Inner integral μ_F((a, y]) = F_sf(y) - F_sf(a) by StieltjesFunction.measure_Ioc
  have h_inner_x : ∀ y ∈ Ioc a b, ∫ x in Ioc a y, (1 : ℝ) ∂μ_F = F_sf y - F_sf a := by
    intro y hy
    rw [setIntegral_const, smul_eq_mul, mul_one]
    -- Goal: (μ_F (Ioc a y)).toReal = F_sf y - F_sf a
    change (F_sf.measure (Ioc a y)).toReal = _
    rw [StieltjesFunction.measure_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (F_sf.mono (le_of_lt hy.1)))
  -- Inner integral μ_u([x, b]) = u_sf(b) - leftLim(u_sf, x); the closed left bracket gives the
  -- left limit via StieltjesFunction.measure_Icc.
  have h_inner_y : ∀ x ∈ Ioc a b, ∫ y in Icc x b, (1 : ℝ) ∂μ_u =
      u_sf b - leftLim (⇑u_sf) x := by
    intro x hx
    rw [setIntegral_const, smul_eq_mul, mul_one]
    -- Goal: (μ_u (Icc x b)).toReal = u_sf b - leftLim u_sf x
    change (u_sf.measure (Icc x b)).toReal = _
    rw [StieltjesFunction.measure_Icc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (Monotone.leftLim_le u_sf.mono hx.2))
  -- Substitute inner evaluations into Fubini to get the identity
  have h_sub : ∫ y in Ioc a b, (F_sf y - F_sf a) ∂μ_u =
      ∫ x in Ioc a b, (u_sf b - leftLim (⇑u_sf) x) ∂μ_F := by
    have lhs_eq : ∫ y in Ioc a b, (F_sf y - F_sf a) ∂μ_u =
        ∫ y in Ioc a b, ∫ x in Ioc a y, (1 : ℝ) ∂μ_F ∂μ_u :=
      setIntegral_congr_fun measurableSet_Ioc (fun y hy => (h_inner_x y hy).symm)
    have rhs_eq : ∫ x in Ioc a b, ∫ y in Icc x b, (1 : ℝ) ∂μ_u ∂μ_F =
        ∫ x in Ioc a b, (u_sf b - leftLim (⇑u_sf) x) ∂μ_F :=
      setIntegral_congr_fun measurableSet_Ioc (fun x hx => h_inner_y x hx)
    exact lhs_eq.trans (h_fubini_swap.trans rhs_eq)
  -- Finiteness lemmas for the measure of (a,b]
  have h_fin_u : μ_u (Ioc a b) ≠ ⊤ := by
    change u_sf.measure (Ioc a b) ≠ ⊤
    simp [StieltjesFunction.measure_Ioc, ENNReal.ofReal_ne_top]
  have h_fin_F : μ_F (Ioc a b) ≠ ⊤ := by
    change F_sf.measure (Ioc a b) ≠ ⊤
    simp [StieltjesFunction.measure_Ioc, ENNReal.ofReal_ne_top]
  -- Integrability of the constant functions on finite-measure sets
  have h_int_const_Fa : IntegrableOn (fun _ => F_sf a) (Ioc a b) μ_u :=
    integrableOn_const h_fin_u
  have h_int_const_ub : IntegrableOn (fun _ => u_sf b) (Ioc a b) μ_F :=
    integrableOn_const h_fin_F
  -- Integrability of F_sf and leftLim u_sf on bounded sets
  -- Monotone functions are measurable and bounded on bounded intervals,
  -- hence integrable against any finite measure on that interval.
  have h_int_Fsf : IntegrableOn (⇑F_sf) (Ioc a b) μ_u := by
    refine Measure.integrableOn_of_bounded (M := max |F_sf a| |F_sf b|)
      h_fin_u F_sf.mono.measurable.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => ?_)
    simp only [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [F_sf.mono (le_of_lt hx.1), neg_abs_le (F_sf a),
                         le_max_left |F_sf a| |F_sf b|],
           by linarith [F_sf.mono hx.2, le_abs_self (F_sf b),
                         le_max_right |F_sf a| |F_sf b|]⟩
  have h_int_ulc : IntegrableOn (leftLim (⇑u_sf)) (Ioc a b) μ_F := by
    refine Measure.integrableOn_of_bounded (M := max |u_sf a| |u_sf b|)
      h_fin_F (u_sf.mono.leftLim.measurable.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => ?_)
    simp only [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [u_sf.mono.le_leftLim hx.1, neg_abs_le (u_sf a),
                         le_max_left |u_sf a| |u_sf b|],
           by linarith [Monotone.leftLim_le u_sf.mono hx.2, le_abs_self (u_sf b),
                         le_max_right |u_sf a| |u_sf b|]⟩
  -- Evaluate μ.real(Ioc a b) for Stieltjes measures
  have h_measureReal_u : μ_u.real (Ioc a b) = u_sf b - u_sf a := by
    rw [measureReal_def]; change (u_sf.measure (Ioc a b)).toReal = _
    rw [StieltjesFunction.measure_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (u_sf.mono (le_of_lt hab)))
  have h_measureReal_F : μ_F.real (Ioc a b) = F_sf b - F_sf a := by
    rw [measureReal_def]; change (F_sf.measure (Ioc a b)).toReal = _
    rw [StieltjesFunction.measure_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.mpr (F_sf.mono (le_of_lt hab)))
  -- ∫ F_sf(a) dμ_u = F_sf(a) · (u_sf(b) - u_sf(a))
  have h_const_Fa : ∫ y in Ioc a b, (fun _ => F_sf a) y ∂μ_u = F_sf a * (u_sf b - u_sf a) := by
    rw [setIntegral_const, smul_eq_mul, mul_comm, h_measureReal_u]
  -- ∫ u_sf(b) dμ_F = u_sf(b) · (F_sf(b) - F_sf(a))
  have h_const_ub : ∫ x in Ioc a b, (fun _ => u_sf b) x ∂μ_F = u_sf b * (F_sf b - F_sf a) := by
    rw [setIntegral_const, smul_eq_mul, mul_comm, h_measureReal_F]
  -- Expand LHS using integral linearity: ∫ (F - c) dμ = ∫ F dμ - c · μ(S)
  have h_LHS : ∫ y in Ioc a b, (F_sf y - F_sf a) ∂μ_u =
               (∫ y in Ioc a b, F_sf y ∂μ_u) - F_sf a * (u_sf b - u_sf a) := by
    rw [integral_sub h_int_Fsf h_int_const_Fa, h_const_Fa]
  -- Expand RHS similarly: ∫ (c - u_lc) dμ = c · μ(S) - ∫ u_lc dμ
  have h_RHS : ∫ x in Ioc a b, (u_sf b - leftLim (⇑u_sf) x) ∂μ_F =
               u_sf b * (F_sf b - F_sf a) - ∫ x in Ioc a b, leftLim (⇑u_sf) x ∂μ_F := by
    rw [integral_sub h_int_const_ub h_int_ulc, h_const_ub]
  -- Algebraic rearrangement isolates the boundary terms
  linarith

end LocalIBP

section GlobalIBP

/-- The boundary decay condition `lim_{x→±∞} F(x)·u(x) = 0`, required to extend the local
integration-by-parts identity to all of `ℝ`. -/
structure DecayAtInfinity (F u : ℝ → ℝ) : Prop where
  /-- The product `F·u` decays to zero at `-∞`. -/
  atBot : Tendsto (fun x => F x * u x) atBot (𝓝 0)
  /-- The product `F·u` decays to zero at `+∞`. -/
  atTop : Tendsto (fun x => F x * u x) atTop (𝓝 0)

variable {F u : ℝ → ℝ} (hF : Monotone F) (hu : Monotone u)

/-- **Integration by parts** for Stieltjes measures on `ℝ`: Under boundary decay and integrability,
the integral of `F_sf` against `μ_u` plus the integral of the left limit of `u_sf` against `μ_F`
vanishes. -/
theorem stieltjes_ibp
    (h_decay : DecayAtInfinity (⇑(hF.stieltjes)) (⇑(hu.stieltjes)))
    (hF_int : Integrable (⇑(hF.stieltjes)) (hu.stieltjesMeasure))
    (hu_int : Integrable (leftLim (⇑(hu.stieltjes))) (hF.stieltjesMeasure)) :
    ∫ y, hF.stieltjes y ∂(hu.stieltjesMeasure) +
    ∫ x, leftLim (⇑(hu.stieltjes)) x ∂(hF.stieltjesMeasure) = 0 := by
  set F_sf := hF.stieltjes; set u_sf := hu.stieltjes
  set μ_F := hF.stieltjesMeasure; set μ_u := hu.stieltjesMeasure
  -- Approximate ℝ by expanding intervals Ioc (-n) n
  set s := fun n : ℕ => Ioc (-(↑n : ℝ)) (↑n : ℝ)
  have hs_meas : ∀ n, MeasurableSet (s n) := fun _ => measurableSet_Ioc
  have hs_mono : Monotone s :=
    fun _ _ h => Ioc_subset_Ioc (neg_le_neg (Nat.cast_le.mpr h)) (Nat.cast_le.mpr h)
  have hs_union : ⋃ n, s n = univ := by
    ext x; simp only [s, mem_iUnion, mem_Ioc, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨n, neg_lt_of_abs_lt hn, le_of_lt (abs_lt.mp hn).2⟩
  -- Set integrals converge to global integrals
  have hF_lim : Tendsto (fun n => ∫ y in s n, F_sf y ∂μ_u) atTop
      (𝓝 (∫ y, F_sf y ∂μ_u)) := by
    rw [← setIntegral_univ, ← hs_union]
    exact tendsto_setIntegral_of_monotone hs_meas hs_mono (hs_union ▸ hF_int.integrableOn)
  have hu_lim : Tendsto (fun n => ∫ x in s n, leftLim (⇑u_sf) x ∂μ_F) atTop
      (𝓝 (∫ x, leftLim (⇑u_sf) x ∂μ_F)) := by
    rw [← setIntegral_univ, ← hs_union]
    exact tendsto_setIntegral_of_monotone hs_meas hs_mono (hs_union ▸ hu_int.integrableOn)
  -- Local identity holds eventually (for n ≥ 1 so that -n < n)
  have h_local : ∀ᶠ n in atTop,
      ∫ y in s n, F_sf y ∂μ_u + ∫ x in s n, leftLim (⇑u_sf) x ∂μ_F =
      F_sf ↑n * u_sf ↑n - F_sf (-(↑n : ℝ)) * u_sf (-(↑n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact stieltjes_ibp_local hF hu (-(↑n : ℝ)) ↑n
      (by have : (0 : ℝ) < ↑n := Nat.cast_pos.mpr (Nat.one_le_iff_ne_zero.mp hn |>.bot_lt)
          linarith)
  -- Boundary terms converge to 0 by the decay assumption
  have h_rhs : Tendsto
      (fun n : ℕ => F_sf ↑n * u_sf ↑n - F_sf (-(↑n : ℝ)) * u_sf (-(↑n : ℝ)))
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = 0 - 0 from (sub_self 0).symm]
    exact (h_decay.2.comp tendsto_natCast_atTop_atTop).sub
      (h_decay.1.comp (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop))
  -- Conclude: the sum tends to both the global integral and 0, so they're equal
  exact tendsto_nhds_unique (hF_lim.add hu_lim) ((tendsto_congr' h_local).mpr h_rhs)

end GlobalIBP

/-- A monotone Stieltjes function is integrable on `Ioc a b` against any locally finite measure: On
`(a, b]` it is sandwiched between `f a` and `f b`, so it is essentially bounded. -/
lemma stieltjes_integrableOn_Ioc (f : StieltjesFunction ℝ) {μ : Measure ℝ}
    (a b : ℝ) (h_fin : μ (Ioc a b) ≠ ⊤) :
    IntegrableOn (⇑f) (Ioc a b) μ :=
  Measure.integrableOn_of_bounded h_fin f.mono.measurable.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => by
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · calc -(max |f a| |f b|) ≤ -|f a| := by linarith [le_max_left |f a| |f b|]
          _ ≤ f a := neg_abs_le _
          _ ≤ f x := f.mono hx.1.le
      · calc f x ≤ f b := f.mono hx.2
          _ ≤ |f b| := le_abs_self _
          _ ≤ max |f a| |f b| := le_max_right _ _))

end MeasureTheory
