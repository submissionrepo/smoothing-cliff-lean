/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.Basic
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Martingale extension on feasible joints

The `IsFeasibleJoint.martingale` field tests against continuous bounded scalar functions
`φ : ℝⁿ → ℝ`. This file extends the martingale test to bounded measurable scalar functions and to
inner products with bounded measurable vector-valued functions `q : ℝⁿ → ℝⁿ`, via an L¹-density
argument using density of bounded continuous functions in `L¹(π_X)`, where `π_X` is the first
marginal of `π`.

## Main statements

* `IsFeasibleJoint.martingale_continuous_scalar` — the martingale field restated for bounded
  continuous scalar test functions.
* `IsFeasibleJoint.martingale_measurable_scalar` — extension to bounded measurable scalar test
  functions.
* `IsFeasibleJoint.integral_phi_mul_m_eq_integral_phi_mul_fst` — split form: The integrals of
  `φ(p.1) · m(p.2)_i` and `φ(p.1) · p.1_i` agree.
* `IsFeasibleJoint.setIntegral_m_eq_setIntegral_fst_ofLp` — set-integral form for measurable sets
  `A ⊆ ℝⁿ`.
* `IsFeasibleJoint.martingale_inner_measurable` — vector-valued form for bounded measurable
  `q : ℝⁿ → ℝⁿ`, as an inner-product cross-term.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900).

## Tags

persuasion, moment persuasion, martingale, density
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]

variable {n : ℕ}

/-- Coordinate projection `x ↦ x i` on `ℝⁿ` (through the `ofLp` identification) is continuous. -/
private lemma continuous_ofLp_proj (i : Fin n) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) :=
  (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))

/-- For a feasible joint, the first coordinate lies in `X` almost everywhere. -/
private lemma IsFeasibleJoint.ae_fst_mem_X
    {s : MomentSetup Ω n} {π : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hπ : IsFeasibleJoint s π) : ∀ᵐ p ∂π.toMeasure, p.1 ∈ s.X := by
  have h_fst_meas : MeasurableSet
      ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
    (s.X_compact.isClosed.measurableSet).preimage measurable_fst
  rw [MeasureTheory.ae_iff,
    show {p : EuclideanSpace ℝ (Fin n) × Ω | ¬ p.1 ∈ s.X}
        = ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
            ⁻¹' s.X)ᶜ from rfl,
    MeasureTheory.prob_compl_eq_zero_iff h_fst_meas]
  exact hπ.fst_supportsOn

/-- **Continuous-scalar martingale.**

For every continuous bounded scalar test function `φ : ℝⁿ → ℝ` and every coordinate `i : Fin n`,
the cross-term integral `∫ φ(p.1) · (m(p.2)_i − p.1_i) dπ` vanishes. -/
lemma IsFeasibleJoint.martingale_continuous_scalar
    {s : MomentSetup Ω n} {π : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hπ : IsFeasibleJoint s π)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ_cont : Continuous φ)
    (hφ_bdd : ∃ M, ∀ x, |φ x| ≤ M) (i : Fin n) :
    ∫ p, φ p.1 * (s.m p.2 i - p.1 i) ∂π.toMeasure = 0 :=
  hπ.martingale φ hφ_cont hφ_bdd i

/-- **Measurable-scalar martingale.**

For every bounded measurable scalar `φ : ℝⁿ → ℝ` and every coordinate `i : Fin n`, the cross-term
integral `∫ φ(p.1) · (m(p.2)_i − p.1_i) dπ` vanishes. -/
lemma IsFeasibleJoint.martingale_measurable_scalar
    {s : MomentSetup Ω n} {π : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hπ : IsFeasibleJoint s π)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ_meas : Measurable φ) (hφ_bdd : ∃ M, ∀ x, |φ x| ≤ M) (i : Fin n) :
    ∫ p, φ p.1 * (s.m p.2 i - p.1 i) ∂π.toMeasure = 0 := by
  obtain ⟨M, hM⟩ := hφ_bdd
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  set πX : Measure (EuclideanSpace ℝ (Fin n)) :=
    Measure.map Prod.fst π.toMeasure with hπX_def
  haveI : IsProbabilityMeasure πX := by
    rw [hπX_def]
    exact MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have h_marg : ∀ {h : EuclideanSpace ℝ (Fin n) → ℝ},
      AEStronglyMeasurable h πX →
      ∫ p, h p.1 ∂π.toMeasure = ∫ x, h x ∂πX := by
    intro h h_aem
    rw [hπX_def, MeasureTheory.integral_map measurable_fst.aemeasurable h_aem]
  have h_ae_p1 : ∀ᵐ p ∂π.toMeasure, p.1 ∈ s.X := hπ.ae_fst_mem_X
  have h_kernel_bdd : ∀ᵐ p ∂π.toMeasure, |s.m p.2 i - p.1 i| ≤ R + R := by
    filter_upwards [h_ae_p1] with p hp1
    have h_m_i : ‖(s.m p.2).ofLp i‖ ≤ R :=
      (PiLp.norm_apply_le (s.m p.2) i).trans (hR _ (s.m_mem_X p.2))
    have h_p_i : ‖p.1.ofLp i‖ ≤ R :=
      (PiLp.norm_apply_le p.1 i).trans (hR _ hp1)
    rw [Real.norm_eq_abs] at h_m_i h_p_i
    have h := abs_sub (s.m p.2 i) (p.1 i)
    linarith
  have h_proj : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) :=
    continuous_ofLp_proj i
  have h_k_meas : Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 i - p.1 i) :=
    ((h_proj.measurable.comp s.m_continuous.measurable).comp measurable_snd).sub
      (h_proj.measurable.comp measurable_fst)
  have h_φ_int_πX : Integrable φ πX := by
    refine Integrable.of_bound hφ_meas.aestronglyMeasurable M ?_
    refine Filter.Eventually.of_forall (fun x => ?_)
    rw [Real.norm_eq_abs]; exact hM x
  set I : ℝ := ∫ p, φ p.1 * (s.m p.2 i - p.1 i) ∂π.toMeasure with hI_def
  have h_φ_p_aem : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1) π.toMeasure :=
    (hφ_meas.comp measurable_fst).aestronglyMeasurable
  have h_φk_aem : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1 * (s.m p.2 i - p.1 i)) π.toMeasure :=
    h_φ_p_aem.mul h_k_meas.aestronglyMeasurable
  have h_φk_int : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1 * (s.m p.2 i - p.1 i)) π.toMeasure := by
    refine Integrable.of_bound h_φk_aem (M * (R + R)) ?_
    filter_upwards [h_kernel_bdd] with p hk
    have h_φ_le : |φ p.1| ≤ M := hM p.1
    have h_M_nn : 0 ≤ M := le_trans (abs_nonneg _) h_φ_le
    have h_k_nn : 0 ≤ |s.m p.2 i - p.1 i| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul h_φ_le hk h_k_nn h_M_nn
  suffices h_abs_le : ∀ ε > 0, |I| ≤ ε by
    have h_abs_zero : |I| ≤ 0 :=
      le_of_forall_pos_le_add (fun ε hε => by simpa using h_abs_le ε hε)
    have h_eq_zero : |I| = 0 := le_antisymm h_abs_zero (abs_nonneg _)
    exact abs_eq_zero.mp h_eq_zero
  intro ε hε
  have h_R_nn : 0 ≤ R + R := by
    rcases s.X_interior.mono interior_subset with ⟨x₀, hx₀⟩
    have := hR x₀ hx₀
    have : 0 ≤ R := le_trans (norm_nonneg _) this
    linarith
  have h_denom_pos : 0 < R + R + 1 := by linarith
  set δ : ℝ := ε / (R + R + 1) with hδ_def
  have hδ_pos : 0 < δ := div_pos hε h_denom_pos
  obtain ⟨g, hg_close, hg_int⟩ :=
    h_φ_int_πX.exists_boundedContinuous_integral_sub_le hδ_pos
  have h_g_axiom : ∫ p, (g : _ → ℝ) p.1 * (s.m p.2 i - p.1 i) ∂π.toMeasure = 0 := by
    refine hπ.martingale_continuous_scalar (g : _ → ℝ) g.continuous ⟨‖g‖, fun x => ?_⟩ i
    have := g.norm_coe_le_norm x
    rwa [Real.norm_eq_abs] at this
  have h_g_p_aem : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => (g : _ → ℝ) p.1) π.toMeasure :=
    (g.continuous.measurable.comp measurable_fst).aestronglyMeasurable
  have h_gk_aem : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        (g : _ → ℝ) p.1 * (s.m p.2 i - p.1 i)) π.toMeasure :=
    h_g_p_aem.mul h_k_meas.aestronglyMeasurable
  have h_gk_int : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        (g : _ → ℝ) p.1 * (s.m p.2 i - p.1 i)) π.toMeasure := by
    refine Integrable.of_bound h_gk_aem (‖g‖ * (R + R)) ?_
    filter_upwards [h_kernel_bdd] with p hk
    have h_g_le : |(g : _ → ℝ) p.1| ≤ ‖g‖ := by
      have := g.norm_coe_le_norm p.1
      rwa [Real.norm_eq_abs] at this
    have h_g_nn : 0 ≤ ‖g‖ := norm_nonneg _
    have h_k_nn : 0 ≤ |s.m p.2 i - p.1 i| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul h_g_le hk h_k_nn h_g_nn
  have h_diff_k_int : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => (φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i))
      π.toMeasure := by
    have heq : (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
          (φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i))
        = (fun p => φ p.1 * (s.m p.2 i - p.1 i)
            - (g : _ → ℝ) p.1 * (s.m p.2 i - p.1 i)) := by
      funext p; ring
    rw [heq]
    exact h_φk_int.sub h_gk_int
  have h_I_split : I = ∫ p, (φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i) ∂π.toMeasure := by
    have h_eq_ae :
        (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1 * (s.m p.2 i - p.1 i))
          =ᵐ[π.toMeasure]
          (fun p => (φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i)
              + (g : _ → ℝ) p.1 * (s.m p.2 i - p.1 i)) :=
      Filter.Eventually.of_forall (fun p => by ring)
    calc I = ∫ p, (φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i)
              + (g : _ → ℝ) p.1 * (s.m p.2 i - p.1 i) ∂π.toMeasure := by
            rw [hI_def]; exact MeasureTheory.integral_congr_ae h_eq_ae
      _ = ∫ p, (φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i) ∂π.toMeasure
          + ∫ p, (g : _ → ℝ) p.1 * (s.m p.2 i - p.1 i) ∂π.toMeasure :=
            MeasureTheory.integral_add h_diff_k_int h_gk_int
      _ = ∫ p, (φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i) ∂π.toMeasure + 0 := by
            rw [h_g_axiom]
      _ = ∫ p, (φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i) ∂π.toMeasure := add_zero _
  have h_M_nn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have h_g_norm_bound : ∀ x : EuclideanSpace ℝ (Fin n), |(g : _ → ℝ) x| ≤ ‖g‖ := fun x => by
    have := g.norm_coe_le_norm x
    rwa [Real.norm_eq_abs] at this
  have h_diff_p_int : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1 - (g : _ → ℝ) p.1) π.toMeasure := by
    refine Integrable.of_bound (h_φ_p_aem.sub h_g_p_aem) (M + ‖g‖) ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [Real.norm_eq_abs]
    calc |φ p.1 - (g : _ → ℝ) p.1| ≤ |φ p.1| + |(g : _ → ℝ) p.1| := abs_sub _ _
      _ ≤ M + ‖g‖ := add_le_add (hM _) (h_g_norm_bound _)
  have h_marg_abs_diff :
      ∫ p, |φ p.1 - (g : _ → ℝ) p.1| ∂π.toMeasure
        = ∫ x, |φ x - (g : _ → ℝ) x| ∂πX :=
    h_marg (hφ_meas.sub g.continuous.measurable).abs.aestronglyMeasurable
  have h_norm_eq_abs : (fun x : EuclideanSpace ℝ (Fin n) => ‖φ x - (g : _ → ℝ) x‖)
      = (fun x => |φ x - (g : _ → ℝ) x|) := by
    funext x; exact Real.norm_eq_abs _
  rw [h_norm_eq_abs] at hg_close
  calc |I|
      = |∫ p, (φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i) ∂π.toMeasure| := by
          rw [h_I_split]
    _ ≤ ∫ p, |(φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i)| ∂π.toMeasure := by
          rw [show (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                |(φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i)|)
              = fun p => ‖(φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i)‖ from
              funext (fun p => (Real.norm_eq_abs _).symm)]
          rw [show |∫ p, (φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i) ∂π.toMeasure|
              = ‖∫ p, (φ p.1 - (g : _ → ℝ) p.1) * (s.m p.2 i - p.1 i) ∂π.toMeasure‖ from
              (Real.norm_eq_abs _).symm]
          exact MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ p, |φ p.1 - (g : _ → ℝ) p.1| * |s.m p.2 i - p.1 i| ∂π.toMeasure := by
          refine MeasureTheory.integral_congr_ae ?_
          refine Filter.Eventually.of_forall (fun p => ?_)
          exact abs_mul (φ p.1 - g p.1) ((s.m p.2).ofLp i - p.1.ofLp i)
    _ ≤ ∫ p, |φ p.1 - (g : _ → ℝ) p.1| * (R + R) ∂π.toMeasure := by
          refine MeasureTheory.integral_mono_ae ?_ ?_ ?_
          · -- LHS integrable
            have h_abs_diff_meas : Measurable
                (fun p : EuclideanSpace ℝ (Fin n) × Ω => |φ p.1 - (g : _ → ℝ) p.1|) :=
              ((hφ_meas.comp measurable_fst).sub
                (g.continuous.measurable.comp measurable_fst)).abs
            refine Integrable.of_bound
              ((h_abs_diff_meas.mul h_k_meas.abs).aestronglyMeasurable)
              ((M + ‖g‖) * (R + R)) ?_
            filter_upwards [h_kernel_bdd] with p hk
            have h_diff_le : |φ p.1 - (g : _ → ℝ) p.1| ≤ M + ‖g‖ :=
              calc |φ p.1 - (g : _ → ℝ) p.1| ≤ |φ p.1| + |(g : _ → ℝ) p.1| := abs_sub _ _
                _ ≤ M + ‖g‖ := add_le_add (hM _) (h_g_norm_bound _)
            have h_diff_nn : 0 ≤ |φ p.1 - (g : _ → ℝ) p.1| := abs_nonneg _
            have h_k_nn : 0 ≤ |s.m p.2 i - p.1 i| := abs_nonneg _
            have h_sum_nn : 0 ≤ M + ‖g‖ := by linarith [h_M_nn, norm_nonneg g]
            rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs]
            exact mul_le_mul h_diff_le hk h_k_nn h_sum_nn
          · -- RHS integrable
            exact h_diff_p_int.abs.mul_const _
          · filter_upwards [h_kernel_bdd] with p hk
            have h_diff_nn : 0 ≤ |φ p.1 - (g : _ → ℝ) p.1| := abs_nonneg _
            exact mul_le_mul_of_nonneg_left hk h_diff_nn
    _ = (R + R) * ∫ p, |φ p.1 - (g : _ → ℝ) p.1| ∂π.toMeasure := by
          rw [MeasureTheory.integral_mul_const, mul_comm]
    _ = (R + R) * ∫ x, |φ x - (g : _ → ℝ) x| ∂πX := by
          rw [h_marg_abs_diff]
    _ ≤ (R + R) * δ :=
          mul_le_mul_of_nonneg_left hg_close h_R_nn
    _ ≤ ε := by
          rw [hδ_def]
          rw [show (R + R) * (ε / (R + R + 1)) = ε * ((R + R) / (R + R + 1)) by ring]
          have h_frac_le_one : (R + R) / (R + R + 1) ≤ 1 := by
            rw [div_le_one h_denom_pos]
            linarith
          have hε_nn : 0 ≤ ε := le_of_lt hε
          calc ε * ((R + R) / (R + R + 1)) ≤ ε * 1 :=
                mul_le_mul_of_nonneg_left h_frac_le_one hε_nn
            _ = ε := mul_one _

/-- **Integrated martingale (split scalar form).**

For every bounded measurable scalar `φ : ℝⁿ → ℝ` and every coordinate `i : Fin n`,
`∫ p, φ(p.1) · m(p.2)_i dπ = ∫ p, φ(p.1) · p.1_i dπ`. -/
lemma IsFeasibleJoint.integral_phi_mul_m_eq_integral_phi_mul_fst
    {s : MomentSetup Ω n} {π : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hπ : IsFeasibleJoint s π)
    {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ_meas : Measurable φ) (hφ_bdd : ∃ M, ∀ x, |φ x| ≤ M) (i : Fin n) :
    ∫ p, φ p.1 * (s.m p.2 i) ∂π.toMeasure
      = ∫ p, φ p.1 * (p.1 i) ∂π.toMeasure := by
  have h_mart := hπ.martingale_measurable_scalar hφ_meas hφ_bdd i
  obtain ⟨M, hM⟩ := hφ_bdd
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  have h_ae_p1 : ∀ᵐ p ∂π.toMeasure, p.1 ∈ s.X := hπ.ae_fst_mem_X
  have h_proj : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) :=
    continuous_ofLp_proj i
  have h_φ_p_aem : AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1) π.toMeasure :=
    (hφ_meas.comp measurable_fst).aestronglyMeasurable
  have h_m_meas : Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => (s.m p.2).ofLp i) :=
    (h_proj.measurable.comp s.m_continuous.measurable).comp measurable_snd
  have h_p1_meas : Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => p.1.ofLp i) :=
    h_proj.measurable.comp measurable_fst
  have h_M_nn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have h_φ_m_int : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1 * (s.m p.2 i)) π.toMeasure := by
    refine Integrable.of_bound (h_φ_p_aem.mul h_m_meas.aestronglyMeasurable) (M * R) ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have h_φ_le : |φ p.1| ≤ M := hM p.1
    have h_m_le : ‖(s.m p.2).ofLp i‖ ≤ R :=
      (PiLp.norm_apply_le (s.m p.2) i).trans (hR _ (s.m_mem_X p.2))
    have h_m_nn : 0 ≤ |s.m p.2 i| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_mul]
    rw [Real.norm_eq_abs] at h_m_le
    exact mul_le_mul h_φ_le h_m_le h_m_nn h_M_nn
  have h_φ_p1_int : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => φ p.1 * (p.1 i)) π.toMeasure := by
    refine Integrable.of_bound (h_φ_p_aem.mul h_p1_meas.aestronglyMeasurable) (M * R) ?_
    filter_upwards [h_ae_p1] with p hp1
    have h_φ_le : |φ p.1| ≤ M := hM p.1
    have h_p1_le : ‖p.1.ofLp i‖ ≤ R :=
      (PiLp.norm_apply_le p.1 i).trans (hR _ hp1)
    have h_p1_nn : 0 ≤ |p.1 i| := abs_nonneg _
    rw [Real.norm_eq_abs, abs_mul]
    rw [Real.norm_eq_abs] at h_p1_le
    exact mul_le_mul h_φ_le h_p1_le h_p1_nn h_M_nn
  have h_diff_eq : (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        φ p.1 * (s.m p.2 i - p.1 i))
      = (fun p => φ p.1 * (s.m p.2 i) - φ p.1 * (p.1 i)) := by
    funext p; ring
  rw [h_diff_eq, MeasureTheory.integral_sub h_φ_m_int h_φ_p1_int] at h_mart
  linarith

/-- **Integrated martingale (set/coordinate form).**

For every measurable `A ⊆ ℝⁿ` and every coordinate `i : Fin n`,
`∫ p ∈ A ×ˢ univ, m(p.2)_i dπ = ∫ p ∈ A ×ˢ univ, p.1_i dπ`. -/
lemma IsFeasibleJoint.setIntegral_m_eq_setIntegral_fst_ofLp
    {s : MomentSetup Ω n} {π : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hπ : IsFeasibleJoint s π)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (i : Fin n) :
    ∫ p in A ×ˢ (Set.univ : Set Ω), s.m p.2 i ∂π.toMeasure
      = ∫ p in A ×ˢ (Set.univ : Set Ω), p.1 i ∂π.toMeasure := by
  let φ : EuclideanSpace ℝ (Fin n) → ℝ := Set.indicator A (fun _ => (1 : ℝ))
  have hφ_meas : Measurable φ := (measurable_const (a := (1 : ℝ))).indicator hA
  have hφ_bdd : ∃ M, ∀ x, |φ x| ≤ M := by
    refine ⟨1, fun x => ?_⟩
    by_cases hx : x ∈ A <;> simp [φ, hx]
  have h_split :=
    hπ.integral_phi_mul_m_eq_integral_phi_mul_fst hφ_meas hφ_bdd i
  have h_prod_meas : MeasurableSet (A ×ˢ (Set.univ : Set Ω)) :=
    hA.prod MeasurableSet.univ
  have h_indicator_eq : ∀ {f : EuclideanSpace ℝ (Fin n) × Ω → ℝ},
      ∫ p, φ p.1 * f p ∂π.toMeasure
        = ∫ p in A ×ˢ (Set.univ : Set Ω), f p ∂π.toMeasure := by
    intro f
    rw [← MeasureTheory.integral_indicator h_prod_meas]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with p
    simp only [φ, Set.indicator]
    by_cases hpA : p.1 ∈ A
    · have hp_prod : p ∈ A ×ˢ (Set.univ : Set Ω) := ⟨hpA, Set.mem_univ _⟩
      simp [hp_prod, hpA]
    · have hp_prod : p ∉ A ×ˢ (Set.univ : Set Ω) := fun hp => hpA hp.1
      simp [hp_prod, hpA]
  rw [← h_indicator_eq, ← h_indicator_eq]
  exact h_split

/-- **Inner-product martingale for measurable vector-valued `q`.**

For any bounded measurable `q : ℝⁿ → ℝⁿ` and any feasible joint `π`,
`∫ ⟨q(p.1), m(p.2) − p.1⟩ dπ = 0`. -/
lemma IsFeasibleJoint.martingale_inner_measurable
    {s : MomentSetup Ω n} {π : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hπ : IsFeasibleJoint s π)
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hq_meas : Measurable q) (hq_bdd : ∃ K, ∀ x, ‖q x‖ ≤ K) :
    ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂π.toMeasure = 0 := by
  obtain ⟨K, hK⟩ := hq_bdd
  have h_phi_meas : ∀ i : Fin n, Measurable (fun x => (q x).ofLp i) := fun i =>
    (continuous_apply i).measurable.comp
      ((PiLp.continuous_ofLp 2 _).measurable.comp hq_meas)
  have h_phi_bdd : ∀ i : Fin n, ∃ M, ∀ x, |(q x).ofLp i| ≤ M := fun i =>
    ⟨K, fun x => by
      have h := (PiLp.norm_apply_le (q x) i).trans (hK x)
      rwa [Real.norm_eq_abs] at h⟩
  have h_inner_eq : ∀ p : EuclideanSpace ℝ (Fin n) × Ω,
      inner ℝ (q p.1) (s.m p.2 - p.1)
        = ∑ i : Fin n, (q p.1).ofLp i * (s.m p.2 i - p.1 i) := by
    intro p
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [PiLp.sub_apply]
    -- For reals, `inner ℝ a b = a * b`.
    simp
    ring
  have h_funext :
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => inner ℝ (q p.1) (s.m p.2 - p.1))
        = (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
            ∑ i : Fin n, (q p.1).ofLp i * (s.m p.2 i - p.1 i)) :=
    funext h_inner_eq
  rw [h_funext]
  have h_ae_p1 : ∀ᵐ p ∂π.toMeasure, p.1 ∈ s.X := hπ.ae_fst_mem_X
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  have h_sum_int : ∀ i : Fin n, MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        (q p.1).ofLp i * (s.m p.2 i - p.1 i)) π.toMeasure := by
    intro i
    have h_aem : MeasureTheory.AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
          (q p.1).ofLp i * (s.m p.2 i - p.1 i)) π.toMeasure := by
      have h_q_aem : MeasureTheory.AEStronglyMeasurable
          (fun p : EuclideanSpace ℝ (Fin n) × Ω => (q p.1).ofLp i) π.toMeasure :=
        ((h_phi_meas i).comp measurable_fst).aestronglyMeasurable
      have h_diff_meas : Measurable
          (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 i - p.1 i) := by
        have h_proj : Continuous
            (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) := continuous_ofLp_proj i
        have h_m_i : Measurable
            (fun p : EuclideanSpace ℝ (Fin n) × Ω => (s.m p.2).ofLp i) :=
          (h_proj.measurable.comp s.m_continuous.measurable).comp measurable_snd
        have h_p1_i : Measurable
            (fun p : EuclideanSpace ℝ (Fin n) × Ω => p.1.ofLp i) :=
          h_proj.measurable.comp measurable_fst
        exact h_m_i.sub h_p1_i
      exact h_q_aem.mul h_diff_meas.aestronglyMeasurable
    refine MeasureTheory.Integrable.of_bound h_aem (K * (R + R)) ?_
    filter_upwards [h_ae_p1] with p hp1
    have h_q_le : ‖(q p.1).ofLp i‖ ≤ K :=
      (PiLp.norm_apply_le (q p.1) i).trans (hK p.1)
    have h_diff_le : |s.m p.2 i - p.1 i| ≤ R + R := by
      have h_m_i_le : ‖(s.m p.2).ofLp i‖ ≤ R := by
        have := PiLp.norm_apply_le (s.m p.2) i
        exact this.trans (hR _ (s.m_mem_X p.2))
      have h_p_i_le : ‖p.1.ofLp i‖ ≤ R :=
        (PiLp.norm_apply_le p.1 i).trans (hR _ hp1)
      rw [Real.norm_eq_abs] at h_m_i_le h_p_i_le
      have : |s.m p.2 i - p.1 i| ≤ |s.m p.2 i| + |p.1 i| := abs_sub _ _
      linarith
    rw [Real.norm_eq_abs, abs_mul]
    have h_q_abs : |(q p.1).ofLp i| ≤ K := by
      rw [show |(q p.1).ofLp i| = ‖(q p.1).ofLp i‖ from (Real.norm_eq_abs _).symm]
      exact h_q_le
    have h_q_nn : 0 ≤ |(q p.1).ofLp i| := abs_nonneg _
    have h_diff_nn : 0 ≤ |s.m p.2 i - p.1 i| := abs_nonneg _
    have h_K_nn : 0 ≤ K := le_trans (norm_nonneg (q 0)) (hK 0)
    exact mul_le_mul h_q_abs h_diff_le h_diff_nn h_K_nn
  rw [MeasureTheory.integral_finset_sum Finset.univ (fun i _ => h_sum_int i)]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  exact hπ.martingale_measurable_scalar (h_phi_meas i) (h_phi_bdd i) i

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
