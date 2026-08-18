/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Probability.Kernel.Disintegration.Integral
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Set form vs. continuous-test form of vector-valued mean preservation

Suppose `π` is a finite Borel measure on `Y × ℝⁿ` (with `Y` Polish) whose first marginal equals a
fixed finite measure `ν` on `Y` and whose support is contained in `Y × K` for some compact
`K ⊆ ℝⁿ`. Let `z₀ : Y → ℝⁿ` be measurable with `z₀ y ∈ K` for every `y`.

The two formulations of the mean-preservation constraint "the conditional barycenter of `π` is
`z₀`" used in the Dworczak–Kolotilin auxiliary problem are:

* **Set form (SF)**: `∀ A ⊆ Y measurable, ∫ p in A ×ˢ univ, p.2 ∂π = ∫ y in A, z₀ y ∂ν`.
* **Continuous-test form (CTF)**: `∀ φ : Y →ᵇ ℝ, ∫ p, φ p.1 • p.2 ∂π = ∫ y, φ y • z₀ y ∂ν`.

The set form matches `Measure.setIntegral_condKernel` and is the convenient form for
*disintegration* arguments. The continuous-test form is the convenient form for *narrow-topology*
arguments — it is preserved under narrow convergence, since the integrand `p ↦ φ(p.1) • p.2` is
bounded continuous on `Y × K`.

Both forms are equivalent to the *kernel-mean form (KMF)*:

* `∀ᵐ y ∂ν, ∫ x ∂(π.condKernel y) = z₀ y`.

We prove `SF ↔ KMF ↔ CTF`, so that the narrow-topology maximizer-existence argument can use the
continuous-test form internally while the rest of the development keeps the set-based admissibility
predicate.

## Main statements

* `meanPreservation_set_iff_contTest`: The set form of vector-valued mean preservation is
  equivalent to the continuous-test form, established through the intermediate kernel-mean form.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Appendix A.10.

## Tags

mean preservation, disintegration, conditional kernel, barycenter, narrow topology, persuasion
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization

open MeasureTheory Set ProbabilityTheory
open scoped Topology BoundedContinuousFunction ENNReal

variable {n : ℕ} {Y : Type*} [MeasurableSpace Y]

/-- Integrability of `(y, x) ↦ f(y) • x` against `π` when `f` is integrable against the first
marginal `ν = π.fst` of `π` and `π` is supported on `Y × K` for a compact `K`. -/
private lemma integrable_proj_smul_snd
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    (ν : Measure Y) [IsFiniteMeasure ν]
    {π : Measure (Y × EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure π]
    (hπ_fst : π.fst = ν)
    (hπ_supp_K : ∀ᵐ p ∂π, p.2 ∈ K)
    {f : Y → ℝ} (hf_int : Integrable f ν) :
    Integrable (fun p : Y × EuclideanSpace ℝ (Fin n) => f p.1 • p.2) π := by
  obtain ⟨M, hM_K⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M :=
    hK_compact.isBounded.exists_norm_le
  have hf_comp : Integrable (fun p : Y × EuclideanSpace ℝ (Fin n) => f p.1) π := by
    have h_map : Integrable f (π.map Prod.fst) := by
      have : π.map Prod.fst = ν := hπ_fst
      rw [this]; exact hf_int
    exact h_map.comp_measurable measurable_fst
  have h_bd : ∀ᵐ p ∂π, ‖(p.2 : EuclideanSpace ℝ (Fin n))‖ ≤ M := by
    filter_upwards [hπ_supp_K] with p hp; exact hM_K _ hp
  exact hf_comp.smul_bdd M measurable_snd.aestronglyMeasurable h_bd

/-- Integrability of `y ↦ f(y) • z₀(y)` against `ν` when `f` is integrable against `ν` and `z₀` is
bounded. -/
private lemma integrable_smul_z₀
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (hz₀_bdd : ∀ y, z₀ y ∈ K)
    (ν : Measure Y) [IsFiniteMeasure ν]
    {f : Y → ℝ} (hf_int : Integrable f ν) :
    Integrable (fun y => f y • z₀ y) ν := by
  obtain ⟨M, hM_K⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M :=
    hK_compact.isBounded.exists_norm_le
  refine hf_int.smul_bdd M hz₀_meas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun y => hM_K _ (hz₀_bdd y)

/-- `ν`-a.e. the conditional kernel of `π` is supported on `K`, derived from the joint support
hypothesis `hπ_supp_K` via disintegration. -/
private lemma condKernel_ae_ae_mem
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (ν : Measure Y)
    {π : Measure (Y × EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure π]
    (hπ_fst : π.fst = ν)
    (hπ_supp_K : ∀ᵐ p ∂π, p.2 ∈ K) :
    ∀ᵐ y ∂ν, ∀ᵐ x ∂(π.condKernel y), x ∈ K := by
  have h_ae : ∀ᵐ p ∂(π.fst ⊗ₘ π.condKernel), p.2 ∈ K :=
    (π.disintegrate π.condKernel).symm ▸ hπ_supp_K
  have := Measure.ae_ae_of_ae_compProd h_ae
  rwa [hπ_fst] at this

/-- For a probability-measure kernel supported `ν`-a.e. on a set bounded in norm by `M`, the
barycenter `∫ x ∂(π.condKernel y)` is bounded in norm by `M`. -/
private lemma norm_integral_condKernel_le
    {K : Set (EuclideanSpace ℝ (Fin n))} {M : ℝ} (hM_K : ∀ x ∈ K, ‖x‖ ≤ M)
    {π : Measure (Y × EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure π]
    {y : Y} (hy_supp : ∀ᵐ x ∂(π.condKernel y), x ∈ K) :
    ‖∫ x, x ∂(π.condKernel y)‖ ≤ M := by
  have h_bd : ∀ᵐ x ∂(π.condKernel y), ‖x‖ ≤ M := by
    filter_upwards [hy_supp] with x hx; exact hM_K _ hx
  simpa using norm_integral_le_of_norm_le_const (μ := π.condKernel y) h_bd

/-- Bound `‖∫ c y • w y ∂ν‖ ≤ M * δ` from a scalar `c` whose `L¹`-norm is `≤ δ` and a vector field
`w` bounded a.e. by `M ≥ 0`. The integrand is dominated pointwise by `|c y| * M`. -/
private lemma norm_integral_smul_le_of_integral_abs_le
    (ν : Measure Y) {M δ : ℝ} (hM_nonneg : 0 ≤ M)
    {c : Y → ℝ} (hc_int : Integrable c ν) (hc_abs_le : ∫ y, |c y| ∂ν ≤ δ)
    {w : Y → EuclideanSpace ℝ (Fin n)} (hw_aesm : AEStronglyMeasurable w ν)
    (hw_bd : ∀ᵐ y ∂ν, ‖w y‖ ≤ M) :
    ‖∫ y, c y • w y ∂ν‖ ≤ M * δ := by
  have hc_abs_int : Integrable (fun y => |c y|) ν := hc_int.abs
  have h_w_norm_bd : ∀ᵐ y ∂ν, ‖‖w y‖‖ ≤ M := by
    filter_upwards [hw_bd] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hy
  have h_bd_left : Integrable (fun y => |c y| * ‖w y‖) ν :=
    hc_abs_int.mul_bdd hw_aesm.norm h_w_norm_bd
  calc ‖∫ y, c y • w y ∂ν‖
      ≤ ∫ y, ‖c y • w y‖ ∂ν := norm_integral_le_integral_norm _
    _ = ∫ y, |c y| * ‖w y‖ ∂ν := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        change ‖c y • w y‖ = |c y| * ‖w y‖
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∫ y, |c y| * M ∂ν := by
        refine integral_mono_ae h_bd_left (hc_abs_int.mul_const M) ?_
        filter_upwards [hw_bd] with y hy
        exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    _ = M * ∫ y, |c y| ∂ν := by rw [integral_mul_const]; ring
    _ ≤ M * δ := mul_le_mul_of_nonneg_left hc_abs_le hM_nonneg

/-! ## SF ↔ Kernel-mean form -/

/-- The set form of mean preservation implies the kernel-mean form: `ν`-a.e., the conditional
kernel of `π` has barycenter `z₀`. -/
private lemma kernelMean_of_setForm
    [TopologicalSpace Y] [PolishSpace Y]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (hz₀_bdd : ∀ y, z₀ y ∈ K)
    (ν : Measure Y) [IsFiniteMeasure ν]
    {π : Measure (Y × EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure π]
    (hπ_fst : π.fst = ν)
    (hπ_supp_K : ∀ᵐ p ∂π, p.2 ∈ K)
    (hSF : ∀ A : Set Y, MeasurableSet A →
        ∫ p in A ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n))), p.2 ∂π =
          ∫ y in A, z₀ y ∂ν) :
    ∀ᵐ y ∂ν, ∫ x, x ∂(π.condKernel y) = z₀ y := by
  obtain ⟨M, hM_K⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M :=
    hK_compact.isBounded.exists_norm_le
  have h_joint_int : Integrable
      (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2) π := by
    refine Integrable.of_bound measurable_snd.aestronglyMeasurable M ?_
    filter_upwards [hπ_supp_K] with p hp; exact hM_K _ hp
  have h_aesm_inner : AEStronglyMeasurable
      (fun y => ∫ x, x ∂(π.condKernel y)) ν := by
    have := h_joint_int.aestronglyMeasurable.integral_condKernel
    rwa [hπ_fst] at this
  have h_supp_ae : ∀ᵐ y ∂ν, ∀ᵐ x ∂(π.condKernel y), x ∈ K :=
    condKernel_ae_ae_mem ν hπ_fst hπ_supp_K
  have h_int_lhs : Integrable (fun y => ∫ x, x ∂(π.condKernel y)) ν := by
    refine Integrable.of_bound h_aesm_inner M ?_
    filter_upwards [h_supp_ae] with y hy
    exact norm_integral_condKernel_le hM_K hy
  have h_int_z₀ : Integrable z₀ ν :=
    integrable_smul_z₀ hK_compact hz₀_meas hz₀_bdd ν (integrable_const (1 : ℝ))
      |>.congr (by filter_upwards with y; simp)
  have h_setInt_eq : ∀ A : Set Y, MeasurableSet A →
      ∫ y in A, ∫ x, x ∂(π.condKernel y) ∂ν = ∫ y in A, z₀ y ∂ν := by
    intro A hA
    have h_int_on : IntegrableOn
        (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2)
        (A ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))) π :=
      h_joint_int.integrableOn
    have h_eq := Measure.setIntegral_condKernel
      (ρ := π) hA MeasurableSet.univ h_int_on
    simp only [Measure.restrict_univ] at h_eq
    rw [hπ_fst] at h_eq
    rw [h_eq]; exact hSF A hA
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ h_int_lhs h_int_z₀ ?_
  intro A hA _; exact h_setInt_eq A hA

/-- The kernel-mean form of mean preservation implies the set form. -/
private lemma setForm_of_kernelMean
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    -- `z₀` regularity is unused in this direction; kept so all four SF↔KMF↔CTF bridge
    -- lemmas share one signature (directions (a) and (c) below do consume it).
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (_hz₀_meas : Measurable z₀)
    (_hz₀_bdd : ∀ y, z₀ y ∈ K)
    (ν : Measure Y) [IsFiniteMeasure ν]
    {π : Measure (Y × EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure π]
    (hπ_fst : π.fst = ν)
    (hπ_supp_K : ∀ᵐ p ∂π, p.2 ∈ K)
    (hKMF : ∀ᵐ y ∂ν, ∫ x, x ∂(π.condKernel y) = z₀ y) :
    ∀ A : Set Y, MeasurableSet A →
        ∫ p in A ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n))), p.2 ∂π =
          ∫ y in A, z₀ y ∂ν := by
  intro A hA
  obtain ⟨M, hM_K⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M :=
    hK_compact.isBounded.exists_norm_le
  have h_joint_int : Integrable
      (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2) π := by
    refine Integrable.of_bound measurable_snd.aestronglyMeasurable M ?_
    filter_upwards [hπ_supp_K] with p hp; exact hM_K _ hp
  have h_int_on : IntegrableOn
      (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2)
      (A ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n)))) π :=
    h_joint_int.integrableOn
  have h_eq := Measure.setIntegral_condKernel
    (ρ := π) hA MeasurableSet.univ h_int_on
  simp only [Measure.restrict_univ] at h_eq
  rw [hπ_fst] at h_eq
  rw [← h_eq]
  refine setIntegral_congr_ae hA ?_
  filter_upwards [hKMF] with y hy
  intro _; exact hy

/-! ## CTF ↔ Kernel-mean form -/

/-- The kernel-mean form of mean preservation implies the continuous-test form. -/
private lemma contTest_of_kernelMean
    [TopologicalSpace Y] [BorelSpace Y]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    -- `z₀` regularity is unused in this direction; kept so all four SF↔KMF↔CTF bridge
    -- lemmas share one signature (directions (a) and (c) below do consume it).
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (_hz₀_meas : Measurable z₀)
    (_hz₀_bdd : ∀ y, z₀ y ∈ K)
    (ν : Measure Y) [IsFiniteMeasure ν]
    {π : Measure (Y × EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure π]
    (hπ_fst : π.fst = ν)
    (hπ_supp_K : ∀ᵐ p ∂π, p.2 ∈ K)
    (hKMF : ∀ᵐ y ∂ν, ∫ x, x ∂(π.condKernel y) = z₀ y) :
    ∀ φ : Y →ᵇ ℝ,
        ∫ p, φ p.1 • p.2 ∂π = ∫ y, φ y • z₀ y ∂ν := by
  intro φ
  obtain ⟨M, hM_K⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M :=
    hK_compact.isBounded.exists_norm_le
  have hφ_int : Integrable (⇑φ) ν := φ.integrable ν
  have h_lhs_int : Integrable
      (fun p : Y × EuclideanSpace ℝ (Fin n) => φ p.1 • p.2) π :=
    integrable_proj_smul_snd hK_compact ν hπ_fst hπ_supp_K hφ_int
  have h_supp_ae_πfst : ∀ᵐ y ∂π.fst, ∀ᵐ x ∂(π.condKernel y), x ∈ K := by
    rw [hπ_fst]; exact condKernel_ae_ae_mem ν hπ_fst hπ_supp_K
  -- Disintegrate the joint integral over the kernel.
  calc ∫ p, φ p.1 • p.2 ∂π
      = ∫ p, φ p.1 • p.2 ∂(π.fst ⊗ₘ π.condKernel) := by
        rw [π.disintegrate π.condKernel]
    _ = ∫ y, ∫ x, φ y • x ∂(π.condKernel y) ∂(π.fst) := by
        rw [Measure.integral_compProd]
        rwa [π.disintegrate π.condKernel]
    _ = ∫ y, φ y • ∫ x, x ∂(π.condKernel y) ∂π.fst := by
        refine integral_congr_ae ?_
        filter_upwards [h_supp_ae_πfst] with y hy_supp
        exact integral_smul ..
    _ = ∫ y, φ y • z₀ y ∂ν := by
        rw [hπ_fst]
        refine integral_congr_ae ?_
        filter_upwards [hKMF] with y hy; rw [hy]

/-- The continuous-test form of mean preservation implies the kernel-mean form: `ν`-a.e., the
conditional kernel of `π` has barycenter `z₀`. -/
private lemma kernelMean_of_contTest
    [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (hz₀_bdd : ∀ y, z₀ y ∈ K)
    (ν : Measure Y) [IsFiniteMeasure ν]
    {π : Measure (Y × EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure π]
    (hπ_fst : π.fst = ν)
    (hπ_supp_K : ∀ᵐ p ∂π, p.2 ∈ K)
    (hCTF : ∀ φ : Y →ᵇ ℝ,
        ∫ p, φ p.1 • p.2 ∂π = ∫ y, φ y • z₀ y ∂ν) :
    ∀ᵐ y ∂ν, ∫ x, x ∂(π.condKernel y) = z₀ y := by
  -- Choose `M > 0` bounding `K`, so that the positivity needed by the ε-argument is available.
  obtain ⟨M, hM_pos, hM_K⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ K, ‖x‖ ≤ M := by
    obtain ⟨M, hM_K⟩ := hK_compact.isBounded.exists_norm_le
    exact ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun x hx => (hM_K x hx).trans (le_max_left _ _)⟩
  set g : Y → EuclideanSpace ℝ (Fin n) := fun y => ∫ x, x ∂(π.condKernel y)
    with hg_def
  have h_supp_ae : ∀ᵐ y ∂ν, ∀ᵐ x ∂(π.condKernel y), x ∈ K :=
    condKernel_ae_ae_mem ν hπ_fst hπ_supp_K
  have h_supp_ae_πfst : ∀ᵐ y ∂π.fst, ∀ᵐ x ∂(π.condKernel y), x ∈ K := by
    rw [hπ_fst]; exact h_supp_ae
  have hg_bdd : ∀ᵐ y ∂ν, ‖g y‖ ≤ M := by
    filter_upwards [h_supp_ae] with y hy_supp
    exact norm_integral_condKernel_le hM_K hy_supp
  have h_snd_int : Integrable (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2) π := by
    refine Integrable.of_bound measurable_snd.aestronglyMeasurable M ?_
    filter_upwards [hπ_supp_K] with p hp; exact hM_K _ hp
  have hg_aesm : AEStronglyMeasurable g ν := by
    have := h_snd_int.aestronglyMeasurable.integral_condKernel
    rwa [hπ_fst] at this
  have hg_int : Integrable g ν := Integrable.of_bound hg_aesm M hg_bdd
  have hz₀_bd : ∀ᵐ y ∂ν, ‖z₀ y‖ ≤ M :=
    Filter.Eventually.of_forall fun y => hM_K _ (hz₀_bdd y)
  have hz₀_int : Integrable z₀ ν :=
    Integrable.of_bound hz₀_meas.aestronglyMeasurable M hz₀_bd
  -- Bridge identity: `∀ φ ∈ Cb, ∫ y, φ y • g y ∂ν = ∫ y, φ y • z₀ y ∂ν`.
  have h_bridge : ∀ φ : Y →ᵇ ℝ,
      ∫ y, φ y • g y ∂ν = ∫ y, φ y • z₀ y ∂ν := by
    intro φ
    have hφ_int : Integrable (⇑φ) ν := φ.integrable ν
    have h_lhs_int : Integrable
        (fun p : Y × EuclideanSpace ℝ (Fin n) => φ p.1 • p.2) π :=
      integrable_proj_smul_snd hK_compact ν hπ_fst hπ_supp_K hφ_int
    calc ∫ y, φ y • g y ∂ν
        = ∫ y, φ y • ∫ x, x ∂(π.condKernel y) ∂π.fst := by rw [hπ_fst]
      _ = ∫ y, ∫ x, φ y • x ∂(π.condKernel y) ∂π.fst := by
          refine integral_congr_ae ?_
          filter_upwards [h_supp_ae_πfst] with y _hy
          exact (integral_smul ..).symm
      _ = ∫ p, φ p.1 • p.2 ∂(π.fst ⊗ₘ π.condKernel) := by
          rw [Measure.integral_compProd]
          rwa [π.disintegrate π.condKernel]
      _ = ∫ p, φ p.1 • p.2 ∂π := by rw [π.disintegrate π.condKernel]
      _ = ∫ y, φ y • z₀ y ∂ν := hCTF φ
  -- For each measurable A with finite measure, `∫_A g dν = ∫_A z₀ dν`.
  have h_setInt_eq : ∀ A : Set Y, MeasurableSet A → ν A < ∞ →
      ∫ y in A, g y ∂ν = ∫ y in A, z₀ y ∂ν := by
    intro A hA _hA_fin
    set IA : Y → ℝ := A.indicator fun _ => (1 : ℝ) with hIA_def
    have h_IA_meas : Measurable IA :=
      Measurable.indicator measurable_const hA
    have h_IA_bd : ∀ y, |IA y| ≤ 1 := by
      intro y
      by_cases hy : y ∈ A
      · simp [IA, Set.indicator_of_mem hy]
      · simp [IA, Set.indicator_of_notMem hy]
    have h_IA_int : Integrable IA ν := by
      refine Integrable.of_bound h_IA_meas.aestronglyMeasurable 1 ?_
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs]; exact h_IA_bd y
    have h_ind_smul_g : ∀ y, A.indicator g y = IA y • g y := by
      intro y
      by_cases hy : y ∈ A
      · simp [IA, Set.indicator_of_mem hy]
      · simp [IA, Set.indicator_of_notMem hy]
    have h_ind_smul_z₀ : ∀ y, A.indicator z₀ y = IA y • z₀ y := by
      intro y
      by_cases hy : y ∈ A
      · simp [IA, Set.indicator_of_mem hy]
      · simp [IA, Set.indicator_of_notMem hy]
    have h_setInt_g : ∫ y in A, g y ∂ν = ∫ y, IA y • g y ∂ν := by
      rw [← integral_indicator hA]
      exact integral_congr_ae (Filter.Eventually.of_forall h_ind_smul_g)
    have h_setInt_z₀ : ∫ y in A, z₀ y ∂ν = ∫ y, IA y • z₀ y ∂ν := by
      rw [← integral_indicator hA]
      exact integral_congr_ae (Filter.Eventually.of_forall h_ind_smul_z₀)
    rw [h_setInt_g, h_setInt_z₀]
    have h_IAg_int : Integrable (fun y => IA y • g y) ν :=
      h_IA_int.smul_bdd M hg_aesm hg_bdd
    have h_IAz₀_int : Integrable (fun y => IA y • z₀ y) ν :=
      h_IA_int.smul_bdd M hz₀_meas.aestronglyMeasurable hz₀_bd
    -- ε-argument: bound the difference of integrals by any ε > 0.
    have h_norm_zero :
        ‖∫ y, IA y • g y ∂ν - ∫ y, IA y • z₀ y ∂ν‖ = 0 := by
      refine le_antisymm ?_ (norm_nonneg _)
      refine le_of_forall_pos_le_add fun ε hε => ?_
      rw [zero_add]
      set δ : ℝ := ε / (2 * M + 1) with hδ_def
      have h_denom : 0 < 2 * M + 1 := by linarith
      have hδ_pos : 0 < δ := by positivity
      obtain ⟨φ, hφ_bd, _hφ_int⟩ :=
        h_IA_int.exists_boundedContinuous_integral_sub_le hδ_pos
      have hφ_int : Integrable (⇑φ) ν := φ.integrable ν
      have h_φg_int : Integrable (fun y => φ y • g y) ν :=
        hφ_int.smul_bdd M hg_aesm hg_bdd
      have h_φz₀_int : Integrable (fun y => φ y • z₀ y) ν :=
        hφ_int.smul_bdd M hz₀_meas.aestronglyMeasurable hz₀_bd
      have h_bridge_φ : ∫ y, φ y • g y ∂ν = ∫ y, φ y • z₀ y ∂ν := h_bridge φ
      -- Telescope `LHS - RHS = (LHS - bridgeL) + (bridgeR - RHS)`.
      have h_eq_telescope :
          ∫ y, IA y • g y ∂ν - ∫ y, IA y • z₀ y ∂ν =
            (∫ y, IA y • g y ∂ν - ∫ y, φ y • g y ∂ν) +
            (∫ y, φ y • z₀ y ∂ν - ∫ y, IA y • z₀ y ∂ν) := by
        rw [h_bridge_φ]; abel
      have h_sub_g :
          ∫ y, IA y • g y ∂ν - ∫ y, φ y • g y ∂ν =
            ∫ y, (IA y - φ y) • g y ∂ν := by
        rw [← integral_sub h_IAg_int h_φg_int]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact (sub_smul _ _ _).symm
      have h_sub_z₀ :
          ∫ y, φ y • z₀ y ∂ν - ∫ y, IA y • z₀ y ∂ν =
            ∫ y, (φ y - IA y) • z₀ y ∂ν := by
        rw [← integral_sub h_φz₀_int h_IAz₀_int]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        exact (sub_smul _ _ _).symm
      rw [h_eq_telescope, h_sub_g, h_sub_z₀]
      have h_abs_le : ∫ y, |IA y - φ y| ∂ν ≤ δ := by
        simpa only [Real.norm_eq_abs] using hφ_bd
      have h_bd1 : ‖∫ y, (IA y - φ y) • g y ∂ν‖ ≤ M * δ :=
        norm_integral_smul_le_of_integral_abs_le ν hM_pos.le (h_IA_int.sub hφ_int)
          h_abs_le hg_aesm hg_bdd
      have h_abs_le' : ∫ y, |φ y - IA y| ∂ν ≤ δ := by
        simp only [abs_sub_comm (φ _) (IA _)]; exact h_abs_le
      have h_bd2 : ‖∫ y, (φ y - IA y) • z₀ y ∂ν‖ ≤ M * δ :=
        norm_integral_smul_le_of_integral_abs_le ν hM_pos.le (hφ_int.sub h_IA_int)
          h_abs_le' hz₀_meas.aestronglyMeasurable hz₀_bd
      calc ‖(∫ y, (IA y - φ y) • g y ∂ν) + ∫ y, (φ y - IA y) • z₀ y ∂ν‖
          ≤ ‖∫ y, (IA y - φ y) • g y ∂ν‖ + ‖∫ y, (φ y - IA y) • z₀ y ∂ν‖ :=
            norm_add_le _ _
        _ ≤ M * δ + M * δ := add_le_add h_bd1 h_bd2
        _ = 2 * M * δ := by ring
        _ ≤ ε := by
            rw [hδ_def]
            have h_rw : 2 * M * (ε / (2 * M + 1)) = (2 * M / (2 * M + 1)) * ε := by
              field_simp
            rw [h_rw]
            have h_frac : 2 * M / (2 * M + 1) ≤ 1 := by
              rw [div_le_one h_denom]; linarith
            nlinarith [hε.le, hM_pos.le]
    exact sub_eq_zero.mp (norm_eq_zero.mp h_norm_zero)
  exact Integrable.ae_eq_of_forall_setIntegral_eq _ _ hg_int hz₀_int h_setInt_eq

/-- The set form of vector-valued mean preservation is equivalent to the continuous-test form, via
the intermediate kernel-mean form. -/
lemma meanPreservation_set_iff_contTest
    [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (hz₀_bdd : ∀ y, z₀ y ∈ K)
    (ν : Measure Y) [IsFiniteMeasure ν]
    {π : Measure (Y × EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure π]
    (hπ_fst : π.fst = ν)
    (hπ_supp_K : ∀ᵐ p ∂π, p.2 ∈ K) :
    (∀ A : Set Y, MeasurableSet A →
       ∫ p in A ×ˢ (univ : Set (EuclideanSpace ℝ (Fin n))), p.2 ∂π =
         ∫ y in A, z₀ y ∂ν) ↔
    (∀ φ : Y →ᵇ ℝ,
       ∫ p, φ p.1 • p.2 ∂π = ∫ y, φ y • z₀ y ∂ν) := by
  refine ⟨fun hSF => ?_, fun hCTF => ?_⟩
  · -- SF → KMF → CTF.
    exact contTest_of_kernelMean hK_compact hz₀_meas hz₀_bdd ν hπ_fst hπ_supp_K
      (kernelMean_of_setForm hK_compact hz₀_meas hz₀_bdd ν hπ_fst hπ_supp_K hSF)
  · -- CTF → KMF → SF.
    exact setForm_of_kernelMean hK_compact hz₀_meas hz₀_bdd ν hπ_fst hπ_supp_K
      (kernelMean_of_contTest hK_compact hz₀_meas hz₀_bdd ν hπ_fst hπ_supp_K hCTF)

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization
