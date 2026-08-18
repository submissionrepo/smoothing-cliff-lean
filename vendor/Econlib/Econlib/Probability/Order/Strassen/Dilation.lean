/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Order.Strassen.Basic

/-!
# Dilation / kernel formulation of martingale couplings

This file gives a kernel-level reformulation of `IsMartingaleCoupling`. A **mean-preserving Markov
kernel** `K : ℝ → ℝ` for `μ` is a Markov kernel with integrable second coordinate whose fiber `K x`
has barycentre `x` for `μ`-a.e. `x` (note this does not reference `ν`). The correspondence runs in
both directions for a fixed coupling: Every martingale coupling `π` of `μ, ν` disintegrates as
`π = μ ⊗ K` with `K` its `condKernel` (which is mean-preserving), and conversely the dilation
`μ ⊗ K` of any mean-preserving `K` is a martingale coupling between `μ` and its second marginal
`∫ K x ∂μ`. Taking second marginals lifts these two directions to an existence equivalence: A
martingale coupling of `(μ, ν)` exists iff some mean-preserving kernel `K` for `μ` has `μ`-average
`ν`.

## Main definitions

* `IsMeanPreservingKernel μ K` — `K : Kernel ℝ ℝ` is a Markov kernel and `∀ᵐ x ∂μ, ∫ y ∂(K x) = x`.
* `ProbDist.dilation μ K` — the joint distribution `μ ⊗ K` as a `ProbDist`.

## Main statements

* `IsMartingaleCoupling.exists_meanPreservingKernel` — every martingale coupling admits a
  mean-preserving kernel representation.
* `IsMeanPreservingKernel.dilation_isMartingaleCoupling` — the dilation of a mean-preserving kernel
  is a martingale coupling between its first and second marginals.
* `isMartingaleCoupling_iff_dilation` — a martingale coupling of `(μ, ν)` exists iff some
  mean-preserving kernel `K` for `μ` has second marginal `ν`.

## Notes

The dilation formulation is often easier to construct directly, e.g. from a Markov chain transition
rule or an explicit mean-zero noise mechanism, and matches the economic reading of `ν` as `μ` plus
conditionally mean-zero noise.

## References

* Strassen, V. 1965. “The Existence of Probability Measures with Given Marginals.” *The Annals of
  Mathematical Statistics* 36 (2): 423–39. [https://doi.org/10.1214/aoms/1177700153](https://doi.org/10.1214/aoms/1177700153).

## Tags

strassen, martingale coupling, dilation, mean-preserving kernel, markov kernel
-/

@[expose] public section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace Econlib.Probability

/-- A **mean-preserving Markov kernel** for `μ`: A Markov kernel `K : ℝ → ℝ` whose joint law
`μ ⊗ K` has an integrable second coordinate and whose fiber `K x` has barycentre equal to `x` for
`μ`-a.e. `x`. -/
structure IsMeanPreservingKernel (μ : ProbDist ℝ) (K : Kernel ℝ ℝ) : Prop where
  /-- Each fiber `K x` is a probability measure. -/
  markov : IsMarkovKernel K
  /-- The second coordinate of the dilation `μ ⊗ K` has finite first moment; equivalently
  `∫ |y| ∂(K x)` is finite for μ-a.e. `x` and is integrable against μ. -/
  integrable_snd : haveI := markov;
    Integrable (fun p : ℝ × ℝ => p.2) (μ.toMeasure.compProd K)
  /-- The barycentre of the fiber equals the base point. -/
  ae_mean_eq : ∀ᵐ x ∂μ.toMeasure, ∫ y, y ∂(K x) = x

namespace ProbDist

/-- The **dilation** of `μ` by a Markov kernel `K`: The joint law `μ ⊗ K`. -/
noncomputable def dilation (μ : ProbDist ℝ) (K : Kernel ℝ ℝ) [IsMarkovKernel K] :
    ProbDist (ℝ × ℝ) :=
  ⟨μ.toMeasure.compProd K, by infer_instance⟩

@[simp] lemma dilation_toMeasure (μ : ProbDist ℝ) (K : Kernel ℝ ℝ) [IsMarkovKernel K] :
    (dilation μ K).toMeasure = μ.toMeasure.compProd K := rfl

/-- The `Prod.fst`-marginal of a dilation recovers `μ`. -/
lemma dilation_fst (μ : ProbDist ℝ) (K : Kernel ℝ ℝ) [IsMarkovKernel K] :
    (ProbDist.map (dilation μ K) Prod.fst measurable_fst) = μ := by
  -- `(μ ⊗ K).map Prod.fst = μ` because `K` is Markov (each fibre has total mass 1).
  apply ProbabilityMeasure.toMeasure_injective
  show ((ProbDist.map (dilation μ K) Prod.fst measurable_fst) : Measure ℝ) = (μ : Measure ℝ)
  rw [ProbDist.map_toMeasure, dilation_toMeasure]
  exact (MeasureTheory.Measure.fst_compProd μ.toMeasure K : _)

end ProbDist

namespace IsMeanPreservingKernel

variable {μ : ProbDist ℝ} {K : Kernel ℝ ℝ}

/-- The `snd`-marginal of the dilation `μ ⊗ K`, viewed as a `ProbDist ℝ`. -/
noncomputable def snd (h : IsMeanPreservingKernel μ K) : ProbDist ℝ :=
  haveI := h.markov
  ProbDist.map (ProbDist.dilation μ K) Prod.snd measurable_snd

/-- Fiber mean `x ↦ ∫ y ∂K x` is integrable against `μ`, derived from `integrable_snd`. -/
lemma integrable_mean (h : IsMeanPreservingKernel μ K) :
    Integrable (fun x => ∫ y, y ∂(K x)) μ.toMeasure := by
  haveI := h.markov
  -- Disintegrate `integrable_snd`: fibrewise integrability of `id` and of `‖·‖`.
  have hcompProd := (MeasureTheory.Measure.integrable_compProd_iff
    measurable_snd.aestronglyMeasurable).mp h.integrable_snd
  have hfib : ∀ᵐ x ∂μ.toMeasure, Integrable (fun y => y) (K x) := hcompProd.1
  have hnorm_int : Integrable (fun x => ∫ y, ‖y‖ ∂(K x)) μ.toMeasure := hcompProd.2
  -- |∫ y ∂K x| ≤ ∫ ‖y‖ ∂K x. Measurability of `x ↦ ∫ y ∂K x`.
  have hmeas : AEStronglyMeasurable (fun x => ∫ y, y ∂(K x)) μ.toMeasure :=
    (StronglyMeasurable.integral_kernel (κ := K) stronglyMeasurable_id).aestronglyMeasurable
  refine hnorm_int.mono' hmeas ?_
  filter_upwards [hfib] with x hxint
  simpa [Real.norm_eq_abs] using (abs_integral_le_integral_abs : |∫ y, y ∂(K x)| ≤ _)

/-- A mean-preserving kernel dilation is a martingale coupling between its first marginal and its
second marginal. -/
lemma dilation_isMartingaleCoupling (h : IsMeanPreservingKernel μ K) :
    IsMartingaleCoupling μ h.snd (haveI := h.markov; ProbDist.dilation μ K) := by
  haveI := h.markov
  -- First deduce `Integrable id μ` from `integrable_mean` and `ae_mean_eq`.
  have h_id_int : Integrable (fun x : ℝ => x) μ.toMeasure := by
    have hcong : (fun x => ∫ y, y ∂(K x)) =ᵐ[μ.toMeasure] (fun x : ℝ => x) :=
      h.ae_mean_eq
    exact (integrable_congr hcong).mp h.integrable_mean
  -- `Integrable (p ↦ p.1)` against the dilation, via `integrable_compProd_iff`.
  have h_fst_int : Integrable (fun p : ℝ × ℝ => p.1) (ProbDist.dilation μ K).toMeasure := by
    rw [ProbDist.dilation_toMeasure]
    refine (MeasureTheory.Measure.integrable_compProd_iff
      (measurable_fst.aestronglyMeasurable)).mpr ⟨?_, ?_⟩
    · refine Filter.Eventually.of_forall fun x => ?_
      -- (fun y => (x, y).1) = const x, integrable since K x is a finite measure
      exact (integrable_const x)
    · -- inner ∫ ‖x‖ ∂K x = ‖x‖ since K x is probability
      have hnorm : (fun x => ∫ y, ‖(x, y).1‖ ∂(K x)) = (fun x : ℝ => ‖x‖) := by
        funext x; simp [integral_const]
      rw [hnorm]; exact h_id_int.norm
  -- `Integrable (p ↦ p.2)` against the dilation is a direct field of `h`.
  have h_snd_int : Integrable (fun p : ℝ × ℝ => p.2) (ProbDist.dilation μ K).toMeasure := by
    rw [ProbDist.dilation_toMeasure]; exact h.integrable_snd
  refine ⟨?_, ?_, h_fst_int, h_snd_int, ?_⟩
  · exact ProbDist.dilation_fst μ K
  · rfl
  · -- Martingale identity: ∫ (p.2 - p.1) φ p.1 d(μ ⊗ K) = 0.
    intro φ hφ hφ_bdd
    obtain ⟨M, hM⟩ := hφ_bdd
    have hMnn : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
    -- Integrability of (p ↦ φ p.1) against the dilation: bounded by M.
    have hφπ_int : Integrable (fun p : ℝ × ℝ => φ p.1) (ProbDist.dilation μ K).toMeasure := by
      have h_meas : AEStronglyMeasurable (fun p : ℝ × ℝ => φ p.1)
          (ProbDist.dilation μ K).toMeasure :=
        (hφ.comp measurable_fst).aestronglyMeasurable
      refine Integrable.mono' (g := fun _ : ℝ × ℝ => M) ?_ h_meas ?_
      · exact integrable_const M
      · filter_upwards with p
        simpa [Real.norm_eq_abs] using hM p.1
    -- Integrability of the integrand (p.2 - p.1) * φ p.1 on μ ⊗ K.
    have h_prod_int : Integrable
        (fun p : ℝ × ℝ => (p.2 - p.1) * φ p.1) (ProbDist.dilation μ K).toMeasure := by
      have h_diff_int : Integrable (fun p : ℝ × ℝ => p.2 - p.1)
          (ProbDist.dilation μ K).toMeasure := h_snd_int.sub h_fst_int
      have hmul_comm : Integrable (fun p : ℝ × ℝ => φ p.1 * (p.2 - p.1))
          (ProbDist.dilation μ K).toMeasure :=
        h_diff_int.bdd_mul (c := M) hφπ_int.aestronglyMeasurable
          (Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hM p.1)
      have heq : (fun p : ℝ × ℝ => (p.2 - p.1) * φ p.1) =
          (fun p : ℝ × ℝ => φ p.1 * (p.2 - p.1)) := by
        funext p; ring
      rw [heq]; exact hmul_comm
    -- Split integrand via integral_compProd.
    rw [ProbDist.dilation_toMeasure, MeasureTheory.Measure.integral_compProd h_prod_int]
    -- Inner integral: ∫ y, (y - x) * φ x ∂K x = φ x * ((∫ y, y ∂K x) - x).
    have h_inner : ∀ᵐ x ∂μ.toMeasure,
        ∫ y, (y - x) * φ x ∂(K x) = φ x * ((∫ y, y ∂(K x)) - x) := by
      -- Need fibre-integrability of `y ↦ y` from integrable_snd.
      have hfib_int : ∀ᵐ x ∂μ.toMeasure, Integrable (fun y => y) (K x) :=
        ((MeasureTheory.Measure.integrable_compProd_iff
          (measurable_snd.aestronglyMeasurable)).mp h.integrable_snd).1
      filter_upwards [hfib_int] with x hxint
      calc ∫ y, (y - x) * φ x ∂(K x)
          = ∫ y, φ x * (y - x) ∂(K x) := by congr 1; ext y; ring
        _ = φ x * ∫ y, (y - x) ∂(K x) := by rw [integral_const_mul]
        _ = φ x * ((∫ y, y ∂(K x)) - x) := by
            rw [integral_sub hxint (integrable_const x), integral_const, probReal_univ, one_smul]
    -- Apply `ae_mean_eq` to simplify further to 0.
    have h_inner_zero : ∀ᵐ x ∂μ.toMeasure, ∫ y, (y - x) * φ x ∂(K x) = 0 := by
      filter_upwards [h_inner, h.ae_mean_eq] with x hx hmean
      rw [hx, hmean, sub_self, mul_zero]
    -- The outer integral is 0.
    rw [MeasureTheory.integral_congr_ae h_inner_zero, integral_zero]

end IsMeanPreservingKernel

namespace IsMartingaleCoupling

variable {μ ν : ProbDist ℝ} {π : ProbDist (ℝ × ℝ)}

/-- Any martingale coupling admits a mean-preserving kernel representation (its `condKernel` over
the first marginal). -/
lemma exists_meanPreservingKernel (h : IsMartingaleCoupling μ ν π) :
    ∃ K : Kernel ℝ ℝ, IsMeanPreservingKernel μ K ∧
      ∀ᵐ x ∂μ.toMeasure, (π.toMeasure.condKernel x = K x) := by
  refine ⟨π.toMeasure.condKernel, ?_, Filter.Eventually.of_forall fun _ => rfl⟩
  -- Markov instance (for ℝ, which is standard Borel).
  have h_markov : IsMarkovKernel π.toMeasure.condKernel := by infer_instance
  -- integrable_snd for the disintegrated measure equals the original via
  -- `Measure.disintegrate`.
  have h_disint : π.toMeasure.fst.compProd π.toMeasure.condKernel = π.toMeasure :=
    π.toMeasure.disintegrate _
  have hfst : π.toMeasure.fst = μ.toMeasure := h.fst_measure
  refine
    { markov := h_markov,
      integrable_snd := ?_,
      ae_mean_eq := ?_ }
  · -- `Integrable (p ↦ p.2) (μ ⊗ condKernel)` = `Integrable (p ↦ p.2) π`
    rw [← hfst, h_disint]; exact h.integrable_snd
  · exact h.ae_conditional_mean_eq

end IsMartingaleCoupling

/-- Equivalence: Martingale couplings of `(μ, ν)` correspond exactly to mean-preserving kernels `K`
whose dilation has `ν` as its second marginal. -/
lemma isMartingaleCoupling_iff_dilation (μ ν : ProbDist ℝ) :
    (∃ π : ProbDist (ℝ × ℝ), IsMartingaleCoupling μ ν π) ↔
    ∃ K : Kernel ℝ ℝ, ∃ h : IsMeanPreservingKernel μ K, h.snd = ν := by
  refine ⟨?_, ?_⟩
  · -- Forward: `IsMartingaleCoupling.exists_meanPreservingKernel`.
    rintro ⟨π, hπ⟩
    obtain ⟨K, hK, hcond⟩ := hπ.exists_meanPreservingKernel
    refine ⟨K, hK, ?_⟩
    -- `hK.snd = (μ ⊗ K).map Prod.snd`. Show `(μ ⊗ K).toMeasure = π.toMeasure`
    -- because `K =ᵐ[μ] π.condKernel` and `π.fst.compProd π.condKernel = π`.
    apply ProbabilityMeasure.toMeasure_injective
    show (hK.snd : Measure ℝ) = (ν : Measure ℝ)
    haveI := hK.markov
    -- `μ ⊗ K = μ ⊗ condKernel = π.fst ⊗ condKernel = π`.
    have h_disint : π.toMeasure.fst.compProd π.toMeasure.condKernel = π.toMeasure :=
      π.toMeasure.disintegrate _
    have hfst : π.toMeasure.fst = μ.toMeasure := hπ.fst_measure
    have hcond_eq : μ.toMeasure.compProd K = π.toMeasure := by
      -- Use `compProd_congr` / ae-equality of kernels.
      have h_ae : K =ᵐ[μ.toMeasure] π.toMeasure.condKernel := by
        filter_upwards [hcond] with x hx; exact hx.symm
      calc μ.toMeasure.compProd K
          = μ.toMeasure.compProd π.toMeasure.condKernel :=
            MeasureTheory.Measure.compProd_congr h_ae
        _ = π.toMeasure.fst.compProd π.toMeasure.condKernel := by rw [hfst]
        _ = π.toMeasure := h_disint
    change ((ProbDist.map (ProbDist.dilation μ K) Prod.snd measurable_snd) : Measure ℝ)
        = (ν : Measure ℝ)
    rw [ProbDist.map_toMeasure, ProbDist.dilation_toMeasure, hcond_eq]
    exact hπ.snd_measure
  · -- Reverse: `IsMeanPreservingKernel.dilation_isMartingaleCoupling`.
    rintro ⟨K, hK, hν⟩
    haveI := hK.markov
    refine ⟨ProbDist.dilation μ K, ?_⟩
    have h_mc := hK.dilation_isMartingaleCoupling
    rw [hν] at h_mc
    exact h_mc

end Econlib.Probability
