/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Projections of a composition-product onto component composition-products

For a measure `μ` and a product kernel `κ.prod η`, the joint **composition-product**
`μ.compProd (κ.prod η)` lives on `α × (β × γ)`. Projecting it onto the first (respectively second)
component of the pair recovers the component composition-products `μ.compProd κ` (respectively
`μ.compProd η`).

## Main statements

* `MeasureTheory.measure_map_compProd_kernel_prod_fst` — the pushforward along
  `(a, (b, c)) ↦ (a, b)` equals `μ.compProd κ`.
* `MeasureTheory.measure_map_compProd_kernel_prod_snd` — the pushforward along
  `(a, (b, c)) ↦ (a, c)` equals `μ.compProd η`.

## Tags

composition-product, kernel, product kernel, pushforward, marginal
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory

/-- Pushing the composition-product `μ.compProd (κ.prod η)` forward along `(a, (b, c)) ↦ (a, b)`
recovers the first component composition-product `μ.compProd κ`. The second kernel `η` is assumed
Markov so that its fiber mass is `1` and cancels under the projection. -/
lemma measure_map_compProd_kernel_prod_fst {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsSFiniteKernel κ]
    (η : Kernel α γ) [IsMarkovKernel η] :
    Measure.map (fun p : α × (β × γ) => (p.1, p.2.1)) (μ.compProd (κ.prod η))
      = μ.compProd κ := by
  apply Measure.ext
  intro s hs
  have hf : Measurable (fun p : α × (β × γ) => (p.1, p.2.1)) := by
    refine Measurable.prod ?_ ?_
    · exact measurable_fst
    · exact (measurable_fst : Measurable (fun p : β × γ => p.1)).comp measurable_snd
  rw [Measure.map_apply hf hs]
  rw [Measure.compProd_apply (hs.preimage hf)]
  rw [Measure.compProd_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards with a
  have hsec :
      {p : β × γ | (a, p.1) ∈ s} = Prod.fst ⁻¹' {b : β | (a, b) ∈ s} := by
    rfl
  change ((κ.prod η) a) {p : β × γ | (a, p.1) ∈ s}
      = (κ a) {b : β | (a, b) ∈ s}
  rw [hsec]
  have hssec : MeasurableSet {b : β | (a, b) ∈ s} := by
    have hpair : Measurable (fun b : β => (a, b)) := by
      refine Measurable.prod ?_ ?_
      · exact measurable_const
      · exact measurable_id
    exact hs.preimage hpair
  calc ((κ.prod η) a) (Prod.fst ⁻¹' {b : β | (a, b) ∈ s})
      = ((κ.prod η).fst a) {b : β | (a, b) ∈ s} := by
        exact (Kernel.fst_apply' (κ.prod η) a hssec).symm
    _ = (κ a) {b : β | (a, b) ∈ s} := by
        rw [Kernel.fst_prod]

/-- Pushing the composition-product `μ.compProd (κ.prod η)` forward along `(a, (b, c)) ↦ (a, c)`
recovers the second component composition-product `μ.compProd η`. The first kernel `κ` is assumed
Markov so that its fiber mass is `1` and cancels under the projection. -/
lemma measure_map_compProd_kernel_prod_snd {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [SFinite μ]
    (κ : Kernel α β) [IsMarkovKernel κ]
    (η : Kernel α γ) [IsSFiniteKernel η] :
    Measure.map (fun p : α × (β × γ) => (p.1, p.2.2)) (μ.compProd (κ.prod η))
      = μ.compProd η := by
  apply Measure.ext
  intro s hs
  have hf : Measurable (fun p : α × (β × γ) => (p.1, p.2.2)) := by
    refine Measurable.prod ?_ ?_
    · exact measurable_fst
    · exact (measurable_snd : Measurable (fun p : β × γ => p.2)).comp measurable_snd
  rw [Measure.map_apply hf hs]
  rw [Measure.compProd_apply (hs.preimage hf)]
  rw [Measure.compProd_apply hs]
  refine lintegral_congr_ae ?_
  filter_upwards with a
  have hsec :
      {p : β × γ | (a, p.2) ∈ s} = Prod.snd ⁻¹' {c : γ | (a, c) ∈ s} := by
    rfl
  change ((κ.prod η) a) {p : β × γ | (a, p.2) ∈ s}
      = (η a) {c : γ | (a, c) ∈ s}
  rw [hsec]
  have hssec : MeasurableSet {c : γ | (a, c) ∈ s} := by
    have hpair : Measurable (fun c : γ => (a, c)) := by
      refine Measurable.prod ?_ ?_
      · exact measurable_const
      · exact measurable_id
    exact hs.preimage hpair
  calc ((κ.prod η) a) (Prod.snd ⁻¹' {c : γ | (a, c) ∈ s})
      = ((κ.prod η).snd a) {c : γ | (a, c) ∈ s} := by
        exact (Kernel.snd_apply' (κ.prod η) a hssec).symm
    _ = (η a) {c : γ | (a, c) ∈ s} := by
        rw [Kernel.snd_prod]

end MeasureTheory
