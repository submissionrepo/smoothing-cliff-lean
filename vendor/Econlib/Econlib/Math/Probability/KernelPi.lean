/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib

/-!
# Finite products of Markov kernels

Mathlib has `Measure.pi` (finite products of measures) and binary `Kernel.prod`, but no finite
product of kernels over a `Fintype` index. This file fills the gap: `ProbabilityTheory.Kernel.pi κ`
sends `a` to the product measure `Measure.pi (fun i => κ i a)`, under which the coordinates are
independent with laws `κ i a`.

## Main definitions

* `ProbabilityTheory.Kernel.pi`: The **product of finitely many Markov kernels** with common source.

## Main statements

* `ProbabilityTheory.Kernel.measurable_measurePi`: The underlying map into product measures is
  measurable.
* `ProbabilityTheory.Kernel.pi_apply`: The product kernel evaluates to `Measure.pi`.
* `ProbabilityTheory.Kernel.pi_congr_ae`: Kernels that agree almost everywhere have almost
  everywhere equal products.

## Notes

The product kernel supplies the distributional-strategy layer of measure-theoretic Bayesian games
(`Econlib.GameTheory.Strategic.Bayesian.Measurable`): Conditionally on a type profile the players
randomize independently, so the joint action law is the product of the per-player behavioral
kernels evaluated at their own coordinates.

## Tags

kernel, product measure, markov kernel
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α]
  {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- The map `a ↦ Measure.pi (fun i => κ i a)` is measurable for Markov kernels `κ i`. This is the
measurability obligation backing `Kernel.pi`; it follows from the rectangle π-system generating the
product σ-algebra. -/
theorem measurable_measurePi (κ : ∀ i, Kernel α (X i)) [∀ i, IsMarkovKernel (κ i)] :
    Measurable (fun a => Measure.pi (fun i => κ i a)) := by
  haveI : ∀ a, IsProbabilityMeasure (Measure.pi (fun i => κ i a)) := fun a => inferInstance
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_pi.symm isPiSystem_pi (fun s hs => ?_)
  obtain ⟨s_fam, hs_fam, rfl⟩ := hs
  simp only [Set.mem_univ_pi] at hs_fam
  have hbox : ∀ a, Measure.pi (fun i => κ i a) (Set.univ.pi s_fam) =
      ∏ i, κ i a (s_fam i) := fun a => Measure.pi_pi _ _
  simp_rw [hbox]
  exact Finset.measurable_prod Finset.univ fun i _ => Kernel.measurable_coe (κ i) (hs_fam i)

/-- The **product of finitely many Markov kernels** with common source: `Kernel.pi κ a` is the
product measure `Measure.pi (fun i => κ i a)`, under which the coordinates are independent with
laws `κ i a`. -/
noncomputable def pi (κ : ∀ i, Kernel α (X i)) [∀ i, IsMarkovKernel (κ i)] :
    Kernel α (∀ i, X i) :=
  ⟨fun a => Measure.pi (fun i => κ i a), measurable_measurePi κ⟩

@[simp] lemma pi_apply (κ : ∀ i, Kernel α (X i)) [∀ i, IsMarkovKernel (κ i)] (a : α) :
    pi κ a = Measure.pi (fun i => κ i a) := rfl

instance (κ : ∀ i, Kernel α (X i)) [∀ i, IsMarkovKernel (κ i)] : IsMarkovKernel (pi κ) := by
  refine ⟨fun a => ?_⟩
  rw [pi_apply]
  infer_instance

/-- Product kernels of almost-everywhere equal kernels are almost everywhere equal. The common
source measure is arbitrary; the hypothesis is pointwise a.e. equality of each factor. -/
lemma pi_congr_ae {μ : Measure α} {κ κ' : ∀ i, Kernel α (X i)} [∀ i, IsMarkovKernel (κ i)]
    [∀ i, IsMarkovKernel (κ' i)] (h : ∀ i, ∀ᵐ a ∂μ, κ i a = κ' i a) :
    ∀ᵐ a ∂μ, pi κ a = pi κ' a := by
  filter_upwards [ae_all_iff.2 h] with a ha
  simp only [pi_apply]
  exact congrArg Measure.pi (funext ha)

end ProbabilityTheory.Kernel
