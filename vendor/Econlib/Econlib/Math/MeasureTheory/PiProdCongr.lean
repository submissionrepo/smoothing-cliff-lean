/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib

/-!
# Reindexing a product of pairs as a pair of products

Mathlib's `MeasurableEquiv.arrowProdEquivProdArrow` handles the non-dependent case
`(γ → α × β) ≃ᵐ (γ → α) × (γ → β)`; this file provides the dependent version
`(∀ i, X i × Y i) ≃ᵐ (∀ i, X i) × (∀ i, Y i)` on top of `Equiv.arrowProdEquivProdArrow`, together
with topological and measure-theoretic transport: The forward map is continuous, and product
measures push forward to product measures with the expected block marginals.

## Main definitions

* `MeasurableEquiv.piProdEquivProdPi`: The dependent reindexing measurable equivalence.

## Main statements

* `MeasurableEquiv.continuous_piProdEquivProdPi`: Continuity of the forward map.
* `MeasureTheory.Measure.map_piProdEquivProdPi_fst`: The first block marginal of a reindexed
  product measure is the product of the per-coordinate first marginals.
* `MeasureTheory.Measure.map_piProdEquivProdPi_snd`: The analogous statement for second marginals.

## Tags

product measure, reindexing, marginal
-/

@[expose] public section

open MeasureTheory

namespace MeasurableEquiv

variable {ι : Type*} {X Y : ι → Type*}

/-- Dependent reindexing: A family of pairs is a pair of families, measurably in both directions.
Dependent analog of `MeasurableEquiv.arrowProdEquivProdArrow`. -/
def piProdEquivProdPi [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)] :
    (∀ i, X i × Y i) ≃ᵐ (∀ i, X i) × (∀ i, Y i) where
  toEquiv := Equiv.arrowProdEquivProdArrow _ X Y
  measurable_toFun := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply i).fst
    · exact measurable_pi_lambda _ fun i => (measurable_pi_apply i).snd
  measurable_invFun := by
    refine measurable_pi_lambda _ fun i => Measurable.prodMk ?_ ?_
    · exact (measurable_pi_apply i).comp measurable_fst
    · exact (measurable_pi_apply i).comp measurable_snd

@[simp] lemma piProdEquivProdPi_apply [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (s : ∀ i, X i × Y i) :
    piProdEquivProdPi s = (fun i => (s i).1, fun i => (s i).2) := rfl

@[simp] lemma piProdEquivProdPi_symm_apply [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableSpace (Y i)] (p : (∀ i, X i) × (∀ i, Y i)) :
    piProdEquivProdPi.symm p = fun i => (p.1 i, p.2 i) := rfl

/-- The forward reindexing map is continuous. -/
lemma continuous_piProdEquivProdPi [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)] :
    Continuous (piProdEquivProdPi (X := X) (Y := Y)) := by
  refine Continuous.prodMk ?_ ?_ <;>
    exact continuous_pi fun i => (Continuous.comp (by fun_prop) (continuous_apply i))

end MeasurableEquiv

namespace MeasureTheory.Measure

variable {ι : Type*} [Fintype ι] {X Y : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]

/-- The first block marginal of a reindexed product of pair measures is the product of the
per-coordinate first marginals. -/
lemma map_piProdEquivProdPi_fst (μ : ∀ i, Measure (X i × Y i)) [∀ i, IsProbabilityMeasure (μ i)] :
    ((Measure.pi μ).map MeasurableEquiv.piProdEquivProdPi).map Prod.fst =
      Measure.pi (fun i => (μ i).map Prod.fst) := by
  rw [Measure.map_map measurable_fst MeasurableEquiv.piProdEquivProdPi.measurable]
  have hcomp : Prod.fst ∘ MeasurableEquiv.piProdEquivProdPi (X := X) (Y := Y) =
      (fun (x : ∀ i, X i × Y i) (i : ι) => (x i).1) := by
    ext x; simp [MeasurableEquiv.piProdEquivProdPi_apply]
  rw [hcomp]
  haveI : ∀ i, SigmaFinite ((μ i).map (@Prod.fst (X i) (Y i))) := fun i => inferInstance
  exact Measure.pi_map_pi fun i => measurable_fst.aemeasurable

/-- The second block marginal of a reindexed product of pair measures is the product of the
per-coordinate second marginals. -/
lemma map_piProdEquivProdPi_snd (μ : ∀ i, Measure (X i × Y i)) [∀ i, IsProbabilityMeasure (μ i)] :
    ((Measure.pi μ).map MeasurableEquiv.piProdEquivProdPi).map Prod.snd =
      Measure.pi (fun i => (μ i).map Prod.snd) := by
  rw [Measure.map_map measurable_snd MeasurableEquiv.piProdEquivProdPi.measurable]
  have hcomp : Prod.snd ∘ MeasurableEquiv.piProdEquivProdPi (X := X) (Y := Y) =
      (fun (x : ∀ i, X i × Y i) (i : ι) => (x i).2) := by
    ext x; simp [MeasurableEquiv.piProdEquivProdPi_apply]
  rw [hcomp]
  haveI : ∀ i, SigmaFinite ((μ i).map (@Prod.snd (X i) (Y i))) := fun i => inferInstance
  exact Measure.pi_map_pi fun i => measurable_snd.aemeasurable

end MeasureTheory.Measure
