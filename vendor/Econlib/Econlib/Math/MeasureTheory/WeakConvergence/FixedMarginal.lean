/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib

/-!
# Probability measures on a product with a fixed first marginal

For a Polish space `T`, a compact metrizable space `A`, and a probability measure `η` on `T`, the
set of probability measures on `T × A` whose first marginal is `η` — Milgrom and Weber's space of
*distributional strategies* — is nonempty, closed, and compact in the topology of weak convergence.

## Main definitions

* `MeasureTheory.fixedFstMarginal`: The set of probability measures on `T × A` with first marginal
  `η`.

## Main statements

* `MeasureTheory.isCompact_fixedFstMarginal`: Compactness under weak convergence.

## References

* Milgrom, Paul R., and Robert J. Weber. 1985. “Distributional Strategies for Games with Incomplete
  Information.” *Mathematics of Operations Research* 10 (4): 619–32.
  [https://doi.org/10.1287/moor.10.4.619](https://doi.org/10.1287/moor.10.4.619).

## Tags

distributional strategy, tightness, prokhorov, weak convergence, marginal
-/

@[expose] public section

open scoped ENNReal
open TopologicalSpace

namespace MeasureTheory

variable {T A : Type*} [TopologicalSpace T] [MeasurableSpace T]
  [TopologicalSpace A] [MeasurableSpace A]

/-- The probability measures on `T × A` whose first marginal is `η` (Milgrom–Weber's
*distributional strategies* for type space `T`, action space `A`, and type law `η`). -/
def fixedFstMarginal (η : Measure T) : Set (ProbabilityMeasure (T × A)) :=
  {μ | (μ : Measure (T × A)).map Prod.fst = η}

omit [TopologicalSpace T] [TopologicalSpace A] in
lemma mem_fixedFstMarginal {η : Measure T} {μ : ProbabilityMeasure (T × A)} :
    μ ∈ fixedFstMarginal η ↔ (μ : Measure (T × A)).map Prod.fst = η := Iff.rfl

omit [TopologicalSpace A] in
/-- The slab measure `η ⊗ δ_a` witnesses nonemptiness of the fixed-marginal set. -/
lemma nonempty_fixedFstMarginal [OpensMeasurableSpace T] [Nonempty A]
    (η : Measure T) [IsProbabilityMeasure η] :
    (fixedFstMarginal (A := A) η).Nonempty := by
  classical
  set a₀ : A := Classical.arbitrary A
  have hpair : Measurable (fun t : T => (t, a₀)) := measurable_id.prodMk measurable_const
  haveI : IsProbabilityMeasure (η.map (fun t : T => (t, a₀))) :=
    Measure.isProbabilityMeasure_map hpair.aemeasurable
  refine ⟨⟨η.map (fun t : T => (t, a₀)), inferInstance⟩, ?_⟩
  change (η.map (fun t : T => (t, a₀))).map Prod.fst = η
  rw [Measure.map_map measurable_fst hpair]
  exact Measure.map_id

/-- The fixed-marginal set is closed in the topology of weak convergence. -/
lemma isClosed_fixedFstMarginal [PseudoMetrizableSpace T] [BorelSpace T]
    [SecondCountableTopology T] [OpensMeasurableSpace A]
    (η : Measure T) [IsProbabilityMeasure η] :
    IsClosed (fixedFstMarginal (A := A) η) := by
  classical
  haveI : OpensMeasurableSpace (T × A) := by
    haveI : SecondCountableTopologyEither T A := secondCountableTopologyEither_of_left T A
    infer_instance
  set Φ : ProbabilityMeasure (T × A) → ProbabilityMeasure T :=
    fun ν => ν.map (continuous_fst (X := T) (Y := A)).measurable.aemeasurable with hΦ
  have hΦ_cont : Continuous Φ := ProbabilityMeasure.continuous_map continuous_fst
  set η' : ProbabilityMeasure T := ⟨η, inferInstance⟩ with hη'
  have hset : fixedFstMarginal (A := A) η = Φ ⁻¹' {η'} := by
    ext μ
    rw [mem_fixedFstMarginal, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      apply ProbabilityMeasure.toMeasure_injective
      simpa [hΦ, ProbabilityMeasure.toMeasure_map, hη'] using h
    · intro h
      have := congrArg (fun ρ : ProbabilityMeasure T => (ρ : Measure T)) h
      simpa [hΦ, ProbabilityMeasure.toMeasure_map, hη'] using this
  rw [hset]
  exact isClosed_singleton.preimage hΦ_cont

/-- The fixed-marginal set is tight: `η` is tight on the Polish space `T` and `A` is compact, so a
single compact box `K × A` carries all but `ε` of every member's mass. -/
lemma isTightMeasureSet_fixedFstMarginal [PolishSpace T] [BorelSpace T]
    [CompactSpace A] (η : Measure T) [IsProbabilityMeasure η] :
    IsTightMeasureSet
      {((μ : ProbabilityMeasure (T × A)) : Measure (T × A)) | μ ∈ fixedFstMarginal (A := A) η} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨C, hC_compact, hηC⟩ :=
    (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
      (isTightMeasureSet_singleton (μ := η))) ε hε
  have hηCε : η Cᶜ ≤ ε := hηC η rfl
  refine ⟨C ×ˢ (Set.univ : Set A), hC_compact.prod isCompact_univ, ?_⟩
  rintro _ ⟨μ, hμ, rfl⟩
  have hKc : (C ×ˢ (Set.univ : Set A))ᶜ = Prod.fst ⁻¹' Cᶜ := by
    ext x; simp [Set.mem_prod]
  have hCmeas : MeasurableSet C := hC_compact.isClosed.measurableSet
  calc (μ : Measure (T × A)) (C ×ˢ (Set.univ : Set A))ᶜ
      = (μ : Measure (T × A)) (Prod.fst ⁻¹' Cᶜ) := by rw [hKc]
    _ = ((μ : Measure (T × A)).map Prod.fst) Cᶜ :=
        (Measure.map_apply measurable_fst hCmeas.compl).symm
    _ = η Cᶜ := by rw [(mem_fixedFstMarginal.1 hμ)]
    _ ≤ ε := hηCε

/-- **Compactness of the distributional-strategy space** (Prokhorov): For Polish `T`, compact
metrizable `A`, and a probability law `η` on `T`, the set of probability measures on `T × A` with
first marginal `η` is compact in the topology of weak convergence. -/
theorem isCompact_fixedFstMarginal [PolishSpace T] [BorelSpace T]
    [CompactSpace A] [MetrizableSpace A] [BorelSpace A]
    (η : Measure T) [IsProbabilityMeasure η] :
    IsCompact (fixedFstMarginal (A := A) η) := by
  haveI : T2Space (T × A) := inferInstance
  haveI : BorelSpace (T × A) := inferInstance
  have hclosed : IsClosed (fixedFstMarginal (A := A) η) :=
    isClosed_fixedFstMarginal η
  have hclosure_compact : IsCompact (closure (fixedFstMarginal (A := A) η)) :=
    isCompact_closure_of_isTightMeasureSet (isTightMeasureSet_fixedFstMarginal η)
  exact hclosure_compact.of_isClosed_subset hclosed subset_closure

end MeasureTheory
