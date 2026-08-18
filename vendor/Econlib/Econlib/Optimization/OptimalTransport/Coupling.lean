/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ProbDist.Coupling
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# The set of couplings

`couplings μ ν` is the set of probability measures on `α × β` whose first marginal is `μ` and whose
second marginal is `ν` (membership is `Econlib.Probability.IsCoupling`). Couplings are the feasible
set of the relaxed Kantorovich transport problem (Kantorovich 1942). This file collects the
topological facts about that set needed to prove existence of optimal transport plans:
Non-emptiness, closedness, and compactness in the weak-* topology.

## Main definitions

* `couplings` — the set of couplings of two probability measures.

## Main statements

* `couplings_nonempty` — the coupling set is non-empty, witnessed by the independent product.
* `couplings_isClosed` — the coupling set is closed in the weak-* topology, as the preimage of a
  pair of singletons under the continuous marginal maps.
* `couplings_isCompact` — when the base spaces are compact and Hausdorff, the coupling set is
  compact in the weak-* topology, being a closed subset of the compact space
  `ProbabilityMeasure (α × β)` via Prokhorov's theorem.

## References

* Kantorovich, Leonid V. 1942. “On the Translocation of Masses.” *Doklady Akademii Nauk SSSR* 37 :
  199–201.
* Villani, Cédric. 2009. *Optimal Transport*. Springer.

## Tags

coupling, optimal transport, kantorovich, weak-* topology, prokhorov
-/

@[expose] public section

open MeasureTheory Set
open Econlib.Probability Econlib.Probability.ProbDist

namespace Econlib.Optimization.OptimalTransport

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The set `Π(μ, ν) ⊂ ProbabilityMeasure (α × β)` of couplings of `μ` and `ν`. -/
def couplings (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    Set (ProbabilityMeasure (α × β)) :=
  { π | IsCoupling μ ν π }

@[simp] lemma mem_couplings {μ : ProbabilityMeasure α} {ν : ProbabilityMeasure β}
    {π : ProbabilityMeasure (α × β)} :
    π ∈ couplings μ ν ↔ IsCoupling μ ν π := Iff.rfl

/-- The product (independent) coupling lies in `Π(μ, ν)`. -/
lemma prod_mem_couplings (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    ProbDist.prod μ ν ∈ couplings μ ν :=
  ProbDist.prod_isCoupling μ ν

/-- `Π(μ, ν)` is non-empty: Take the product coupling. -/
lemma couplings_nonempty (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    (couplings μ ν).Nonempty :=
  ⟨ProbDist.prod μ ν, prod_mem_couplings μ ν⟩

section Topology

variable {α β : Type*}
  [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]

/-- The "first marginal" map `π ↦ π.fst : ProbabilityMeasure (α × β) → ProbabilityMeasure α` is
continuous in the weak-* topology. -/
lemma continuous_fst_marginal :
    Continuous (fun π : ProbabilityMeasure (α × β) =>
      ProbDist.map π Prod.fst measurable_fst) :=
  ProbabilityMeasure.continuous_map (f := Prod.fst) continuous_fst

/-- The "second marginal" map `π ↦ π.snd : ProbabilityMeasure (α × β) → ProbabilityMeasure β` is
continuous in the weak-* topology. -/
lemma continuous_snd_marginal :
    Continuous (fun π : ProbabilityMeasure (α × β) =>
      ProbDist.map π Prod.snd measurable_snd) :=
  ProbabilityMeasure.continuous_map (f := Prod.snd) continuous_snd

variable [TopologicalSpace.PseudoMetrizableSpace α]
  [TopologicalSpace.PseudoMetrizableSpace β]

/-- `Π(μ, ν)` is closed in the weak-* topology. -/
lemma couplings_isClosed (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    IsClosed (couplings μ ν) := by
  have h_eq :
      couplings μ ν =
        (fun π : ProbabilityMeasure (α × β) => ProbDist.map π Prod.fst measurable_fst) ⁻¹' {μ}
        ∩ (fun π : ProbabilityMeasure (α × β) =>
            ProbDist.map π Prod.snd measurable_snd) ⁻¹' {ν} := by
    ext π
    exact ⟨fun hπ => ⟨hπ.fst_marginal, hπ.snd_marginal⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩
  rw [h_eq]
  exact (isClosed_singleton.preimage continuous_fst_marginal).inter
        (isClosed_singleton.preimage continuous_snd_marginal)

end Topology

section Compact

variable {α β : Type*}
  [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β] [SecondCountableTopology β]
  [TopologicalSpace.PseudoMetrizableSpace α]
  [TopologicalSpace.PseudoMetrizableSpace β]
  [T2Space α] [T2Space β]
  [CompactSpace α] [CompactSpace β]

/-- When the base spaces are compact (and Hausdorff), `Π(μ, ν)` is compact in the weak-* topology,
as a closed subset of the compact space `ProbabilityMeasure (α × β)` (Prokhorov's theorem). -/
lemma couplings_isCompact (μ : ProbabilityMeasure α) (ν : ProbabilityMeasure β) :
    IsCompact (couplings μ ν) :=
  (couplings_isClosed μ ν).isCompact

end Compact

end Econlib.Optimization.OptimalTransport
