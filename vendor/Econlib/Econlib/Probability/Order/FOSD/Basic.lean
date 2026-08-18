/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.ProbDist
public import Econlib.Probability.Order.Core.Basic

/-!
# First-order stochastic dominance on `ProbDist`

`FOSD μ ν` is the **first-order stochastic dominance** relation, stated directly on the
measure-theoretic carrier `ProbDist`: `μ` dominates `ν` exactly when its mass below every cutoff is
no larger, `∀ a, μ {x ≤ a} ≤ ν {x ≤ a}`. Equivalently the CDF of `μ` lies weakly below that of `ν`,
matching the `IntegratedCDFTower 1` convention.

This is the user-facing relation; the CDF-level analytic engine remains available as
`IntegratedCDFTower 1`, bridged here by `fosd_iff_integratedCDFTower_one` on `ProbDist ℝ`. At order
`1` no integral is involved, so no lower-tail witness is needed.

## Main definitions

* `FOSD` — first-order stochastic dominance on `ProbDist α`.
* `FinDist.FOSD` — the combinatorial finite-distribution version.

## Main statements

* `FOSD.trans`, `FOSD.antisymm` — order properties of the dominance relation.
* `fosd_iff_integratedCDFTower_one` — coherence with the CDF-level engine on `ProbDist ℝ`.
* `FinDist.fosd_iff` — coherence of the combinatorial and measure-theoretic finite relations.

## Notes

The finite-distribution version `FinDist.FOSD` stays combinatorial (a sum of point masses at or
below the cutoff) so the Markov-chain lattice can reason about it without invoking the measure.

## References

* Hadar, Josef, and William R. Russell. 1969. “Rules for Ordering Uncertain Prospects.” *The
  American Economic Review* 59 (1): 25–34.

## Tags

first-order stochastic dominance, fosd, cdf, probability measure
-/

@[expose] public section

open MeasureTheory Set BigOperators Function Filter
open scoped Topology ENNReal Real

namespace Econlib.Probability

open Econlib

/-- **First-order stochastic dominance.** `FOSD μ ν` holds when `μ` puts no more mass than `ν`
weakly below every cutoff, i.e. its CDF lies weakly below `ν`'s. The minimal typeclass bundle
`[OpensMeasurableSpace][ClosedIicTopology]` over a `Preorder` is exactly what `measurableSet_Iic`
needs; both `ℝ` and `Fin n` satisfy it. -/
def FOSD {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
    [Preorder α] [ClosedIicTopology α] (μ ν : ProbDist α) : Prop :=
  ∀ a : α, μ.toMeasure (Set.Iic a) ≤ ν.toMeasure (Set.Iic a)

namespace FOSD

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α]
  [Preorder α] [ClosedIicTopology α]

@[refl] lemma refl (μ : ProbDist α) : FOSD μ μ := fun _ => le_rfl

lemma trans {μ ν ρ : ProbDist α} (h₁ : FOSD μ ν) (h₂ : FOSD ν ρ) : FOSD μ ρ :=
  fun a => le_trans (h₁ a) (h₂ a)

/-- Antisymmetry holds once the order is rich enough for `Iic`-mass to determine the measure
(`Measure.ext_of_Iic`): Mutual dominance forces equal mass below every cutoff, hence equal laws.
`ℝ` and `Fin n` both supply the required `LinearOrder`/`OrderTopology`/`SecondCountableTopology`/
`BorelSpace`. -/
lemma antisymm {α : Type*} [MeasurableSpace α] [TopologicalSpace α] [SecondCountableTopology α]
    [LinearOrder α] [OrderTopology α] [BorelSpace α] {μ ν : ProbDist α}
    (h₁ : FOSD μ ν) (h₂ : FOSD ν μ) : μ = ν :=
  ProbabilityMeasure.toMeasure_injective
    (Measure.ext_of_Iic _ _ fun a => le_antisymm (h₁ a) (h₂ a))

end FOSD

/-- **Coherence with the analytic engine on `ℝ`.** First-order dominance on `ProbDist ℝ` is exactly
`IntegratedCDFTower 1` of the associated CDFs. The CDF is the real-valued lower-tail mass
`cdf μ x = (μ {· ≤ x}).toReal`, and on probability measures the lower-tail mass is finite, so
`ENNReal.toReal` is order-faithful and the measure-form and toReal-form comparisons coincide. -/
lemma fosd_iff_integratedCDFTower_one (μ ν : ProbDist ℝ) :
    FOSD μ ν ↔ IntegratedCDFTower 1 (CDF.ofProbDist μ) (CDF.ofProbDist ν) := by
  rw [IntegratedCDFTower.one_iff]
  refine forall_congr' (fun x => ?_)
  -- Translate each CDF value to a finite lower-tail mass, then drop the order-faithful `toReal`.
  rw [CDF.ofProbDist_apply, CDF.ofProbDist_apply,
    ProbabilityTheory.cdf_eq_real, ProbabilityTheory.cdf_eq_real,
    MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
    ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)]

/-- **First-order stochastic dominance for finite distributions.** Kept combinatorial: `d₁`
dominates `d₂` when the mass at or below every cutoff is no larger. Specializes to
`FinDist (Fin n)` for the Markov-chain API, whose lattice reasons about this finite-sum form
directly. -/
def FinDist.FOSD {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    (d₁ d₂ : FinDist α) : Prop :=
  ∀ a : α, ∑ i ∈ Finset.univ.filter (fun j => j ≤ a), d₁.pmf i ≤
           ∑ i ∈ Finset.univ.filter (fun j => j ≤ a), d₂.pmf i

/-- The probability mass of a lower set `Iic a` under the embedded measure is the finite sum of
`pmf`s at or below `a`. The set `Iic a` is the coercion of the `· ≤ a` filter, and the
`PMF`-measure of a `Finset` is the finite sum of its masses. -/
lemma FinDist.toProbDist_measure_Iic {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (d : FinDist α) (a : α) :
    d.toProbDist.toMeasure (Set.Iic a) =
      ∑ i ∈ Finset.univ.filter (fun j => j ≤ a), ENNReal.ofReal (d.pmf i) := by
  have hset : (Set.Iic a) = ↑(Finset.univ.filter (fun j => j ≤ a)) := by
    ext x; simp [Set.mem_Iic]
  rw [FinDist.toProbDist_toMeasure, hset, PMF.toMeasure_apply_finset]
  rfl

/-- **Coherence of the combinatorial and measure-theoretic finite FOSD.** The finite-sum relation
agrees with the canonical `ProbDist` relation under the embedding `FinDist.toProbDist`. -/
lemma FinDist.fosd_iff {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
    [MeasurableSpace α] [TopologicalSpace α] [OpensMeasurableSpace α] [ClosedIicTopology α]
    [MeasurableSingletonClass α] (d₁ d₂ : FinDist α) :
    FinDist.FOSD d₁ d₂ ↔ Econlib.Probability.FOSD d₁.toProbDist d₂.toProbDist := by
  refine forall_congr' (fun a => ?_)
  rw [FinDist.toProbDist_measure_Iic, FinDist.toProbDist_measure_Iic,
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => d₁.nonneg i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => d₂.nonneg i),
    ENNReal.ofReal_le_ofReal_iff]
  exact Finset.sum_nonneg (fun i _ => d₂.nonneg i)

end Econlib.Probability
