/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.MixedDist.Expect
public import Econlib.Probability.ProbDist.Basic
public import Econlib.Probability.ProbLaw

/-!
# Measures associated to mixed distributions

This file constructs the atomic, continuous, and total measures associated to a mixed distribution,
proves the total measure is a probability measure, embeds mixed distributions into `ProbDist`, and
identifies `MixedDist.expect` with integration against the total measure.

## Main definitions

* `MixedDist.atomicMeasure`: Finite atomic component.
* `MixedDist.continuousMeasure`: Density-induced continuous component.
* `MixedDist.toMeasure`: Total measure of a mixed distribution.
* `MixedDist.toProbDist`: Probability-measure embedding.

## Main statements

* `MixedDist.toMeasure_isProbability`: The total measure is a probability measure.
* `MixedDist.expect_eq_measure_integral`: `expect` is integration against `toMeasure`.
* `MixedDist.expect_eq_probDist_expect`: Agreement with `ProbDist.expect`.

## Tags

probability, mixed distributions, measures
-/

@[expose] public section

open BigOperators MeasureTheory Filter Topology Set

namespace Econlib.Probability

namespace MixedDist

/-- The atomic component as a measure: `∑_x atoms x • δ(x)`. -/
noncomputable def atomicMeasure (d : MixedDist) : Measure ℝ :=
  d.atoms.sum fun x w => ENNReal.ofReal w • Measure.dirac x

/-- The continuous component as a measure. -/
noncomputable def continuousMeasure (d : MixedDist) : Measure ℝ :=
  Measure.withDensity volume (fun x => ENNReal.ofReal (d.density x))

/-- The measure associated to a mixed distribution: `∑_x atoms x • δ(x) + density · λ`. -/
noncomputable def toMeasure (d : MixedDist) : Measure ℝ :=
  d.atomicMeasure + d.continuousMeasure

/-- `toMeasure` is the sum of the atomic and continuous measures. -/
@[simp] lemma toMeasure_eq (d : MixedDist) :
    d.toMeasure = d.atomicMeasure + d.continuousMeasure := rfl

/-- `atomicMeasure` as a `Finset.sum` over the atom support. -/
lemma atomicMeasure_eq_finsetSum (d : MixedDist) :
    d.atomicMeasure =
      ∑ x ∈ d.atoms.support, ENNReal.ofReal (d.atoms x) • Measure.dirac x := rfl

/-! ### Probability measure -/

/-- The total atomic mass is the discrete weight. -/
lemma atomicMeasure_univ (d : MixedDist) :
    d.atomicMeasure Set.univ = ENNReal.ofReal d.discreteWeight := by
  rw [atomicMeasure_eq_finsetSum, Measure.finset_sum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
  rw [discreteWeight, Finsupp.sum,
    ENNReal.ofReal_sum_of_nonneg (fun x _ => d.atoms_nonneg x)]

/-- The total continuous mass is the continuous weight. -/
lemma continuousMeasure_univ (d : MixedDist) :
    d.continuousMeasure Set.univ = ENNReal.ofReal d.continuousWeight := by
  simp only [continuousMeasure, continuousWeight]
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal d.density_integrable
    (ae_of_all _ d.density_nonneg)).symm

/-- The total measure of a mixed distribution is a probability measure. -/
lemma toMeasure_isProbability (d : MixedDist) : IsProbabilityMeasure d.toMeasure := by
  constructor
  rw [toMeasure_eq, Measure.add_apply, atomicMeasure_univ, continuousMeasure_univ,
    ← ENNReal.ofReal_add d.discreteWeight_nonneg d.continuousWeight_nonneg]
  have hweights_sum : d.discreteWeight + d.continuousWeight = 1 := by
    simp only [discreteWeight, continuousWeight]; linarith [d.total_one]
  simp [hweights_sum]

/-- Bridge to `ProbDist ℝ`. -/
noncomputable def toProbDist (d : MixedDist) : ProbDist ℝ :=
  ⟨d.toMeasure, d.toMeasure_isProbability⟩

/-- The measure underlying `toProbDist` is `toMeasure`. -/
@[simp] lemma toProbDist_toMeasure (d : MixedDist) :
    (d.toProbDist : Measure ℝ) = d.toMeasure := rfl

/-- `MixedDist` is a probability law via its `toProbDist` embedding. -/
noncomputable instance instProbLaw : ProbLaw MixedDist ℝ where
  toProbDist := MixedDist.toProbDist

/-! ### Expectation agreement -/

/-- For an integrable `f`, the expectation agrees with the integral against `toMeasure`. -/
lemma expect_eq_measure_integral (d : MixedDist) (f : ℝ → ℝ)
    (hf_int : Integrable f d.toMeasure) :
    d.expect f = ∫ x, f x ∂d.toMeasure := by
  -- Split toMeasure = atomicMeasure + continuousMeasure
  rw [toMeasure_eq] at hf_int ⊢
  obtain ⟨hf_a, hf_c⟩ := integrable_add_measure.mp hf_int
  rw [integral_add_measure hf_a hf_c]
  simp only [expect]
  congr 1
  · -- Atomic part: ∫ f ∂(∑_x ofReal (atoms x) • δ(x)) = ∑_x atoms x * f x
    rw [atomicMeasure_eq_finsetSum] at hf_a ⊢
    have h_int_each := integrable_finset_sum_measure.mp hf_a
    rw [integral_finset_sum_measure h_int_each, Finsupp.sum]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (d.atoms_nonneg x), mul_comm]
  · -- Continuous part: ∫ f ∂withDensity(ofReal ∘ density) = ∫ density * f
    simp only [continuousMeasure] at hf_c ⊢
    rw [integral_withDensity_eq_integral_toReal_smul₀
      d.density_integrable.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) f]
    congr 1; ext x; simp [smul_eq_mul, ENNReal.toReal_ofReal (d.density_nonneg x)]

/-- For an integrable `f`, `MixedDist.expect` agrees with `ProbDist.expect` under the `toProbDist`
embedding. -/
lemma expect_eq_probDist_expect (d : MixedDist) (f : ℝ → ℝ)
    (hf_int : Integrable f d.toMeasure) :
    d.expect f = d.toProbDist.expect f := by
  simp only [ProbDist.expect, toProbDist_toMeasure, expect_eq_measure_integral d f hf_int]

end MixedDist

end Econlib.Probability
