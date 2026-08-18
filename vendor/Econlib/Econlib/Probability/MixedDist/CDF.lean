/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.CDF
public import Econlib.Probability.MixedDist.Measure

/-!
# CDFs of mixed distributions

This file defines the discrete, continuous, and combined cumulative distribution functions of a
mixed distribution in closed form (cumulative atom mass plus a density integral) and identifies the
combined form with the measure-theoretic CDF of `MixedDist.toMeasure` (`cdfFun_eq_cdf_toMeasure`).
Monotonicity, right-continuity, and the endpoint limits then transfer from Mathlib's
`ProbabilityTheory.cdf` API.

## Main definitions

* `MixedDist.discreteCDF`: Cumulative atom mass.
* `MixedDist.continuousCDF`: Cumulative continuous mass.
* `MixedDist.cdfFun`: Total cumulative distribution function (closed form).
* `MixedDist.toCDF`: The CDF carrier, via `CDF.ofMeasure d.toMeasure`.

## Main statements

* `MixedDist.toMeasure_Iic` — `d.toMeasure (Iic x) = ENNReal.ofReal (d.cdfFun x)`.
* `MixedDist.cdfFun_eq_cdf_toMeasure` — the closed form is the measure-theoretic CDF.
* `MixedDist.cdfFun_mono`, `cdfFun_right_continuous`, `cdfFun_tendsto_bot`, `cdfFun_tendsto_top` —
  monotonicity, right-continuity, and endpoint limits.

## Tags

probability, mixed distributions, cdf
-/

@[expose] public section

open BigOperators MeasureTheory Filter Topology Set

namespace Econlib.Probability

namespace MixedDist

/-- The discrete component of the CDF: `∑_x [x ≤ t] · atoms x`. -/
noncomputable def discreteCDF (d : MixedDist) (x : ℝ) : ℝ :=
  d.atoms.sum fun y w => if y ≤ x then w else 0

/-- The continuous component of the CDF: `∫ t in (-∞, x], density t`. -/
noncomputable def continuousCDF (d : MixedDist) (x : ℝ) : ℝ :=
  ∫ t in Iic x, d.density t

/-- The CDF of a mixed distribution. -/
noncomputable def cdfFun (d : MixedDist) (x : ℝ) : ℝ :=
  d.discreteCDF x + d.continuousCDF x

/-- `discreteCDF` as a `Finset.sum` over the atom support. -/
lemma discreteCDF_eq_finsetSum (d : MixedDist) (x : ℝ) :
    d.discreteCDF x = ∑ y ∈ d.atoms.support, if y ≤ x then d.atoms y else 0 := rfl

/-- The discrete component of the CDF is nonnegative. -/
lemma discreteCDF_nonneg (d : MixedDist) (x : ℝ) : 0 ≤ d.discreteCDF x := by
  rw [discreteCDF_eq_finsetSum]
  refine Finset.sum_nonneg fun y _ => ?_
  split_ifs
  · exact d.atoms_nonneg y
  · exact le_rfl

/-- The continuous component of the CDF is nonnegative. -/
lemma continuousCDF_nonneg (d : MixedDist) (x : ℝ) : 0 ≤ d.continuousCDF x :=
  setIntegral_nonneg measurableSet_Iic (fun t _ => d.density_nonneg t)

/-- The CDF is nonnegative. -/
lemma cdfFun_nonneg (d : MixedDist) (x : ℝ) : 0 ≤ d.cdfFun x :=
  add_nonneg (d.discreteCDF_nonneg x) (d.continuousCDF_nonneg x)

/-! ### Measure of half-lines -/

/-- The atomic measure of a half-line is the cumulative atom mass. -/
lemma atomicMeasure_Iic (d : MixedDist) (x : ℝ) :
    d.atomicMeasure (Iic x) = ENNReal.ofReal (d.discreteCDF x) := by
  rw [atomicMeasure_eq_finsetSum, Measure.finset_sum_apply, discreteCDF_eq_finsetSum,
    ENNReal.ofReal_sum_of_nonneg (fun y _ => by
      split_ifs
      · exact d.atoms_nonneg y
      · exact le_rfl)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ measurableSet_Iic, smul_eq_mul]
  by_cases h : y ≤ x
  · rw [if_pos h, Set.indicator_of_mem (mem_Iic.mpr h), Pi.one_apply, mul_one]
  · rw [if_neg h, Set.indicator_of_notMem (fun hy => h (mem_Iic.mp hy)), mul_zero,
      ENNReal.ofReal_zero]

/-- The continuous measure of a half-line is the cumulative density integral. -/
lemma continuousMeasure_Iic (d : MixedDist) (x : ℝ) :
    d.continuousMeasure (Iic x) = ENNReal.ofReal (d.continuousCDF x) := by
  rw [continuousMeasure, withDensity_apply _ measurableSet_Iic]
  exact (ofReal_integral_eq_lintegral_ofReal d.density_integrable.integrableOn
    (ae_of_all _ d.density_nonneg)).symm

/-- The measure of a half-line under `toMeasure` is the closed-form CDF. -/
lemma toMeasure_Iic (d : MixedDist) (x : ℝ) :
    d.toMeasure (Iic x) = ENNReal.ofReal (d.cdfFun x) := by
  rw [toMeasure_eq, Measure.add_apply, atomicMeasure_Iic, continuousMeasure_Iic,
    ← ENNReal.ofReal_add (d.discreteCDF_nonneg x) (d.continuousCDF_nonneg x)]
  rfl

/-! ### Identification with the measure-theoretic CDF -/

/-- **The closed form is the measure-theoretic CDF.** The closed-form `cdfFun` (cumulative atom
mass plus density integral) agrees with `ProbabilityTheory.cdf` of `d.toMeasure`. -/
lemma cdfFun_eq_cdf_toMeasure (d : MixedDist) :
    d.cdfFun = ⇑(ProbabilityTheory.cdf d.toMeasure) := by
  haveI := d.toMeasure_isProbability
  funext x
  rw [ProbabilityTheory.cdf_eq_real, measureReal_def, toMeasure_Iic,
    ENNReal.toReal_ofReal (d.cdfFun_nonneg x)]

/-- The CDF is monotone. -/
lemma cdfFun_mono (d : MixedDist) : Monotone d.cdfFun :=
  d.cdfFun_eq_cdf_toMeasure ▸ ProbabilityTheory.monotone_cdf d.toMeasure

/-- The CDF is right-continuous. -/
lemma cdfFun_right_continuous (d : MixedDist) (x : ℝ) :
    ContinuousWithinAt d.cdfFun (Ici x) x :=
  d.cdfFun_eq_cdf_toMeasure ▸ (ProbabilityTheory.cdf d.toMeasure).right_continuous' x

/-- The CDF tends to `0` at `-∞`. -/
lemma cdfFun_tendsto_bot (d : MixedDist) :
    Tendsto d.cdfFun atBot (𝓝 0) :=
  d.cdfFun_eq_cdf_toMeasure ▸ ProbabilityTheory.tendsto_cdf_atBot d.toMeasure

/-- The CDF tends to `1` at `+∞`. -/
lemma cdfFun_tendsto_top (d : MixedDist) :
    Tendsto d.cdfFun atTop (𝓝 1) :=
  d.cdfFun_eq_cdf_toMeasure ▸ ProbabilityTheory.tendsto_cdf_atTop d.toMeasure

/-! ### The CDF structure -/

/-- CDF of a mixed distribution: The measure-theoretic CDF of `toMeasure`. Its pointwise values are
the closed form `cdfFun` (`toCDF_apply`). -/
noncomputable def toCDF (d : MixedDist) : CDF :=
  haveI := d.toMeasure_isProbability
  CDF.ofMeasure d.toMeasure

@[simp] lemma toCDF_apply (d : MixedDist) (x : ℝ) : d.toCDF x = d.cdfFun x :=
  (congrFun d.cdfFun_eq_cdf_toMeasure x).symm

end MixedDist

end Econlib.Probability
