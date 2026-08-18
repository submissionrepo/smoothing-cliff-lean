/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.CountDist.Basic
public import Mathlib.Order.Interval.Finset.Nat

/-!
# CDF of a countable distribution

The cumulative distribution function of a `CountDist α` over a linear order whose lower intervals
are finite: `CountDist.cdf d a` is the total mass at or below the cutoff `a`.

## Main definitions

* `CountDist.cdf` — total mass at or below a cutoff.

## Main statements

* `CountDist.cdf_nonneg`, `CountDist.cdf_le_one`, `CountDist.cdf_mono` — bounds and monotonicity.
* `CountDist.cdf_eq_sum_range` — over `ℕ`, the CDF at `n` is the partial sum up to `n`.
* `CountDist.tendsto_cdf_atTop` — over `ℕ`, the CDF tends to `1` at `+∞`.

## Tags

probability, countable distributions, cumulative distribution function, cdf
-/

@[expose] public section

open Filter Topology BigOperators

namespace Econlib.Probability

namespace CountDist

variable {α : Type*} [Encodable α] [LinearOrder α] [LocallyFiniteOrderBot α]

/-- CDF of a countable distribution at a cutoff: The total mass at or below `a`. Requires the lower
intervals `Iic a` to be finite (`LocallyFiniteOrderBot`), as is the case for `ℕ`. -/
noncomputable def cdf (d : CountDist α) (a : α) : ℝ :=
  ∑ x ∈ Finset.Iic a, d.pmf x

@[simp] lemma cdf_eq_sum (d : CountDist α) (a : α) :
    d.cdf a = ∑ x ∈ Finset.Iic a, d.pmf x := rfl

/-- The CDF is nonnegative. -/
lemma cdf_nonneg (d : CountDist α) (a : α) : 0 ≤ d.cdf a :=
  Finset.sum_nonneg fun i _ => d.nonneg i

/-- The CDF is bounded above by one. -/
lemma cdf_le_one (d : CountDist α) (a : α) : d.cdf a ≤ 1 := by
  calc d.cdf a
      ≤ ∑' x, d.pmf x :=
        d.summable_pmf.sum_le_tsum _ fun i _ => d.nonneg i
    _ = 1 := d.tsum_one

/-- The CDF is monotone. -/
lemma cdf_mono (d : CountDist α) : Monotone d.cdf :=
  fun _ _ hab => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Iic_subset_Iic.mpr hab) fun i _ _ => d.nonneg i

/-! ## Distributions on `ℕ` -/

/-- Over `ℕ`, the CDF at `n` is the partial sum of the pmf up to and including `n`. -/
lemma cdf_eq_sum_range (d : CountDist ℕ) (n : ℕ) :
    d.cdf n = ∑ k ∈ Finset.range (n + 1), d.pmf k := by
  rw [cdf_eq_sum]
  congr 1
  ext a
  simp

/-- Over `ℕ`, the CDF at `0` is the mass at `0`. -/
@[simp] lemma cdf_zero (d : CountDist ℕ) : d.cdf 0 = d.pmf 0 := by
  rw [cdf_eq_sum_range]
  simp

/-- Discrete-derivative recursion: The CDF advances by the mass at the new point. -/
lemma cdf_succ (d : CountDist ℕ) (n : ℕ) :
    d.cdf (n + 1) = d.cdf n + d.pmf (n + 1) := by
  rw [cdf_eq_sum_range, cdf_eq_sum_range, Finset.sum_range_succ]

/-- Over `ℕ`, the CDF exhausts the total mass: It tends to `1` at `+∞`. -/
lemma tendsto_cdf_atTop (d : CountDist ℕ) :
    Tendsto d.cdf atTop (𝓝 1) := by
  have hsum : HasSum d.pmf 1 := d.summable_pmf.hasSum_iff.mpr d.tsum_one
  have hpartial : Tendsto (fun m => ∑ k ∈ Finset.range m, d.pmf k) atTop (𝓝 1) :=
    hsum.tendsto_sum_nat
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hcomp : Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), d.pmf k) atTop (𝓝 1) := by
    simpa [Function.comp_def] using hpartial.comp hshift
  exact hcomp.congr fun n => (cdf_eq_sum_range d n).symm

end CountDist

end Econlib.Probability
