/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib

/-!
# Linearity of `Measure.pi` in a single coordinate

`Measure.pi` is multilinear in its factors: Replacing one factor by a sum (or scalar multiple) of
finite measures splits (scales) the product.

This is what makes expected payoffs affine in a player's own distributional strategy in
measure-theoretic Bayesian games, the convexity input to the fixed-point argument.

## Main statements

* `MeasureTheory.Measure.pi_update_add`: Additivity of `Measure.pi` in one coordinate.
* `MeasureTheory.Measure.pi_update_smul`: Scalar homogeneity of `Measure.pi` in one coordinate.

## Tags

product measure, multilinearity
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- `Measure.pi` is additive in any single coordinate. -/
lemma pi_update_add (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)] (i : ι)
    (ν₁ ν₂ : Measure (X i)) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] :
    Measure.pi (Function.update μ i (ν₁ + ν₂)) =
      Measure.pi (Function.update μ i ν₁) + Measure.pi (Function.update μ i ν₂) := by
  haveI hupd1 : ∀ j, SigmaFinite (Function.update μ i ν₁ j) := fun j => by
    rcases eq_or_ne j i with rfl | hji
    · simp only [Function.update_self]; infer_instance
    · simp only [Function.update_of_ne hji]; infer_instance
  haveI hupd2 : ∀ j, SigmaFinite (Function.update μ i ν₂ j) := fun j => by
    rcases eq_or_ne j i with rfl | hji
    · simp only [Function.update_self]; infer_instance
    · simp only [Function.update_of_ne hji]; infer_instance
  haveI hupdadd : ∀ j, SigmaFinite (Function.update μ i (ν₁ + ν₂) j) := fun j => by
    rcases eq_or_ne j i with rfl | hji
    · simp only [Function.update_self]; infer_instance
    · simp only [Function.update_of_ne hji]; infer_instance
  refine Measure.pi_eq (μ := Function.update μ i (ν₁ + ν₂)) (fun s hs => ?_)
  rw [Measure.add_apply, Measure.pi_pi, Measure.pi_pi]
  have hi : i ∈ Finset.univ := Finset.mem_univ i
  rw [← Finset.prod_erase_mul (Finset.univ) (fun j => Function.update μ i ν₁ j (s j)) hi,
      ← Finset.prod_erase_mul (Finset.univ) (fun j => Function.update μ i ν₂ j (s j)) hi,
      ← Finset.prod_erase_mul (Finset.univ) (fun j => Function.update μ i (ν₁ + ν₂) j (s j)) hi]
  have htail_eq : ∀ (ν' : Measure (X i)),
      ∏ j ∈ Finset.univ.erase i, Function.update μ i ν' j (s j) =
      ∏ j ∈ Finset.univ.erase i, μ j (s j) := fun ν' => by
    apply Finset.prod_congr rfl
    intro j hj
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  simp only [Function.update_self]
  rw [htail_eq ν₁, htail_eq ν₂, htail_eq (ν₁ + ν₂)]
  simp only [Measure.add_apply]
  ring

/-- `Measure.pi` is scalar-homogeneous in any single coordinate, for finite scalars. The finiteness
guard is necessary: For `c = ⊤` the left side can charge sets (e.g. a diagonal) that the right side
annihilates, because `⊤ • ν` is no longer σ-finite and the product construction degenerates. -/
lemma pi_update_smul (μ : ∀ i, Measure (X i)) [∀ i, IsFiniteMeasure (μ i)] (i : ι)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (ν : Measure (X i)) [IsFiniteMeasure ν] :
    Measure.pi (Function.update μ i (c • ν)) = c • Measure.pi (Function.update μ i ν) := by
  haveI hcν : IsFiniteMeasure (c • ν) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top hc.lt_top (measure_lt_top ν _)
  haveI hupd : ∀ (ρ : Measure (X i)) [IsFiniteMeasure ρ] (j : ι),
      SigmaFinite (Function.update μ i ρ j) := fun ρ _ j => by
    rcases eq_or_ne j i with rfl | hji
    · simp only [Function.update_self]; infer_instance
    · simp only [Function.update_of_ne hji]; infer_instance
  haveI := hupd (c • ν)
  haveI := hupd ν
  refine Measure.pi_eq (μ' := c • Measure.pi (Function.update μ i ν)) fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi]
  have hi : i ∈ Finset.univ := Finset.mem_univ i
  rw [← Finset.prod_erase_mul Finset.univ (fun j => Function.update μ i (c • ν) j (s j)) hi,
    ← Finset.prod_erase_mul Finset.univ (fun j => Function.update μ i ν j (s j)) hi]
  have htail_eq : ∀ ρ : Measure (X i),
      ∏ j ∈ Finset.univ.erase i, Function.update μ i ρ j (s j) =
      ∏ j ∈ Finset.univ.erase i, μ j (s j) := fun ρ =>
    Finset.prod_congr rfl fun j hj => by
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [htail_eq, htail_eq]
  simp only [Function.update_self, Measure.smul_apply, smul_eq_mul]
  ring

end MeasureTheory.Measure
