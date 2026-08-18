/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ContDist.Basic
public import Econlib.Probability.MixedDist.Basic
public import Mathlib.Data.Real.StarOrdered

/-!
# Expectations for mixed distributions

This file defines expectation and variance for mixed distributions and records the basic algebraic
identities (constants, monotonicity, additivity, scaling) along with agreement with the pure
continuous (`ofContDist`) and pure atomic (`ofAtoms`) embeddings.

## Main definitions

* `MixedDist.expect`: Expectation over atomic and continuous components.
* `MixedDist.variance`: Variance of a real-valued function.

## Main statements

* `MixedDist.expect_add`: Additivity of expectation.
* `MixedDist.expect_smul`: Scaling of expectation.
* `MixedDist.ofContDist_expect`, `MixedDist.ofAtoms_expect`: Agreement with the embeddings.

## Tags

probability, mixed distributions, expectation
-/

@[expose] public section

open BigOperators MeasureTheory

namespace Econlib.Probability

namespace MixedDist

variable {n : ℕ}

/-- Expected value under a mixed distribution. -/
noncomputable def expect (d : MixedDist) (f : ℝ → ℝ) : ℝ :=
  (d.atoms.sum fun x w => w * f x) + ∫ x, d.density x * f x

/-- Variance under a mixed distribution. -/
noncomputable def variance (d : MixedDist) (f : ℝ → ℝ) : ℝ :=
  d.expect (fun x => (f x) ^ 2) - (d.expect f) ^ 2

/-! ### Basic lemmas -/

/-- Definitional unfolding of `expect` into its atomic sum and density integral. -/
@[simp] lemma expect_eq (d : MixedDist) (f : ℝ → ℝ) :
    d.expect f = (d.atoms.sum fun x w => w * f x) + ∫ x, d.density x * f x := rfl

/-- The expectation of a constant is that constant. -/
lemma expect_const (d : MixedDist) (c : ℝ) :
    d.expect (fun _ => c) = c := by
  simp only [expect]
  have h_atoms : (d.atoms.sum fun x w => w * c) = (d.atoms.sum fun _ w => w) * c :=
    (Finsupp.sum_mul c d.atoms (f := fun _ w => w)).symm
  rw [h_atoms]
  simp_rw [mul_comm (d.density _) c]
  rw [integral_const_mul_of_integrable d.density_integrable]
  rw [mul_comm c (∫ _, _), ← add_mul, d.total_one, one_mul]

/-- The expectation of a nonnegative function is nonnegative. -/
lemma expect_nonneg (d : MixedDist) (f : ℝ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ d.expect f := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun x _ => mul_nonneg (d.atoms_nonneg x) (hf _))
  · exact integral_nonneg (fun x => mul_nonneg (d.density_nonneg x) (hf x))

/-- Expectation is monotone in the integrand. -/
lemma expect_mono (d : MixedDist) {f g : ℝ → ℝ} (hfg : ∀ x, f x ≤ g x)
    (hf_int : Integrable (fun x => d.density x * f x))
    (hg_int : Integrable (fun x => d.density x * g x)) :
    d.expect f ≤ d.expect g := by
  apply add_le_add
  · exact Finset.sum_le_sum (fun x _ =>
      mul_le_mul_of_nonneg_left (hfg _) (d.atoms_nonneg x))
  · exact integral_mono hf_int hg_int (fun x =>
      mul_le_mul_of_nonneg_left (hfg x) (d.density_nonneg x))

/-- Expectation is additive in the integrand. -/
lemma expect_add (d : MixedDist) (f g : ℝ → ℝ)
    (hf_int : Integrable (fun x => d.density x * f x))
    (hg_int : Integrable (fun x => d.density x * g x)) :
    d.expect (f + g) = d.expect f + d.expect g := by
  simp only [expect, Pi.add_apply]
  have h_atoms : (d.atoms.sum fun x w => w * (f x + g x)) =
      (d.atoms.sum fun x w => w * f x) + (d.atoms.sum fun x w => w * g x) := by
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr (fun x _ => ?_)
    ring
  rw [h_atoms]
  simp_rw [mul_add]
  rw [integral_add hf_int hg_int]
  ring

/-- Scaling the integrand by `c` scales the expectation by `c`. -/
lemma expect_smul (d : MixedDist) (c : ℝ) (f : ℝ → ℝ) :
    d.expect (c • f) = c * d.expect f := by
  simp only [expect, Pi.smul_apply, smul_eq_mul]
  have h_atoms : (d.atoms.sum fun x w => w * (c * f x)) =
      c * d.atoms.sum fun x w => w * f x := by
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr (fun x _ => ?_)
    ring
  rw [h_atoms]
  simp_rw [mul_left_comm (d.density _) c]
  rw [integral_const_mul]
  ring

/-! ### Embedding agreement -/

/-- The expectation of `ofContDist d` agrees with the `ContDist` expectation of `d`. -/
lemma ofContDist_expect (d : ContDist) (f : ℝ → ℝ) :
    (ofContDist d).expect f = d.expect f := by
  simp [expect, ofContDist, ContDist.expect]

/-- The expectation of a pure discrete distribution is the weighted sum over its atoms. -/
lemma ofAtoms_expect {n : ℕ} (locations : Fin n → ℝ) (weights : FinDist (Fin n)) (f : ℝ → ℝ) :
    (ofAtoms locations weights).expect f =
    ∑ i, weights.pmf i * f (locations i) := by
  simp only [expect, ofAtoms]
  rw [show (∫ x, (fun _ : ℝ => (0 : ℝ)) x * f x) = 0 by simp, add_zero]
  rw [← Finsupp.sum_finset_sum_index (h := fun x w => w * f x)
    (fun a => by simp) (fun a b₁ b₂ => by ring)]
  exact Finset.sum_congr rfl (fun i _ => Finsupp.sum_single_index (by simp))

end MixedDist

end Econlib.Probability
