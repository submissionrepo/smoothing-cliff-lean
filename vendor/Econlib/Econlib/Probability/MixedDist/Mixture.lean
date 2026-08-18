/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.MixedDist.Expect
public import Mathlib.Topology.UnitInterval

/-!
# Mixtures of mixed distributions

This file constructs convex mixtures of mixed distributions and records the induced expectation
identity.

## Main definitions

* `MixedDist.mixture`: Convex mixture of two mixed distributions.

## Main statements

* `MixedDist.expect_mixture`: Expectation of a mixed-distribution mixture.

## Tags

probability, mixed distributions, mixture
-/

@[expose] public section

open BigOperators MeasureTheory

namespace Econlib.Probability

namespace MixedDist

/-- The total weight of a convex combination of atom families. -/
private lemma sum_smul_add_smul (a₁ a₂ : ℝ →₀ ℝ) (s u : ℝ) :
    ((s • a₁ + u • a₂).sum fun _ w => w)
      = s * (a₁.sum fun _ w => w) + u * (a₂.sum fun _ w => w) := by
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  rw [Finsupp.sum_smul_index' (fun _ => rfl), Finsupp.sum_smul_index' (fun _ => rfl)]
  rw [Finsupp.mul_sum, Finsupp.mul_sum]
  simp only [smul_eq_mul]

/-- The convex combination of atom families, applied at a point. -/
private lemma smul_add_smul_apply (a₁ a₂ : ℝ →₀ ℝ) (s u : ℝ) (x : ℝ) :
    (s • a₁ + u • a₂) x = s * a₁ x + u * a₂ x := by
  rw [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]

/-- Convex combination of two `MixedDist`s. Duplicate atom locations merge automatically, so the
result stays in `MixedDist`. -/
noncomputable def mixture (t : unitInterval) (d₁ d₂ : MixedDist) :
    MixedDist where
  atoms := (t : ℝ) • d₁.atoms + (1 - (t : ℝ)) • d₂.atoms
  atoms_nonneg x := by
    rw [smul_add_smul_apply]
    exact add_nonneg (mul_nonneg t.2.1 (d₁.atoms_nonneg x))
      (mul_nonneg (by linarith [t.2.2]) (d₂.atoms_nonneg x))
  density := fun x => (t : ℝ) * d₁.density x + (1 - (t : ℝ)) * d₂.density x
  density_nonneg := fun x => add_nonneg
    (mul_nonneg t.2.1 (d₁.density_nonneg x))
    (mul_nonneg (by linarith [t.2.2]) (d₂.density_nonneg x))
  density_integrable :=
    (d₁.density_integrable.const_mul (t : ℝ)).add (d₂.density_integrable.const_mul (1 - (t : ℝ)))
  total_one := by
    rw [sum_smul_add_smul,
      integral_add (d₁.density_integrable.const_mul (t : ℝ))
        (d₂.density_integrable.const_mul (1 - (t : ℝ))),
      integral_const_mul_of_integrable d₁.density_integrable,
      integral_const_mul_of_integrable d₂.density_integrable]
    linear_combination (t : ℝ) * d₁.total_one + (1 - (t : ℝ)) * d₂.total_one

/-! ### Mixture expectation -/

/-- The expectation under a mixture is the convex combination of the component expectations. -/
lemma expect_mixture (t : unitInterval) (d₁ d₂ : MixedDist) (f : ℝ → ℝ)
    (hf₁ : Integrable (fun x => d₁.density x * f x))
    (hf₂ : Integrable (fun x => d₂.density x * f x)) :
    (mixture t d₁ d₂).expect f =
    (t : ℝ) * d₁.expect f + (1 - (t : ℝ)) * d₂.expect f := by
  simp only [expect, mixture]
  -- Split and refactor the atom sum
  have h_atoms : (((t : ℝ) • d₁.atoms + (1 - (t : ℝ)) • d₂.atoms).sum fun x w => w * f x)
      = (t : ℝ) * (d₁.atoms.sum fun x w => w * f x)
        + (1 - (t : ℝ)) * (d₂.atoms.sum fun x w => w * f x) := by
    rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)]
    rw [Finsupp.sum_smul_index' (fun _ => by simp), Finsupp.sum_smul_index' (fun _ => by simp)]
    rw [Finsupp.mul_sum, Finsupp.mul_sum]
    congr 1 <;> · refine Finsupp.sum_congr (fun x _ => ?_); rw [smul_eq_mul]; ring
  rw [h_atoms]
  -- Split the density integral
  rw [show (fun x => ((t : ℝ) * d₁.density x + (1 - (t : ℝ)) * d₂.density x) * f x) =
    fun x => (t : ℝ) * (d₁.density x * f x) + (1 - (t : ℝ)) * (d₂.density x * f x) from
    funext (fun x => by ring)]
  rw [integral_add (hf₁.const_mul (t : ℝ)) (hf₂.const_mul (1 - (t : ℝ))),
    integral_const_mul, integral_const_mul]
  ring

end MixedDist

end Econlib.Probability
