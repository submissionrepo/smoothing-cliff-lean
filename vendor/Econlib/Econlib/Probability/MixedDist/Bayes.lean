/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.MixedDist.Expect

/-!
# Bayesian updating for mixed distributions

This file defines the evidence (marginal likelihood) and Bayesian posterior of a mixed distribution
under a likelihood function on the real line, together with the posterior expectation formula. The
posterior preserves atom locations and rescales each atom weight and the density by the likelihood,
renormalizing by the evidence.

## Main definitions

* `MixedDist.evidence`: Total likelihood-weighted mass.
* `MixedDist.posterior`: Posterior mixed distribution.
* `MixedDist.posteriorOfLikelihood`: Cross-carrier alias for `posterior`.

## Main statements

* `MixedDist.posterior_atoms_apply`: Pointwise posterior atom-weight formula.
* `MixedDist.posterior_density`: Pointwise posterior density formula.
* `MixedDist.posterior_expect`: Posterior expectation formula.

## Tags

probability, mixed distributions, bayes
-/

@[expose] public section

open BigOperators MeasureTheory

namespace Econlib.Probability

namespace MixedDist

/-- The normalizing constant (marginal likelihood) for Bayesian updating. -/
noncomputable def evidence (d : MixedDist) (likelihood : ℝ → ℝ) : ℝ :=
  (d.atoms.sum fun x w => w * likelihood x) + ∫ x, d.density x * likelihood x

/-- Bayesian posterior of a mixed distribution given a likelihood function. Atom locations are
preserved; weights and density are rescaled by the likelihood. -/
noncomputable def posterior (d : MixedDist) (likelihood : ℝ → ℝ)
    (h_lk_nn : ∀ x, 0 ≤ likelihood x)
    (h_lk_int : Integrable (fun x => d.density x * likelihood x))
    (h_ev : 0 < d.evidence likelihood) : MixedDist where
  atoms := Finsupp.onFinset d.atoms.support
    (fun x => d.atoms x * likelihood x / d.evidence likelihood)
    (fun x hx => by
      -- A reweighted atom can be nonzero only where the original atom is nonzero.
      rw [Finsupp.mem_support_iff]
      intro h0
      apply hx
      change d.atoms x * likelihood x / d.evidence likelihood = 0
      rw [h0, zero_mul, zero_div])
  atoms_nonneg x := by
    rw [Finsupp.onFinset_apply]
    exact div_nonneg (mul_nonneg (d.atoms_nonneg x) (h_lk_nn _)) (le_of_lt h_ev)
  density x := d.density x * likelihood x / d.evidence likelihood
  density_nonneg x :=
    div_nonneg (mul_nonneg (d.density_nonneg x) (h_lk_nn x)) (le_of_lt h_ev)
  density_integrable := (h_lk_int.div_const _)
  total_one := by
    -- Factor `/Z` out of both the atom sum and the density integral, leaving evidence / Z = 1.
    rw [Finsupp.onFinset_sum _ (fun _ => by simp)]
    rw [← Finset.sum_div, integral_div, ← add_div]
    rw [show ((∑ x ∈ d.atoms.support, d.atoms x * likelihood x) +
      ∫ x, d.density x * likelihood x) = d.evidence likelihood from by
      rw [evidence, Finsupp.sum]]
    exact div_self (ne_of_gt h_ev)

/-- Cross-carrier alias for `MixedDist.posterior`, exposing the likelihood-reweighting primitive
under the name `posteriorOfLikelihood` shared with `FinDist`/`CountDist`/`ContDist`. Here
`likelihood : ℝ → ℝ` is the bare per-point likelihood value. -/
noncomputable abbrev posteriorOfLikelihood (d : MixedDist) (likelihood : ℝ → ℝ)
    (h_lk_nn : ∀ x, 0 ≤ likelihood x)
    (h_lk_int : Integrable (fun x => d.density x * likelihood x))
    (h_ev : 0 < d.evidence likelihood) : MixedDist :=
  d.posterior likelihood h_lk_nn h_lk_int h_ev

/-- Pointwise atom-weight formula for the posterior. -/
@[simp] lemma posterior_atoms_apply (d : MixedDist) (likelihood : ℝ → ℝ)
    (h_lk_nn : ∀ x, 0 ≤ likelihood x)
    (h_lk_int : Integrable (fun x => d.density x * likelihood x))
    (h_ev : 0 < d.evidence likelihood) (x : ℝ) :
    (d.posterior likelihood h_lk_nn h_lk_int h_ev).atoms x =
      d.atoms x * likelihood x / d.evidence likelihood := by
  rw [posterior, Finsupp.onFinset_apply]

/-- Pointwise density formula for the posterior. -/
@[simp] lemma posterior_density (d : MixedDist) (likelihood : ℝ → ℝ)
    (h_lk_nn : ∀ x, 0 ≤ likelihood x)
    (h_lk_int : Integrable (fun x => d.density x * likelihood x))
    (h_ev : 0 < d.evidence likelihood) (x : ℝ) :
    (d.posterior likelihood h_lk_nn h_lk_int h_ev).density x =
      d.density x * likelihood x / d.evidence likelihood := rfl

/-! ### Posterior expectation -/

/-- The posterior expectation of `f` is the prior expectation of `likelihood · f`, divided by the
evidence. -/
lemma posterior_expect (d : MixedDist) (likelihood f : ℝ → ℝ)
    (h_lk_nn : ∀ x, 0 ≤ likelihood x)
    (h_lk_int : Integrable (fun x => d.density x * likelihood x))
    (h_ev : 0 < d.evidence likelihood)
    -- Kept for the caller's contract: integrability of the reweighted integrand against `f`.
    (_hf_int : Integrable (fun x => d.density x * likelihood x * f x)) :
    (d.posterior likelihood h_lk_nn h_lk_int h_ev).expect f =
    d.expect (fun x => likelihood x * f x) / d.evidence likelihood := by
  simp only [expect, posterior]
  rw [Finsupp.onFinset_sum _ (fun _ => by simp), Finsupp.sum]
  -- Pull the common `/Z` out of the atom sum and density integral, then match numerators.
  simp_rw [show ∀ y w : ℝ, y * likelihood w / d.evidence likelihood * f w
      = y * (likelihood w * f w) / d.evidence likelihood from fun y w => by ring]
  rw [← Finset.sum_div, integral_div, ← add_div]

end MixedDist

end Econlib.Probability
