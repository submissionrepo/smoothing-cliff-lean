/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Expect
public import Mathlib.Algebra.BigOperators.Field

/-!
# Bayesian updating for finite distributions

This file defines posterior beliefs for finite priors and finite signal likelihoods, together with
finite total-probability and consistency identities.

Bayesian updating is one operation across every carrier: Reweight the prior by a per-state
likelihood value and renormalize. The primitive `FinDist.posteriorOfLikelihood` takes the
likelihood as a bare function `ℓ : α → ℝ`. The signal-kernel form `FinDist.posterior` is a thin
wrapper that supplies `θ ↦ (likelihood θ).pmf signal` as the likelihood value.

## Main definitions

* `FinDist.signalMarginal`: Marginal (evidence) probability of a signal — the Bayes normalizer and
  the positivity gate of `FinDist.posterior` (mirrors `CountDist.signalMarginal`).
* `FinDist.posteriorOfLikelihoodOrPrior`: Totalized posterior from a bare per-state likelihood
  value (returns the prior on zero evidence).
* `FinDist.posteriorOrPrior`: Totalized posterior after a signal (returns the prior on zero
  evidence).
* `FinDist.posteriorOfLikelihood`: Posterior from a bare per-state likelihood value, gated on
  positive evidence.
* `FinDist.posterior`: Posterior distribution after a signal, gated on positive evidence.

## Main statements

* `FinDist.posteriorOfLikelihood_apply`: Pointwise posterior formula for the primitive.
* `FinDist.posterior_apply`: Pointwise posterior formula.
* `FinDist.total_probability`: Total-probability identity.
* `FinDist.total_probability_signalMarginal`: Total probability with the evidence sum named
  `signalMarginal` (totalized `posteriorOrPrior` value).
* `FinDist.total_probability_of_posterior`: Total probability in the positive-marginal regime,
  stated against the gated `posterior`.
* `FinDist.bayes_consistent`: Posterior expectations average to prior expectation.

## Notes

The names `posteriorOfLikelihood` and `posterior` carry a positive-evidence hypothesis
`0 < ∑ θ, prior.pmf θ * ℓ θ`, the regime in which the Bayes formula is valid; the characterization
lemmas (`posteriorOfLikelihood_apply`, `posterior_apply`) hold under this hypothesis. The totalized
conventions `posteriorOfLikelihoodOrPrior`/`posteriorOrPrior` keep the result total by returning
the prior on zero evidence (the signal has zero marginal probability); a value read under an
`…OrPrior` name must not be interpreted as a posterior without first checking that the evidence is
positive.

## Tags

probability, finite distributions, bayes
-/

@[expose] public section

open BigOperators

namespace Econlib.Probability
namespace FinDist

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Marginal (evidence) probability of a signal under a finite prior and a finite likelihood
kernel: The prior-weighted total likelihood `∑ θ, prior.pmf θ * (likelihood θ).pmf signal`. This is
the normalizer in Bayes' rule and the positivity gate of `FinDist.posterior`. Mirrors
`CountDist.signalMarginal`, so the two carriers read in parallel. -/
noncomputable def signalMarginal
    (prior : FinDist α) (likelihood : α → FinDist β) (signal : β) : ℝ :=
  ∑ θ : α, prior.pmf θ * (likelihood θ).pmf signal

/-- `signalMarginal` is the prior-weighted likelihood sum. In the `findist_eval` set so worked
examples unfold the marginal to concrete arithmetic; kept off the default simp set so the name
survives as a handle in theoretical files. -/
@[findist_eval] lemma signalMarginal_eq_sum
    (prior : FinDist α) (likelihood : α → FinDist β) (signal : β) :
    prior.signalMarginal likelihood signal
      = ∑ θ : α, prior.pmf θ * (likelihood θ).pmf signal := rfl

/-- Signal marginals are nonnegative (a sum of nonnegative prior-weighted likelihoods). -/
lemma signalMarginal_nonneg
    (prior : FinDist α) (likelihood : α → FinDist β) (signal : β) :
    0 ≤ prior.signalMarginal likelihood signal :=
  Finset.sum_nonneg fun θ _ => mul_nonneg (prior.nonneg θ) ((likelihood θ).nonneg signal)

/-- Totalized posterior distribution from a bare per-state likelihood value `ℓ : α → ℝ`.

This is the carrier-independent Bayesian primitive: Reweight the prior by `ℓ` and renormalize. If
the normalizer `∑ θ, prior.pmf θ * ℓ θ` is not positive, the posterior is defined to be the prior,
keeping the result total. A value read under this name on zero evidence is the prior, not a
posterior; the positivity-gated form is `FinDist.posteriorOfLikelihood`. -/
noncomputable def posteriorOfLikelihoodOrPrior
    (prior : FinDist α) (ℓ : α → ℝ) (h_nn : ∀ θ, 0 ≤ ℓ θ) : FinDist α :=
  let denom := ∑ θ : α, prior.pmf θ * ℓ θ
  if h : 0 < denom then
    { pmf := fun θ => (prior.pmf θ * ℓ θ) / denom,
      nonneg := fun θ => div_nonneg
        (mul_nonneg (prior.nonneg θ) (h_nn θ)) (le_of_lt h),
      sum_one := by rw [← Finset.sum_div]; exact div_self (ne_of_gt h) }
  else
    prior

/-- Totalized posterior distribution via Bayes' rule, finite case.

The effective likelihood value of state `θ` is `(likelihood θ).pmf signal`; this is a thin wrapper
over `posteriorOfLikelihoodOrPrior`. Returns the prior on zero evidence; the positivity-gated form
is `FinDist.posterior`. -/
noncomputable def posteriorOrPrior
  (prior : FinDist α) (likelihood : α → FinDist β) (signal : β) : FinDist α :=
  prior.posteriorOfLikelihoodOrPrior (fun θ => (likelihood θ).pmf signal)
    (fun θ => (likelihood θ).nonneg signal)

/-- Posterior distribution from a bare per-state likelihood value `ℓ : α → ℝ`, gated on positive
evidence.

The hypothesis `h_pos : 0 < ∑ θ, prior.pmf θ * ℓ θ` is the positivity gate: It forces the regime in
which the Bayes formula (`posteriorOfLikelihood_apply`) is valid. On the value level this agrees
with `posteriorOfLikelihoodOrPrior` (see the bridge lemma `posteriorOfLikelihood_eq_orPrior`), but
the hypothesis means this name cannot be formed on zero evidence. -/
noncomputable def posteriorOfLikelihood
    (prior : FinDist α) (ℓ : α → ℝ) (h_nn : ∀ θ, 0 ≤ ℓ θ)
    -- `h_pos` is the positivity gate; it is load-bearing for the characterization lemma
    -- `posteriorOfLikelihood_apply` even though the body reuses the total convention.
    (_h_pos : 0 < ∑ θ : α, prior.pmf θ * ℓ θ) : FinDist α :=
  prior.posteriorOfLikelihoodOrPrior ℓ h_nn

/-- Posterior distribution via Bayes' rule, finite case, gated on positive evidence.

The hypothesis `h_pos : 0 < prior.signalMarginal likelihood signal` is the positivity gate: It
forces the regime in which the signal has positive marginal probability and the Bayes formula
(`posterior_apply`) is valid. On the value level this agrees with `posteriorOrPrior` (see the
bridge lemma `posterior_eq_orPrior`). -/
noncomputable def posterior
  (prior : FinDist α) (likelihood : α → FinDist β) (signal : β)
  -- `h_pos` is the positivity gate; load-bearing for `posterior_apply`.
  (_h_pos : 0 < prior.signalMarginal likelihood signal) : FinDist α :=
  prior.posteriorOrPrior likelihood signal

/-- The positivity-gated posterior agrees on the value level with the totalized `…OrPrior`
convention; the only difference is the load-bearing positivity gate. Applied explicitly (not
`@[simp]`) so that proofs working on `posterior` are not silently rewritten to the totalized
form. -/
lemma posteriorOfLikelihood_eq_orPrior (prior : FinDist α) (ℓ : α → ℝ)
    (h_nn : ∀ θ, 0 ≤ ℓ θ) (h_pos : 0 < ∑ θ : α, prior.pmf θ * ℓ θ) :
    prior.posteriorOfLikelihood ℓ h_nn h_pos = prior.posteriorOfLikelihoodOrPrior ℓ h_nn := rfl

/-- The positivity-gated posterior agrees on the value level with the totalized `…OrPrior`
convention; the only difference is the load-bearing positivity gate. Applied explicitly (not
`@[simp]`) so that proofs working on `posterior` are not silently rewritten to the totalized
form. -/
lemma posterior_eq_orPrior (prior : FinDist α) (lk : α → FinDist β) (s : β)
    (h_pos : 0 < prior.signalMarginal lk s) :
    prior.posterior lk s h_pos = prior.posteriorOrPrior lk s := rfl

/-- Pointwise Bayes formula for the likelihood-primitive posterior: On positive evidence the mass
at `θ` is the prior-weighted likelihood `prior.pmf θ * ℓ θ` over the normalizer.

In the `findist_eval` set: The positivity gate `h_denom` is bound by the posterior term itself, so
`simp [findist_eval]` evaluates a concrete posterior mass without re-supplying it. Opt-in only (not
global `@[simp]`), so proofs reasoning abstractly about `posterior` are not silently expanded. -/
@[findist_eval]
lemma posteriorOfLikelihood_apply (prior : FinDist α) (ℓ : α → ℝ) (h_nn : ∀ θ, 0 ≤ ℓ θ)
    (θ : α) (h_denom : 0 < ∑ θ', prior.pmf θ' * ℓ θ') :
    (prior.posteriorOfLikelihood ℓ h_nn h_denom).pmf θ
    = (prior.pmf θ * ℓ θ) / ∑ θ', prior.pmf θ' * ℓ θ' := by
  unfold posteriorOfLikelihood posteriorOfLikelihoodOrPrior; rw [dif_pos h_denom]

/-- Pointwise Bayes formula for the signal-kernel posterior: On positive marginal the mass at `θ`
is `prior.pmf θ * (lk θ).pmf s` over the signal's marginal probability.

In the `findist_eval` set (see `posteriorOfLikelihood_apply` for the rationale):
`simp [findist_eval]` evaluates a concrete posterior mass without re-supplying the
marginal-positivity gate. -/
@[findist_eval]
lemma posterior_apply (prior : FinDist α) (lk : α → FinDist β) (s : β)
  (θ : α) (h_denom : 0 < prior.signalMarginal lk s) :
    (prior.posterior lk s h_denom).pmf θ
    = (prior.pmf θ * (lk θ).pmf s) / prior.signalMarginal lk s := by
  rw [signalMarginal_eq_sum]
  unfold posterior posteriorOrPrior; exact posteriorOfLikelihood_apply prior _ _ θ h_denom

/-- On the positive-marginal regime the totalized posterior obeys the Bayes formula, since there it
coincides with the positivity-gated `posterior`. -/
lemma posteriorOrPrior_apply (prior : FinDist α) (lk : α → FinDist β) (s : β)
  (θ : α) (h_denom : 0 < ∑ θ', prior.pmf θ' * (lk θ').pmf s) :
    (prior.posteriorOrPrior lk s).pmf θ
    = (prior.pmf θ * (lk θ).pmf s) / ∑ θ', prior.pmf θ' * (lk θ').pmf s := by
  rw [← posterior_eq_orPrior prior lk s h_denom]; exact posterior_apply prior lk s θ h_denom

/-- When the Bayes normalizer is not positive — the signal has zero marginal probability — the
totalized posterior defaults to the prior by convention (see `posteriorOrPrior`). -/
lemma posteriorOrPrior_eq_prior_of_denom_nonpos (prior : FinDist α) (lk : α → FinDist β) (s : β)
    (h : ¬ 0 < ∑ θ', prior.pmf θ' * (lk θ').pmf s) :
    prior.posteriorOrPrior lk s = prior := by
  unfold posteriorOrPrior posteriorOfLikelihoodOrPrior
  exact dif_neg h

/-- The totalized posterior is a distribution: Its masses sum to one (immediate from `sum_one`). -/
lemma posteriorOrPrior_is_dist (prior : FinDist α) (lk : α → FinDist β) (s : β) :
    ∑ i, (prior.posteriorOrPrior lk s).pmf i = 1 :=
  (prior.posteriorOrPrior lk s).sum_one

/-- Updating a point-mass prior `pure θ₀` on any signal the support assigns positive likelihood
leaves the belief at `pure θ₀`: A degenerate prior is unmoved by evidence. -/
lemma posterior_pure (θ₀ : α) (lk : α → FinDist β) (s : β)
    (h_pos : 0 < (lk θ₀).pmf s) :
    (FinDist.pure θ₀).posterior lk s
      (by simpa [signalMarginal, pure] using h_pos) = FinDist.pure θ₀ := by
  have h_denom_pos : 0 < ∑ θ, (FinDist.pure θ₀).pmf θ * (lk θ).pmf s := by simp [pure, h_pos]
  unfold posterior posteriorOrPrior posteriorOfLikelihoodOrPrior; rw [dif_pos h_denom_pos]
  ext θ; simp only [pure]
  split_ifs with h
  · subst h; simp only [one_mul]
    have : ∑ x, (if θ₀ = x then 1 else 0) * (lk x).pmf s = (lk θ₀).pmf s := by simp
    rw [this, div_self (ne_of_gt h_pos)]
  · simp only [zero_mul, zero_div]

/-- When the Bayes normalizer is not positive, every prior-weighted likelihood term vanishes (each
term is nonnegative, so a non-positive total forces them all to zero). Shared by the degenerate
branch of `total_probability` and `bayes_consistent`. -/
private lemma weighted_likelihood_eq_zero_of_denom_nonpos
    (prior : FinDist α) (lk : α → FinDist β) (s : β)
    (h : ¬ 0 < ∑ θ', prior.pmf θ' * (lk θ').pmf s) (θ : α) :
    prior.pmf θ * (lk θ).pmf s = 0 := by
  have h_nonneg : ∀ θ' ∈ Finset.univ, 0 ≤ prior.pmf θ' * (lk θ').pmf s :=
    fun θ' _ => mul_nonneg (prior.nonneg θ') ((lk θ').nonneg s)
  have h_zero : ∑ θ', prior.pmf θ' * (lk θ').pmf s = 0 :=
    le_antisymm (not_lt.mp h) (Finset.sum_nonneg h_nonneg)
  exact (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_zero θ (Finset.mem_univ _)

/-- **Total probability:** averaging the posterior mass at `θ₀` against each signal's marginal
probability recovers the prior mass `prior.pmf θ₀`. -/
lemma total_probability
  (prior : FinDist α) (lk : α → FinDist β) (θ₀ : α) :
    ∑ s : β, (∑ θ : α, prior.pmf θ * (lk θ).pmf s) * (prior.posteriorOrPrior lk s).pmf θ₀
    = prior.pmf θ₀ := by
  have h_summand : ∀ s, (∑ θ, prior.pmf θ * (lk θ).pmf s) * (prior.posteriorOrPrior lk s).pmf θ₀ =
      prior.pmf θ₀ * (lk θ₀).pmf s := by
    intro s; unfold posteriorOrPrior posteriorOfLikelihoodOrPrior
    by_cases h : 0 < ∑ θ, prior.pmf θ * (lk θ).pmf s
    · rw [dif_pos h]; simp only; rw [mul_div_cancel₀ _ (ne_of_gt h)]
    · -- Degenerate branch: the normalizer is zero, so both sides collapse to zero.
      rw [dif_neg h, Finset.sum_eq_zero
        (fun θ _ => weighted_likelihood_eq_zero_of_denom_nonpos prior lk s h θ), zero_mul]
      exact (weighted_likelihood_eq_zero_of_denom_nonpos prior lk s h θ₀).symm
  simp_rw [h_summand, ← Finset.mul_sum, (lk θ₀).sum_one, mul_one]

/-- **Total probability, `signalMarginal` form.** Naming the Bayes normalizer, the
`signalMarginal`-weighted posterior masses at `θ₀` average back to the prior mass. This is
`total_probability` with the evidence sum abbreviated; the sum still ranges over every signal,
including zero-marginal ones, so it is stated for the totalized `posteriorOrPrior`. -/
lemma total_probability_signalMarginal
    (prior : FinDist α) (lk : α → FinDist β) (θ₀ : α) :
    ∑ s : β, prior.signalMarginal lk s * (prior.posteriorOrPrior lk s).pmf θ₀ = prior.pmf θ₀ := by
  simp_rw [signalMarginal_eq_sum]; exact total_probability prior lk θ₀

/-- **Total probability, posterior form.** When every signal has positive marginal, the
`signalMarginal`-weighted `posterior` masses (the positivity-gated `FinDist.posterior`) average
back to the prior mass. The positive-marginal hypothesis lets the law be cited directly against
`posterior` objects, without detouring through the totalized `posteriorOrPrior`. -/
lemma total_probability_of_posterior
    (prior : FinDist α) (lk : α → FinDist β) (θ₀ : α)
    (h_pos : ∀ s, 0 < prior.signalMarginal lk s) :
    ∑ s : β, prior.signalMarginal lk s * (prior.posterior lk s (h_pos s)).pmf θ₀
      = prior.pmf θ₀ := by
  rw [← total_probability_signalMarginal prior lk θ₀]
  exact Finset.sum_congr rfl fun s _ => by rw [posterior_eq_orPrior prior lk s (h_pos s)]

/-- A signal whose likelihood `lk θ` is the same distribution `d` for every state is uninformative:
The posterior equals the prior. -/
lemma posterior_uniform_likelihood
  (prior : FinDist α) (lk : α → FinDist β) (s : β)
  (d : FinDist β) (h : ∀ θ, lk θ = d) (h_pos : 0 < d.pmf s)
  (h_denom : 0 < prior.signalMarginal lk s :=
    by
      rw [signalMarginal_eq_sum]
      have hsum : ∑ θ, prior.pmf θ * (lk θ).pmf s = (∑ θ, prior.pmf θ) * d.pmf s := by
        simp_rw [h, Finset.sum_mul]
      rw [hsum, prior.sum_one, one_mul]; exact h_pos) :
    prior.posterior lk s h_denom = prior := by
  have h_denom' : 0 < ∑ θ, prior.pmf θ * (lk θ).pmf s := h_denom
  unfold posterior posteriorOrPrior posteriorOfLikelihoodOrPrior; rw [dif_pos h_denom']
  ext θ; simp only [h]
  have h_denom_eq : ∑ θ', prior.pmf θ' * d.pmf s = d.pmf s := by
    rw [← Finset.sum_mul, prior.sum_one, one_mul]
  rw [h_denom_eq]
  exact mul_div_cancel_of_imp (fun h0 => absurd h_pos (by rw [h0]; exact lt_irrefl 0))

/-- **Bayesian consistency:** the marginal-weighted average of posterior expectations of any `f`
equals the prior expectation `prior.expect f`. -/
lemma bayes_consistent (prior : FinDist α) (lk : α → FinDist β) (f : α → ℝ) :
    ∑ s : β, (∑ θ : α, prior.pmf θ * (lk θ).pmf s) * (prior.posteriorOrPrior lk s).expect f
    = prior.expect f := by
  simp only [FinDist.expect]
  -- Each summand: denom_s * ∑_θ posterior(θ|s)*f(θ) = ∑_θ prior(θ)*lk(θ,s)*f(θ)
  have h_summand : ∀ s, (∑ θ, prior.pmf θ * (lk θ).pmf s) *
      ∑ θ, (prior.posteriorOrPrior lk s).pmf θ * f θ =
    ∑ θ, prior.pmf θ * (lk θ).pmf s * f θ := by
    intro s; rw [Finset.mul_sum]; congr 1; ext θ
    unfold FinDist.posteriorOrPrior posteriorOfLikelihoodOrPrior
    by_cases h : 0 < ∑ θ', prior.pmf θ' * (lk θ').pmf s
    · rw [dif_pos h]; field_simp
    · -- Degenerate branch: the normalizer is zero, killing the summand.
      rw [dif_neg h, Finset.sum_eq_zero
        (fun θ' _ => weighted_likelihood_eq_zero_of_denom_nonpos prior lk s h θ'), zero_mul,
        weighted_likelihood_eq_zero_of_denom_nonpos prior lk s h θ, zero_mul]
  simp_rw [h_summand]
  -- Swap sums, factor out, use ∑_s lk(θ,s) = 1
  rw [Finset.sum_comm]; congr 1; ext θ
  have : ∀ s, prior.pmf θ * (lk θ).pmf s * f θ
    = prior.pmf θ * f θ * (lk θ).pmf s := fun s => by ring
  simp_rw [this, ← Finset.mul_sum, (lk θ).sum_one, mul_one]

end FinDist

/-- Finite posterior expectations average back to the prior expectation. This is the `Fin`-indexed
specialization of `FinDist.bayes_consistent`. The sum ranges over every signal, including
zero-marginal ones, so it is stated for the totalized `posteriorOrPrior`. -/
lemma bayes_consistent {n m : ℕ} (prior : FinDist (Fin n))
    (lk : Fin n → FinDist (Fin m)) (f : Fin n → ℝ) :
    ∑ s : Fin m, (∑ θ : Fin n, prior.pmf θ * (lk θ).pmf s) * (prior.posteriorOrPrior lk s).expect f
    = prior.expect f :=
  FinDist.bayes_consistent prior lk f

end Econlib.Probability
