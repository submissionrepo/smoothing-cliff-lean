/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.CountDist.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Bayesian updating for countable distributions

This file defines signal marginals and posterior distributions for a countable prior and a
countable signal likelihood. Bayesian updating reweights the prior by a per-state likelihood value
and renormalizes. The primitive `CountDist.posteriorOfLikelihood` takes the likelihood as a bare
function `ℓ : α → ℝ` together with a summability obligation for the joint mass; the signal-kernel
form `CountDist.posterior` is a thin wrapper supplying `θ ↦ (likelihood θ).pmf signal` as the
likelihood value.

## Main definitions

* `CountDist.posteriorOfLikelihoodOrPrior`: Posterior from a bare per-state likelihood value,
  returning the prior on zero evidence.
* `CountDist.posteriorOrPrior`: Posterior after observing a signal, returning the prior on zero
  evidence.
* `CountDist.posteriorOfLikelihood`: Posterior from a bare per-state likelihood value, with a
  positive-evidence hypothesis.
* `CountDist.signalMarginal`: Marginal probability of a signal.
* `CountDist.posterior`: Posterior distribution after observing a signal, with a positive-evidence
  hypothesis.

## Main statements

* `CountDist.posteriorOfLikelihood_apply`: Pointwise posterior formula for the primitive.
* `CountDist.signalMarginal_mul_posterior_apply`: Posterior-marginal product identity.
* `CountDist.signalMarginal_mul_posterior_expect`: Expectation form of the Bayes identity.

## Notes

The `…OrPrior` definitions carry no positivity hypothesis and return the prior when the signal has
zero marginal probability, so the result stays a distribution for every signal; they are the form
used in the total-probability and Bayes-consistency identities, which range over all signals. The
gated `posteriorOfLikelihood`/`posterior` carry a positivity hypothesis under which the Bayes
formula (`posteriorOfLikelihood_apply`, `posterior_apply`) holds, and agree with the `…OrPrior`
form on the value level (`posteriorOfLikelihood_eq_orPrior`, `posterior_eq_orPrior`).

## Tags

probability, countable distributions, bayes
-/

@[expose] public section

open BigOperators

namespace Econlib.Probability
namespace CountDist

/-- Every atom of a countable probability distribution has mass at most one. -/
lemma prob_le_one {α : Type*} [Encodable α] (d : CountDist α) (a : α) : d.pmf a ≤ 1 := by
  have h : ENNReal.ofReal (d.pmf a) ≤ (1 : ENNReal) := PMF.coe_le_one d.toPMF a
  exact ENNReal.ofReal_le_one.mp h

/-- Posterior distribution from a bare per-state likelihood value `ℓ : α → ℝ`, returning the prior
on zero evidence.

Reweight the prior by `ℓ` and renormalize. The summability hypothesis `h_summ` is the countable
analog of "the joint mass is finite". When the normalizer `∑' θ, prior.pmf θ * ℓ θ` is not
positive, the posterior is the prior, so the result stays a distribution. The gated form
`CountDist.posteriorOfLikelihood` carries a positive-evidence hypothesis. -/
noncomputable def posteriorOfLikelihoodOrPrior {α : Type*} [Encodable α]
    (prior : CountDist α) (ℓ : α → ℝ) (h_nn : ∀ a, 0 ≤ ℓ a)
    -- Load-bearing for the contract though unused in the body: without summability the normalizer
    -- `tsum` returns junk zero and the definition would silently reduce to the prior.
    (_h_summ : Summable fun a => prior.pmf a * ℓ a) : CountDist α :=
  let denom := ∑' a : α, prior.pmf a * ℓ a
  if h : 0 < denom then
    { pmf := fun a => prior.pmf a * ℓ a / denom
      nonneg := fun a => div_nonneg
        (mul_nonneg (prior.nonneg a) (h_nn a)) (le_of_lt h)
      tsum_one := by
        rw [tsum_div_const]
        exact div_self (ne_of_gt h) }
  else
    prior

/-- Posterior distribution from a bare per-state likelihood value `ℓ : α → ℝ`, with a
positive-evidence hypothesis.

The hypothesis `h_pos : 0 < ∑' θ, prior.pmf θ * ℓ θ` is the regime in which the Bayes formula
(`posteriorOfLikelihood_apply`) holds. On the value level this agrees with
`posteriorOfLikelihoodOrPrior` (see `posteriorOfLikelihood_eq_orPrior`). -/
noncomputable def posteriorOfLikelihood {α : Type*} [Encodable α]
    (prior : CountDist α) (ℓ : α → ℝ) (h_nn : ∀ a, 0 ≤ ℓ a)
    (h_summ : Summable fun a => prior.pmf a * ℓ a)
    -- `h_pos` is the positive-evidence hypothesis; load-bearing for `posteriorOfLikelihood_apply`.
    (_h_pos : 0 < ∑' a : α, prior.pmf a * ℓ a) : CountDist α :=
  prior.posteriorOfLikelihoodOrPrior ℓ h_nn h_summ

/-- `posteriorOfLikelihood` agrees on the value level with `posteriorOfLikelihoodOrPrior`; the only
difference is the positivity hypothesis. -/
lemma posteriorOfLikelihood_eq_orPrior {α : Type*} [Encodable α]
    (prior : CountDist α) (ℓ : α → ℝ) (h_nn : ∀ a, 0 ≤ ℓ a)
    (h_summ : Summable fun a => prior.pmf a * ℓ a)
    (h_pos : 0 < ∑' a : α, prior.pmf a * ℓ a) :
    prior.posteriorOfLikelihood ℓ h_nn h_summ h_pos =
      prior.posteriorOfLikelihoodOrPrior ℓ h_nn h_summ := rfl

/-- Pointwise Bayes formula: Under positive evidence the posterior mass at `a` is the prior mass
times the likelihood, normalized by the total joint mass. -/
lemma posteriorOfLikelihood_apply {α : Type*} [Encodable α]
    (prior : CountDist α) (ℓ : α → ℝ) (h_nn : ∀ a, 0 ≤ ℓ a)
    (h_summ : Summable fun a => prior.pmf a * ℓ a) (a : α)
    (h_denom : 0 < ∑' a' : α, prior.pmf a' * ℓ a') :
    (prior.posteriorOfLikelihood ℓ h_nn h_summ h_denom).pmf a =
      prior.pmf a * ℓ a / ∑' a' : α, prior.pmf a' * ℓ a' := by
  unfold posteriorOfLikelihood posteriorOfLikelihoodOrPrior
  rw [dif_pos h_denom]

/-- Marginal probability of a signal under a countable prior and a countable likelihood kernel. -/
noncomputable def signalMarginal {α β : Type*} [Encodable α] [Encodable β]
    (prior : CountDist α) (likelihood : α → CountDist β) (signal : β) : ℝ :=
  ∑' state : α, prior.pmf state * (likelihood state).pmf signal

/-- The joint mass of a state and a signal is summable in the state coordinate. -/
lemma summable_joint_signal {α β : Type*} [Encodable α] [Encodable β]
    (prior : CountDist α) (likelihood : α → CountDist β) (signal : β) :
    Summable fun state : α => prior.pmf state * (likelihood state).pmf signal := by
  apply Summable.of_nonneg_of_le
  · intro state
    exact mul_nonneg (prior.nonneg state) ((likelihood state).nonneg signal)
  · intro state
    exact mul_le_of_le_one_right (prior.nonneg state) ((likelihood state).prob_le_one signal)
  · exact prior.summable_pmf

/-- Signal marginals are nonnegative. -/
lemma signalMarginal_nonneg {α β : Type*} [Encodable α] [Encodable β]
    (prior : CountDist α) (likelihood : α → CountDist β) (signal : β) :
    0 ≤ signalMarginal prior likelihood signal := by
  unfold signalMarginal
  exact tsum_nonneg fun state =>
    mul_nonneg (prior.nonneg state) ((likelihood state).nonneg signal)

/-- If a signal has zero marginal probability, every state-signal joint mass is zero. -/
lemma joint_signal_eq_zero_of_signalMarginal_eq_zero
    {α β : Type*} [Encodable α] [Encodable β]
    (prior : CountDist α) (likelihood : α → CountDist β) {signal : β}
    (hzero : signalMarginal prior likelihood signal = 0) (state : α) :
    prior.pmf state * (likelihood state).pmf signal = 0 := by
  have hle := (summable_joint_signal prior likelihood signal).le_tsum state
    (fun other _ => mul_nonneg (prior.nonneg other) ((likelihood other).nonneg signal))
  unfold signalMarginal at hzero
  exact le_antisymm (hzero ▸ hle)
    (mul_nonneg (prior.nonneg state) ((likelihood state).nonneg signal))

/-- Posterior distribution via Bayes' rule for countable distributions, returning the prior on zero
evidence.

The likelihood value of state `θ` is `(likelihood θ).pmf signal`; this is a thin wrapper over
`posteriorOfLikelihoodOrPrior`. When the signal has zero marginal probability the posterior is the
prior, matching the finite `FinDist.posteriorOrPrior` convention. The gated form is
`CountDist.posterior`. -/
noncomputable def posteriorOrPrior {α β : Type*} [Encodable α] [Encodable β]
    (prior : CountDist α) (likelihood : α → CountDist β) (signal : β) : CountDist α :=
  prior.posteriorOfLikelihoodOrPrior (fun state => (likelihood state).pmf signal)
    (fun state => (likelihood state).nonneg signal)
    (summable_joint_signal prior likelihood signal)

/-- Posterior distribution via Bayes' rule for countable distributions, with a positive-evidence
hypothesis.

The hypothesis `h_pos : 0 < signalMarginal prior likelihood signal` is the regime in which the
signal has positive marginal probability and the Bayes formula (`posterior_apply`) holds. On the
value level this agrees with `posteriorOrPrior` (see `posterior_eq_orPrior`). -/
noncomputable def posterior {α β : Type*} [Encodable α] [Encodable β]
    (prior : CountDist α) (likelihood : α → CountDist β) (signal : β)
    -- `h_pos` is the positive-evidence hypothesis; load-bearing for `posterior_apply`.
    (_h_pos : 0 < signalMarginal prior likelihood signal) : CountDist α :=
  prior.posteriorOrPrior likelihood signal

/-- `posterior` agrees on the value level with `posteriorOrPrior`; the only difference is the
positivity hypothesis. -/
lemma posterior_eq_orPrior {α β : Type*} [Encodable α] [Encodable β]
    (prior : CountDist α) (likelihood : α → CountDist β) (signal : β)
    (h_pos : 0 < signalMarginal prior likelihood signal) :
    posterior prior likelihood signal h_pos = posteriorOrPrior prior likelihood signal := rfl

/-- Pointwise Bayes formula: Under positive marginal probability the posterior mass at `state` is
the prior mass times the likelihood, normalized by the signal marginal. -/
lemma posterior_apply {α β : Type*} [Encodable α] [Encodable β]
    (prior : CountDist α) (likelihood : α → CountDist β) (signal : β) (state : α)
    (hdenom : 0 < signalMarginal prior likelihood signal) :
    (posterior prior likelihood signal hdenom).pmf state =
      prior.pmf state * (likelihood state).pmf signal /
        signalMarginal prior likelihood signal := by
  unfold posterior posteriorOrPrior
  exact posteriorOfLikelihood_apply prior _ _ _ state hdenom

/-- The posterior masses sum to one. -/
lemma posteriorOrPrior_is_dist {α β : Type*} [Encodable α] [Encodable β]
    (prior : CountDist α) (likelihood : α → CountDist β) (signal : β) :
    ∑' state : α, (posteriorOrPrior prior likelihood signal).pmf state = 1 :=
  (posteriorOrPrior prior likelihood signal).tsum_one

/-- Multiplying a posterior atom by the signal marginal recovers the joint mass. Stated for
`posteriorOrPrior` since the identity must hold even when the signal has zero marginal. -/
lemma signalMarginal_mul_posterior_apply
    {α β : Type*} [Encodable α] [Encodable β]
    (prior : CountDist α) (likelihood : α → CountDist β) (signal : β) (state : α) :
    signalMarginal prior likelihood signal *
        (posteriorOrPrior prior likelihood signal).pmf state =
      prior.pmf state * (likelihood state).pmf signal := by
  by_cases h : 0 < signalMarginal prior likelihood signal
  · rw [← posterior_eq_orPrior prior likelihood signal h,
        posterior_apply prior likelihood signal state h]
    field_simp [ne_of_gt h]
  · have hzero : signalMarginal prior likelihood signal = 0 :=
      le_antisymm (not_lt.mp h) (signalMarginal_nonneg prior likelihood signal)
    have hjoint :=
      joint_signal_eq_zero_of_signalMarginal_eq_zero prior likelihood hzero state
    rw [hzero, hjoint]
    simp

/-- Multiplying a posterior expectation by the signal marginal recovers the joint expectation over
states for that signal. Stated for `posteriorOrPrior` since the identity must hold even when the
signal has zero marginal. -/
lemma signalMarginal_mul_posterior_expect
    {α β : Type*} [Encodable α] [Encodable β]
    (prior : CountDist α) (likelihood : α → CountDist β) (signal : β) (f : α → ℝ) :
    signalMarginal prior likelihood signal *
        (posteriorOrPrior prior likelihood signal).expect f =
      ∑' state : α, prior.pmf state * (likelihood state).pmf signal * f state := by
  rw [CountDist.expect_eq_tsum]
  rw [← tsum_mul_left]
  refine tsum_congr fun state => ?_
  rw [← mul_assoc, signalMarginal_mul_posterior_apply prior likelihood signal state]

/-- On finite state spaces, `signalMarginal` is the usual finite marginal likelihood sum. -/
lemma signalMarginal_eq_finsum
    {α β : Type*} [Encodable α] [Encodable β] [Fintype α]
    (prior : CountDist α) (likelihood : α → CountDist β) (signal : β) :
    signalMarginal prior likelihood signal =
      ∑ state : α, prior.pmf state * (likelihood state).pmf signal := by
  simp [signalMarginal, tsum_fintype]

/-- Law of total probability for finite state and signal spaces. The sum ranges over every signal,
including zero-marginal ones, so it is stated for the totalized `posteriorOrPrior`. -/
lemma total_probability_fintype
    {α β : Type*} [Encodable α] [Encodable β] [Fintype β]
    (prior : CountDist α) (likelihood : α → CountDist β) (state : α) :
    ∑ signal : β,
        signalMarginal prior likelihood signal *
          (posteriorOrPrior prior likelihood signal).pmf state =
      prior.pmf state := by
  simp_rw [signalMarginal_mul_posterior_apply prior likelihood]
  have hsum : (∑ signal : β, (likelihood state).pmf signal) = 1 := by
    simpa [tsum_fintype] using (likelihood state).tsum_one
  rw [← Finset.mul_sum, hsum, mul_one]

/-- Bayes consistency for finite state and signal spaces.

Averaging posterior expectations over signal marginals recovers the prior expectation. The sum
ranges over every signal, including zero-marginal ones, so it is stated for the totalized
`posteriorOrPrior`. -/
lemma bayes_consistent_fintype
    {α β : Type*} [Encodable α] [Encodable β] [Finite α] [Fintype β]
    (prior : CountDist α) (likelihood : α → CountDist β) (f : α → ℝ) :
    ∑ signal : β,
        signalMarginal prior likelihood signal *
          (posteriorOrPrior prior likelihood signal).expect f =
      prior.expect f := by
  simp_rw [signalMarginal_mul_posterior_expect prior likelihood]
  rw [CountDist.expect_eq_tsum]
  have : Fintype α := Fintype.ofFinite α; simp only [tsum_fintype]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro state _
  have hsum : (∑ signal : β, (likelihood state).pmf signal) = 1 := by
    simpa [tsum_fintype] using (likelihood state).tsum_one
  -- ∑ signal, (p·f)·L(signal) = p·f·∑ L = p·f
  simp_rw [mul_right_comm (prior.pmf state) _ (f state), ← Finset.mul_sum, hsum, mul_one]

end CountDist
end Econlib.Probability
