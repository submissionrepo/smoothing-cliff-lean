/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.Basic

open Econlib.Probability

/-!
# Signal construction from Bayes-plausible splittings

Any **Bayes-plausible** splitting of a prior can be realized by a signal structure, for an
arbitrary prior — no full-support assumption is needed (Kamenica and Gentzkow 2011). Given weights
`w` and beliefs `μ_s` satisfying `∑_s w(s) μ_s(θ) = p(θ)`, we construct a likelihood `π(θ, ·)`
whose posteriors match the prescribed beliefs `μ_s` on every signal of positive weight.

## Main definitions

* `signalFromSplitting` — the signal structure realizing a Bayes-plausible splitting.

## Main statements

* `signalMarginal_signalFromSplitting` — its marginal signal law is the splitting weights.
* `posterior_signalFromSplitting` — its posterior on a positive-weight signal is the prescribed
  belief.
* `exists_signal_from_splitting` — existence form: A signal structure realizing the splitting.

## Notes

At a state `θ` of positive prior probability the likelihood row is `π(θ, s) = w(s) μ_s(θ) / p(θ)`,
the usual Bayes inversion. At a state `θ` with `p(θ) = 0` the formula is undefined, but the row is
irrelevant: Bayes-plausibility `∑_s w(s) μ_s(θ) = 0` together with nonnegativity forces every term
`w(s) μ_s(θ) = 0`, so the prescribed posteriors put zero mass on such `θ` wherever `w(s) > 0`, and
the row enters the marginal signal law only through the factor `p(θ) = 0`. The construction assigns
the weights `w` there as an arbitrary valid row.

## References

* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).

## Tags

persuasion, bayesian persuasion, splitting, signal structure
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Finite

variable {n m : ℕ}

/-- **Key fact at a zero-prior state.** When `p(θ) = 0`, Bayes plausibility forces every weighted
belief term `w(s) μ_s(θ)` to vanish: A nonnegative sum equal to zero has all-zero terms. This makes
the likelihood row at `θ` irrelevant to both the marginal signal law and the recovered
posteriors. -/
private lemma weighted_belief_eq_zero_of_prior_zero
    (prior : FinDist (Fin n)) (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n))
    (h_bp : ∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = prior.pmf i)
    {θ : Fin n} (hθ : prior.pmf θ = 0) (s : Fin m) :
    weights.pmf s * (beliefs s).pmf θ = 0 := by
  have h_nonneg : ∀ s' ∈ Finset.univ, 0 ≤ weights.pmf s' * (beliefs s').pmf θ :=
    fun s' _ => mul_nonneg (weights.nonneg s') ((beliefs s').nonneg θ)
  have h_zero : ∑ s', weights.pmf s' * (beliefs s').pmf θ = 0 := (h_bp θ).trans hθ
  exact (Finset.sum_eq_zero_iff_of_nonneg h_nonneg).mp h_zero s (Finset.mem_univ s)

/-- Construct a signal structure from a Bayes-plausible splitting of an **arbitrary** prior. At a
state `θ` of positive prior probability the likelihood is `π(θ, s) = w(s) μ_s(θ) / p(θ)`; at a
state with `p(θ) = 0` (where this formula is undefined) the row is irrelevant, so we assign the
weights `w` as an arbitrary valid distribution. -/
noncomputable def signalFromSplitting
    (prior : FinDist (Fin n))
    (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n))
    (h_bp : ∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = prior.pmf i) :
    SignalStructure n m where
  π θ :=
    if hθ : prior.pmf θ = 0 then weights
    else
      { pmf := fun s => weights.pmf s * (beliefs s).pmf θ / prior.pmf θ
        nonneg := fun s => div_nonneg
          (mul_nonneg (weights.nonneg s) ((beliefs s).nonneg θ)) (prior.nonneg θ)
        sum_one := by
          rw [← Finset.sum_div, h_bp θ]
          exact div_self hθ }

/-- For every state `θ`, the marginal contribution `p(θ) · π(θ, s)` of the constructed signal
equals the weighted belief `w(s) μ_s(θ)`. On positive-prior states this cancels the division; on
zero-prior states both sides vanish. -/
private lemma prior_mul_signalFromSplitting
    (prior : FinDist (Fin n)) (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n))
    (h_bp : ∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = prior.pmf i) (θ : Fin n) (s : Fin m) :
    prior.pmf θ * ((signalFromSplitting prior weights beliefs h_bp).π θ).pmf s
    = weights.pmf s * (beliefs s).pmf θ := by
  dsimp only [signalFromSplitting]
  by_cases hθ : prior.pmf θ = 0
  · rw [dif_pos hθ, hθ, zero_mul,
      weighted_belief_eq_zero_of_prior_zero prior weights beliefs h_bp hθ s]
  · rw [dif_neg hθ]
    exact mul_div_cancel₀ _ hθ

/-- The marginal signal probability of the constructed signal equals the weight. -/
lemma signalMarginal_signalFromSplitting
    (prior : FinDist (Fin n))
    (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n))
    (h_bp : ∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = prior.pmf i) (s : Fin m) :
    prior.signalMarginal (signalFromSplitting prior weights beliefs h_bp).π s
    = weights.pmf s := by
  simp only [FinDist.signalMarginal_eq_sum]
  -- Each summand equals `w(s) μ_s(θ)` (positive- and zero-prior states alike), leaving
  -- `w(s) ∑_θ μ_s(θ) = w(s)` since the beliefs are distributions.
  simp_rw [prior_mul_signalFromSplitting prior weights beliefs h_bp, ← Finset.mul_sum,
    (beliefs s).sum_one, mul_one]

/-- **The posterior of the constructed signal recovers the prescribed belief.** On any signal of
positive weight, Bayes' rule inverts the construction exactly: Positive-prior states invert the
division, and zero-prior states match because both the posterior and the prescribed belief place
zero mass there. -/
lemma posterior_signalFromSplitting (prior : FinDist (Fin n))
    (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n))
    (h_bp : ∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = prior.pmf i)
    (s : Fin m) (h_ws_pos : 0 < weights.pmf s)
    (h_denom_pos : 0 < ∑ θ,
      prior.pmf θ * ((signalFromSplitting prior weights beliefs h_bp).π θ).pmf s) :
    prior.posterior (signalFromSplitting prior weights beliefs h_bp).π s h_denom_pos
      = beliefs s := by
  have h_marg := signalMarginal_signalFromSplitting prior weights beliefs h_bp s
  -- The Bayes normalizer is the marginal `w(s)`; the numerator is `p(θ) · π(θ, s) = w(s) μ_s(θ)`.
  have h_denom_eq : ∑ θ', prior.pmf θ' *
      ((signalFromSplitting prior weights beliefs h_bp).π θ').pmf s = weights.pmf s := by
    rw [← FinDist.signalMarginal_eq_sum, h_marg]
  ext θ
  rw [FinDist.posterior_apply _ _ _ _ h_denom_pos, FinDist.signalMarginal_eq_sum, h_denom_eq,
    prior_mul_signalFromSplitting prior weights beliefs h_bp,
    mul_div_cancel_left₀ _ (ne_of_gt h_ws_pos)]

/-- The constructed-signal Bayes normalizer at `s` is positive whenever the splitting weight there
is positive. This supplies the positivity hypothesis of `posterior_signalFromSplitting`. -/
lemma denom_pos_signalFromSplitting (prior : FinDist (Fin n))
    (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n))
    (h_bp : ∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = prior.pmf i)
    (s : Fin m) (h_ws_pos : 0 < weights.pmf s) :
    0 < ∑ θ, prior.pmf θ * ((signalFromSplitting prior weights beliefs h_bp).π θ).pmf s := by
  rw [← FinDist.signalMarginal_eq_sum,
    signalMarginal_signalFromSplitting prior weights beliefs h_bp s]
  exact h_ws_pos

/-- Every Bayes-plausible splitting of a prior is realized by some signal structure: A
Bayes-plausible signal whose posterior on each positive-marginal signal is the prescribed belief. -/
theorem exists_signal_from_splitting (prior : FinDist (Fin n))
    (m : ℕ) (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n))
    (h_bp : ∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = prior.pmf i) :
    ∃ σ : SignalStructure n m,
      BayesPlausible prior σ ∧
      ∀ s, (hs : 0 < prior.signalMarginal σ.π s) →
        prior.posterior σ.π s hs = beliefs s := by
  refine ⟨signalFromSplitting prior weights beliefs h_bp,
    SignalStructure.bayesPlausible prior _, fun s hs => ?_⟩
  -- A positive marginal of the constructed signal is exactly a positive weight.
  have h_ws_pos : 0 < weights.pmf s := by
    rwa [signalMarginal_signalFromSplitting] at hs
  exact posterior_signalFromSplitting prior weights beliefs h_bp s h_ws_pos hs

end Econlib.MechanismDesign.InformationDesign.Persuasion.Finite
