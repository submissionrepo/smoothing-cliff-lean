/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.Basic

open Econlib.Probability

/-!
# The no-information benchmark

When the sender's payoff function is concave over the belief simplex, no signal structure can
improve on the no-information benchmark `v(prior)` (Kamenica and Gentzkow 2011).

## Main definitions

* `ConcaveOnSimplex` — Jensen-type concavity for finite Bayes-plausible splittings.

## Main statements

* `expectedSenderPayoff_eq_expect` — rewrites `expectedSenderPayoff` as a `FinDist.expect`.
* `strategic_ambiguity_finite` — a concave payoff makes no information optimal.

## References

* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).

## Tags

persuasion, information design, concavity, strategic ambiguity
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Finite

variable {n m : ℕ}

/-- A function on the simplex is concave if Jensen's inequality holds for all finite
Bayes-plausible splittings. -/
def ConcaveOnSimplex (v : FinDist (Fin n) → ℝ) : Prop :=
  ∀ (k : ℕ) (weights : FinDist (Fin k)) (beliefs : Fin k → FinDist (Fin n)) (μ : FinDist (Fin n)),
    (∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = μ.pmf i) →
    weights.expect (fun s => v (beliefs s)) ≤ v μ

/-- The sender's expected payoff equals the marginal signal distribution's expectation of `v`
applied to posteriors. -/
lemma expectedSenderPayoff_eq_expect (prior : FinDist (Fin n)) (σ : SignalStructure n m)
    (v : FinDist (Fin n) → ℝ) :
    expectedSenderPayoff prior σ v =
    (signalLaw prior σ).expect (fun s => v (prior.posteriorOrPrior σ.π s)) := by
  unfold expectedSenderPayoff FinDist.expect signalLaw FinDist.signalMarginal
  congr 1; ext s
  by_cases hs : 0 < ∑ θ, prior.pmf θ * (σ.π θ).pmf s
  · rw [dif_pos hs]
  · rw [dif_neg hs]
    push Not at hs
    have h_zero : (∑ θ, prior.pmf θ * (σ.π θ).pmf s) = 0 :=
      le_antisymm hs (Finset.sum_nonneg fun θ _ =>
        mul_nonneg (prior.nonneg θ) ((σ.π θ).nonneg s))
    simp [h_zero]

/-- **No-information benchmark (finite case)** (Kamenica and Gentzkow 2011). If the sender's payoff
is concave over the belief simplex, no signal structure can improve on the no-information benchmark
`v(prior)`. -/
theorem strategic_ambiguity_finite {n m : ℕ}
    (prior : FinDist (Fin n)) (σ : SignalStructure n m)
    (v : FinDist (Fin n) → ℝ)
    (h_concave : ConcaveOnSimplex v) :
    expectedSenderPayoff prior σ v ≤ v prior := by
  rw [expectedSenderPayoff_eq_expect]
  apply h_concave m (signalLaw prior σ) (fun s => prior.posteriorOrPrior σ.π s) prior
  intro i
  exact FinDist.total_probability prior σ.π i

end Econlib.MechanismDesign.InformationDesign.Persuasion.Finite
