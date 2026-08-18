/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Bayes

open Econlib.Probability

/-!
# Bayesian persuasion: Finite signal structures

Core definitions for Bayesian persuasion with finite type and signal spaces. A sender commits to a
**signal structure** mapping types to distributions over public signals. A receiver observes the
signal, updates beliefs via Bayes' rule, and acts. The sender's achievable payoffs are
characterized by the **concave closure** of the value function over posteriors (Kamenica and
Gentzkow 2011).

## Main definitions

* `SignalStructure` — likelihood function `π : Fin n → FinDist (Fin m)`.
* `signalLaw` — marginal signal distribution (over `FinDist.signalMarginal`).
* `BayesPlausible` — the expected posterior equals the prior.
* `concaveClosure` — the supremum over **Bayes-plausible** splittings.
* `expectedSenderPayoff` — the sender's expected payoff from a signal structure.

## Main statements

* `SignalStructure.bayesPlausible` — every signal structure is Bayes-plausible.
* `concaveClosure_ge` — the concave closure dominates `v` at every prior.

## References

* Kamenica, Emir, and Matthew Gentzkow. 2011. “Bayesian Persuasion.” *American Economic Review* 101
  (6): 2590–615. [https://doi.org/10.1257/aer.101.6.2590](https://doi.org/10.1257/aer.101.6.2590).

## Tags

persuasion, bayesian persuasion, concavification, signal structure
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Finite

variable {n m : ℕ}

/-- A signal structure maps each type to a distribution over signals. -/
structure SignalStructure (n m : ℕ) where
  π : Fin n → FinDist (Fin m)

/-- Two signal structures are equal when their likelihood rows agree at every type. -/
@[ext] lemma SignalStructure.ext {σ₁ σ₂ : SignalStructure n m}
    (h : ∀ θ, σ₁.π θ = σ₂.π θ) : σ₁ = σ₂ := by
  cases σ₁; cases σ₂
  simp only [SignalStructure.mk.injEq]
  exact funext h

/-- The marginal distribution over signals; the `pmf` is the prior-weighted likelihood sum
`FinDist.signalMarginal`. -/
noncomputable def signalLaw
    (prior : FinDist (Fin n)) (σ : SignalStructure n m) : FinDist (Fin m) where
  pmf := prior.signalMarginal σ.π
  nonneg s := FinDist.signalMarginal_nonneg prior σ.π s
  sum_one := by
    simp only [FinDist.signalMarginal_eq_sum]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, fun θ => (σ.π θ).sum_one, mul_one]
    exact prior.sum_one

/-- **Bayes-plausibility:** the expected posterior equals the prior. For each type `θ`, the prior
probability equals the sum over signals of the marginal signal probability times the posterior
probability. -/
def BayesPlausible (prior : FinDist (Fin n)) (σ : SignalStructure n m) : Prop :=
  ∀ θ, prior.pmf θ = ∑ s,
    if _ : 0 < prior.signalMarginal σ.π s
    then prior.signalMarginal σ.π s * (prior.posteriorOrPrior σ.π s).pmf θ
    else 0

/-- Unfolds `BayesPlausible` to its defining condition. -/
@[simp] lemma BayesPlausible_def (prior : FinDist (Fin n)) (σ : SignalStructure n m) :
    BayesPlausible prior σ
      ↔ ∀ θ, prior.pmf θ =
          ∑ s, if _ : 0 < prior.signalMarginal σ.π s
               then prior.signalMarginal σ.π s * (prior.posteriorOrPrior σ.π s).pmf θ
               else 0 := Iff.rfl

/-- Every signal structure is Bayes-plausible. This is the law of total probability restated in the
persuasion language. -/
lemma SignalStructure.bayesPlausible (prior : FinDist (Fin n)) (σ : SignalStructure n m) :
    BayesPlausible prior σ := by
  intro θ
  have h_eq : ∀ s, (if h : 0 < prior.signalMarginal σ.π s
      then prior.signalMarginal σ.π s * (prior.posteriorOrPrior σ.π s).pmf θ
      else 0) = prior.pmf θ * (σ.π θ).pmf s := by
    intro s
    simp only [FinDist.signalMarginal_eq_sum]
    by_cases hs : 0 < ∑ θ', prior.pmf θ' * (σ.π θ').pmf s
    · rw [dif_pos hs]
      simp only [FinDist.posteriorOrPrior, FinDist.posteriorOfLikelihoodOrPrior, dif_pos hs]
      rw [mul_div_cancel₀ _ (ne_of_gt hs)]
    · rw [dif_neg hs]
      -- The θ-term is squeezed between 0 and the full sum, which is ≤ 0.
      have h_le : prior.pmf θ * (σ.π θ).pmf s ≤ ∑ θ', prior.pmf θ' * (σ.π θ').pmf s :=
        Finset.single_le_sum (fun θ' _ => mul_nonneg (prior.nonneg θ') ((σ.π θ').nonneg s))
          (Finset.mem_univ θ)
      have h_nonneg := mul_nonneg (prior.nonneg θ) ((σ.π θ).nonneg s)
      linarith [not_lt.mp hs]
  simp_rw [h_eq, ← Finset.mul_sum, (σ.π θ).sum_one, mul_one]

/-- The **concave closure** of `v` at `μ`: The supremum of expected payoffs achievable by any
Bayes-plausible splitting of `μ`. -/
noncomputable def concaveClosure (v : FinDist (Fin n) → ℝ) (μ : FinDist (Fin n)) : ℝ :=
  sSup { E | ∃ (m : ℕ) (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n)),
    (∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = μ.pmf i) ∧
    E = weights.expect (fun s => v (beliefs s)) }

/-- The sender's expected payoff from signal structure `σ`. Zero-probability signals contribute `0`
to the sum, since the posterior is undefined there. -/
noncomputable def expectedSenderPayoff
    (prior : FinDist (Fin n)) (σ : SignalStructure n m) (v : FinDist (Fin n) → ℝ) : ℝ :=
  ∑ s, if _ : 0 < prior.signalMarginal σ.π s
       then prior.signalMarginal σ.π s * v (prior.posteriorOrPrior σ.π s)
       else 0

/-- Unfolds `expectedSenderPayoff` to its defining sum. -/
@[simp] lemma expectedSenderPayoff_def (prior : FinDist (Fin n)) (σ : SignalStructure n m)
    (v : FinDist (Fin n) → ℝ) :
    expectedSenderPayoff prior σ v
      = ∑ s, if _ : 0 < prior.signalMarginal σ.π s
             then prior.signalMarginal σ.π s * v (prior.posteriorOrPrior σ.π s)
             else 0 := rfl

/-- The trivial splitting (no signal) achieves `v(μ)`, so the concave closure is at least `v(μ)`. -/
lemma concaveClosure_ge (v : FinDist (Fin n) → ℝ) (μ : FinDist (Fin n))
    (h_bdd : BddAbove
      { E | ∃ (m : ℕ) (weights : FinDist (Fin m)) (beliefs : Fin m → FinDist (Fin n)),
      (∀ i, ∑ s, weights.pmf s * (beliefs s).pmf i = μ.pmf i) ∧
      E = weights.expect (fun s => v (beliefs s)) }) :
    v μ ≤ concaveClosure v μ := by
  apply le_csSup h_bdd
  exact ⟨1, FinDist.pure 0, fun _ => μ, by
    intro i; simp [FinDist.pure],
    by simp [FinDist.expect, FinDist.pure]⟩

/-- When `f` is nonneg, the `dite` guard `0 < f s` is redundant: Zero terms contribute `0` either
way. -/
lemma sum_dite_nonneg_eq {k : ℕ} (f g : Fin k → ℝ) (hf : ∀ s, 0 ≤ f s) :
    (∑ s, if _ : 0 < f s then f s * g s else 0) = ∑ s, f s * g s := by
  congr 1; ext s; by_cases hs : 0 < f s
  · exact dif_pos hs
  · rw [dif_neg hs]
    have h0 : f s = 0 := le_antisymm (not_lt.mp hs) (hf s)
    rw [h0, zero_mul]

/-- `expectedSenderPayoff` is an element of the `concaveClosure` feasible set. -/
lemma expectedSenderPayoff_mem_achievableSet
    {n m : ℕ} (prior : FinDist (Fin n)) (σ : SignalStructure n m) (v : FinDist (Fin n) → ℝ) :
    expectedSenderPayoff prior σ v ∈
      { E | ∃ (k : ℕ) (w : FinDist (Fin k)) (b : Fin k → FinDist (Fin n)),
      (∀ i, ∑ s, w.pmf s * (b s).pmf i = prior.pmf i) ∧
      E = w.expect (fun s => v (b s)) } := by
  refine ⟨m, signalLaw prior σ, fun s => prior.posteriorOrPrior σ.π s, ?_, ?_⟩
  · intro i
    have h := SignalStructure.bayesPlausible prior σ i
    symm; rw [h]
    exact (sum_dite_nonneg_eq _ _ (fun s => (signalLaw prior σ).nonneg s))
  · simp only [expectedSenderPayoff, FinDist.expect_eq_sum]
    exact sum_dite_nonneg_eq _ _ (fun s => (signalLaw prior σ).nonneg s)

end Econlib.MechanismDesign.InformationDesign.Persuasion.Finite
