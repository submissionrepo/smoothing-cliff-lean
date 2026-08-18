/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Signaling.PBE

/-!
# Pooling assessments: Bayes consistency and payoff evaluation

A **pure pooling** sender strategy sends a fixed message `m₀` regardless of type
(`∀ θ, σ θ = FinDist.pure m₀`). Under such a strategy the message marginal is the point mass at
`m₀`, so `m₀` is the only on-path message, its posterior is the prior, and Bayes consistency
reduces to the single requirement that the belief at `m₀` equal the prior. Equilibrium-payoff
evaluation collapses likewise: A pooling type's payoff is its expected payoff at `m₀`, a single
payoff-table entry when the receiver is also pure there.

## Main statements

* `marginalProb_pooling`: The message marginal is the point mass at the pooling message.
* `isOffPath_pooling`: Every message other than the pooling message is off-path.
* `pooling_posterior_eq_prior`: The posterior at the pooling message is the prior.
* `pooling_bayesConsistent`: Bayes consistency reduces to `a.belief m₀ = sg.prior`.
* `equilibriumPayoff_pooling`, `equilibriumPayoff_pure_pure`: Payoff evaluation under pooling.

## References

* Spence, Michael. 1973. “Job Market Signaling.” *The Quarterly Journal of Economics* 87 (3): 355.
  [https://doi.org/10.2307/1882010](https://doi.org/10.2307/1882010).
* Fudenberg, Drew, and Jean Tirole. 1991. “Perfect Bayesian Equilibrium and Sequential
  Equilibrium.” *Journal of Economic Theory* 53 (2): 236–60.
  [https://doi.org/10.1016/0022-0531(91)90155-w](https://doi.org/10.1016/0022-0531(91)90155-w).

## Tags

signaling games, pooling equilibrium, bayes consistency, perfect bayesian equilibrium
-/

@[expose] public noncomputable section

open Econlib.Probability Econlib.GameTheory

namespace Econlib.GameTheory

namespace SignalingGame

variable (sg : SignalingGame)

/-- Under a pooling sender strategy `θ ↦ pure m₀`, the message marginal is the point mass at `m₀`:
The prior integrates out. -/
lemma marginalProb_pooling {σ : sg.SenderMixedStrategy} {m₀ : sg.Msg}
    (hσ : ∀ θ, σ θ = FinDist.pure m₀) (m : sg.Msg) :
    sg.marginalProb σ m = (FinDist.pure (α := sg.Msg) m₀).pmf m := by
  rw [marginalProb_eq_sum]
  calc ∑ θ, sg.prior.pmf θ * (σ θ).pmf m
      = ∑ θ, sg.prior.pmf θ * (FinDist.pure (α := sg.Msg) m₀).pmf m :=
        Finset.sum_congr rfl fun θ _ => by rw [hσ θ]
    _ = (∑ θ, sg.prior.pmf θ) * (FinDist.pure (α := sg.Msg) m₀).pmf m := by
        rw [Finset.sum_mul]
    _ = (FinDist.pure (α := sg.Msg) m₀).pmf m := by rw [sg.prior.sum_one, one_mul]

/-- Messages other than the pooling message are off-path: Under pooling at `m₀` the marginal is the
point mass at `m₀`, so every other message has zero marginal. -/
lemma isOffPath_pooling {a : sg.SignalingAssessment} {m₀ : sg.Msg}
    (hσ : ∀ θ, a.senderStrategy θ = FinDist.pure m₀) {m : sg.Msg} (hm : m ≠ m₀) :
    sg.isOffPath a m := by
  rw [isOffPath, sg.marginalProb_pooling hσ m]
  exact FinDist.pure_apply_ne fun h => hm h.symm

/-- A pure pooling strategy is pooling in the sense of `IsPooling`. -/
lemma isPooling_of_pure {a : sg.SignalingAssessment} {m₀ : sg.Msg}
    (hσ : ∀ θ, a.senderStrategy θ = FinDist.pure m₀) :
    sg.IsPooling a :=
  ⟨m₀, fun θ => by rw [hσ θ]; exact FinDist.pure_apply_self m₀⟩

/-- At the pooling message the posterior is the prior: The pooled message carries no information. -/
lemma pooling_posterior_eq_prior {σ : sg.SenderMixedStrategy} {m₀ : sg.Msg}
    (hσ : ∀ θ, σ θ = FinDist.pure m₀) :
    sg.posterior σ m₀ = sg.prior := by
  have hmarg : sg.marginalProb σ m₀ = 1 := by
    rw [sg.marginalProb_pooling hσ, FinDist.pure_apply_self]
  have hpos : 0 < sg.marginalProb σ m₀ := by rw [hmarg]; norm_num
  apply FinDist.ext
  intro θ
  rw [sg.posterior_apply σ m₀ θ hpos, hmarg, hσ θ, FinDist.pure_apply_self]
  ring

/-- **Bayes consistency of a pooling assessment.** The pooling message is the only on-path message
and its posterior is the prior; off-path beliefs are unconstrained. So Bayes consistency reduces to
one equation: The belief at the pooling message must be the prior. -/
theorem pooling_bayesConsistent {a : sg.SignalingAssessment} {m₀ : sg.Msg}
    (hσ : ∀ θ, a.senderStrategy θ = FinDist.pure m₀)
    (hbel : a.belief m₀ = sg.prior) :
    sg.signalingBayesConsistent a := by
  intro m hm
  by_cases hmm : m = m₀
  · subst hmm
    rw [hbel, sg.pooling_posterior_eq_prior hσ]
  · -- Off the pooling message the marginal vanishes, contradicting `0 < marginal`.
    exfalso
    rw [sg.marginalProb_pooling hσ m,
      FinDist.pure_apply_ne fun h => hmm h.symm] at hm
    exact lt_irrefl _ hm

/-- A pooling type's equilibrium payoff is its expected payoff at the pooling message. -/
lemma equilibriumPayoff_pooling {a : sg.SignalingAssessment} {m₀ : sg.Msg}
    (hσ : ∀ θ, a.senderStrategy θ = FinDist.pure m₀) (θ : sg.Theta) :
    sg.equilibriumPayoff a θ = sg.senderExpectedPayoff a.receiverStrategy θ m₀ := by
  rw [equilibriumPayoff_eq_expect, hσ θ, FinDist.expect_pure]

/-- Fully deterministic evaluation: Pure pooling sender, pure receiver response at the pooling
message — each type's equilibrium payoff is a single payoff-table entry. -/
lemma equilibriumPayoff_pure_pure {a : sg.SignalingAssessment} {m₀ : sg.Msg} {a₀ : sg.Act}
    (hσ : ∀ θ, a.senderStrategy θ = FinDist.pure m₀)
    (hR : a.receiverStrategy m₀ = FinDist.pure a₀) (θ : sg.Theta) :
    sg.equilibriumPayoff a θ = sg.payoff .sender θ m₀ a₀ := by
  rw [sg.equilibriumPayoff_pooling hσ θ, senderExpectedPayoff_eq_expect, hR,
    FinDist.expect_pure]

end SignalingGame

end Econlib.GameTheory

end
