/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Signaling.Basic

/-!
# Signaling PBE: Workhorse lemmas

`IsSignalingPBE` quantifies optimality over all mixed unilateral deviations (`signalingSwap`).
Because `signalingValue` is linear in the deviator's own mixed strategy, optimality against all
mixed swaps is equivalent to optimality against pure alternatives. This file records that reduction
in both directions: The constructive lemmas one uses to prove an assessment is a PBE, and the
extraction of pure-deviation optimality from a PBE.

On the constructive side it suffices, for the sender, that every on-support message of each type
maximizes `senderExpectedPayoff` over messages, and, for the receiver, that every on-support action
at each message maximizes `receiverPosteriorPayoff` against the held belief;
`isSignalingPBE_of_pure` bundles both with Bayes consistency.

## Main definitions

* `receiverPosteriorPayoff`: Receiver's expected payoff at a message given a posterior.
* `isReceiverBestResponse`: A pure receiver action is a best response to a posterior.
* `equilibriumPayoff`: A sender type's expected payoff in an assessment.

## Main statements

* `signalingValue_sender_eq`, `signalingValue_receiver_eq`: The deviator values as `expect`s over
  the deviator's own mixed strategy.
* `senderOptimal_of_pure`, `receiverOptimal_of_pure`: Pure-deviation sufficiency, by deviator.
* `isSignalingPBE_of_pure`: The bundled constructive characterization.
* `IsSignalingPBE.sender_bestResponse`, `IsSignalingPBE.receiver_bestResponse`: Pure-deviation
  optimality extracted from a PBE.

## Notes

The underlying linearity is `FinDist.expect_le_expect_of_support_max`: A distribution supported on
maximizers of `f` weakly dominates every mixture in `f`-expectation.

## References

* Spence, Michael. 1973. “Job Market Signaling.” *The Quarterly Journal of Economics* 87 (3): 355.
  [https://doi.org/10.2307/1882010](https://doi.org/10.2307/1882010).
* Fudenberg, Drew, and Jean Tirole. 1991. “Perfect Bayesian Equilibrium and Sequential
  Equilibrium.” *Journal of Economic Theory* 53 (2): 236–60.
  [https://doi.org/10.1016/0022-0531(91)90155-w](https://doi.org/10.1016/0022-0531(91)90155-w).

## Tags

signaling games, perfect bayesian equilibrium, one-shot deviation, best response
-/

@[expose] public noncomputable section

open Econlib.Probability Econlib.GameTheory

namespace Econlib.GameTheory

namespace SignalingGame

variable (sg : SignalingGame)

/-! ## Receiver best responses to a belief -/

/-- Receiver's expected payoff at message `m` from a pure action `a`, evaluated against a posterior
`μ` over sender types. -/
def receiverPosteriorPayoff
    (μ : FinDist sg.Theta) (m : sg.Msg) (a : sg.Act) : ℝ :=
  μ.expect fun θ => sg.payoff .receiver θ m a

@[signaling_eval] lemma receiverPosteriorPayoff_eq_expect
    (μ : FinDist sg.Theta) (m : sg.Msg) (a : sg.Act) :
    sg.receiverPosteriorPayoff μ m a = μ.expect (fun θ => sg.payoff .receiver θ m a) := rfl

/-- Against a receiver playing the pure action `a₀` at `m`, the sender's expected payoff is a
single payoff-table entry. -/
lemma senderExpectedPayoff_pure_receiver {σR : sg.ReceiverMixedStrategy} {m : sg.Msg}
    {a₀ : sg.Act} (hR : σR m = FinDist.pure a₀) (θ : sg.Theta) :
    sg.senderExpectedPayoff σR θ m = sg.payoff .sender θ m a₀ := by
  rw [senderExpectedPayoff_eq_expect, hR, FinDist.expect_pure]

/-- A pure receiver action `a` is a *best response* at message `m` to belief `μ` if no other pure
action yields strictly higher expected payoff against `μ`. -/
def isReceiverBestResponse
    (μ : FinDist sg.Theta) (m : sg.Msg) (a : sg.Act) : Prop :=
  ∀ a', sg.receiverPosteriorPayoff μ m a ≥ sg.receiverPosteriorPayoff μ m a'

/-- Against a point belief, best response means pointwise payoff-table domination. -/
lemma isReceiverBestResponse_pure_iff {θ : sg.Theta} {m : sg.Msg} {a : sg.Act} :
    sg.isReceiverBestResponse (FinDist.pure θ) m a ↔
      ∀ a', sg.payoff .receiver θ m a ≥ sg.payoff .receiver θ m a' := by
  unfold isReceiverBestResponse
  simp_rw [receiverPosteriorPayoff_eq_expect, FinDist.expect_pure]

/-! ## Deviator values as expectations over the deviator's own strategy -/

/-- The sender deviator's value is the expectation of `senderExpectedPayoff` over the type's own
message mixture. Definitional. -/
@[signaling_eval]
lemma signalingValue_sender_eq (a : sg.SignalingAssessment) (θ : sg.Theta) :
    sg.signalingValue (.sender θ) a =
      (a.senderStrategy θ).expect
        (fun m => sg.senderExpectedPayoff a.receiverStrategy θ m) := rfl

/-- The receiver deviator's value is the expectation of `receiverPosteriorPayoff` against the held
belief, over the receiver's own action mixture. -/
@[signaling_eval]
lemma signalingValue_receiver_eq (a : sg.SignalingAssessment) (m : sg.Msg) :
    sg.signalingValue (.receiver m) a =
      (a.receiverStrategy m).expect
        (fun act => sg.receiverPosteriorPayoff (a.belief m) m act) := by
  simp only [signalingValue, receiverPosteriorPayoff, FinDist.expect_eq_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun act _ => Finset.sum_congr rfl fun θ _ => by ring

/-! ## Equilibrium payoff of a sender type -/

/-- A sender type's expected payoff under the assessment. -/
def equilibriumPayoff (a : sg.SignalingAssessment) (θ : sg.Theta) : ℝ :=
  (a.senderStrategy θ).expect fun m =>
    sg.senderExpectedPayoff a.receiverStrategy θ m

@[signaling_eval] lemma equilibriumPayoff_eq_expect (a : sg.SignalingAssessment) (θ : sg.Theta) :
    sg.equilibriumPayoff a θ =
      (a.senderStrategy θ).expect
        (fun m => sg.senderExpectedPayoff a.receiverStrategy θ m) := rfl

/-- The sender deviator's value *is* the type's equilibrium payoff. Definitional. -/
lemma signalingValue_sender_eq_equilibriumPayoff (a : sg.SignalingAssessment) (θ : sg.Theta) :
    sg.signalingValue (.sender θ) a = sg.equilibriumPayoff a θ := rfl

/-! ## Pure-deviation sufficiency (constructive direction) -/

/-- **Pure deviations suffice, sender side.** If every message in the support of type `θ`'s mixture
maximizes the sender's expected payoff over pure messages, then no mixed swap at `θ` improves on
the assessment. -/
theorem senderOptimal_of_pure (a : sg.SignalingAssessment) (θ : sg.Theta)
    (h : ∀ m, 0 < (a.senderStrategy θ).pmf m →
      ∀ m', sg.senderExpectedPayoff a.receiverStrategy θ m' ≤
        sg.senderExpectedPayoff a.receiverStrategy θ m)
    (a' : sg.SignalingAssessment)
    (hswap : sg.signalingSwap (.sender θ) a a') :
    sg.signalingValue (.sender θ) a ≥ sg.signalingValue (.sender θ) a' := by
  obtain ⟨hRec, _hBel, _hOther⟩ := hswap
  rw [ge_iff_le, signalingValue_sender_eq, signalingValue_sender_eq, hRec]
  exact FinDist.expect_le_expect_of_support_max h _

/-- **Pure deviations suffice, receiver side.** If every action in the support of the receiver's
mixture at `m` maximizes `receiverPosteriorPayoff` against the held belief `a.belief m`, then no
mixed swap at `m` improves on the assessment. -/
theorem receiverOptimal_of_pure (a : sg.SignalingAssessment) (m : sg.Msg)
    (h : ∀ act, 0 < (a.receiverStrategy m).pmf act →
      ∀ act', sg.receiverPosteriorPayoff (a.belief m) m act' ≤
        sg.receiverPosteriorPayoff (a.belief m) m act)
    (a' : sg.SignalingAssessment)
    (hswap : sg.signalingSwap (.receiver m) a a') :
    sg.signalingValue (.receiver m) a ≥ sg.signalingValue (.receiver m) a' := by
  obtain ⟨_hSen, hBel, _hOther⟩ := hswap
  rw [ge_iff_le, signalingValue_receiver_eq, signalingValue_receiver_eq, hBel]
  exact FinDist.expect_le_expect_of_support_max h _

/-- **The constructive PBE characterization.** Bayes consistency plus pure-deviation optimality on
both sides yields `IsSignalingPBE`. For an assessment with pure strategies, the two optimality
hypotheses are finite payoff-table checks. -/
theorem isSignalingPBE_of_pure (a : sg.SignalingAssessment)
    (hBayes : sg.signalingBayesConsistent a)
    (hSender : ∀ θ m, 0 < (a.senderStrategy θ).pmf m →
      ∀ m', sg.senderExpectedPayoff a.receiverStrategy θ m' ≤
        sg.senderExpectedPayoff a.receiverStrategy θ m)
    (hReceiver : ∀ m act, 0 < (a.receiverStrategy m).pmf act →
      ∀ act', sg.receiverPosteriorPayoff (a.belief m) m act' ≤
        sg.receiverPosteriorPayoff (a.belief m) m act) :
    sg.IsSignalingPBE a := by
  refine ⟨hBayes, ?_⟩
  intro dev a' hswap
  cases dev with
  | sender θ => exact sg.senderOptimal_of_pure a θ (hSender θ) a' hswap
  | receiver m => exact sg.receiverOptimal_of_pure a m (hReceiver m) a' hswap

/-! ## Pure-deviation extraction (destructive direction) -/

-- Implicit game for the `IsSignalingPBE.*` lemmas: With `sg` explicit, dot notation
-- (`h_pbe.sender_bestResponse θ m'`) would feed `θ` into the game slot.
variable {sg}

/-- **A PBE sender cannot gain from any pure message.** Each type's equilibrium payoff weakly
dominates the expected payoff of every message against the equilibrium receiver. -/
theorem IsSignalingPBE.sender_bestResponse {a : sg.SignalingAssessment}
    (h_pbe : sg.IsSignalingPBE a) (θ : sg.Theta) (m' : sg.Msg) :
    sg.senderExpectedPayoff a.receiverStrategy θ m' ≤ sg.equilibriumPayoff a θ := by
  -- The point-mass deviation: type θ sends m' for sure; everything else unchanged.
  let σ' : sg.SignalingAssessment :=
    { senderStrategy := Function.update a.senderStrategy θ (FinDist.pure m')
      receiverStrategy := a.receiverStrategy
      belief := a.belief }
  have h_swap : sg.signalingSwap (.sender θ) a σ' :=
    ⟨rfl, rfl, fun θ' hθ' => by simp [σ', Function.update_of_ne hθ']⟩
  have h_ineq : sg.signalingValue (.sender θ) a ≥ sg.signalingValue (.sender θ) σ' :=
    h_pbe.2 (.sender θ) σ' h_swap
  rw [signalingValue_sender_eq_equilibriumPayoff, signalingValue_sender_eq] at h_ineq
  have hσ'θ : σ'.senderStrategy θ = FinDist.pure m' := by simp [σ']
  rw [hσ'θ, FinDist.expect_pure] at h_ineq
  exact h_ineq

/-- **A PBE receiver plays a best response to its belief at every message** — even off-path. The
mixed action's posterior value weakly dominates every pure action's.

This is a general PBE fact, not an intuitive-criterion one: The Cho-Kreps (1987) clause 2 composes
it with the intuitive-criterion belief restriction. -/
theorem IsSignalingPBE.receiver_bestResponse {a : sg.SignalingAssessment}
    (h_pbe : sg.IsSignalingPBE a) (m : sg.Msg) (a' : sg.Act) :
    sg.receiverPosteriorPayoff (a.belief m) m a' ≤
      (a.receiverStrategy m).expect
        (fun act => sg.receiverPosteriorPayoff (a.belief m) m act) := by
  -- The point-mass deviation: the receiver plays a' for sure at m; everything else unchanged.
  let σ' : sg.SignalingAssessment :=
    { senderStrategy := a.senderStrategy
      receiverStrategy := Function.update a.receiverStrategy m (FinDist.pure a')
      belief := a.belief }
  have h_swap : sg.signalingSwap (.receiver m) a σ' :=
    ⟨rfl, rfl, fun m' hm' => by simp [σ', Function.update_of_ne hm']⟩
  have h_ineq : sg.signalingValue (.receiver m) a ≥ sg.signalingValue (.receiver m) σ' :=
    h_pbe.2 (.receiver m) σ' h_swap
  rw [signalingValue_receiver_eq, signalingValue_receiver_eq] at h_ineq
  have hσ'm : σ'.receiverStrategy m = FinDist.pure a' := by simp [σ']
  rw [hσ'm, FinDist.expect_pure] at h_ineq
  exact h_ineq

end SignalingGame

end Econlib.GameTheory

end
