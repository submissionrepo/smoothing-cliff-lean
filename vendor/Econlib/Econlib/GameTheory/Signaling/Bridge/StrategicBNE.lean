/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Signaling.PBE
public import Econlib.GameTheory.Strategic.Bayesian.PureBNE

/-!
# Signaling PBE induces a pure Bayesian Nash equilibrium

A pure signaling perfect Bayesian equilibrium induces a pure Bayesian Nash equilibrium of the
agent-normal-form finite Bayesian game `SignalingGame.toFinBayesianGame`, via the embedding
`SignalingGame.toBayesianPureStrategy`. This is the textbook refinement fact "every PBE is a BNE",
specialized to the strategic-form representation of a signaling game.

The connection is one-directional: A PBE is a refinement of a BNE, so the converse fails (a BNE
imposes no off-path receiver optimality). It is also restricted to pure strategies — the receiver
of the agent normal form mixes over whole response functions `Msg → Act`, whereas the behavioral
signaling receiver mixes per message, so the mixed analog is the Kuhn behavioral↔mixed problem
(deferred). The behavioral connection to the general extensive-form API is supplied separately by
`Bridge/Morphism.lean`.

## Main definitions

* `SignalingGame.purePBEAssessment`: The pure-data signaling assessment with Dirac sender/receiver
  strategies and a chosen belief system.

## Main statements

* `SignalingGame.toFinBayesianGame_marginalD_sender`,
  `SignalingGame.toFinBayesianGame_marginalD_receiver`: The agent-normal-form prior marginals.
* `SignalingGame.interimPayoffAction_sender_eq`, `SignalingGame.interimPayoffAction_receiver_eq`:
  Closed forms of the agent-normal-form interim payoffs at a pure signaling strategy.
* `SignalingGame.isBNE_toBayesianPureStrategy_of_isSignalingPBE`: A pure signaling PBE embeds as a
  pure BNE of `toFinBayesianGame`.

## References

* Fudenberg, Drew, and Jean Tirole. 1991. “Perfect Bayesian Equilibrium and Sequential
  Equilibrium.” *Journal of Economic Theory* 53 (2): 236–60.
* Harsanyi, John C. 1968. “Games with Incomplete Information Played by 'Bayesian' Players, Parts
  I-Iii.” *Management Science* 14 : 159–82, 320–34, 486–502.

## Tags

signaling games, perfect bayesian equilibrium, bayesian nash equilibrium, agent normal form
-/

@[expose] public noncomputable section

open Function BigOperators Econlib.Probability

namespace Econlib.GameTheory

namespace SignalingGame

variable (sg : SignalingGame)

/-! ## Definitional projections of the agent-normal-form game -/

@[simp] lemma toFinBayesianGame_payoff_sender
    (a : Π p, sg.toFinBayesianGame.Action p) (θ : Π p, sg.toFinBayesianGame.Theta p) :
    sg.toFinBayesianGame.payoff .sender a θ =
      sg.payoff .sender (θ .sender) (a .sender) ((a .receiver) (a .sender)) := rfl

@[simp] lemma toFinBayesianGame_payoff_receiver
    (a : Π p, sg.toFinBayesianGame.Action p) (θ : Π p, sg.toFinBayesianGame.Theta p) :
    sg.toFinBayesianGame.payoff .receiver a θ =
      sg.payoff .receiver (θ .sender) (a .sender) ((a .receiver) (a .sender)) := rfl

lemma toFinBayesianGame_prior_apply (θ : Π p, sg.toFinBayesianGame.Theta p) :
    sg.toFinBayesianGame.prior θ = sg.prior.pmf (θ .sender) := rfl

@[simp] lemma typeProfileEquiv_symm_sender (τ : sg.Theta) :
    (sg.typeProfileEquiv.symm τ) .sender = τ := rfl

@[simp] lemma typeProfileEquiv_symm_receiver (τ : sg.Theta) :
    (sg.typeProfileEquiv.symm τ) .receiver = PUnit.unit := rfl

/-! ## Reindexing sums over type profiles

A type profile `θ : Π p, BayesianTheta p` is determined by its sender coordinate (the
receiver's type is trivial). These two lemmas reindex a sum over profiles — whose summand depends
only on `θ .sender` — to a sum over sender types, via `typeProfileEquiv`. They are stated with
explicit summand functions to avoid the brittle higher-order matching `Equiv.sum_comp` would
require. -/

/-- Reindex a full sum over type profiles whose summand depends only on the sender coordinate. -/
lemma sum_typeProfile {M : Type*} [AddCommMonoid M] (F : sg.Theta → M) :
    (∑ θ : (Π p, sg.toFinBayesianGame.Theta p), F (θ .sender)) = ∑ t, F t :=
  Fintype.sum_equiv sg.typeProfileEquiv (fun θ => F (θ .sender)) F (fun _ => rfl)

/-- Reindex the sender-coordinate fiber `{θ | θ.sender = t}` to the single term `F t`. -/
lemma sum_typeProfile_filter {M : Type*} [AddCommMonoid M] (t : sg.Theta) (F : sg.Theta → M) :
    (∑ θ ∈ Finset.univ.filter (fun θ : (Π p, sg.toFinBayesianGame.Theta p) => θ .sender = t),
      F (θ .sender)) = F t := by
  rw [Finset.sum_filter]
  refine (Finset.sum_congr rfl (fun θ _ => rfl)).trans
    ((sg.sum_typeProfile (fun s => if s = t then F s else 0)).trans ?_)
  rw [Finset.sum_ite_eq']
  simp

/-! ## Prior marginals of the agent-normal-form game -/

/-- The sender's agent-normal-form prior marginal at type `t` is the signaling prior mass at `t`:
The receiver coordinate is trivial, so the fiber `{θ | θ.sender = t}` is a singleton. -/
lemma toFinBayesianGame_marginalD_sender (t : sg.Theta) :
    sg.toFinBayesianGame.prior.marginalD .sender t = sg.prior.pmf t := by
  unfold FinDist.marginalD
  exact sg.sum_typeProfile_filter t (fun s => sg.prior.pmf s)

/-- The receiver's agent-normal-form prior marginal is `1`: The receiver's type is trivial, so the
fiber `{θ | θ.receiver = u}` is everything. -/
lemma toFinBayesianGame_marginalD_receiver (u : PUnit) :
    sg.toFinBayesianGame.prior.marginalD .receiver u = 1 := by
  unfold FinDist.marginalD
  rw [Finset.filter_true_of_mem (fun θ _ => Subsingleton.elim (θ .receiver) u)]
  exact (Finset.sum_congr rfl (fun θ _ => sg.toFinBayesianGame_prior_apply θ)).trans
    ((sg.sum_typeProfile (fun s => sg.prior.pmf s)).trans sg.prior.sum_one)

/-! ## Closed forms of the agent-normal-form interim payoffs -/

/-- At a pure embedded signaling strategy, the receiver's agent-normal-form interim payoff from a
response function `b` is the prior-weighted realized receiver payoff, summing over sender types
each sending message `σS t`. -/
lemma interimPayoffAction_receiver_eq
    (σS : sg.SenderPureStrategy) (σR : sg.ReceiverPureStrategy)
    (u : PUnit) (b : sg.Msg → sg.Act) :
    sg.toFinBayesianGame.interimPayoffAction .receiver u b (sg.toBayesianPureStrategy σS σR) =
      ∑ t, sg.prior.pmf t * sg.payoff .receiver t (σS t) (b (σS t)) := by
  unfold FinBayesianGame.interimPayoffAction
  rw [Finset.filter_true_of_mem (fun θ _ => Subsingleton.elim (θ .receiver) u)]
  refine (Finset.sum_congr rfl (fun θ _ => ?_)).trans
    (sg.sum_typeProfile (fun s => sg.prior.pmf s * sg.payoff .receiver s (σS s) (b (σS s))))
  -- condProbD reduces to the prior mass; the payoff reduces definitionally.
  have hcp : sg.toFinBayesianGame.prior.condProbD .receiver u θ = sg.prior.pmf (θ .sender) := by
    rw [FinDist.condProbD_eq_of_pos sg.toFinBayesianGame.prior .receiver u (Subsingleton.elim _ u)
          (by rw [sg.toFinBayesianGame_marginalD_receiver]; exact one_pos),
        sg.toFinBayesianGame_marginalD_receiver, div_one, toFinBayesianGame_prior_apply]
  have hpay : sg.toFinBayesianGame.payoff .receiver
        (Function.update (sg.toFinBayesianGame.actionProfile (sg.toBayesianPureStrategy σS σR) θ)
          .receiver b) θ =
      sg.payoff .receiver (θ .sender) (σS (θ .sender)) (b (σS (θ .sender))) := rfl
  rw [hcp, hpay]

/-- At a pure embedded signaling strategy, the sender's agent-normal-form interim payoff from a
message `b` at a positive-prior type `t` is the single realized payoff entry: The type-profile
fiber `{θ | θ.sender = t}` has conditional probability one. -/
lemma interimPayoffAction_sender_eq
    (σS : sg.SenderPureStrategy) (σR : sg.ReceiverPureStrategy)
    (t : sg.Theta) (b : sg.Msg) (ht : 0 < sg.prior.pmf t) :
    sg.toFinBayesianGame.interimPayoffAction .sender t b (sg.toBayesianPureStrategy σS σR) =
      sg.payoff .sender t b (σR b) := by
  unfold FinBayesianGame.interimPayoffAction
  refine (Finset.sum_congr rfl (fun θ hθ => ?_)).trans
    (sg.sum_typeProfile_filter t (fun s => sg.payoff .sender s b (σR b)))
  have hsender : θ .sender = t := (Finset.mem_filter.mp hθ).2
  -- On the fiber the conditional probability is one; the payoff reduces definitionally.
  have hcp : sg.toFinBayesianGame.prior.condProbD .sender t θ = 1 := by
    rw [FinDist.condProbD_eq_of_pos sg.toFinBayesianGame.prior .sender t hsender
          (by rw [sg.toFinBayesianGame_marginalD_sender]; exact ht),
        sg.toFinBayesianGame_marginalD_sender, toFinBayesianGame_prior_apply, hsender,
        div_self (ne_of_gt ht)]
  have hpay : sg.toFinBayesianGame.payoff .sender
        (Function.update (sg.toFinBayesianGame.actionProfile (sg.toBayesianPureStrategy σS σR) θ)
          .sender b) θ =
      sg.payoff .sender (θ .sender) b (σR b) := rfl
  rw [hcp, one_mul, hpay]

/-! ## The pure signaling assessment -/

variable (σS : sg.SenderPureStrategy) (σR : sg.ReceiverPureStrategy) (μ : sg.ReceiverBelief)

/-- The pure-data signaling assessment built from a pure sender strategy, a pure receiver strategy,
and a belief system: Both strategies are Dirac. -/
def purePBEAssessment : sg.SignalingAssessment where
  senderStrategy θ := FinDist.pure (σS θ)
  receiverStrategy m := FinDist.pure (σR m)
  belief := μ

@[simp] lemma purePBEAssessment_senderStrategy (θ : sg.Theta) :
    (sg.purePBEAssessment σS σR μ).senderStrategy θ = FinDist.pure (σS θ) := rfl

@[simp] lemma purePBEAssessment_receiverStrategy (m : sg.Msg) :
    (sg.purePBEAssessment σS σR μ).receiverStrategy m = FinDist.pure (σR m) := rfl

@[simp] lemma purePBEAssessment_belief :
    (sg.purePBEAssessment σS σR μ).belief = μ := rfl

/-! ## The bridge theorem -/

/-- **A pure signaling PBE induces a pure BNE of the agent normal form.** If the pure assessment
`purePBEAssessment σS σR μ` is a signaling PBE, then the embedded pure strategy
`toBayesianPureStrategy σS σR` is a Bayesian Nash equilibrium of `toFinBayesianGame`.

Sender incentives transfer directly from `IsSignalingPBE.sender_bestResponse`. Receiver incentives
use `IsSignalingPBE.receiver_bestResponse` at each on-path message: The agent-normal-form receiver
optimizes a single response function, which decomposes message-by-message into the per-message
posterior best responses that PBE supplies. Off-path messages carry no incentive constraint on
either side. -/
theorem isBNE_toBayesianPureStrategy_of_isSignalingPBE
    (h : sg.IsSignalingPBE (sg.purePBEAssessment σS σR μ)) :
    sg.toFinBayesianGame.IsBNE (sg.toBayesianPureStrategy σS σR) := by
  -- Per-message receiver optimality, extracted from the PBE. Phrased via the assessment's sender
  -- strategy so the marginal/posterior terms match `marginalProb`/`posterior`/Bayes-consistency
  -- syntactically (no raw-lambda beta-redex mismatch).
  have hmsg : ∀ (m : sg.Msg) (a : sg.Act),
      (∑ t, sg.prior.pmf t *
          ((sg.purePBEAssessment σS σR μ).senderStrategy t).pmf m * sg.payoff .receiver t m a) ≤
        ∑ t, sg.prior.pmf t *
          ((sg.purePBEAssessment σS σR μ).senderStrategy t).pmf m *
            sg.payoff .receiver t m (σR m) := by
    intro m a
    by_cases hpos : 0 < sg.marginalProb (sg.purePBEAssessment σS σR μ).senderStrategy m
    · -- On-path: scale the posterior best-response inequality by the positive marginal.
      have hne : sg.marginalProb (sg.purePBEAssessment σS σR μ).senderStrategy m ≠ 0 :=
        ne_of_gt hpos
      have hkey : ∀ a',
          (∑ t, sg.prior.pmf t *
              ((sg.purePBEAssessment σS σR μ).senderStrategy t).pmf m *
              sg.payoff .receiver t m a') =
            sg.marginalProb (sg.purePBEAssessment σS σR μ).senderStrategy m *
              (sg.posterior (sg.purePBEAssessment σS σR μ).senderStrategy m).expect
                (fun θ => sg.payoff .receiver θ m a') := by
        intro a'
        rw [FinDist.expect_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [sg.posterior_apply (sg.purePBEAssessment σS σR μ).senderStrategy m t hpos]
        field_simp
      rw [hkey a, hkey (σR m)]
      apply mul_le_mul_of_nonneg_left _ hpos.le
      have hbel := h.1 m hpos
      have hbr := h.receiver_bestResponse m a
      simp only [purePBEAssessment_receiverStrategy, receiverPosteriorPayoff_eq_expect,
        FinDist.expect_pure] at hbr
      rwa [hbel] at hbr
    · -- Off-path: the marginal is zero, so every term vanishes.
      have hm0 : sg.marginalProb (sg.purePBEAssessment σS σR μ).senderStrategy m = 0 :=
        le_antisymm (not_lt.mp hpos)
          (sg.marginalProb_nonneg (sg.purePBEAssessment σS σR μ).senderStrategy m)
      have hz : ∀ t, sg.prior.pmf t *
          ((sg.purePBEAssessment σS σR μ).senderStrategy t).pmf m = 0 := by
        have hsum := hm0
        rw [marginalProb_eq_sum] at hsum
        exact fun t => (Finset.sum_eq_zero_iff_of_nonneg
          (fun t _ => mul_nonneg (sg.prior.nonneg t)
            (((sg.purePBEAssessment σS σR μ).senderStrategy t).nonneg m))).mp hsum t
            (Finset.mem_univ t)
      have hga : ∀ a',
          (∑ t, sg.prior.pmf t *
              ((sg.purePBEAssessment σS σR μ).senderStrategy t).pmf m *
              sg.payoff .receiver t m a') = 0 :=
        fun a' => Finset.sum_eq_zero fun t _ => by rw [hz t, zero_mul]
      rw [hga a, hga (σR m)]
  -- Regrouping the receiver interim payoff message-by-message.
  have hregroup : ∀ (bb : sg.Msg → sg.Act),
      (∑ t, sg.prior.pmf t * sg.payoff .receiver t (σS t) (bb (σS t))) =
        ∑ m, ∑ t, sg.prior.pmf t *
          ((sg.purePBEAssessment σS σR μ).senderStrategy t).pmf m *
            sg.payoff .receiver t m (bb m) := by
    intro bb
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [purePBEAssessment_senderStrategy]
    rw [Finset.sum_eq_single_of_mem (σS t) (Finset.mem_univ _)]
    · rw [FinDist.pure_pmf, if_pos rfl, mul_one]
    · intro m _ hm
      rw [FinDist.pure_pmf, if_neg (Ne.symm hm), mul_zero, zero_mul]
  -- Assemble via the concrete best-response characterization.
  rw [FinBayesianGame.IsBNE_iff]
  intro i
  cases i with
  | sender =>
      intro θ_i hpos a_i
      rw [ge_iff_le, sg.toBayesianPureStrategy_sender σS σR θ_i]
      have ht : 0 < sg.prior.pmf θ_i := by
        rwa [sg.toFinBayesianGame_marginalD_sender θ_i] at hpos
      rw [sg.interimPayoffAction_sender_eq σS σR θ_i (σS θ_i) ht,
          sg.interimPayoffAction_sender_eq σS σR θ_i a_i ht]
      have hbr := h.sender_bestResponse θ_i a_i
      have hsep : sg.senderExpectedPayoff (sg.purePBEAssessment σS σR μ).receiverStrategy θ_i a_i =
          sg.payoff .sender θ_i a_i (σR a_i) :=
        sg.senderExpectedPayoff_pure_receiver rfl θ_i
      have hep : sg.equilibriumPayoff (sg.purePBEAssessment σS σR μ) θ_i =
          sg.payoff .sender θ_i (σS θ_i) (σR (σS θ_i)) := by
        rw [equilibriumPayoff_eq_expect, purePBEAssessment_senderStrategy, FinDist.expect_pure]
        exact sg.senderExpectedPayoff_pure_receiver rfl θ_i
      rwa [hsep, hep] at hbr
  | receiver =>
      intro u _hpos b
      rw [ge_iff_le, sg.toBayesianPureStrategy_receiver σS σR u,
          sg.interimPayoffAction_receiver_eq σS σR u b,
          sg.interimPayoffAction_receiver_eq σS σR u σR,
          hregroup b, hregroup σR]
      exact Finset.sum_le_sum fun m _ => hmsg m (b m)

/-- **General form.** A signaling PBE whose sender and receiver strategies are pure (Dirac) induces
a pure BNE of the agent normal form, for the embedded pure strategies. This frees the user from
having to build the assessment through `purePBEAssessment`; any assessment with pure strategies
qualifies. -/
theorem isBNE_of_isSignalingPBE_of_pure
    (a : sg.SignalingAssessment)
    (hS : a.senderStrategy = fun θ => FinDist.pure (σS θ))
    (hR : a.receiverStrategy = fun m => FinDist.pure (σR m))
    (h : sg.IsSignalingPBE a) :
    sg.toFinBayesianGame.IsBNE (sg.toBayesianPureStrategy σS σR) := by
  refine sg.isBNE_toBayesianPureStrategy_of_isSignalingPBE σS σR a.belief ?_
  have ha : sg.purePBEAssessment σS σR a.belief = a := by
    obtain ⟨ss, rs, bel⟩ := a
    obtain rfl : ss = (fun θ => FinDist.pure (σS θ)) := hS
    obtain rfl : rs = (fun m => FinDist.pure (σR m)) := hR
    rfl
  rwa [ha]

end SignalingGame

end Econlib.GameTheory
