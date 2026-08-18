/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.ExtensiveForm.Refinements.PBE
public import Econlib.GameTheory.Strategic.Bayesian.Game
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Finite.Basic
public import Econlib.Probability.FinDist.Bayes

/-!
# Signaling games

A signaling game (Spence 1973) is a two-player Bayesian game with extensive-form structure: Nature
draws a type for the sender, the sender observes the type and sends a message, the receiver
observes the message (but not the type) and takes an action.

This file defines the concrete signaling-game primitives used throughout the library. The carrier
types `Theta`, `Msg`, and `Act` are abstract finite inhabited types, so empty type, message, and
action spaces are not constructible as signaling games.

## Main definitions

* `SignalingPlayer`: The sender and receiver players.
* `SignalingGame`: A signaling game with one payoff field indexed by `SignalingPlayer`.
* `SenderPureStrategy`, `ReceiverPureStrategy`, `SenderMixedStrategy`, `ReceiverMixedStrategy`,
  `ReceiverBelief`: Strategy and belief spaces.
* `toFinBayesianGame`: The strategic-form finite Bayesian game induced by a signaling game.
* `marginalProb`, `joint`, `posterior`: Bayes-rule primitives for messages and sender types.
* `SignalingAssessment`: The pure-data assessment of sender strategy, receiver strategy, and
  receiver beliefs.
* `SignalingDeviator`, `signalingSwap`, `signalingValue`, `signalingBayesConsistent`,
  `signalingPBEPred`, `IsSignalingPBE`: The refined-equilibrium API.
* `isOffPath`: A message reached with probability zero — the probability-path off-path boundary,
  complementary to the `0 < marginalProb` gate of `signalingBayesConsistent`.
* `SignalingAssessment.senderExAntePayoff`, `SignalingAssessment.receiverExAntePayoff`: Ex-ante
  payoff functionals.
* `IsPooling`, `IsSeparating`: Structural predicates on sender strategies (no equilibrium content).
* `IsPoolingPBE`, `IsSeparatingPBE`: PBE bundled with the corresponding structural predicate.

## References

* Spence, Michael. 1973. “Job Market Signaling.” *The Quarterly Journal of Economics* 87 (3): 355.
  [https://doi.org/10.2307/1882010](https://doi.org/10.2307/1882010).

## Tags

signaling games, bayesian games, beliefs, perfect bayesian equilibrium
-/

@[expose] public section

open Econlib.Probability Econlib.GameTheory

namespace Econlib.GameTheory

/-- The two strategic players in a signaling game. -/
inductive SignalingPlayer where
  | sender
  | receiver
  deriving DecidableEq, Fintype, Inhabited

/-- A signaling game: Sender has a type, chooses a message; receiver observes the message and
chooses an action. Payoffs are unified into a single `payoff` field indexed by `SignalingPlayer`.

The carrier types `Theta`, `Msg`, `Act` are abstract finite types. The `Inhabited` bracket fields
make the empty-carrier case unrepresentable at the structure level. -/
structure SignalingGame where
  /-- Sender's private type. -/
  Theta : Type
  /-- Messages available to the sender. -/
  Msg : Type
  /-- Actions available to the receiver. -/
  Act : Type
  [instFintypeTheta   : Fintype Theta]
  [instDecEqTheta     : DecidableEq Theta]
  [instInhabitedTheta : Inhabited Theta]
  [instFintypeMsg     : Fintype Msg]
  [instDecEqMsg       : DecidableEq Msg]
  [instInhabitedMsg   : Inhabited Msg]
  [instFintypeAct     : Fintype Act]
  [instDecEqAct       : DecidableEq Act]
  [instInhabitedAct   : Inhabited Act]
  /-- Prior distribution over sender types. -/
  prior : FinDist Theta
  /-- Unified payoff: Indexed by player, sender's type, message, and receiver's action. -/
  payoff : SignalingPlayer → Theta → Msg → Act → ℝ

namespace SignalingGame

attribute [instance] instFintypeTheta instDecEqTheta instInhabitedTheta
attribute [instance] instFintypeMsg   instDecEqMsg   instInhabitedMsg
attribute [instance] instFintypeAct   instDecEqAct   instInhabitedAct

/-! ## Smart constructor: Signaling games on `Fin n` carriers

The `mkFin` smart constructor produces a `SignalingGame` whose abstract carriers `Theta`,
`Msg`, `Act` are *definitionally* `Fin nTheta`, `Fin nMsg`, `Fin nAct`. The constructor is marked
`@[reducible]` so that downstream `(0 : sg.Theta)`, `fin_cases (m : sg.Msg)`, and `decide` on the
carrier all reduce through the field projection. This removes the bracket-bound carrier opacity
friction documented in `DesignNotes/WorkedExampleFrictions.md` for `Fin n`-shaped signaling
games. -/

/-- A signaling game on `Fin n` carriers. Marked `@[reducible]` so `(mkFin ...).Theta` reduces to
`Fin nTheta` for instance synthesis, allowing direct numeric literals like `(0 : sg.Theta)`. -/
@[reducible] noncomputable def mkFin
    (nTheta nMsg nAct : ℕ) [NeZero nTheta] [NeZero nMsg] [NeZero nAct]
    (prior : FinDist (Fin nTheta))
    (payoff : SignalingPlayer → Fin nTheta → Fin nMsg → Fin nAct → ℝ) :
    SignalingGame where
  Theta := Fin nTheta
  Msg := Fin nMsg
  Act := Fin nAct
  prior := prior
  payoff := payoff

@[simp, signaling_eval]
lemma mkFin_Theta (nTheta nMsg nAct : ℕ) [NeZero nTheta] [NeZero nMsg] [NeZero nAct]
    (prior : FinDist (Fin nTheta))
    (payoff : SignalingPlayer → Fin nTheta → Fin nMsg → Fin nAct → ℝ) :
    (mkFin nTheta nMsg nAct prior payoff).Theta = Fin nTheta := rfl

@[simp, signaling_eval]
lemma mkFin_Msg (nTheta nMsg nAct : ℕ) [NeZero nTheta] [NeZero nMsg] [NeZero nAct]
    (prior : FinDist (Fin nTheta))
    (payoff : SignalingPlayer → Fin nTheta → Fin nMsg → Fin nAct → ℝ) :
    (mkFin nTheta nMsg nAct prior payoff).Msg = Fin nMsg := rfl

@[simp, signaling_eval]
lemma mkFin_Act (nTheta nMsg nAct : ℕ) [NeZero nTheta] [NeZero nMsg] [NeZero nAct]
    (prior : FinDist (Fin nTheta))
    (payoff : SignalingPlayer → Fin nTheta → Fin nMsg → Fin nAct → ℝ) :
    (mkFin nTheta nMsg nAct prior payoff).Act = Fin nAct := rfl

@[simp, signaling_eval]
lemma mkFin_prior (nTheta nMsg nAct : ℕ) [NeZero nTheta] [NeZero nMsg] [NeZero nAct]
    (prior : FinDist (Fin nTheta))
    (payoff : SignalingPlayer → Fin nTheta → Fin nMsg → Fin nAct → ℝ) :
    (mkFin nTheta nMsg nAct prior payoff).prior = prior := rfl

@[simp, signaling_eval]
lemma mkFin_payoff (nTheta nMsg nAct : ℕ) [NeZero nTheta] [NeZero nMsg] [NeZero nAct]
    (prior : FinDist (Fin nTheta))
    (payoff : SignalingPlayer → Fin nTheta → Fin nMsg → Fin nAct → ℝ) :
    (mkFin nTheta nMsg nAct prior payoff).payoff = payoff := rfl

variable (sg : SignalingGame)

/-! ## Strategy-type abbreviations -/

/-- Sender's pure strategy: A map from types to messages. -/
abbrev SenderPureStrategy (sg : SignalingGame) := sg.Theta → sg.Msg

/-- Receiver's pure strategy: A map from messages to actions. -/
abbrev ReceiverPureStrategy (sg : SignalingGame) := sg.Msg → sg.Act

/-- Sender's mixed strategy: A map from types to distributions over messages. -/
abbrev SenderMixedStrategy (sg : SignalingGame) := sg.Theta → FinDist sg.Msg

/-- Receiver's mixed strategy: A map from messages to distributions over actions. -/
abbrev ReceiverMixedStrategy (sg : SignalingGame) := sg.Msg → FinDist sg.Act

/-- Receiver's belief system: A map from messages to posteriors over types. -/
abbrev ReceiverBelief (sg : SignalingGame) := sg.Msg → FinDist sg.Theta

/-! ## Bridge to finite Bayesian games -/

/-- Type spaces for the strategic-form representation of a signaling game: The sender has the
private type, while the receiver has the trivial type. -/
abbrev BayesianTheta : SignalingPlayer → Type
  | .sender => sg.Theta
  | .receiver => PUnit

instance instFintypeBayesianTheta (p : SignalingPlayer) : Fintype (sg.BayesianTheta p) := by
  cases p <;> infer_instance

instance instDecEqBayesianTheta (p : SignalingPlayer) : DecidableEq (sg.BayesianTheta p) := by
  cases p <;> infer_instance

/-- Action spaces for the strategic-form representation of a signaling game: The sender chooses a
message, while the receiver chooses a full response function from messages to actions. -/
abbrev BayesianAction : SignalingPlayer → Type
  | .sender => sg.Msg
  | .receiver => sg.Msg → sg.Act

instance instFintypeBayesianAction (p : SignalingPlayer) : Fintype (sg.BayesianAction p) := by
  cases p <;> infer_instance

instance instDecEqBayesianAction (p : SignalingPlayer) : DecidableEq (sg.BayesianAction p) := by
  cases p <;> infer_instance

/-- A type profile in the strategic-form signaling representation is equivalent to the sender's
type, since the receiver's type is trivial. -/
def typeProfileEquiv : (Π p : SignalingPlayer, sg.BayesianTheta p) ≃ sg.Theta where
  toFun θ := θ .sender
  invFun θ
    | .sender => θ
    | .receiver => PUnit.unit
  left_inv θ := by
    funext p
    cases p <;> simp
  right_inv θ := rfl

/-- Common prior over signaling-game type profiles. -/
noncomputable def typeDist : TypeDist SignalingPlayer sg.BayesianTheta :=
  ⟨fun θ => sg.prior.pmf (θ .sender),
    fun θ => sg.prior.nonneg (θ .sender), by
      rw [Fintype.sum_equiv sg.typeProfileEquiv
        (fun θ : Π p : SignalingPlayer, sg.BayesianTheta p => sg.prior.pmf (θ .sender))
        (fun θ : sg.Theta => sg.prior.pmf θ) (fun _ => rfl)]
      exact sg.prior.sum_one⟩

/-- Strategic-form finite Bayesian game induced by the signaling game.

Receiver actions are complete response functions `message → action`, so this is the standard
agent-normal-form representation of the signaling game. -/
noncomputable def toFinBayesianGame : FinBayesianGame where
  Player := SignalingPlayer
  instInhabitedPlayer := inferInstance
  Theta := sg.BayesianTheta
  Action := sg.BayesianAction
  payoff
    | .sender, a, θ => sg.payoff .sender (θ .sender) (a .sender) ((a .receiver) (a .sender))
    | .receiver, a, θ => sg.payoff .receiver (θ .sender) (a .sender) ((a .receiver) (a .sender))
  instFintypePlayer := inferInstance
  instDecEqPlayer := inferInstance
  -- Use the named global instances so the `prior` field's expected type and `typeDist sg`'s type
  -- carry syntactically identical instance arguments (tactic-built instances are defeq but make
  -- the `FinDist` product-instance unification blow past the heartbeat limit).
  instFintypeTheta := sg.instFintypeBayesianTheta
  instDecEqTheta := sg.instDecEqBayesianTheta
  instFintypeAction := by intro p; cases p <;> infer_instance
  instDecEqAction := by intro p; cases p <;> infer_instance
  instInhabitedAction := by intro p; cases p <;> infer_instance
  instInhabitedTheta := by intro p; cases p <;> infer_instance
  prior := typeDist sg

/-- Embed pure signaling strategies into the induced finite Bayesian game. -/
def toBayesianPureStrategy
    (σS : sg.SenderPureStrategy)
    (σR : sg.ReceiverPureStrategy) :
    sg.toFinBayesianGame.PureStrategy
  | .sender, θ => σS θ
  | .receiver, _ => σR

@[simp] lemma toBayesianPureStrategy_sender
    (σS : sg.SenderPureStrategy)
    (σR : sg.ReceiverPureStrategy)
    (θ : sg.Theta) :
    sg.toBayesianPureStrategy σS σR .sender θ = σS θ := rfl

@[simp] lemma toBayesianPureStrategy_receiver
    (σS : sg.SenderPureStrategy)
    (σR : sg.ReceiverPureStrategy)
    (u : PUnit) :
    sg.toBayesianPureStrategy σS σR .receiver u = σR := rfl

/-! ## Bayes-rule primitives: Wrappers over `FinDist.posteriorOrPrior`

`posterior` is literally `FinDist.posteriorOrPrior` applied to the prior with the sender
strategy as the likelihood, and `marginalProb` is its normalizer. The totalized `posteriorOrPrior`
is used (not the positive-evidence `FinDist.posterior`) because `posterior` must be a total
function of the message `m`: It appears in the `signalingBayesConsistent` predicate, which is
defined for every `m` and gates on `0 < marginalProb` only inside the implication. On-path
(positive-marginal) messages, where the value is the Bayesian posterior, are exactly those for
which `posterior_apply` applies. The underlying Bayes mechanics live in
`Econlib.Probability.FinDist.Bayes`. -/

/-- Marginal probability of message `m` under the prior and a sender strategy. This is the
normalizer of `FinDist.posteriorOfLikelihoodOrPrior` for the likelihood `θ ↦ (σ θ).pmf m`. -/
noncomputable def marginalProb (σ : sg.SenderMixedStrategy) (m : sg.Msg) : ℝ :=
  ∑ θ, sg.prior.pmf θ * (σ θ).pmf m

@[signaling_eval] lemma marginalProb_eq_sum (σ : sg.SenderMixedStrategy) (m : sg.Msg) :
    sg.marginalProb σ m = ∑ θ, sg.prior.pmf θ * (σ θ).pmf m := rfl

/-- A message is on-path (positive marginal) as soon as one prior-supported type sends it with
positive probability. -/
lemma marginalProb_pos {σ : sg.SenderMixedStrategy} {m : sg.Msg} {θ₀ : sg.Theta}
    (hprior : 0 < sg.prior.pmf θ₀) (hpos : 0 < (σ θ₀).pmf m) :
    0 < sg.marginalProb σ m := by
  rw [marginalProb_eq_sum]
  exact Finset.sum_pos'
    (fun θ _ => mul_nonneg (sg.prior.nonneg θ) ((σ θ).nonneg m))
    ⟨θ₀, Finset.mem_univ θ₀, mul_pos hprior hpos⟩

/-- The message marginal is nonnegative: A prior-weighted sum of probabilities. -/
lemma marginalProb_nonneg (σ : sg.SenderMixedStrategy) (m : sg.Msg) :
    0 ≤ sg.marginalProb σ m :=
  Finset.sum_nonneg fun θ _ => mul_nonneg (sg.prior.nonneg θ) ((σ θ).nonneg m)

/-- Joint distribution over `(θ, m)` induced by the prior and a sender strategy. -/
noncomputable def joint (σ : sg.SenderMixedStrategy) : FinDist (sg.Theta × sg.Msg) :=
  ⟨fun p => sg.prior.pmf p.1 * (σ p.1).pmf p.2,
    fun p => mul_nonneg (sg.prior.nonneg p.1) ((σ p.1).nonneg p.2),
    by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, FinDist.sum_one, mul_one]
      exact sg.prior.sum_one⟩

/-- Posterior over types given an observed message: `FinDist.posteriorOrPrior` of the prior with
the sender strategy as likelihood. Falls back to the prior at zero-probability (off-path) messages
(the `FinDist.posteriorOfLikelihoodOrPrior` convention). The totalized form is required because
this is a total function of the message `m`; at on-path messages (positive marginal) it is the
Bayesian posterior, characterized by `posterior_apply`. -/
noncomputable def posterior (σ : sg.SenderMixedStrategy) (m : sg.Msg) : FinDist sg.Theta :=
  sg.prior.posteriorOrPrior σ m

lemma posterior_apply (σ : sg.SenderMixedStrategy) (m : sg.Msg) (θ : sg.Theta)
    (h_denom : 0 < sg.marginalProb σ m) :
    (sg.posterior σ m).pmf θ
      = (sg.prior.pmf θ * (σ θ).pmf m) / sg.marginalProb σ m := by
  rw [posterior, ← FinDist.posterior_eq_orPrior sg.prior σ m h_denom]
  exact FinDist.posterior_apply sg.prior σ m θ h_denom

/-! ## Expected payoffs -/

/-- Sender's expected payoff from sending message `m` when type is `θ`, given receiver strategy
`σR`. -/
noncomputable def senderExpectedPayoff (σR : sg.ReceiverMixedStrategy)
    (θ : sg.Theta) (m : sg.Msg) : ℝ :=
  (σR m).expect (fun a => sg.payoff .sender θ m a)

@[signaling_eval] lemma senderExpectedPayoff_eq_expect (σR : sg.ReceiverMixedStrategy)
    (θ : sg.Theta) (m : sg.Msg) :
    sg.senderExpectedPayoff σR θ m = (σR m).expect (fun a => sg.payoff .sender θ m a) := rfl

/-- Receiver's expected payoff from taking action `a` at message `m`, given beliefs `μ`. -/
noncomputable def receiverExpectedPayoff (μ : sg.ReceiverBelief)
    (m : sg.Msg) (a : sg.Act) : ℝ :=
  (μ m).expect (fun θ => sg.payoff .receiver θ m a)

@[signaling_eval] lemma receiverExpectedPayoff_eq_expect (μ : sg.ReceiverBelief)
    (m : sg.Msg) (a : sg.Act) :
    sg.receiverExpectedPayoff μ m a = (μ m).expect (fun θ => sg.payoff .receiver θ m a) := rfl

/-! ## Signaling assessment: Pure data -/

/-- Pure-data signaling assessment: Sender's mixed strategy, receiver's mixed strategy, and the
receiver's belief system over types per message. No optimality / consistency conditions; this is
the candidate space of `signalingPBEPred`. -/
structure SignalingAssessment where
  /-- Sender's mixed strategy. -/
  senderStrategy : sg.SenderMixedStrategy
  /-- Receiver's mixed strategy. -/
  receiverStrategy : sg.ReceiverMixedStrategy
  /-- Receiver's belief system. -/
  belief : sg.ReceiverBelief

/-- A deviator in the signaling refined equilibrium: A sender at type `θ`, or a receiver at message
`m`. -/
inductive SignalingDeviator where
  | sender (θ : sg.Theta)
  | receiver (m : sg.Msg)

/-! ## Signaling refined equilibrium substrate -/

/-- Signaling-level deviation: Only the deviator's mixed strategy changes; everything else fixed. A
sender deviation at `θ` modifies only `a.senderStrategy θ`; a receiver deviation at `m` modifies
only `a.receiverStrategy m`; in both cases the belief system is held fixed. -/
def signalingSwap :
    sg.SignalingDeviator → sg.SignalingAssessment → sg.SignalingAssessment → Prop
  | .sender θ, a, a' =>
      a'.receiverStrategy = a.receiverStrategy ∧
      a'.belief = a.belief ∧
      ∀ θ' : sg.Theta, θ' ≠ θ → a'.senderStrategy θ' = a.senderStrategy θ'
  | .receiver m, a, a' =>
      a'.senderStrategy = a.senderStrategy ∧
      a'.belief = a.belief ∧
      ∀ m' : sg.Msg, m' ≠ m → a'.receiverStrategy m' = a.receiverStrategy m'

/-- Signaling-level value at a deviator. Sender deviator at type `θ`: The type-`θ` expected payoff
under `a.senderStrategy θ` mixed over messages, with the receiver responding via
`a.receiverStrategy`. Receiver deviator at message `m`: The receiver's expected payoff under
`a.receiverStrategy m`, with types weighted by the receiver's belief `a.belief m`. -/
noncomputable def signalingValue : sg.SignalingDeviator → sg.SignalingAssessment → ℝ
  | .sender θ, a =>
      ∑ m : sg.Msg, (a.senderStrategy θ).pmf m *
        sg.senderExpectedPayoff a.receiverStrategy θ m
  | .receiver m, a =>
      ∑ θ : sg.Theta, (a.belief m).pmf θ *
        ∑ act : sg.Act, (a.receiverStrategy m).pmf act *
          sg.payoff .receiver θ m act

/-- Signaling-level Bayes consistency: On-path beliefs equal Bayesian posteriors. -/
def signalingBayesConsistent (a : sg.SignalingAssessment) : Prop :=
  ∀ (m : sg.Msg),
    0 < sg.marginalProb a.senderStrategy m →
    a.belief m = sg.posterior a.senderStrategy m

/-- The signaling refined equilibrium substrate. Strategy space is `SignalingAssessment`, the
deviator index is `SignalingDeviator`, the swap relation is `signalingSwap`, the value is
`signalingValue`, and validity is signaling Bayes consistency. -/
noncomputable def signalingPBEPred (sg : SignalingGame) : EquilibriumRefinement where
  S := sg.SignalingAssessment
  I := sg.SignalingDeviator
  swap := sg.signalingSwap
  value := sg.signalingValue
  valid := sg.signalingBayesConsistent

/-- The substrate-uniform signaling PBE predicate: `IsSignalingPBE a` iff `a` is a refined
equilibrium of `signalingPBEPred`. Substrate-uniformity (locked-in decision #2): No native
predicate carve-out. -/
def IsSignalingPBE (sg : SignalingGame) (a : sg.SignalingAssessment) : Prop :=
  sg.signalingPBEPred.IsRefinedEquilibrium a

/-! ## Off the equilibrium path

There is a single path boundary in the signaling refinements: A message's prior-weighted
marginal `marginalProb`. `signalingBayesConsistent` pins beliefs on the positive-marginal (reached)
messages; `isOffPath` is the exact complement — the zero-marginal messages, on which beliefs are
free and which the intuitive criterion disciplines. Defining off-path as `marginalProb = 0` (the
textbook Cho-Kreps probability-path notion) rather than as strategy support keeps the two notions
complementary by construction, so no message can be both belief-unconstrained and
refinement-undisciplined. Strategy support — no type sends `m` — is only *sufficient* for off-path
(`isOffPath_of_forall_pmf_zero`): It is strictly stronger once a prior-zero type can send a message
with positive probability. -/

/-- A message is **off the equilibrium path** under an assessment when it is reached with
probability zero — its prior-weighted marginal vanishes. This is the textbook (Cho-Kreps)
probability-path notion and the exact complement of the `0 < marginalProb` gate of
`signalingBayesConsistent` (`isOffPath_iff_not_marginalProb_pos`). A message can be off path yet
still be sent by a prior-zero type, so strategy support is only sufficient; see
`isOffPath_of_forall_pmf_zero`. -/
def isOffPath (a : sg.SignalingAssessment) (m : sg.Msg) : Prop :=
  sg.marginalProb a.senderStrategy m = 0

/-- **Strategy support is sufficient for off-path.** If no sender type sends `m` with positive
probability, then `m` is off the equilibrium path. The converse fails exactly when a prior-zero
type sends `m` with positive probability — the message is then reached with probability zero yet
has a type sending it. -/
lemma isOffPath_of_forall_pmf_zero {a : sg.SignalingAssessment} {m : sg.Msg}
    (h : ∀ θ, (a.senderStrategy θ).pmf m = 0) : sg.isOffPath a m := by
  rw [isOffPath, marginalProb_eq_sum]
  exact Finset.sum_eq_zero fun θ _ => by rw [h θ, mul_zero]

/-- Off path is exactly the complement of the Bayes-consistency gate: A message is off path iff its
marginal is not positive. The two signaling refinements thus partition messages along one boundary
— `signalingBayesConsistent` constrains beliefs on the reached side, the intuitive criterion on the
off-path side — so no message escapes both. -/
lemma isOffPath_iff_not_marginalProb_pos {a : sg.SignalingAssessment} {m : sg.Msg} :
    sg.isOffPath a m ↔ ¬ 0 < sg.marginalProb a.senderStrategy m := by
  rw [isOffPath]
  refine ⟨fun h => by rw [h]; exact lt_irrefl 0, fun h => ?_⟩
  exact le_antisymm (not_lt.mp h) (sg.marginalProb_nonneg a.senderStrategy m)

/-! ## Equilibrium payoffs -/

/-- Sender's ex-ante expected payoff under a signaling assessment. -/
noncomputable def SignalingAssessment.senderExAntePayoff (a : sg.SignalingAssessment) : ℝ :=
  sg.prior.expect fun θ =>
    (a.senderStrategy θ).expect fun m =>
      sg.senderExpectedPayoff a.receiverStrategy θ m

/-- Receiver's ex-ante expected payoff under a signaling assessment. -/
noncomputable def SignalingAssessment.receiverExAntePayoff (a : sg.SignalingAssessment) : ℝ :=
  sg.prior.expect fun θ =>
    (a.senderStrategy θ).expect fun m =>
      (a.receiverStrategy m).expect fun act =>
        sg.payoff .receiver θ m act

/-! ## Pooling and separating: Structural predicates and bundled PBEs

The structural predicates `IsPooling` and `IsSeparating` examine only the sender's mixed
strategy and say nothing about equilibrium. The bundled structures `IsPoolingPBE` and
`IsSeparatingPBE` pair the structural condition with `IsSignalingPBE`. -/

/-- A signaling assessment's sender strategy is *pooling*: All types send a common message with
probability one. This is a purely structural condition on `a.senderStrategy`; it does not assert
that `a` is a PBE. For the bundled notion see `IsPoolingPBE`. -/
def IsPooling (a : sg.SignalingAssessment) : Prop :=
  ∃ m : sg.Msg, ∀ θ : sg.Theta, (a.senderStrategy θ).pmf m = 1

/-- A signaling assessment's sender strategy is *separating*: Distinct types never both assign
positive probability to the same message. This is a purely structural condition on
`a.senderStrategy`; it does not assert that `a` is a PBE. For the bundled notion see
`IsSeparatingPBE`. -/
def IsSeparating (a : sg.SignalingAssessment) : Prop :=
  ∀ θ₁ θ₂ : sg.Theta, θ₁ ≠ θ₂ →
    ∀ m : sg.Msg,
      ¬((a.senderStrategy θ₁).pmf m > 0 ∧ (a.senderStrategy θ₂).pmf m > 0)

/-- A *pooling PBE*: A signaling PBE whose sender strategy is pooling. -/
structure IsPoolingPBE (a : sg.SignalingAssessment) : Prop where
  /-- The assessment is a signaling PBE. -/
  isSignalingPBE : sg.IsSignalingPBE a
  /-- All sender types send a common message with probability one. -/
  isPooling : sg.IsPooling a

/-- A *separating PBE*: A signaling PBE whose sender strategy is separating. -/
structure IsSeparatingPBE (a : sg.SignalingAssessment) : Prop where
  /-- The assessment is a signaling PBE. -/
  isSignalingPBE : sg.IsSignalingPBE a
  /-- Distinct sender types never both put positive probability on the same message. -/
  isSeparating : sg.IsSeparating a

end SignalingGame

end Econlib.GameTheory
