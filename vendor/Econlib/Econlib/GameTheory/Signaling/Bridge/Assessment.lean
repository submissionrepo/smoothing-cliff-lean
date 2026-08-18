/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.GameTheory.Signaling.Bridge.GameTree

/-!
# Embedding signaling assessments as extensive-form assessments

Embeds a `SignalingAssessment` as an `Assessment` on the encoded extensive game: The behavioral
strategy via `SignalingAssessment.toBehavioral`, the belief system via
`SignalingAssessment.toBeliefSystem`, and the packaging via `SignalingAssessment.toAssessment`. The
reach-probability and information-set-probability identities bridge the framework's
path-probability calculations to the signaling primitives and underlie the Bayes-consistency
transport.

## Main definitions

* `SignalingAssessment.toBehavioral`: The embedded behavioral strategy.
* `SignalingAssessment.toBeliefSystem`: The embedded belief system.
* `SignalingAssessment.toAssessment`: The bundled assessment.
* `SignalingGame.receiverSupport` / `receiverBelief`: The receiver's belief support and mass.

## Main statements

* `SignalingGame.reachProb_type` / `reachProb_typeMsg`: Reach probabilities of the embedded
  behavioral strategy at the sender and receiver histories.
* `SignalingGame.infoSetProb_sender` / `infoSetProb_receiver`: Information-set probabilities at the
  sender and receiver observations.
* `SignalingAssessment.toAssessment_IsBayesConsistent`: Signaling-level Bayes consistency
  transports to Bayes consistency of the embedded assessment.

## Tags

signaling game, assessment, belief system, bayes consistency, extensive form
-/

@[expose] public noncomputable section

open Econlib.Probability

namespace Econlib.GameTheory

/-! ## Embedding `SignalingAssessment` as an `Assessment`

The substrate types (`SignalingAssessment`, `SignalingDeviator`, `signalingSwap`,
`signalingValue`, `signalingBayesConsistent`, `signalingPBEPred`, `IsSignalingPBE`) all live in
`Signaling/Basic.lean`. This section embeds a `SignalingAssessment` as an `Assessment` on the
encoded extensive game. -/

namespace SignalingGame

variable (sg : SignalingGame)

/-- Embed a sender + receiver mixed-strategy pair as a behavioral strategy on the encoded extensive
form. -/
def SignalingAssessment.toBehavioral
    (a : sg.SignalingAssessment) :
    (sg.toExtensiveForm).BehavioralStrategy
  | .sender,   θ => (a.senderStrategy θ).toSimplex
  | .receiver, m => (a.receiverStrategy m).toSimplex

@[simp] lemma SignalingAssessment.toBehavioral_sender
    (a : sg.SignalingAssessment) (θ : sg.Theta) :
    (SignalingAssessment.toBehavioral (sg := sg) a) .sender θ
      = (a.senderStrategy θ).toSimplex := rfl

@[simp] lemma SignalingAssessment.toBehavioral_receiver
    (a : sg.SignalingAssessment) (m : sg.Msg) :
    (SignalingAssessment.toBehavioral (sg := sg) a) .receiver m
      = (a.receiverStrategy m).toSimplex := rfl

/-! ### Receiver belief construction

The receiver's belief at message `m` is supported on the set of histories
`{[type θ, msg m] | θ : sg.Theta}`. We construct the belief by injective pushforward of
`pbe.belief m` along the canonical history map. -/

/-- The canonical receiver-history map: Type θ at message m. -/
def receiverHist (m : sg.Msg) (θ : sg.Theta) : List sg.Event :=
  [Event.type θ, Event.msg m]

lemma receiverHist_injective (m : sg.Msg) :
    Function.Injective (sg.receiverHist m) := fun θ₁ θ₂ h => by
  simpa [receiverHist] using h

/-- Canonical sender info-set element at type θ, with witness
`(.player sender).movesAt sender ∧
observe sender [type θ] = θ`. -/
def senderInfoSet
        (θ : sg.Theta) :
    (sg.toExtensiveForm).InfoSet .sender θ :=
  ⟨[Event.type θ], rfl, rfl⟩

/-- Canonical receiver info-set element at (type θ, message m), with witness that the receiver
moves at `[type θ, msg m]` and observes `m`. -/
def receiverInfoSet
        (m : sg.Msg) (θ : sg.Theta) :
    (sg.toExtensiveForm).InfoSet .receiver m :=
  ⟨[Event.type θ, Event.msg m], rfl, rfl⟩

lemma receiverInfoSet_injective
        (m : sg.Msg) :
    Function.Injective (sg.receiverInfoSet m) := fun _ _ h =>
  sg.receiverHist_injective m (congrArg Subtype.val h)

/-- The receiver's belief support at message m: Subtype-witnessed histories `[type θ, msg m]`. -/
def receiverSupport
        (m : sg.Msg) :
    Finset ((sg.toExtensiveForm).InfoSet .receiver m) :=
  Finset.univ.image (sg.receiverInfoSet m)

/-- Belief mass on a receiver info-set subtype element, equal to `(a.belief m).pmf θ` at the
canonical history `[type θ, msg m]` and `0` everywhere else (the fall-through is vacuous since the
receiver's info set only contains such histories). -/
def receiverBelief
    (a : sg.SignalingAssessment)
        (m : sg.Msg)
    (x : (sg.toExtensiveForm).InfoSet .receiver m) : ℝ :=
  match x.1 with
  | [Event.type θ, Event.msg _] => (a.belief m).pmf θ
  | _ => 0

@[simp] lemma receiverBelief_canonical
    (a : sg.SignalingAssessment)
        (m : sg.Msg) (θ : sg.Theta) :
    sg.receiverBelief a m
        (sg.receiverInfoSet m θ) = (a.belief m).pmf θ := rfl

/-- Embed a signaling-level assessment as a `BeliefSystem` on the encoded extensive form. The
sender's belief at type θ is concentrated on the subtype witness for `[type θ]` (its own
information is its type). The receiver's belief at message m is supported on subtype witnesses
`{[type θ, msg m] | θ}` with mass `a.belief m θ` on each. -/
noncomputable def SignalingAssessment.toBeliefSystem
    (a : sg.SignalingAssessment) :
    BeliefSystem (sg.toExtensiveForm) where
  support
    | .sender => fun θ => {sg.senderInfoSet θ}
    | .receiver => fun m => sg.receiverSupport m
  belief
    | .sender => fun _ _ => 1
    | .receiver => fun m x => sg.receiverBelief a m x
  belief_nonneg := by
    intro i obs x
    cases i with
    | sender => exact zero_le_one
    | receiver =>
        -- The receiver belief is either (a.belief m).pmf θ (≥ 0) or 0 by the fall-through.
        change 0 ≤ sg.receiverBelief a obs x
        unfold receiverBelief
        split
        · exact (a.belief obs).nonneg _
        · exact le_rfl
  belief_eq_zero_of_not_mem
    | .sender, θ, x, hxnotmem => by
        -- `x` is in `InfoSet .sender θ`, so `x.1 = [type θ]` by
        -- `sender_movesAt_iff` and the observation equation.
        exfalso
        obtain ⟨θ', hθ'⟩ := (sg.sender_movesAt_iff x.1).mp x.2.1
        have hobs : θ' = θ := by have := x.2.2; rw [hθ'] at this; exact this
        subst hobs
        apply hxnotmem
        rw [Finset.mem_singleton]
        exact Subtype.ext hθ'
    | .receiver, m, x, hxnotmem => by
        exfalso
        obtain ⟨θ, m', hθm⟩ := (sg.receiver_movesAt_iff x.1).mp x.2.1
        have hobs : m' = m := by have := x.2.2; rw [hθm] at this; exact this
        subst hobs
        apply hxnotmem
        unfold receiverSupport
        rw [Finset.mem_image]
        exact ⟨θ, Finset.mem_univ _, Subtype.ext hθm.symm⟩
  support_exhaustive
    -- Both supports already enumerate the *entire* info set, so exhaustiveness holds for every
    -- history (reachable or not). Each info-set element is forced to its canonical history form
    -- by `sender_movesAt_iff` / `receiver_movesAt_iff` and the observation equation, hence lands
    -- in the singleton / image support.
    | .sender, θ, x, _hreach => by
        obtain ⟨θ', hθ'⟩ := (sg.sender_movesAt_iff x.1).mp x.2.1
        have hobs : θ' = θ := by have := x.2.2; rw [hθ'] at this; exact this
        subst hobs
        rw [Finset.mem_singleton]
        exact Subtype.ext hθ'
    | .receiver, m, x, _hreach => by
        obtain ⟨θ, m', hθm⟩ := (sg.receiver_movesAt_iff x.1).mp x.2.1
        have hobs : m' = m := by have := x.2.2; rw [hθm] at this; exact this
        subst hobs
        unfold receiverSupport
        rw [Finset.mem_image]
        exact ⟨θ, Finset.mem_univ _, Subtype.ext hθm.symm⟩
  belief_sum_one
    | .sender, θ, _ => by
        rw [Finset.sum_singleton]
    | .receiver, m, _ => by
        unfold receiverSupport
        rw [Finset.sum_image
          (fun θ₁ _ θ₂ _ h => sg.receiverInfoSet_injective m h)]
        exact (a.belief m).sum_one

/-- Bundle the embedded strategy and belief system into an `Assessment`. -/
def SignalingAssessment.toAssessment
    (a : sg.SignalingAssessment) :
    Assessment (sg.toExtensiveForm) where
  strategy := SignalingAssessment.toBehavioral (sg := sg) a
  beliefs := SignalingAssessment.toBeliefSystem (sg := sg) a

@[simp] lemma SignalingAssessment.toAssessment_strategy
    (a : sg.SignalingAssessment) :
    (SignalingAssessment.toAssessment (sg := sg) a).strategy =
      SignalingAssessment.toBehavioral (sg := sg) a := rfl

@[simp] lemma SignalingAssessment.toAssessment_beliefs
    (a : sg.SignalingAssessment) :
    (SignalingAssessment.toAssessment (sg := sg) a).beliefs =
      SignalingAssessment.toBeliefSystem (sg := sg) a := rfl

/-! ## Reach- and information-set-probability identities

Reach probabilities for the embedded behavioral strategy, bridging the framework's
path-probability calculations to the signaling primitives. -/

@[simp] lemma reachProb_type
    (a : sg.SignalingAssessment) (θ : sg.Theta) :
    reachProb (sg.toExtensiveForm)
      (SignalingAssessment.toBehavioral (sg := sg) a) [Event.type θ] =
      sg.prior.pmf θ := by
  unfold reachProb ExtensiveForm.finitePrefixProb ExtensiveForm.finitePrefixProbFrom
    ExtensiveForm.stepProb
  change NodeKind.eventProb (sg.toExtensiveForm.tree.nodeKind []) _ (Event.type θ) * 1 = _
  rw [mul_one]
  change ∑ θ' : sg.Theta, (if Event.type θ' = Event.type θ then sg.prior.pmf θ' else 0)
    = sg.prior.pmf θ
  simp only [Event.type.injEq, Fintype.sum_ite_eq']

@[simp] lemma reachProb_typeMsg
    (a : sg.SignalingAssessment) (θ : sg.Theta) (m : sg.Msg) :
    reachProb (sg.toExtensiveForm)
      (SignalingAssessment.toBehavioral (sg := sg) a)
      [Event.type θ, Event.msg m] =
      sg.prior.pmf θ * (a.senderStrategy θ).pmf m := by
  unfold reachProb ExtensiveForm.finitePrefixProb
  rw [ExtensiveForm.finitePrefixProbFrom_cons, ExtensiveForm.finitePrefixProbFrom_cons,
    ExtensiveForm.finitePrefixProbFrom_nil, mul_one]
  congr 1
  · unfold ExtensiveForm.stepProb
    change ∑ θ' : sg.Theta, (if Event.type θ' = Event.type θ then sg.prior.pmf θ' else 0)
      = sg.prior.pmf θ
    simp only [Event.type.injEq, Fintype.sum_ite_eq']
  · unfold ExtensiveForm.stepProb
    change ∑ m' : sg.Msg, (if Event.msg m' = Event.msg m then
      ((SignalingAssessment.toBehavioral (sg := sg) a).atHistory
        [Event.type θ]).val m' else 0) = (a.senderStrategy θ).pmf m
    simp only [Event.msg.injEq, Fintype.sum_ite_eq']
    rfl

/-- The information-set probability at a sender observation θ is the prior on θ. The sender's
information set is a singleton `{senderInfoSet θ}` and the only history in it has reach probability
`prior.pmf θ`. -/
@[simp] lemma infoSetProb_sender
    (a : sg.SignalingAssessment) (θ : sg.Theta) :
    infoSetProb (sg.toExtensiveForm)
      (SignalingAssessment.toBehavioral (sg := sg) a)
      (SignalingAssessment.toBeliefSystem (sg := sg) a)
      .sender θ = sg.prior.pmf θ := by
  change ∑ x ∈ ({sg.senderInfoSet θ} : Finset ((sg.toExtensiveForm).InfoSet .sender θ)),
    reachProb (sg.toExtensiveForm) (SignalingAssessment.toBehavioral (sg := sg) a) x.1 = _
  rw [Finset.sum_singleton]
  exact sg.reachProb_type a θ

/-- The information-set probability at a receiver observation m equals the marginal signal
probability of m under the prior and the sender's strategy. Bridges the framework's
path-probability sum to the persuasion-style marginal. -/
@[simp] lemma infoSetProb_receiver
    (a : sg.SignalingAssessment) (m : sg.Msg) :
    infoSetProb (sg.toExtensiveForm)
      (SignalingAssessment.toBehavioral (sg := sg) a)
      (SignalingAssessment.toBeliefSystem (sg := sg) a)
      .receiver m =
      sg.marginalProb a.senderStrategy m := by
  change ∑ x ∈ sg.receiverSupport m,
    reachProb (sg.toExtensiveForm) (SignalingAssessment.toBehavioral (sg := sg) a) x.1 = _
  unfold receiverSupport
  rw [Finset.sum_image (fun θ₁ _ θ₂ _ heq => sg.receiverInfoSet_injective m heq)]
  unfold SignalingGame.marginalProb
  refine Finset.sum_congr rfl (fun θ _ => ?_)
  change reachProb (sg.toExtensiveForm) (SignalingAssessment.toBehavioral (sg := sg) a)
      [Event.type θ, Event.msg m] = _
  rw [reachProb_typeMsg]

/-- Bayesian consistency of the embedded assessment from a `SignalingAssessment` satisfying
signaling-level Bayes consistency. Sender's beliefs are trivially consistent (singleton support).
Receiver's beliefs at on-path messages match the posterior derived from `a.senderStrategy` via the
hypothesis `h_consistent` and the identity `infoSetProb receiver m = signalMarginal`. -/
theorem SignalingAssessment.toAssessment_IsBayesConsistent
    (a : sg.SignalingAssessment) (h_consistent : sg.signalingBayesConsistent a) :
    IsBayesConsistent (sg.toExtensiveForm)
      (SignalingAssessment.toAssessment (sg := sg) a) := by
  classical
  intro i obs hpos h
  change 0 < infoSetProb (sg.toExtensiveForm)
      (SignalingAssessment.toBehavioral (sg := sg) a)
      (SignalingAssessment.toBeliefSystem (sg := sg) a) i obs at hpos
  change (SignalingAssessment.toBeliefSystem (sg := sg) a).prob i obs h =
    bayesBeliefAt (sg.toExtensiveForm)
      (SignalingAssessment.toBehavioral (sg := sg) a)
      (SignalingAssessment.toBeliefSystem (sg := sg) a) i obs h
  cases i with
  | sender =>
    have hinfo := sg.infoSetProb_sender a obs
    have hprior_pos : 0 < sg.prior.pmf obs := hinfo ▸ hpos
    by_cases hin : ((sg.toExtensiveForm).tree.nodeKind h).movesAt .sender ∧
        (sg.toExtensiveForm).info.observe .sender h = obs
    · have hheq : h = [Event.type obs] := by
        obtain ⟨θ', hθ'⟩ := (sg.sender_movesAt_iff h).mp hin.1
        have hθobs : θ' = obs := by have := hin.2; rw [hθ'] at this; exact this
        rw [hθ', hθobs]
      rw [BeliefSystem.prob_of_mem _ _ _ hin]
      have hbelief :
          (SignalingAssessment.toBeliefSystem (sg := sg) a).belief
            SignalingPlayer.sender obs ⟨h, hin⟩ = 1 := rfl
      rw [hbelief]
      symm
      unfold bayesBeliefAt
      have hmem : (⟨h, hin⟩ :
          (sg.toExtensiveForm).InfoSet .sender obs) ∈
            (SignalingAssessment.toBeliefSystem (sg := sg) a).support
              SignalingPlayer.sender obs := by
        change ⟨h, hin⟩ ∈ ({sg.senderInfoSet obs} :
          Finset ((sg.toExtensiveForm).InfoSet .sender obs))
        rw [Finset.mem_singleton]
        exact Subtype.ext hheq
      simp only [dif_pos hin, if_pos hmem, dif_pos hpos]
      rw [show reachProb (sg.toExtensiveForm)
            (SignalingAssessment.toBehavioral (sg := sg) a) h = sg.prior.pmf obs
          from hheq ▸ sg.reachProb_type a obs,
        hinfo, div_self (ne_of_gt hprior_pos)]
    · rw [BeliefSystem.prob_of_not_mem _ _ _ hin]
      symm
      unfold bayesBeliefAt
      simp only [dif_neg hin]
  | receiver =>
    have hinfo := sg.infoSetProb_receiver a obs
    have hmarginal_pos :
        0 < sg.marginalProb a.senderStrategy obs :=
      hinfo ▸ hpos
    have hbayes : a.belief obs = sg.posterior a.senderStrategy obs :=
      h_consistent obs hmarginal_pos
    by_cases hin : ((sg.toExtensiveForm).tree.nodeKind h).movesAt .receiver ∧
        (sg.toExtensiveForm).info.observe .receiver h = obs
    · obtain ⟨θ, m', hθm⟩ := (sg.receiver_movesAt_iff h).mp hin.1
      have hmobs : m' = obs := by have := hin.2; rw [hθm] at this; exact this
      have hheq : h = [Event.type θ, Event.msg obs] := by rw [hθm, hmobs]
      rw [BeliefSystem.prob_of_mem _ _ _ hin]
      have hbelief :
          (SignalingAssessment.toBeliefSystem (sg := sg) a).belief
            SignalingPlayer.receiver obs ⟨h, hin⟩ = (a.belief obs).pmf θ := by
        change sg.receiverBelief a obs ⟨h, hin⟩ = _
        rw [show sg.receiverBelief a obs ⟨h, hin⟩ =
              sg.receiverBelief a obs ⟨[Event.type θ, Event.msg obs], hheq ▸ hin⟩ from
            congrArg _ (Subtype.ext hheq)]
        rfl
      rw [hbelief]
      symm
      unfold bayesBeliefAt
      have hmem : (⟨h, hin⟩ :
          (sg.toExtensiveForm).InfoSet .receiver obs) ∈
            (SignalingAssessment.toBeliefSystem (sg := sg) a).support
              SignalingPlayer.receiver obs := by
        change ⟨h, hin⟩ ∈ sg.receiverSupport obs
        unfold receiverSupport
        rw [Finset.mem_image]
        exact ⟨θ, Finset.mem_univ _, Subtype.ext hheq.symm⟩
      simp only [dif_pos hin, if_pos hmem, dif_pos hpos]
      rw [show reachProb (sg.toExtensiveForm)
            (SignalingAssessment.toBehavioral (sg := sg) a) h =
            sg.prior.pmf θ * (a.senderStrategy θ).pmf obs from
          hheq ▸ sg.reachProb_typeMsg a θ obs, hinfo, hbayes]
      exact (sg.posterior_apply a.senderStrategy obs θ hmarginal_pos).symm
    · -- h not in receiver info set: both sides 0.
      rw [BeliefSystem.prob_of_not_mem _ _ _ hin]
      symm
      unfold bayesBeliefAt
      simp only [dif_neg hin]

end SignalingGame

end Econlib.GameTheory
