/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.GameTheory
import EconlibExamples.GameTheory.BeerQuiche
import EconlibExamples.GameTheory.SpenceSignaling
import Mathlib

/-!
# Signaling Extensive-Form Bridge & Sequential-Equilibrium Existence — Non-Vacuity Checks

Compile-time semantic witnesses for the `Econlib.GameTheory.Signaling.Bridge.*` and
`Signaling.Perturbation` substrate: The encoded game tree (`Bridge/GameTree.lean`), the assessment
embedding (`Bridge/Assessment.lean`), the tremble machinery and sequential-equilibrium existence
(`Bridge/SequentialEquilibrium.lean`), the perturbation sequence (`Bridge/Existence.lean`), and the
perturbed simplex (`Perturbation.lean`).

These declarations are almost all unconditional structural / continuity / convergence facts whose
*content* is the encoding (node-kind dispatch, reach probabilities, posterior tremble limits). The
two semantically loaded endpoints are:

* **`reachProb_type` / `reachProb_typeMsg`** — anchored to concrete numbers on the Spence
  separating assessment (uniform prior `1/2`): The high type reaches `[type high]` with `1/2` and
  `[type high, msg degree]` with `1/2`, but `[type high, msg noDegree]` with `0`. A reach-prob
  miscomputation (forgetting the sender mix, or transposing on/off-path messages) is caught.
* **`exists_signalingSequentialEquilibrium`** — instantiated on the **full-support-prior** Spence
  game. The library memo records that signaling sequential-equilibrium existence *requires* a
  full-support prior (a zero-prior sender info set makes `HasConsistentBeliefs` unsatisfiable), so
  the witness routes through `hfull` explicitly, and we re-derive the same endpoint via the PBE
  bridge (`isSignalingSequentialEquilibrium_of_isSignalingPBE`) on the genuine separating PBE.

## Transitivity judgments

The deep tremble plumbing (`senderWeight`/`receiverWeight` families, `trembleAssessment`,
`hasConsistentBeliefs_toAssessment_of_senderTremble`) is *transitively* exercised by
`exists_signalingSequentialEquilibrium` and `hasConsistentBeliefs_of_signalingBayesConsistent`,
which route through it on a concrete full-support game. Where a standalone concrete witness adds
nothing over the endpoint (e.g. the abstract continuity of `marginalProbRaw`, the compactness of
`JointState`), we exercise the declaration directly but do not re-anchor numbers. The
necessity-of-full-support direction (no SE without it) is *not* cheaply witnessed — proving a
non-existence claim requires unfolding `HasConsistentBeliefs` on a degenerate-prior game — and is
documented rather than fabricated.
-/

noncomputable section

namespace EconlibTest.GameTheory.SignalingBridge

open Econlib.GameTheory Econlib.Probability
open scoped BigOperators

open EconlibExamples.GameTheory.SpenceSignaling
  (spence spenceSeparating spenceSenderStrategy spenceReceiverStrategy spenceBelief
   spence_separating_isSignalingPBE spence_separating_PBE_exists low high noDegree degree
   lowWage highWage spencePrior)

open EconlibExamples.GameTheory.BeerQuiche
  (beerQuiche beerQuichePrior weak strong quiche beer beerQuichePooling beerQuichePoolingSender
   beerQuichePooling_isSignalingPBE beerQuichePooling_beer_isOffPath)

/-! ## Chunk 4a — The encoded game tree (`Bridge/GameTree.lean`)

The node-kind dispatcher encodes the four canonical depths: Chance root, sender at `[type θ]`,
receiver at `[type θ, msg m]`, terminal at `[type θ, msg m, act a]`. We exercise the simp lemmas
that read each depth back, plus the `movesAt` characterizations and the info-structure
observations, on the Spence game. -/

/-- `toGameTree_nodeKind`: The encoded tree's node kind at a history is the dispatcher value. -/
theorem spence_toGameTree_nodeKind (h : List spence.Event) :
    spence.toGameTree.nodeKind h = spence.toNodeKind h :=
  spence.toGameTree_nodeKind h

/-- `toNodeKind_nil`: The root is the chance node drawing the type from the prior. -/
theorem spence_toNodeKind_nil :
    spence.toNodeKind [] =
      .chanceFinite
        { Outcome := spence.Theta
          dist := spence.prior
          emit := SignalingGame.Event.type } :=
  spence.toNodeKind_nil

/-- `toNodeKind_type`: At `[type θ]` the sender moves, choosing a message. -/
theorem spence_toNodeKind_type (θ : spence.Theta) :
    spence.toNodeKind [.type θ] =
      .player
        { mover := .sender
          Choice := spence.Msg
          emit := SignalingGame.Event.msg } :=
  spence.toNodeKind_type θ

/-- `toNodeKind_typeMsg`: At `[type θ, msg m]` the receiver moves, choosing an action. -/
theorem spence_toNodeKind_typeMsg (θ : spence.Theta) (m : spence.Msg) :
    spence.toNodeKind [.type θ, .msg m] =
      .player
        { mover := .receiver
          Choice := spence.Act
          emit := SignalingGame.Event.act } :=
  spence.toNodeKind_typeMsg θ m

/-- `toNodeKind_terminal`: At `[type θ, msg m, act a]` the node is terminal with realized
payoffs. -/
theorem spence_toNodeKind_terminal (θ : spence.Theta) (m : spence.Msg) (a : spence.Act) :
    spence.toNodeKind [.type θ, .msg m, .act a] =
      .terminal
        (fun
          | .sender => spence.payoff .sender θ m a
          | .receiver => spence.payoff .receiver θ m a) :=
  spence.toNodeKind_terminal θ m a

/-- `sender_movesAt_iff`: The sender moves *only* at singleton type histories `[type θ]` — the
information structure of a signaling game (one sender decision per type). A bridge that let the
sender move elsewhere would break the extensive-form encoding. -/
theorem spence_sender_movesAt_iff (h : List spence.Event) :
    (spence.toGameTree.nodeKind h).movesAt SignalingPlayer.sender ↔
      ∃ θ : spence.Theta, h = [SignalingGame.Event.type θ] :=
  spence.sender_movesAt_iff h

/-- `receiver_movesAt_iff`: The receiver moves *only* at `[type θ, msg m]` histories — after a
message, before an action. -/
theorem spence_receiver_movesAt_iff (h : List spence.Event) :
    (spence.toGameTree.nodeKind h).movesAt SignalingPlayer.receiver ↔
      ∃ (θ : spence.Theta) (m : spence.Msg), h = [SignalingGame.Event.type θ, .msg m] :=
  spence.receiver_movesAt_iff h

/-- `observe_sender_type`: At `[type θ]` the sender observes their own type `θ`. -/
theorem spence_observe_sender_type (θ : spence.Theta) :
    spence.infoStructure.observe .sender [.type θ] = θ :=
  spence.observe_sender_type θ

/-- `observe_receiver_typeMsg`: At `[type θ, msg m]` the receiver observes the message `m` —
**not** the type. This is the privacy of `θ`, the defining feature of a signaling game; a bridge
that leaked `θ` here would collapse the receiver's information set. -/
theorem spence_observe_receiver_typeMsg (θ : spence.Theta) (m : spence.Msg) :
    spence.infoStructure.observe .receiver [.type θ, .msg m] = m :=
  spence.observe_receiver_typeMsg θ m

/-- `toExtensiveForm_tree`: The bundled extensive form's tree is the encoded game tree. -/
theorem spence_toExtensiveForm_tree :
    spence.toExtensiveForm.tree = spence.toGameTree :=
  spence.toExtensiveForm_tree

/-- `toExtensiveForm_info`: The bundled extensive form's info structure is the signaling info
structure (hiding `θ` from the receiver). -/
theorem spence_toExtensiveForm_info :
    spence.toExtensiveForm.info = spence.infoStructure :=
  spence.toExtensiveForm_info

/-- `playerBehavior_sender_val`: At `[type θ]`, the behavioral strategy's local mix coincides with
the sender's extracted behavioral mix at `θ` — the cast/transport along the constructor equality is
the identity on the underlying pmf. -/
theorem spence_playerBehavior_sender_val
    (σ : spence.toExtensiveForm.BehavioralStrategy) (θ : spence.Theta) :
    (σ.playerBehavior (G := spence.toExtensiveForm) [SignalingGame.Event.type θ] rfl).val =
      (spence.behavioralSender σ θ).val :=
  spence.playerBehavior_sender_val σ θ

/-- `playerBehavior_receiver_val`: At `[type θ, msg m]`, the behavioral strategy's local mix
coincides with the receiver's extracted behavioral mix at `m`. -/
theorem spence_playerBehavior_receiver_val
    (σ : spence.toExtensiveForm.BehavioralStrategy) (θ : spence.Theta) (m : spence.Msg) :
    (σ.playerBehavior (G := spence.toExtensiveForm) [.type θ, .msg m] rfl).val =
      (spence.behavioralReceiver σ θ m).val :=
  spence.playerBehavior_receiver_val σ θ m

/-- `toExtensiveGame_toExtensiveForm`: The encoded extensive *game* sits over the encoded extensive
*form* — the packaging keeps the tree/info structure intact. -/
theorem spence_toExtensiveGame_toExtensiveForm :
    spence.toExtensiveGame.toExtensiveForm = spence.toExtensiveForm :=
  spence.toExtensiveGame_toExtensiveForm

/-! ## Chunk 4b — Assessment embedding (`Bridge/Assessment.lean`)

The receiver-history / info-set maps are injective (distinct types give distinct histories),
the embedded belief reads back the signaling belief, and the reach / info-set probabilities compute
as the canonical Bayes quantities. We anchor the reach probabilities on the Spence separating
assessment (uniform prior `1/2`). -/

/-- `receiverHist_injective`: Distinct types yield distinct receiver histories `[type θ, msg m]`. -/
theorem spence_receiverHist_injective (m : spence.Msg) :
    Function.Injective (spence.receiverHist m) :=
  spence.receiverHist_injective m

/-- `receiverInfoSet_injective`: Distinct types index distinct receiver info-set elements at a
fixed message. -/
theorem spence_receiverInfoSet_injective (m : spence.Msg) :
    Function.Injective (spence.receiverInfoSet m) :=
  spence.receiverInfoSet_injective m

/-- `receiverBelief_canonical`: The embedded receiver belief at the info-set element for type `θ`
reads back the signaling belief mass `(a.belief m).pmf θ` — the embedding does not distort
beliefs. -/
theorem spence_receiverBelief_canonical (m : spence.Msg) (θ : spence.Theta) :
    spence.receiverBelief spenceSeparating m (spence.receiverInfoSet m θ) =
      (spenceSeparating.belief m).pmf θ :=
  spence.receiverBelief_canonical spenceSeparating m θ

/-- **`reachProb_type`, anchored.** The high type reaches its decision node `[type high]` with
probability `1/2` — the uniform prior mass on the high type. -/
theorem spence_reachProb_type_high :
    reachProb spence.toExtensiveForm (SignalingGame.SignalingAssessment.toBehavioral spence
        spenceSeparating) [SignalingGame.Event.type high] = 1 / 2 := by
  rw [spence.reachProb_type spenceSeparating high]
  rw [show spence.prior.pmf high = (Fintype.card (Fin 2) : ℝ)⁻¹ from rfl]
  norm_num [Fintype.card_fin]

/-- **`reachProb_typeMsg`, on-path anchor.** The high type reaches `[type high, msg degree]` with
probability `1/2 · 1 = 1/2`: Prior mass `1/2` times the (point-mass) sender probability of sending
`degree`. -/
theorem spence_reachProb_typeMsg_high_degree :
    reachProb spence.toExtensiveForm (SignalingGame.SignalingAssessment.toBehavioral spence
        spenceSeparating) [SignalingGame.Event.type high, SignalingGame.Event.msg degree] =
      1 / 2 := by
  rw [spence.reachProb_typeMsg spenceSeparating high degree]
  rw [show spence.prior.pmf high = (Fintype.card (Fin 2) : ℝ)⁻¹ from rfl,
    show (spenceSeparating.senderStrategy high).pmf degree = 1 from FinDist.pure_apply_self degree]
  norm_num [Fintype.card_fin]

/-- **`reachProb_typeMsg`, off-path anchor.** The high type reaches `[type high, msg noDegree]`
with probability `1/2 · 0 = 0`: The high type never sends `noDegree` under the separating strategy.
This is the discriminating direction — a reach computation that forgot the sender mixture would
report `1/2` here. -/
theorem spence_reachProb_typeMsg_high_noDegree :
    reachProb spence.toExtensiveForm
        (SignalingGame.SignalingAssessment.toBehavioral spence spenceSeparating)
        [SignalingGame.Event.type high, SignalingGame.Event.msg noDegree] = 0 := by
  rw [spence.reachProb_typeMsg spenceSeparating high noDegree,
    show (spenceSeparating.senderStrategy high).pmf noDegree = 0 from
      FinDist.pure_apply_ne (by decide : (high : Fin 2) ≠ noDegree)]
  ring

/-- `infoSetProb_sender`: The probability of reaching the sender's info set at `θ` is the prior
mass on `θ` — for the high type, `1/2`. -/
theorem spence_infoSetProb_sender_high :
    infoSetProb spence.toExtensiveForm
        (SignalingGame.SignalingAssessment.toBehavioral spence spenceSeparating)
        (SignalingGame.SignalingAssessment.toBeliefSystem spence spenceSeparating)
        SignalingPlayer.sender high = 1 / 2 := by
  rw [spence.infoSetProb_sender spenceSeparating high,
    show spence.prior.pmf high = (Fintype.card (Fin 2) : ℝ)⁻¹ from rfl]
  norm_num [Fintype.card_fin]

/-- **The message marginal at `degree` is `1/2`.** Under the separating strategy `degree` is sent
only by the high type (prior `1/2`), so its marginal is `1/2 · 1 + 1/2 · 0 = 1/2`. This is the
numeric anchor the receiver info-set probability reduces to. -/
theorem spence_marginalProb_degree :
    spence.marginalProb spenceSeparating.senderStrategy degree = 1 / 2 := by
  change spence.marginalProb spenceSenderStrategy degree = 1 / 2
  unfold SignalingGame.marginalProb
  rw [Fin.sum_univ_two]
  rw [show spencePrior.pmf 0 = (Fintype.card (Fin 2) : ℝ)⁻¹ from rfl,
      show spencePrior.pmf 1 = (Fintype.card (Fin 2) : ℝ)⁻¹ from rfl]
  rw [show (spenceSenderStrategy 0).pmf degree = 0 from
        FinDist.pure_apply_ne (by decide : (0 : Fin 2) ≠ degree),
      show (spenceSenderStrategy 1).pmf degree = 1 from
        FinDist.pure_apply_self degree]
  norm_num [Fintype.card_fin]

/-- **`infoSetProb_receiver`, anchored at the numeric value `1/2`.** The probability of reaching the
receiver's info set at message `m` is the message marginal `marginalProb`; at `degree` (sent only by
the high type, prior `1/2`) this is exactly `1/2`. Strengthened from the bare equality to the
hand-computed number via `spence_marginalProb_degree`. -/
theorem spence_infoSetProb_receiver_degree :
    infoSetProb spence.toExtensiveForm
        (SignalingGame.SignalingAssessment.toBehavioral spence spenceSeparating)
        (SignalingGame.SignalingAssessment.toBeliefSystem spence spenceSeparating)
        SignalingPlayer.receiver degree = 1 / 2 := by
  rw [spence.infoSetProb_receiver spenceSeparating degree, spence_marginalProb_degree]

/-! ## Chunk 4c — Tremble machinery & sequential-equilibrium existence

(`Bridge/SequentialEquilibrium.lean`)

The trembles perturb the equilibrium strategies toward full support so that off-path beliefs are
pinned by Bayes in the limit. We exercise the building blocks (`trembleRate`, the
`senderWeight`/`receiverWeight` pos/sum/tendsto families, `senderTremble_posterior_tendsto`,
`hasConsistentBeliefs_*`) on the Spence game with its **full-support uniform prior**, then the
headline `exists_signalingSequentialEquilibrium`. The full-support prior is load-bearing: It is the
explicit hypothesis of every consistency lemma below (a zero-prior sender info set makes
`HasConsistentBeliefs` unsatisfiable). -/

/-- The Spence uniform prior has **full support**: Every type carries strictly positive mass `1/2`.
This is the hypothesis the whole tremble-consistency chain consumes; we establish it once. -/
theorem spence_prior_full_support : ∀ θ : spence.Theta, 0 < spence.prior.pmf θ := by
  intro θ
  rw [show spence.prior.pmf θ = (Fintype.card (Fin 2) : ℝ)⁻¹ from rfl]
  norm_num [Fintype.card_fin]

/-- `trembleRate_pos`: The tremble rate `1/(n+1)` is strictly positive at every stage. -/
theorem spence_trembleRate_pos (n : ℕ) : 0 < SignalingGame.trembleRate n :=
  SignalingGame.trembleRate_pos n

/-- `trembleRate_tendsto`: The tremble rate vanishes in the limit, so the perturbed strategies
converge to the un-trembled equilibrium. -/
theorem spence_trembleRate_tendsto :
    Filter.Tendsto SignalingGame.trembleRate Filter.atTop (nhds 0) :=
  SignalingGame.trembleRate_tendsto

/-- `senderWeight_pos`: Each trembled sender weight is strictly positive — the perturbation gives
every message positive probability (the defining property of a tremble). -/
theorem spence_senderWeight_pos (n : ℕ) (θ : spence.Theta) (m : spence.Msg) :
    0 < spence.senderWeight spenceSeparating n θ m :=
  spence.senderWeight_pos spenceSeparating n θ m

/-- `senderWeight_sum_pos`: The trembled sender weights sum to something positive (so the
normalization `senderTremble` is well-defined). -/
theorem spence_senderWeight_sum_pos (n : ℕ) (θ : spence.Theta) :
    0 < ∑ m : spence.Msg, spence.senderWeight spenceSeparating n θ m :=
  spence.senderWeight_sum_pos spenceSeparating n θ

/-- `senderWeight_tendsto`: Each trembled sender weight converges to the equilibrium sender
probability — the tremble vanishes. -/
theorem spence_senderWeight_tendsto (θ : spence.Theta) (m : spence.Msg) :
    Filter.Tendsto (fun n => spence.senderWeight spenceSeparating n θ m) Filter.atTop
      (nhds ((spenceSeparating.senderStrategy θ).pmf m)) :=
  spence.senderWeight_tendsto spenceSeparating θ m

/-- `senderTremble_pos`: The normalized sender tremble assigns every message positive
probability. -/
theorem spence_senderTremble_pos (n : ℕ) (θ : spence.Theta) (m : spence.Msg) :
    0 < (spence.senderTremble spenceSeparating n θ).pmf m :=
  spence.senderTremble_pos spenceSeparating n θ m

/-- `senderTremble_tendsto`: The normalized sender tremble converges to the equilibrium sender
strategy. -/
theorem spence_senderTremble_tendsto (θ : spence.Theta) (m : spence.Msg) :
    Filter.Tendsto (fun n => (spence.senderTremble spenceSeparating n θ).pmf m) Filter.atTop
      (nhds ((spenceSeparating.senderStrategy θ).pmf m)) :=
  spence.senderTremble_tendsto spenceSeparating θ m

/-- **`senderTremble_posterior_tendsto`, the consistency engine (on-path case).** Under the
full-support prior, the posteriors induced by the *trembled* sender strategy converge to the
equilibrium beliefs `(a.belief m).pmf θ`. This is the Kreps–Wilson consistency limit, and the place
the full-support hypothesis is consumed. *Caveat:* on the Spence **separating** assessment *every*
message is on-path — `noDegree` is sent by the low type and `degree` by the high type, each with
marginal `1/2` — so this Spence witness never exercises the *off-path* (zero-marginal) branch of the
lemma. That branch is exercised by the BeerQuiche pooling witness
`beerQuiche_pooling_offpath_posterior_tendsto` below, where `beer` has marginal `0`. -/
theorem spence_senderTremble_posterior_tendsto (m : spence.Msg) (θ : spence.Theta) :
    Filter.Tendsto
      (fun n => (spence.posterior (spence.senderTrembleStrat spenceSeparating n) m).pmf θ)
      Filter.atTop (nhds ((spenceSeparating.belief m).pmf θ)) :=
  spence.senderTremble_posterior_tendsto spenceSeparating spence_prior_full_support
    spence_separating_isSignalingPBE.1 m θ

/-! ### Off-path consistency witness: BeerQuiche all-quiche pooling

The Spence separating assessment has no off-path message, so to exercise the zero-marginal branch of
`senderTremble_posterior_tendsto` we anchor on the **all-quiche pooling** BeerQuiche assessment,
under which `beer` is genuinely off-path (marginal `0`). The off-path belief there is the point mass
`pure weak`, and the trembled-posterior limit converges to it — the substantive off-path content. -/

/-- **BeerQuiche pooling prior has full support** (`1/10, 9/10`). The hypothesis consumed by the
off-path consistency limit. -/
theorem beerQuiche_pooling_prior_full_support :
    ∀ θ : beerQuiche.Theta, 0 < beerQuiche.prior.pmf θ := by
  intro θ
  have hval : beerQuiche.prior.pmf θ = if θ = weak then (1 : ℝ) / 10 else 9 / 10 := rfl
  rw [hval]; split_ifs <;> norm_num

/-- **`beer` is off-path under pooling: marginal `0`.** Both types order quiche, so the message
marginal at `beer` is exactly `0` — the genuinely off-path, zero-marginal case that the Spence
separating witness cannot reach. -/
theorem beerQuiche_pooling_marginal_beer_zero :
    beerQuiche.marginalProb beerQuichePoolingSender beer = 0 := by
  unfold SignalingGame.marginalProb
  apply Finset.sum_eq_zero
  intro θ _
  rw [show (beerQuichePoolingSender θ).pmf beer = 0 from
    FinDist.pure_apply_ne (show (quiche : Fin 2) ≠ beer by decide)]
  ring

/-- **Off-path belief at `beer` is `pure weak`: mass `1` on `weak`.** The pooling assessment assigns
the off-path message `beer` the belief `pure weak`. -/
theorem beerQuiche_pooling_belief_beer_weak :
    (beerQuichePooling.belief beer).pmf weak = 1 := by
  have hne : (beer : Fin 2) ≠ quiche := by decide
  change (if beer = quiche then beerQuichePrior else FinDist.pure weak).pmf weak = 1
  rw [if_neg hne, FinDist.pmf_eq_coe]
  exact FinDist.pure_apply_self weak

/-- **Off-path belief at `beer` is `pure weak`: mass `0` on `strong`.** -/
theorem beerQuiche_pooling_belief_beer_strong :
    (beerQuichePooling.belief beer).pmf strong = 0 := by
  have hne : (beer : Fin 2) ≠ quiche := by decide
  change (if beer = quiche then beerQuichePrior else FinDist.pure weak).pmf strong = 0
  rw [if_neg hne, FinDist.pmf_eq_coe]
  exact FinDist.pure_apply_ne (by decide : (weak : Fin 2) ≠ strong)

/-- **`senderTremble_posterior_tendsto`, the *off-path* branch.** At the off-path message `beer`
(marginal `0`, `beerQuiche_pooling_marginal_beer_zero`), the trembled-sender posteriors still
converge to the equilibrium off-path belief `(beerQuichePooling.belief beer).pmf θ` — which is the
point mass `pure weak` (`beerQuiche_pooling_belief_beer_weak/_strong`). This exercises the
zero-marginal branch of the consistency engine that the Spence separating witness cannot reach. -/
theorem beerQuiche_pooling_offpath_posterior_tendsto (θ : beerQuiche.Theta) :
    Filter.Tendsto
      (fun n =>
        (beerQuiche.posterior (beerQuiche.senderTrembleStrat beerQuichePooling n) beer).pmf θ)
      Filter.atTop (nhds ((beerQuichePooling.belief beer).pmf θ)) :=
  beerQuiche.senderTremble_posterior_tendsto beerQuichePooling
    beerQuiche_pooling_prior_full_support beerQuichePooling_isSignalingPBE.1 beer θ

/-- `receiverWeight_pos`: Each trembled receiver weight is strictly positive. -/
theorem spence_receiverWeight_pos (n : ℕ) (m : spence.Msg) (act : spence.Act) :
    0 < spence.receiverWeight spenceSeparating n m act :=
  spence.receiverWeight_pos spenceSeparating n m act

/-- `receiverWeight_sum_pos`: The trembled receiver weights sum to something positive. -/
theorem spence_receiverWeight_sum_pos (n : ℕ) (m : spence.Msg) :
    0 < ∑ act : spence.Act, spence.receiverWeight spenceSeparating n m act :=
  spence.receiverWeight_sum_pos spenceSeparating n m

/-- `receiverWeight_tendsto`: Each trembled receiver weight converges to the equilibrium receiver
probability. -/
theorem spence_receiverWeight_tendsto (m : spence.Msg) (act : spence.Act) :
    Filter.Tendsto (fun n => spence.receiverWeight spenceSeparating n m act) Filter.atTop
      (nhds ((spenceSeparating.receiverStrategy m).pmf act)) :=
  spence.receiverWeight_tendsto spenceSeparating m act

/-- `receiverTremble_pos`: The normalized receiver tremble assigns every action positive
probability. -/
theorem spence_receiverTremble_pos (n : ℕ) (m : spence.Msg) (act : spence.Act) :
    0 < (spence.receiverTremble spenceSeparating n m).pmf act :=
  spence.receiverTremble_pos spenceSeparating n m act

/-- **`hasConsistentBeliefs_toAssessment_of_senderTremble`.** Fed a full-support sender-tremble
sequence converging to the equilibrium (here the canonical `senderTrembleStrat`) whose posteriors
converge to the equilibrium beliefs, the embedded assessment is Kreps–Wilson belief-consistent.
This is the general tremble-to-consistency map; we instantiate it on the canonical Spence
tremble. -/
theorem spence_hasConsistentBeliefs_of_senderTremble :
    HasConsistentBeliefs spence.toExtensiveForm
      (SignalingGame.SignalingAssessment.toAssessment spence spenceSeparating) :=
  spence.hasConsistentBeliefs_toAssessment_of_senderTremble spenceSeparating
    spence_prior_full_support (spence.senderTrembleStrat spenceSeparating)
    (fun n θ m => spence.senderTremble_pos spenceSeparating n θ m)
    (fun θ m => spence.senderTremble_tendsto spenceSeparating θ m)
    (fun m θ => spence.senderTremble_posterior_tendsto spenceSeparating spence_prior_full_support
      spence_separating_isSignalingPBE.1 m θ)

/-- **`hasConsistentBeliefs_of_signalingBayesConsistent`** (Fudenberg–Tirole consistency half): On
the full-support Spence game, the Bayes-consistent separating beliefs embed as Kreps–Wilson
consistent beliefs — the tremble limit agrees with the PBE beliefs. -/
theorem spence_hasConsistentBeliefs_of_bayesConsistent :
    HasConsistentBeliefs spence.toExtensiveForm
      (SignalingGame.SignalingAssessment.toAssessment spence spenceSeparating) :=
  spence.hasConsistentBeliefs_of_signalingBayesConsistent spenceSeparating
    spence_prior_full_support spence_separating_isSignalingPBE.1

/-- `isSignalingSequentialEquilibrium_of_isSignalingPBE`: On the full-support Spence game, the
genuine separating PBE is a sequential equilibrium. The bridge from PBE to SE that the existence
endpoint routes through. -/
theorem spence_separating_isSignalingSequentialEquilibrium :
    spence.IsSignalingSequentialEquilibrium spenceSeparating :=
  spence.isSignalingSequentialEquilibrium_of_isSignalingPBE spenceSeparating
    spence_prior_full_support spence_separating_isSignalingPBE

/-- **The headline: `exists_signalingSequentialEquilibrium`.** The full-support Spence game admits
a sequential equilibrium. The `hfull` hypothesis is mandatory — supplied here by
`spence_prior_full_support` — because signaling sequential-equilibrium existence requires a
full-support prior. This calls the *abstract* existence theorem (so the witness it selects is
unspecified); the *concrete* non-vacuity is `spence_separating_witnesses_existence` below, which
binds the existential to the genuine separating equilibrium `spenceSeparating`. -/
theorem spence_exists_signalingSequentialEquilibrium :
    ∃ a : spence.SignalingAssessment, spence.IsSignalingSequentialEquilibrium a :=
  spence.exists_signalingSequentialEquilibrium spence_prior_full_support

/-- **Concrete existence witness.** The genuine separating equilibrium `spenceSeparating` *is* a
sequential equilibrium of the Spence game — binding the existential of
`spence_exists_signalingSequentialEquilibrium` to a named, hand-verified assessment rather than the
abstract existence theorem's unspecified selection. -/
theorem spence_separating_witnesses_existence :
    ∃ a : spence.SignalingAssessment, spence.IsSignalingSequentialEquilibrium a :=
  ⟨spenceSeparating, spence_separating_isSignalingSequentialEquilibrium⟩

/-- The same existence endpoint on the **BeerQuiche** game (prior `(1/10, 9/10)`, also full
support) — a second full-support carrier, confirming the existence theorem is not specific to a
uniform prior. -/
theorem beerQuiche_exists_signalingSequentialEquilibrium :
    ∃ a : beerQuiche.SignalingAssessment, beerQuiche.IsSignalingSequentialEquilibrium a := by
  refine beerQuiche.exists_signalingSequentialEquilibrium (fun θ => ?_)
  have hval : beerQuiche.prior.pmf θ = if θ = weak then (1 : ℝ) / 10 else 9 / 10 := rfl
  rw [hval]; split_ifs <;> norm_num

/-! ## Chunk 4d — The trembling-hand sequence (`Bridge/Existence.lean`)

The `ε`-sequence `epsSeq n = 1/(|Msg|·(n+2))` drives the perturbation toward zero while staying
below the uniform floor `1/|Msg|`; the joint state space is compact (a finite product of
simplices), so a convergent subsequence exists. These are the scaffolding of `exists_signalingPBE`.
We exercise them on the Spence game (`|Msg| = 2`). -/

/-- `epsSeq_pos`: The perturbation level is strictly positive at every stage. -/
theorem spence_epsSeq_pos (n : ℕ) : 0 < spence.epsSeq n :=
  spence.epsSeq_pos n

/-- `epsSeq_le`: The perturbation level stays at or below the uniform floor `1/|Msg|` — exactly the
bound `nonempty_PerturbedSimplex_of_le_inv` needs for the perturbed slice to be inhabited. -/
theorem spence_epsSeq_le (n : ℕ) :
    spence.epsSeq n ≤ 1 / (Fintype.card spence.Msg : ℝ) :=
  spence.epsSeq_le n

/-- `epsSeq_tendsto`: The perturbation vanishes in the limit, so the perturbed equilibria converge
to an un-perturbed one. -/
theorem spence_epsSeq_tendsto :
    Filter.Tendsto spence.epsSeq Filter.atTop (nhds 0) :=
  spence.epsSeq_tendsto

/-- `exists_perturbed_seq`: At each perturbation level `epsSeq n` the perturbed Kakutani data
admits an equilibrium, packaged as a single sequence. This is the per-step fixed-point input the
limiting argument consumes; it is non-vacuous (the perturbed slices are inhabited and
compact-convex). -/
theorem spence_exists_perturbed_seq :
    ∃ σ : ∀ n : ℕ, (d : spence.SignalingDeviator) → ↑(spence.deviatorSlice (spence.epsSeq n) d),
      ∀ n : ℕ, (spence.toPerturbedNashExistenceData (spence.epsSeq n)
        (spence.epsSeq_nn n) (spence.epsSeq_le n)).toEquilibriumProblem.IsEquilibrium (σ n) :=
  spence.exists_perturbed_seq

/-- `jointState_compact`: The joint state space (sender simplices × receiver simplices × belief
systems) is compact, so the perturbed-equilibrium sequence has a convergent subsequence — the
existence proof's compactness input. -/
theorem spence_jointState_compact :
    IsCompact (Set.univ : Set (SignalingGame.JointState spence)) :=
  spence.jointState_compact

/-- `exists_signalingPBE`: The endpoint of the perturbation argument — every signaling game (no
full-support hypothesis needed for PBE) admits a perfect Bayesian equilibrium. This calls the
*abstract* existence theorem; the concrete witness binding is `spence_separating_witnesses_PBE`. -/
theorem spence_exists_signalingPBE :
    ∃ a : spence.SignalingAssessment, spence.IsSignalingPBE a :=
  spence.exists_signalingPBE

/-- **Concrete PBE existence witness.** The separating assessment `spenceSeparating` *is* a perfect
Bayesian equilibrium — binding the existential of `spence_exists_signalingPBE` to the named,
hand-verified separating PBE rather than the abstract existence theorem's unspecified selection. -/
theorem spence_separating_witnesses_PBE :
    ∃ a : spence.SignalingAssessment, spence.IsSignalingPBE a :=
  ⟨spenceSeparating, spence_separating_isSignalingPBE⟩

/-- **Consumer of `Bridge/StrategicBNE.lean`.** The separating signaling PBE `spenceSeparating`
induces a pure Bayesian Nash equilibrium of the agent-normal-form game `spence.toFinBayesianGame`
(every PBE is a BNE), via `isBNE_of_isSignalingPBE_of_pure`. The sender/receiver pure strategies are
the diagonal maps (type `θ ↦ message θ`, message `m ↦ action m`), matching the separating PBE's
Dirac strategies. This binds the strategic-form bridge to a concrete, hand-verified PBE. -/
theorem spence_separating_isBNE :
    spence.toFinBayesianGame.IsBNE (spence.toBayesianPureStrategy (fun θ => θ) (fun m => m)) :=
  spence.isBNE_of_isSignalingPBE_of_pure (fun θ => θ) (fun m => m) spenceSeparating rfl rfl
    spence_separating_isSignalingPBE

/-! ## Chunk 4e — The perturbed simplex (`Perturbation.lean`)

`PerturbedSimplex ε` is the standard simplex with every coordinate at least `ε`; it is convex,
compact, and (for `ε ≤ 1/|α|`) nonempty. The raw marginal / posterior maps are continuous and
bounded below on it. These are the geometric inputs to the per-step Kakutani fixed point. We anchor
the simplex facts on `Fin 2` with `ε = 1/2` (the uniform-floor boundary case, where nonemptiness is
tightest), and the continuity facts on the Spence game. -/

/-- `convex_PerturbedSimplex`: The `ε`-perturbed simplex is convex (a Kakutani-domain
precondition). -/
theorem perturbedSimplex_convex :
    Convex ℝ (PerturbedSimplex (α := Fin 2) (1 / 2)) :=
  convex_PerturbedSimplex (1 / 2)

/-- `isCompact_PerturbedSimplex`: The `ε`-perturbed simplex is compact. -/
theorem perturbedSimplex_isCompact :
    IsCompact (PerturbedSimplex (α := Fin 2) (1 / 2)) :=
  isCompact_PerturbedSimplex (1 / 2)

/-- **`nonempty_PerturbedSimplex_of_le_inv`, the boundary case.** At `ε = 1/2 = 1/|Fin 2|` the
perturbed simplex is *just* nonempty. The tightness claims advertised here — that the uniform
distribution is its *only* point, and that any larger `ε` empties the slice — are proved
separately as `perturbedSimplex_eq_half_of_mem` and `perturbedSimplex_empty_of_gt_half`. -/
theorem perturbedSimplex_nonempty :
    (PerturbedSimplex (α := Fin 2) (1 / 2)).Nonempty := by
  refine nonempty_PerturbedSimplex_of_le_inv (by norm_num) ?_
  rw [Fintype.card_fin]; norm_num

/-- **Uniqueness at the boundary `ε = 1/2`.** Any point of `PerturbedSimplex (1/2)` over `Fin 2` is
the uniform distribution `(1/2, 1/2)`: each coordinate is `≥ 1/2` and they sum to `1`, forcing both
to equal `1/2`. This is the tightness claim — the boundary slice is the single uniform point. -/
theorem perturbedSimplex_eq_half_of_mem {x : Fin 2 → ℝ}
    (hx : x ∈ PerturbedSimplex (α := Fin 2) (1 / 2)) :
    x = fun _ => 1 / 2 := by
  obtain ⟨hsum, hlb⟩ := hx
  have h0 := hlb 0
  have h1 := hlb 1
  have hs : x 0 + x 1 = 1 := by
    have := hsum.2; rwa [Fin.sum_univ_two] at this
  funext a
  fin_cases a
  · change x 0 = 1 / 2; linarith
  · change x 1 = 1 / 2; linarith

/-- **Emptiness above the boundary: `ε > 1/2 ⇒ slice empty`.** Over `Fin 2`, two coordinates each
`≥ ε > 1/2` sum to `> 1`, contradicting the simplex constraint — so any `ε` strictly above the
uniform floor empties the perturbed simplex and would make the Kakutani domain vacuous. This
certifies the inhabitation bound `ε ≤ 1/|α|` is tight. -/
theorem perturbedSimplex_empty_of_gt_half {ε : ℝ} (hε : 1 / 2 < ε) :
    PerturbedSimplex (α := Fin 2) ε = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hsum, hlb⟩
  have h0 := hlb 0
  have h1 := hlb 1
  have hs : x 0 + x 1 = 1 := by
    have := hsum.2; rwa [Fin.sum_univ_two] at this
  linarith

/-- `marginalProbRaw_continuous`: The raw message marginal is a continuous function of the raw
sender profile — the continuity input for upper-hemicontinuity of the perturbed best-response
map. -/
theorem spence_marginalProbRaw_continuous (m : spence.Msg) :
    Continuous fun f : spence.Theta → spence.Msg → ℝ => spence.marginalProbRaw f m :=
  spence.marginalProbRaw_continuous m

/-- **`marginalProbRaw_ge_eps_of_perturbed`, the off-path floor (`≥ ε`).** On the perturbed simplex
every raw marginal is at least `ε`. -/
theorem spence_marginalProbRaw_ge_eps_of_perturbed {ε : ℝ} (hε : 0 ≤ ε)
    (f : spence.Theta → spence.Msg → ℝ)
    (hf : ∀ θ, f θ ∈ PerturbedSimplex ε) (m : spence.Msg) :
    ε ≤ spence.marginalProbRaw f m :=
  spence.marginalProbRaw_ge_eps_of_perturbed hε f hf m

/-- **Strict off-path floor: `0 < ε ⇒ 0 < marginalProbRaw`.** When the perturbation level is
*strictly* positive, every raw marginal is strictly positive — so *every* message (including
off-path ones) is genuinely on-path during the perturbation, forcing posteriors by Bayes everywhere.
This is the load-bearing strict positivity (the bare `≥ ε` version degenerates to nonnegativity at
`ε = 0`). -/
theorem spence_marginalProbRaw_pos_of_perturbed {ε : ℝ} (hε : 0 < ε)
    (f : spence.Theta → spence.Msg → ℝ)
    (hf : ∀ θ, f θ ∈ PerturbedSimplex ε) (m : spence.Msg) :
    0 < spence.marginalProbRaw f m :=
  lt_of_lt_of_le hε (spence.marginalProbRaw_ge_eps_of_perturbed hε.le f hf m)

/-- `posteriorNumerator_continuous`: The raw posterior numerator (prior × likelihood) is continuous
in the raw sender profile — the other half of the Bayes-map continuity. -/
theorem spence_posteriorNumerator_continuous (m : spence.Msg) (a : spence.Act) :
    Continuous fun f : spence.Theta → spence.Msg → ℝ => spence.posteriorNumerator f m a :=
  spence.posteriorNumerator_continuous m a

/-- `profileSenderRaw_continuous_eval`: Each coordinate of the raw sender profile extracted from a
perturbed deviation profile is continuous — so the Kakutani fixed-point map is continuous. -/
theorem spence_profileSenderRaw_continuous_eval (ε : ℝ) (θ : spence.Theta) (m : spence.Msg) :
    Continuous fun σ : (d : spence.SignalingDeviator) → ↑(spence.deviatorSlice ε d) =>
      spence.profileSenderRaw ε σ θ m :=
  spence.profileSenderRaw_continuous_eval ε θ m

/-- `profileReceiverRaw_continuous_eval`: Each coordinate of the raw receiver profile is likewise
continuous in the perturbed deviation profile. -/
theorem spence_profileReceiverRaw_continuous_eval (ε : ℝ) (m : spence.Msg) (a : spence.Act) :
    Continuous fun σ : (d : spence.SignalingDeviator) → ↑(spence.deviatorSlice ε d) =>
      spence.profileReceiverRaw ε σ m a :=
  spence.profileReceiverRaw_continuous_eval ε m a

/-- The deviator-ambient carrier of each signaling deviator is a finite-dimensional normed space —
the ambient in which the perturbed simplices live and the Kakutani fixed point is taken. We
exercise the synthesized instances directly (sender deviator slot). -/
theorem spence_deviatorAmbient_instances :
    Nonempty (NormedAddCommGroup (spence.deviatorAmbient (.sender high))) ∧
      Nonempty (FiniteDimensional ℝ (spence.deviatorAmbient (.sender high))) :=
  ⟨⟨spence.instNAGDeviatorAmbient (.sender high)⟩,
    ⟨spence.instFDDeviatorAmbient (.sender high)⟩⟩

end EconlibTest.GameTheory.SignalingBridge

end
