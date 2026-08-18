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
# Signaling Primitives, PBE, and the Intuitive Criterion — Non-Vacuity Checks

Compile-time semantic witnesses for the `Econlib.GameTheory.Signaling` substrate (`Basic.lean`,
`PBE.lean`, `Pooling.lean`, `Separating.lean`, `IntuitiveCriterion.lean`). Most of these
declarations are unconditional algebra lemmas (`marginalProb_eq_sum`, `posterior_apply`,
`receiverPosteriorPayoff_eq_expect`, …): A direction-reversed Bayes rule, a sender/receiver payoff
swap, or a vacuously satisfied domination test would survive the abstract proofs unnoticed. We
anchor on the two canonical worked games from `EconlibExamples` — `spence` (separating) and
`beerQuiche` (pooling + intuitive criterion) — plus one purpose-built **asymmetric-prior** game
`pbGame` that pins the Bayes arithmetic on a non-uniform prior `(2/3, 1/3)`, where a posterior /
prior swap actually changes the numbers.

## The games

* **`pbGame`** — a two-type, two-message, two-action game with the *asymmetric* prior `(2/3, 1/3)`.
  It carries no payoff content (every payoff is `0`); its only purpose is to anchor the Bayes
  primitives:

  * *pooling strategy* (both types send `m = 0`) ⇒ marginal `1`, posterior `= prior` `(2/3,1/3)`;
  * *separating strategy* (type `t` sends `m = t`) ⇒ posterior at `m = 0` is the **point mass on
    type `0`** (`(2/3·1)/(2/3) = 1`), not the prior. The asymmetric split is what makes the
    point-mass collapse visible: A prior/posterior swap here would read `2/3`, not `1`.
* **`spence`** (`EconlibExamples`) — Spence (1973) job-market signaling; the low type sends
  `noDegree`, the high type `degree`, the firm matches the wage. The separating PBE we reuse.
* **`beerQuiche`** (`EconlibExamples`) — Cho-Kreps (1987); both types pool on quiche, sustained by
  the unreasonable off-path belief `μ(weak | beer) = 1`. The intuitive-criterion failure we reuse.

## Failure modes caught

* **posterior / prior swap** — `pbGame_posterior_pooling_eq_prior` keeps the pooled posterior at
  the asymmetric prior `(2/3,1/3)`; `pbGame_posterior_separating_is_point_mass` collapses the
  separating posterior to a point mass `1`. The two numbers differ, so a swapped Bayes rule is
  caught.
* **sender / receiver payoff-direction flip** — `pbGame`'s expected-payoff witnesses are *all-zero*
  (it carries no payoff content) and so only sanity-check that the unfolding routes the right
  player's table; the *direction* of the receiver optimization is pinned by the genuine negative
  best-response checks on the worked games: Spence's `spence_highWage_not_bestResponse_to_pure_low`
  (`highWage` loses `4`) and BeerQuiche's `beerQuiche_notFight_not_bestResponse_to_pure_weak`
  (`notFight` pays `0 < 1`).
* **vacuous domination / best-response** — the reused intuitive-criterion witnesses show the
  dominated set is *nonempty* (the weak type *is* eliminated at beer) and that the guard
  `intuitive_criterion_vacuous` does **not** fire on the live equilibrium.
-/

noncomputable section

namespace EconlibTest.GameTheory.SignalingCore

open Econlib.GameTheory Econlib.Probability
open scoped BigOperators

/-! ## The asymmetric-prior anchor game `pbGame`

`pbGame` exists only to exercise the Bayes primitives on a *non-uniform* prior, where a
prior/posterior confusion changes the arithmetic. Types, messages, and actions are all `Fin 2`;
every payoff is `0` (no equilibrium content is intended here). -/

/-- The asymmetric prior `(2/3, 1/3)` over `Fin 2`: Type `0` gets `2/3`, type `1` gets `1/3`. The
non-uniform split is the whole point — it makes the point-mass collapse of a separating posterior
numerically distinct from the prior. -/
def pbPrior : FinDist (Fin 2) :=
  ⟨fun θ => if θ = 0 then (2 : ℝ) / 3 else 1 / 3,
    fun θ => by dsimp only; split_ifs <;> norm_num,
    by
      change ∑ θ, (if θ = 0 then (2 : ℝ) / 3 else 1 / 3) = 1
      rw [Fin.sum_univ_two]; norm_num⟩

/-- The anchor game: Two types, two messages, two actions, asymmetric prior, all payoffs `0`. -/
abbrev pbGame : SignalingGame :=
  SignalingGame.mkFin 2 2 2 pbPrior fun _ _ _ _ => 0

/-! ### `mkFin` field projections (Chunk 1)

The `mkFin_*` simp lemmas reduce the abstract carriers to `Fin 2` and read back the prior /
payoff exactly as supplied. *Caveat:* since `pbGame` uses `Fin 2` for all three carriers
(`Theta = Msg = Act = Fin 2`), the carrier-projection witnesses below cannot detect a *reshuffle*
of the carrier *arguments* (which would be invisible at equal cardinalities); they check that the
constructor preserves each carrier and the supplied prior/payoff. The load-bearing anchors here are
the asymmetric-prior Bayes computations, where a prior/posterior confusion *does* change the
numbers. -/

/-- `mkFin_Theta`: The sender's type carrier reduces to `Fin 2`. -/
theorem pbGame_Theta_eq : pbGame.Theta = Fin 2 := SignalingGame.mkFin_Theta 2 2 2 _ _

/-- `mkFin_Msg`: The message carrier reduces to `Fin 2`. -/
theorem pbGame_Msg_eq : pbGame.Msg = Fin 2 := SignalingGame.mkFin_Msg 2 2 2 _ _

/-- `mkFin_Act`: The action carrier reduces to `Fin 2`. -/
theorem pbGame_Act_eq : pbGame.Act = Fin 2 := SignalingGame.mkFin_Act 2 2 2 _ _

/-- `mkFin_prior`: The prior is read back exactly as supplied (the asymmetric `(2/3,1/3)`), not
substituted by a default uniform. -/
theorem pbGame_prior_eq : pbGame.prior = pbPrior := SignalingGame.mkFin_prior 2 2 2 _ _

/-- `mkFin_payoff`: The payoff table is read back exactly as supplied. -/
theorem pbGame_payoff_eq : pbGame.payoff = (fun _ _ _ _ => (0 : ℝ)) :=
  SignalingGame.mkFin_payoff 2 2 2 _ _

/-- The two prior masses, in usable form: `2/3` on type `0`, `1/3` on type `1`. -/
private theorem pbPrior_val (θ : Fin 2) :
    pbPrior.pmf θ = if θ = 0 then (2 : ℝ) / 3 else 1 / 3 := rfl

/-- `BayesianAction` synthesis: The receiver's strategic-form action carrier (`Msg → Act`) admits a
`Fintype` instance — i.e. the agent-normal-form representation is finite. Exercising the instance
directly catches a missing-`Fintype` regression that would otherwise surface only deep inside the
strategic-form bridge. (This checks *instance existence*, not the carrier's cardinality; with
`Msg = Act = Fin 2`, `card (Msg → Act) = 4` but a distinct-cardinality game would be needed to
distinguish `Msg → Act` from `Act` by cardinality alone.) -/
theorem pbGame_bayesianAction_receiver_fintype :
    Nonempty (Fintype (pbGame.BayesianAction .receiver)) :=
  ⟨pbGame.instFintypeBayesianAction .receiver⟩

/-- `BayesianAction` `DecidableEq` synthesis on the receiver's response-function carrier. -/
theorem pbGame_bayesianAction_receiver_decEq :
    Nonempty (DecidableEq (pbGame.BayesianAction .receiver)) :=
  ⟨pbGame.instDecEqBayesianAction .receiver⟩

/-! ### Strategic-form embedding (Chunk 1) -/

/-- The pooling sender pure strategy: Both types send message `0`. -/
private def pbPoolSender : pbGame.SenderPureStrategy := fun _ => (0 : Fin 2)

/-- A receiver pure response: Always take action `0`. -/
private def pbReceiverPure : pbGame.ReceiverPureStrategy := fun _ => (0 : Fin 2)

/-- `toBayesianPureStrategy_sender`: The sender slot of the embedded pure profile reads back the
sender strategy on the sender's type. -/
theorem pbGame_toBayesianPureStrategy_sender (θ : pbGame.Theta) :
    pbGame.toBayesianPureStrategy pbPoolSender pbReceiverPure .sender θ = pbPoolSender θ :=
  pbGame.toBayesianPureStrategy_sender pbPoolSender pbReceiverPure θ

/-- `toBayesianPureStrategy_receiver`: The receiver slot reads back the full response function
(independent of the trivial receiver type). -/
theorem pbGame_toBayesianPureStrategy_receiver (u : PUnit) :
    pbGame.toBayesianPureStrategy pbPoolSender pbReceiverPure .receiver u = pbReceiverPure :=
  pbGame.toBayesianPureStrategy_receiver pbPoolSender pbReceiverPure u

/-! ### Bayes primitives: Pooling strategy (Chunk 1)

Pooling sender strategy `θ ↦ pure 0`. Marginal at `m = 0` is `(2/3)·1 + (1/3)·1 = 1`; the
posterior there is the prior `(2/3,1/3)` — the pooled message reveals nothing. -/

/-- The pooling sender *mixed* strategy `θ ↦ pure 0`. -/
private def pbPoolMixed : pbGame.SenderMixedStrategy := fun _ => FinDist.pure (0 : Fin 2)

/-- `marginalProb_eq_sum`: The marginal of message `0` under pooling unfolds to the prior-weighted
sum, which equals `(2/3)·1 + (1/3)·1 = 1`. -/
theorem pbGame_marginalProb_pooling_zero :
    pbGame.marginalProb pbPoolMixed (0 : Fin 2) = 1 := by
  rw [pbGame.marginalProb_eq_sum]
  rw [Fin.sum_univ_two]
  rw [show pbGame.prior = pbPrior from pbGame_prior_eq]
  simp only [pbPoolMixed, FinDist.pure_apply_self, pbPrior_val]
  norm_num

/-- `marginalProb_pos`: Message `0` is on-path under pooling — the prior puts mass `2/3 > 0` on
type `0`, which sends `0` with probability `1`. The *positive-marginal* witness `posterior_apply`
needs. -/
theorem pbGame_marginalProb_pooling_pos :
    0 < pbGame.marginalProb pbPoolMixed (0 : Fin 2) := by
  refine pbGame.marginalProb_pos (θ₀ := (0 : Fin 2)) ?_ ?_
  · rw [show pbGame.prior = pbPrior from pbGame_prior_eq, pbPrior_val]; norm_num
  · simp only [pbPoolMixed]; rw [FinDist.pure_apply_self]; norm_num

/-- **Posterior under pooling equals the prior.** At the pooled message `0` the posterior assigns
`2/3` to type `0` and `1/3` to type `1` — exactly the prior. A Bayes rule that swapped prior and
posterior would read these the same way *by luck* only because pooling is informationless; the
separating witness below is the discriminating one. We compute via `posterior_apply` on the
positive marginal. -/
theorem pbGame_posterior_pooling_eq_prior (θ : Fin 2) :
    (pbGame.posterior pbPoolMixed (0 : Fin 2)).pmf θ = pbPrior.pmf θ := by
  rw [pbGame.posterior_apply pbPoolMixed (0 : Fin 2) θ pbGame_marginalProb_pooling_pos,
    pbGame_marginalProb_pooling_zero, div_one,
    show pbGame.prior = pbPrior from pbGame_prior_eq]
  simp only [pbPoolMixed, FinDist.pure_apply_self, mul_one]

/-! ### Bayes primitives: Separating strategy (Chunk 1)

Separating sender strategy `θ ↦ pure θ` (type `t` sends message `t`). Marginal at `m = 0` is
`(2/3)·1 + (1/3)·0 = 2/3`; the posterior there is the **point mass on type `0`**:
`(2/3·1)/(2/3) = 1`. -/

/-- The separating sender mixed strategy `θ ↦ pure θ`. -/
private def pbSepMixed : pbGame.SenderMixedStrategy := fun θ => FinDist.pure θ

/-- The `joint` distribution evaluated at `(0, 0)` under the separating strategy: The prior mass on
type `0` times the (unit) likelihood of sending `0`, i.e. `2/3`. Exercises `joint` directly. -/
theorem pbGame_joint_separating_zero_zero :
    (pbGame.joint pbSepMixed).pmf ((0 : Fin 2), (0 : Fin 2)) = 2 / 3 := by
  change pbGame.prior.pmf 0 * (pbSepMixed 0).pmf 0 = 2 / 3
  rw [show pbGame.prior = pbPrior from pbGame_prior_eq, pbPrior_val]
  simp only [pbSepMixed, FinDist.pure_apply_self]
  norm_num

/-- **Off-diagonal joint anchor (`(type 1, msg 0) = 1/3`), the type/message transpose guard.** Under
*pooling* (both types send `0`), the joint mass at `(θ, m) = (1, 0)` is `prior(1) · 1 = 1/3`. This
is the off-diagonal entry the diagonal `(0,0)` check cannot reach: a transpose of the type/message
coordinates of `joint` would read `prior(0) = 2/3 ≠ 1/3` here, since the asymmetric prior makes the
two coordinates numerically distinct. -/
theorem pbGame_joint_pooling_one_zero :
    (pbGame.joint pbPoolMixed).pmf ((1 : Fin 2), (0 : Fin 2)) = 1 / 3 := by
  change pbGame.prior.pmf 1 * (pbPoolMixed 1).pmf 0 = 1 / 3
  rw [show pbGame.prior = pbPrior from pbGame_prior_eq, pbPrior_val]
  simp only [pbPoolMixed, FinDist.pure_apply_self]
  norm_num

/-- `marginalProb_pos`: Message `0` is on-path under separation — type `0` (prior `2/3`) sends it
with probability `1`. -/
theorem pbGame_marginalProb_separating_pos :
    0 < pbGame.marginalProb pbSepMixed (0 : Fin 2) := by
  refine pbGame.marginalProb_pos (θ₀ := (0 : Fin 2)) ?_ ?_
  · rw [show pbGame.prior = pbPrior from pbGame_prior_eq, pbPrior_val]; norm_num
  · simp only [pbSepMixed]; rw [FinDist.pure_apply_self]; norm_num

/-- The separating marginal at `m = 0` is `2/3` (only type `0` sends `0`). -/
private theorem pbGame_marginalProb_separating_zero :
    pbGame.marginalProb pbSepMixed (0 : Fin 2) = 2 / 3 := by
  rw [pbGame.marginalProb_eq_sum, Fin.sum_univ_two,
    show pbGame.prior = pbPrior from pbGame_prior_eq]
  simp only [pbSepMixed, pbPrior_val, FinDist.pure_apply_self,
    FinDist.pure_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  norm_num

/-- **Posterior under separation is a point mass on type `0`.** `posterior_apply` at `m = 0`,
`θ = 0` gives `(2/3·1)/(2/3) = 1` — *not* the prior value `2/3`. This is the discriminating
posterior / prior swap check: The separating message identifies its sender, so the posterior
collapses to a point mass; a swap would wrongly report `2/3`. -/
theorem pbGame_posterior_separating_is_point_mass :
    (pbGame.posterior pbSepMixed (0 : Fin 2)).pmf (0 : Fin 2) = 1 := by
  rw [pbGame.posterior_apply pbSepMixed (0 : Fin 2) (0 : Fin 2)
      pbGame_marginalProb_separating_pos,
    pbGame_marginalProb_separating_zero,
    show pbGame.prior = pbPrior from pbGame_prior_eq, pbPrior_val]
  simp only [pbSepMixed, FinDist.pure_apply_self]
  norm_num

/-- The separating posterior puts zero mass on type `1` at `m = 0` — completing the point mass.
Catches a swap that would instead report `1/3` (the prior). -/
theorem pbGame_posterior_separating_zero_at_one :
    (pbGame.posterior pbSepMixed (0 : Fin 2)).pmf (1 : Fin 2) = 0 := by
  rw [pbGame.posterior_apply pbSepMixed (0 : Fin 2) (1 : Fin 2)
      pbGame_marginalProb_separating_pos]
  simp only [pbSepMixed, FinDist.pure_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero,
    zero_div]

/-! ### Expected-payoff unfoldings (Chunk 1)

`senderExpectedPayoff_eq_expect` and `receiverExpectedPayoff_eq_expect` expose the expected
payoffs as `FinDist.expect`s. On `pbGame` every payoff is `0`, so both collapse to `0` — a sanity
anchor that the unfolding routes the right player's table. -/

/-- A receiver pure mixed strategy `m ↦ pure 0` for `pbGame`. -/
private def pbReceiverMixed : pbGame.ReceiverMixedStrategy := fun _ => FinDist.pure (0 : Fin 2)

/-- `senderExpectedPayoff_eq_expect`: The sender's expected payoff unfolds to the expectation of
the sender table; on `pbGame` (all payoffs `0`) it is `0`. -/
theorem pbGame_senderExpectedPayoff_eq_zero (θ m : Fin 2) :
    pbGame.senderExpectedPayoff pbReceiverMixed θ m = 0 := by
  rw [pbGame.senderExpectedPayoff_eq_expect, FinDist.expect_eq_sum]
  simp

/-- `receiverExpectedPayoff_eq_expect`: The receiver's expected payoff unfolds to the expectation
of the *receiver* table against the belief; on `pbGame` it is `0`. -/
theorem pbGame_receiverExpectedPayoff_eq_zero
    (μ : pbGame.ReceiverBelief) (m a : Fin 2) :
    pbGame.receiverExpectedPayoff μ m a = 0 := by
  rw [pbGame.receiverExpectedPayoff_eq_expect, FinDist.expect_eq_sum]
  simp

/-! ### Ex-ante payoff functionals (Chunk 1)

`SignalingAssessment.senderExAntePayoff` / `receiverExAntePayoff` integrate the per-type
payoffs against the prior. On `pbGame` both are `0`. -/

/-- A complete `pbGame` assessment (pooling sender, constant receiver, prior beliefs). -/
private def pbAssessment : pbGame.SignalingAssessment where
  senderStrategy := pbPoolMixed
  receiverStrategy := pbReceiverMixed
  belief := fun _ => pbPrior

/-- `SignalingAssessment.senderExAntePayoff`: The ex-ante sender payoff integrates the per-type
expected payoffs against the prior; on `pbGame` it is `0`. -/
theorem pbGame_senderExAntePayoff_eq_zero :
    pbAssessment.senderExAntePayoff = 0 := by
  unfold SignalingGame.SignalingAssessment.senderExAntePayoff
  rw [FinDist.expect_eq_sum]
  have hz : ∀ θ : Fin 2, (pbAssessment.senderStrategy θ).expect
      (fun m => pbGame.senderExpectedPayoff pbAssessment.receiverStrategy θ m) = 0 := by
    intro θ
    rw [FinDist.expect_eq_sum]
    refine Finset.sum_eq_zero (fun m _ => ?_)
    rw [show pbAssessment.receiverStrategy = pbReceiverMixed from rfl,
      pbGame_senderExpectedPayoff_eq_zero, mul_zero]
  simp_rw [hz]; simp

/-- `SignalingAssessment.receiverExAntePayoff`: The ex-ante receiver payoff integrates the receiver
table along the realized `(θ, m, a)` path against the prior; on `pbGame` it is `0`. -/
theorem pbGame_receiverExAntePayoff_eq_zero :
    pbAssessment.receiverExAntePayoff = 0 := by
  unfold SignalingGame.SignalingAssessment.receiverExAntePayoff
  rw [FinDist.expect_eq_sum]
  refine Finset.sum_eq_zero (fun θ _ => ?_)
  rw [mul_eq_zero]; right
  rw [FinDist.expect_eq_sum]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  rw [mul_eq_zero]; right
  rw [FinDist.expect_eq_sum]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  simp

/-! ## Chunk 2 — PBE, pooling, separating

We reuse the two worked games from `EconlibExamples`: The Spence separating PBE and the
BeerQuiche all-quiche pooling PBE. The semantically loaded witnesses are the receiver best-response
*direction* check (`isReceiverBestResponse_pure_iff`, including a negative), the off-path-belief =
prior pooling posterior, and the point-mass separating posterior. -/

open EconlibExamples.GameTheory.SpenceSignaling
  (spence spenceSeparating spenceSenderStrategy spenceReceiverStrategy spenceBelief
   spence_separating_isSignalingPBE wage productivity educationCost spenceSenderPayoff
   spenceReceiverPayoff low high noDegree degree lowWage highWage spencePrior)

open EconlibExamples.GameTheory.BeerQuiche
  (beerQuiche beerQuichePooling beerQuichePoolingSender beerQuichePoolingReceiver
   beerQuichePrior beerQuicheSenderPayoff beerQuicheReceiverPayoff weak strong quiche beer
   notFight fight beerQuichePooling_beer_isOffPath beerQuichePooling_weak_dominated_at_beer
   beerQuichePooling_strong_not_dominated_at_beer beerQuichePooling_isSignalingPBE
   beerQuichePooling_isPooling beerQuicheBeerPooling beerQuicheBeerPooling_passes_IC
   beerQuicheBeerPooling_quiche_isOffPath beerQuicheBeerPooling_strong_dominated_at_quiche
   beerQuicheBeerPooling_weak_not_dominated_at_quiche)

/-! ### Receiver best-response direction (Chunk 2)

On Spence, the belief `pure low` at message `degree`. The receiver's payoff is
`-(wage a - 1)²`: `lowWage` pays `0`, `highWage` pays `-4`. So `lowWage` *is* a best response,
`highWage` is *not* — the negative witness that pins the optimization direction. -/

/-- `receiverPosteriorPayoff_eq_expect`: The receiver's posterior payoff unfolds to the expectation
of the receiver table against the belief. Against the point belief `pure low` at `degree`, paying
`lowWage` yields `-(1 - 1)² = 0`. -/
theorem spence_receiverPosteriorPayoff_pure_low_lowWage :
    spence.receiverPosteriorPayoff (FinDist.pure low) degree lowWage = 0 := by
  rw [spence.receiverPosteriorPayoff_eq_expect, FinDist.expect_pure]
  norm_num [spenceReceiverPayoff, wage, productivity, low, lowWage]

/-- Paying `highWage` against the point belief `pure low` yields `-(3 - 1)² = -4`. -/
private theorem spence_receiverPosteriorPayoff_pure_low_highWage :
    spence.receiverPosteriorPayoff (FinDist.pure low) degree highWage = -4 := by
  rw [spence.receiverPosteriorPayoff_eq_expect, FinDist.expect_pure]
  norm_num [spenceReceiverPayoff, wage, productivity, low, highWage]

/-- **`isReceiverBestResponse_pure_iff`, positive direction.** `lowWage` *is* a best response to
the point belief `pure low` (the firm matches the low type's wage): `-(wage a - 1)²` is maximized
at `a = lowWage`. Reduces via the iff to a payoff-table check. -/
theorem spence_lowWage_isBestResponse_to_pure_low :
    spence.isReceiverBestResponse (FinDist.pure low) degree lowWage := by
  rw [spence.isReceiverBestResponse_pure_iff]
  intro a'
  fin_cases a' <;>
    norm_num [spenceReceiverPayoff, wage, productivity, low, lowWage, highWage]

/-- **`isReceiverBestResponse_pure_iff`, negative direction.** `highWage` is **not** a best
response to `pure low`: Paying the high wage to the low type loses `4`, while `lowWage` loses
nothing (`-4 < 0`). A payoff-sign flip in the quadratic loss would wrongly admit `highWage` here. -/
theorem spence_highWage_not_bestResponse_to_pure_low :
    ¬ spence.isReceiverBestResponse (FinDist.pure low) degree highWage := by
  rw [spence.isReceiverBestResponse_pure_iff]
  intro h
  have hbad := h lowWage
  rw [show spence.payoff .receiver low degree highWage = -4 from by
      norm_num [spenceReceiverPayoff, wage, productivity, low, highWage],
    show spence.payoff .receiver low degree lowWage = 0 from by
      norm_num [spenceReceiverPayoff, wage, productivity, low, lowWage]] at hbad
  norm_num at hbad

/-- **BeerQuiche negative best-response check (the one the module docstring advertises).**
`notFight` is **not** a best response to the point belief `pure weak` at `beer`: fighting the weak
type pays `+1`, not fighting pays `0`, so `0 ≥ 1` is false. This is the BeerQuiche
`notFight`-vs-`pure weak` negative check; together with the Spence `highWage` negative check it
pins the receiver optimization direction on both worked games. -/
theorem beerQuiche_notFight_not_bestResponse_to_pure_weak :
    ¬ beerQuiche.isReceiverBestResponse (FinDist.pure weak) beer notFight := by
  rw [beerQuiche.isReceiverBestResponse_pure_iff]
  intro h
  have hbad := h fight
  rw [show beerQuiche.payoff .receiver weak beer notFight = 0 from by
      norm_num [beerQuicheReceiverPayoff, weak, notFight, fight],
    show beerQuiche.payoff .receiver weak beer fight = 1 from by
      norm_num [beerQuicheReceiverPayoff, weak, notFight, fight]] at hbad
  norm_num at hbad

/-! ### Sender expected payoff against a pure receiver (Chunk 2)

On Spence the receiver plays `pure m` at message `m`. So against the receiver strategy, the
high type sending `degree` faces action `highWage`: Payoff
`wage highWage - educationCost high degree =
3 - 1 = 2`. -/

/-- `senderExpectedPayoff_pure_receiver`: With the receiver playing `pure highWage` at `degree`,
the high type's expected payoff there is the single table entry
`wage highWage - cost high degree =
3 - 1 = 2`. -/
theorem spence_senderExpectedPayoff_high_degree :
    spence.senderExpectedPayoff spenceReceiverStrategy high degree = 2 := by
  rw [spence.senderExpectedPayoff_pure_receiver (a₀ := highWage)
      (show spenceReceiverStrategy degree = FinDist.pure highWage from rfl) high]
  norm_num [spenceSenderPayoff, wage, educationCost, high, degree, highWage]

/-! ### Deviator value = equilibrium payoff (Chunk 2)

`signalingValue_sender_eq` / `signalingValue_sender_eq_equilibriumPayoff` /
`equilibriumPayoff_eq_expect`: On the Spence separating assessment the high type's value is `2`
(degree, high wage). -/

/-- `equilibriumPayoff_eq_expect` + `equilibriumPayoff_pooling`-style collapse: The high type's
equilibrium payoff on the Spence separating assessment is `2`. -/
theorem spence_equilibriumPayoff_high :
    spence.equilibriumPayoff spenceSeparating high = 2 := by
  rw [spence.equilibriumPayoff_eq_expect,
    show spenceSeparating.senderStrategy high = FinDist.pure high from rfl, FinDist.expect_pure,
    show spenceSeparating.receiverStrategy = spenceReceiverStrategy from rfl]
  exact spence_senderExpectedPayoff_high_degree

/-- `signalingValue_sender_eq_equilibriumPayoff`: The sender deviator's value at the high type *is*
the high type's equilibrium payoff (`= 2`). A confusion that read the deviator value off the wrong
type or strategy would not match. -/
theorem spence_signalingValue_sender_high_eq_two :
    spence.signalingValue (.sender high) spenceSeparating = 2 := by
  rw [spence.signalingValue_sender_eq_equilibriumPayoff]
  exact spence_equilibriumPayoff_high

/-- `signalingValue_sender_eq`: The sender deviator value unfolds to the expectation of
`senderExpectedPayoff` over the high type's (point-mass) message mixture — confirming the unfolding
agrees with the closed-form value `2`. -/
theorem spence_signalingValue_sender_high_eq_expect :
    spence.signalingValue (.sender high) spenceSeparating =
      (spenceSeparating.senderStrategy high).expect
        (fun m => spence.senderExpectedPayoff spenceSeparating.receiverStrategy high m) :=
  spence.signalingValue_sender_eq spenceSeparating high

/-- `signalingValue_receiver_eq`: The receiver deviator value at `degree` unfolds to the
expectation of `receiverPosteriorPayoff` against the held belief over the receiver's action
mixture. We exercise the unfolding directly (structural). -/
theorem spence_signalingValue_receiver_degree_eq_expect :
    spence.signalingValue (.receiver degree) spenceSeparating =
      (spenceSeparating.receiverStrategy degree).expect
        (fun act => spence.receiverPosteriorPayoff (spenceSeparating.belief degree) degree act) :=
  spence.signalingValue_receiver_eq spenceSeparating degree

/-! ### `isSignalingPBE_of_pure` (Chunk 2)

The Spence separating PBE is exactly an instance of the bundled constructive characterization.
We re-derive it through `isSignalingPBE_of_pure` directly (the example proves it via
`senderOptimal_of_pure`/`receiverOptimal_of_pure`; here we route the single bundled endpoint),
confirming the bundle is non-vacuously satisfiable on a genuine separating equilibrium. -/

/-- Bayes consistency of the Spence separating assessment, extracted from the example's PBE proof
(so the `isSignalingPBE_of_pure` reconstruction has its first hypothesis). -/
private theorem spence_separating_bayesConsistent :
    spence.signalingBayesConsistent spenceSeparating :=
  spence_separating_isSignalingPBE.1

/-- `isSignalingPBE_of_pure`: The Spence separating assessment is a PBE via the bundled
constructive characterization (Bayes consistency + pure-deviation optimality on both sides). The
sender check is the single-crossing payoff table; the receiver check is the quadratic-loss table at
each point belief. This confirms `isSignalingPBE_of_pure` is satisfiable on a real separating
equilibrium, not vacuously. -/
theorem spence_separating_isSignalingPBE_of_pure :
    spence.IsSignalingPBE spenceSeparating := by
  refine spence.isSignalingPBE_of_pure spenceSeparating spence_separating_bayesConsistent ?_ ?_
  · -- Sender side: only m = θ is on-support; payoff-table check.
    intro θ m hm m'
    have hmθ : m = θ := by
      by_contra hne
      rw [show (spenceSeparating.senderStrategy θ).pmf m = 0 from
        FinDist.pure_apply_ne fun h => hne h.symm] at hm
      exact lt_irrefl _ hm
    subst hmθ
    rw [show spenceSeparating.receiverStrategy = spenceReceiverStrategy from rfl]
    rw [spence.senderExpectedPayoff_pure_receiver (a₀ := m)
        (show spenceReceiverStrategy m = FinDist.pure m from rfl),
      spence.senderExpectedPayoff_pure_receiver (a₀ := m')
        (show spenceReceiverStrategy m' = FinDist.pure m' from rfl)]
    fin_cases m <;> fin_cases m' <;>
      norm_num [spenceSenderPayoff, wage, educationCost, low, high, noDegree, degree,
        lowWage, highWage]
  · -- Receiver side: only act = m is on-support; belief is pure m; payoff-table check.
    intro m act hact act'
    have hactm : act = m := by
      by_contra hne
      rw [show (spenceSeparating.receiverStrategy m).pmf act = 0 from
        FinDist.pure_apply_ne fun h => hne h.symm] at hact
      exact lt_irrefl _ hact
    subst hactm
    rw [show spenceSeparating.belief act = FinDist.pure (α := Fin 2) act from rfl]
    simp_rw [SignalingGame.receiverPosteriorPayoff_eq_expect, FinDist.expect_pure]
    fin_cases act <;> fin_cases act' <;>
      norm_num [spenceReceiverPayoff, wage, productivity, low, lowWage, highWage]

/-! ### Pooling primitives (Chunk 2)

The BeerQuiche all-quiche assessment pools on `quiche`. We exercise the generic pooling lemmas:
Marginal, off-path, structural pooling, and the **off-path posterior = prior** at the pooled
message. -/

/-- `marginalProb_pooling`: Under the all-quiche pooling, the message marginal at the pooled message
`quiche` is `1`. -/
theorem beerQuiche_marginalProb_pooling_quiche :
    beerQuiche.marginalProb beerQuichePoolingSender quiche = 1 := by
  rw [beerQuiche.marginalProb_pooling (σ := beerQuichePoolingSender) (m₀ := quiche)
    (fun _ => rfl) quiche]
  exact FinDist.pure_apply_self quiche

/-- **The off-path coordinate: marginal at `beer` is `0`.** Completing the point-mass-at-quiche
claim: under all-quiche pooling no type orders beer, so its marginal is `0`. A
`marginalProb_pooling` bug that got the off-path coordinate wrong would be caught here (the
`quiche = 1` check alone could not). -/
theorem beerQuiche_marginalProb_pooling_beer :
    beerQuiche.marginalProb beerQuichePoolingSender beer = 0 := by
  unfold SignalingGame.marginalProb
  apply Finset.sum_eq_zero
  intro θ _
  rw [show (beerQuichePoolingSender θ).pmf beer = 0 from
    FinDist.pure_apply_ne (show (quiche : Fin 2) ≠ beer by decide)]
  ring

/-- `isOffPath_pooling`: `beer` is off-path under all-quiche pooling (no type orders beer). -/
theorem beerQuiche_isOffPath_pooling_beer :
    beerQuiche.isOffPath beerQuichePooling beer :=
  beerQuiche.isOffPath_pooling (fun _ => rfl) (by decide)

/-- `isPooling_of_pure`: The all-quiche assessment is pooling (both types order quiche). -/
theorem beerQuiche_isPooling_of_pure :
    beerQuiche.IsPooling beerQuichePooling :=
  beerQuiche.isPooling_of_pure (fun _ => rfl)

/-- **`pooling_posterior_eq_prior`, the posterior/prior swap catch.** At the pooled message
`quiche` the *Bayes posterior* is the prior `beerQuichePrior` — the pooled message reveals nothing.
This is the on-path side of the swap check (separating's point-mass collapse, `pbGame` above, is
the other side): The intuitive-criterion story turns on this off-path belief *not* being forced to
the prior, so getting the on-path posterior right is load-bearing. -/
theorem beerQuiche_pooling_posterior_eq_prior :
    beerQuiche.posterior beerQuichePoolingSender quiche = beerQuichePrior :=
  beerQuiche.pooling_posterior_eq_prior (fun _ => rfl)

/-- `equilibriumPayoff_pooling`: The weak type's equilibrium payoff collapses to its expected
payoff at the pooled message `quiche`. -/
theorem beerQuiche_equilibriumPayoff_pooling_weak :
    beerQuiche.equilibriumPayoff beerQuichePooling weak =
      beerQuiche.senderExpectedPayoff beerQuichePoolingReceiver weak quiche :=
  beerQuiche.equilibriumPayoff_pooling (fun _ => rfl) weak

/-- `equilibriumPayoff_pure_pure`: Pure pooling sender + pure receiver response at `quiche` gives
the weak type the single table entry `beerQuicheSenderPayoff weak quiche notFight = 1` (quiche, not
fought). -/
theorem beerQuiche_equilibriumPayoff_pure_pure_weak :
    beerQuiche.equilibriumPayoff beerQuichePooling weak = 1 := by
  rw [beerQuiche.equilibriumPayoff_pure_pure (m₀ := quiche) (a₀ := notFight)
    (fun _ => rfl) rfl weak]
  norm_num [beerQuicheSenderPayoff, weak, quiche, notFight, fight]

/-! ### Separating posterior point mass (Chunk 2)

`posterior_eq_pure_of_unique_sender` on the Spence separating sender strategy: At `degree`,
only the high type sends with positive probability (the diagonal `pure θ`), and the prior supports
the high type, so the posterior is `pure high`. -/

/-- `posterior_eq_pure_of_unique_sender`: The Spence separating posterior at `degree` is the point
mass on `high` (the unique sender of `degree`). The point-mass collapse — the receiver learns the
type — exactly as in `pbGame_posterior_separating_is_point_mass`, here on a genuine PBE. -/
theorem spence_posterior_degree_is_pure_high :
    spence.posterior spenceSenderStrategy degree = FinDist.pure high := by
  refine spence.posterior_eq_pure_of_unique_sender (θ₀ := high) ?_ ?_ ?_
  · -- prior supports high: uniform prior on Fin 2 puts 1/2 > 0.
    rw [show spence.prior.pmf high = (Fintype.card (Fin 2) : ℝ)⁻¹ from rfl]
    norm_num [Fintype.card_fin]
  · -- high sends degree with probability 1 (diagonal pure high; high = degree).
    rw [show (spenceSenderStrategy high).pmf degree = 1 from FinDist.pure_apply_self degree]
    norm_num
  · -- every other type sends degree with probability 0 (`high = degree` are both `1`).
    intro θ hθ
    exact FinDist.pure_apply_ne (a := θ) (b := degree) hθ

/-! ## Chunk 3 — Intuitive criterion

All witnesses are on the BeerQuiche game. The semantically loaded ones are: The dominated set
is *nonempty* (the weak type genuinely *is* eliminated at beer —
`intuitiveCriterion_eliminates_…`), the vacuity guard `intuitive_criterion_vacuous` does **not**
fire on the live equilibrium (a non-dominated type exists), and a profitable pooling deviation
contradicts sender optimality. -/

/-- `mem_possibleReceiverActions_of_pure_belief`: `fight` is a possible receiver action at `beer`
because it is a best response to the point belief `pure weak` (fighting the weak type pays `+1`,
not fighting `0`). This is the witness `beerQuiche`'s `possibleReceiverActions = univ` reduction is
built from; we exercise the entry point directly on a concrete belief. -/
theorem beerQuiche_fight_mem_possibleReceiverActions_beer :
    fight ∈ beerQuiche.possibleReceiverActions Set.univ beer := by
  refine beerQuiche.mem_possibleReceiverActions_of_pure_belief (Set.mem_univ weak)
    (beerQuiche.isReceiverBestResponse_pure_iff.mpr fun a' => ?_)
  fin_cases a' <;> norm_num [beerQuicheReceiverPayoff, weak, notFight, fight]

/-- Both receiver actions are best responses to some belief at `beer`, so `BR(univ, beer)` is the
full action set. (`notFight` is a best response to `pure strong`; `fight` to `pure weak`.) This is
the textbook Cho-Kreps simplification for BeerQuiche, restated locally so the `bestResponsePayoff`
witness below can fire. -/
private theorem beerQuiche_possibleReceiverActions_beer_eq_univ :
    beerQuiche.possibleReceiverActions Set.univ beer = Set.univ := by
  ext a
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  fin_cases a
  · -- notFight: best response to pure strong.
    refine beerQuiche.mem_possibleReceiverActions_of_pure_belief (Set.mem_univ strong)
      (beerQuiche.isReceiverBestResponse_pure_iff.mpr fun a' => ?_)
    fin_cases a' <;> norm_num [beerQuicheReceiverPayoff, strong, weak, notFight, fight]
  · -- fight: best response to pure weak.
    refine beerQuiche.mem_possibleReceiverActions_of_pure_belief (Set.mem_univ weak)
      (beerQuiche.isReceiverBestResponse_pure_iff.mpr fun a' => ?_)
    fin_cases a' <;> norm_num [beerQuicheReceiverPayoff, weak, notFight, fight]

/-- `bestResponsePayoff_eq_iSup_of_univ`: When `BR(univ, beer)` is the whole action set, the weak
type's Cho-Kreps best-case payoff at beer is the supremum over all actions, `max 0 (-2) = 0`. The
most favorable receiver response (not fight) preserves weak's intrinsic-zero beer payoff. -/
theorem beerQuiche_bestResponsePayoff_weak_beer_eq_zero :
    beerQuiche.bestResponsePayoff Set.univ weak beer = 0 := by
  rw [beerQuiche.bestResponsePayoff_eq_iSup_of_univ
      beerQuiche_possibleReceiverActions_beer_eq_univ weak,
    iSup_fin_two (fun act => beerQuiche.payoff .sender weak beer act)]
  norm_num [beerQuicheSenderPayoff, weak, beer, notFight, fight]

/-- **`intuitive_criterion_vacuous` does NOT fire on the live equilibrium.** At the off-path
message `beer` of the all-quiche pooling equilibrium there *is* a non-dominated type (the strong
type), so the vacuity guard `intuitive_criterion_vacuous`'s hypothesis
(`∀ θ, equilibriumDominated … θ`) is unsatisfiable here. Equivalently, the belief restriction at
beer is *not* imposed vacuously — which is exactly what makes `beerQuichePooling_fails_IC` a
genuine failure, not a degenerate one. -/
theorem beerQuiche_pooling_beer_not_all_dominated :
    ¬ ∀ θ, beerQuiche.equilibriumDominated beerQuichePooling beer θ := by
  intro h_all
  exact beerQuichePooling_strong_not_dominated_at_beer (h_all strong)

/-- **`intuitiveCriterion_eliminates_dominated_types`, the nonempty dominated set.** Exercised on
the *surviving* all-beer equilibrium, where the belief restriction genuinely holds (extracted from
`beerQuicheBeerPooling_passes_IC`). At the off-path message `quiche` the dominated set is
**nonempty** — the *strong* type is the eliminated one (it is equilibrium-dominated at quiche) —
and the eliminator forces its off-path belief mass to `0`. Naming the eliminated type explicitly is
the non-vacuity content: A vacuously-true belief restriction would eliminate nobody. -/
theorem beerQuiche_intuitiveCriterion_eliminates_strong_at_quiche :
    beerQuiche.equilibriumDominated beerQuicheBeerPooling quiche strong ∧
      (beerQuicheBeerPooling.belief quiche).pmf strong = 0 := by
  refine ⟨beerQuicheBeerPooling_strong_dominated_at_quiche, ?_⟩
  -- The eliminator consumes the genuine belief restriction of the surviving all-beer equilibrium.
  have h_nonempty : ∃ θ, ¬ beerQuiche.equilibriumDominated beerQuicheBeerPooling quiche θ :=
    ⟨weak, beerQuicheBeerPooling_weak_not_dominated_at_quiche⟩
  exact beerQuiche.intuitiveCriterion_eliminates_dominated_types beerQuicheBeerPooling quiche
    beerQuicheBeerPooling_quiche_isOffPath h_nonempty beerQuicheBeerPooling_passes_IC.2
    strong beerQuicheBeerPooling_strong_dominated_at_quiche

/-- The *failing* all-quiche equilibrium's dominated set at beer is also nonempty: The **weak**
type is the eliminated one there. (No belief restriction holds for the all-quiche assessment — that
is the content of `beerQuichePooling_fails_IC` — so we only record that the dominated set is
nonempty, which is what stops `beerQuichePooling_fails_IC` from being a vacuous failure.) -/
theorem beerQuiche_pooling_weak_dominated_nonvacuous :
    beerQuiche.equilibriumDominated beerQuichePooling beer weak :=
  beerQuichePooling_weak_dominated_at_beer

/-- `SurvivesIntuitiveCriterion.receiver_optimal_on_nonDominated` (Cho-Kreps clause 2, derived): On
the surviving all-beer equilibrium at the off-path message `quiche`, the belief is supported on the
non-dominated types and the receiver's action is a best response to it. We extract both conjuncts
on the live witness — the support confinement is what gives the receiver's threat its teeth. -/
theorem beerQuiche_receiver_optimal_on_nonDominated_quiche :
    (∀ θ, 0 < (beerQuicheBeerPooling.belief quiche).pmf θ →
        θ ∈ beerQuiche.nonDominatedTypes beerQuicheBeerPooling quiche) ∧
      ∀ a', beerQuiche.receiverPosteriorPayoff (beerQuicheBeerPooling.belief quiche) quiche a' ≤
        (beerQuicheBeerPooling.receiverStrategy quiche).expect
          (fun act => beerQuiche.receiverPosteriorPayoff
            (beerQuicheBeerPooling.belief quiche) quiche act) :=
  beerQuicheBeerPooling_passes_IC.receiver_optimal_on_nonDominated quiche
    beerQuicheBeerPooling_quiche_isOffPath
    ⟨weak, beerQuicheBeerPooling_weak_not_dominated_at_quiche⟩

/-- `pooling_profitable_deviation_contradicts_sender_optimality`: On a pooling assessment with
sender optimality, no sender type can have a strictly profitable deviation. We instantiate the
contrapositive shape on the all-quiche pooling equilibrium: Feeding the genuine sender-optimality
fact (extracted from the PBE), a hypothetical profitable beer deviation by the weak type is absurd.
This catches a sender-optimality / profitability direction reversal. -/
theorem beerQuiche_no_profitable_pooling_deviation
    (h_dev_profitable : beerQuiche.senderExpectedPayoff beerQuichePoolingReceiver weak beer
      > beerQuiche.equilibriumPayoff beerQuichePooling weak) : False := by
  -- Extract sender optimality from the all-quiche PBE: each on-support message weakly dominates.
  have h_sender_opt : ∀ (θ : beerQuiche.Theta) (m : beerQuiche.Msg),
      (beerQuichePooling.senderStrategy θ).pmf m > 0 →
      ∀ (m' : beerQuiche.Msg),
        beerQuiche.senderExpectedPayoff beerQuichePooling.receiverStrategy θ m ≥
        beerQuiche.senderExpectedPayoff beerQuichePooling.receiverStrategy θ m' := by
    intro θ m hm m'
    -- Only quiche is on-support; the equilibrium payoff there dominates every message.
    have hmq : m = quiche := by
      by_contra hne
      rw [show (beerQuichePooling.senderStrategy θ).pmf m = 0 from
        FinDist.pure_apply_ne fun h => hne h.symm] at hm
      exact lt_irrefl _ hm
    subst hmq
    -- equilibriumPayoff at θ collapses to the quiche payoff (pooling); PBE bounds every deviation.
    have heq : beerQuiche.senderExpectedPayoff beerQuichePooling.receiverStrategy θ quiche =
        beerQuiche.equilibriumPayoff beerQuichePooling θ :=
      (beerQuiche.equilibriumPayoff_pooling (fun _ => rfl) θ).symm
    rw [ge_iff_le, heq]
    exact beerQuichePooling_isSignalingPBE.sender_bestResponse θ m'
  exact beerQuiche.pooling_profitable_deviation_contradicts_sender_optimality
    beerQuichePooling beerQuichePooling_isPooling
    (by
      simpa [show beerQuichePooling.receiverStrategy = beerQuichePoolingReceiver from rfl]
        using h_sender_opt)
    beer weak
    (by simpa [show beerQuichePooling.receiverStrategy = beerQuichePoolingReceiver from rfl]
        using h_dev_profitable)

end EconlibTest.GameTheory.SignalingCore

end
