/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Spence (1973): Job-Market Signaling

This file formalizes the canonical separating Perfect Bayesian Equilibrium (PBE) of the two-type,
two-message, two-action signaling game introduced by Michael Spence in "Job Market Signaling"
(*Quarterly Journal of Economics*, 1973).

## The model

A worker (sender) has a privately observed *productivity type* `θ ∈ {low, high}`. Before entering
the labor market, the worker chooses whether to acquire an education credential
`m ∈ {no-degree, degree}`. A firm (receiver) observes the credential — but not the underlying
productivity — and pays a *wage* `a ∈ {low-wage, high-wage}`.

Education is costly, and more costly for the low type than for the high type (the single-crossing /
Spence–Mirrlees condition). The classical insight is that, even though the firm cannot observe `θ`
directly, there is a self-enforcing equilibrium in which:

* the low type does not get a degree;
* the high type gets a degree;
* the firm pays the low wage to anyone without a degree, and the high wage to anyone with a degree.

In this equilibrium the credential signals productivity even though it is intrinsically useless:
The marginal cost differential makes acquiring the degree just barely worthwhile for the high type
and prohibitively expensive for the low type.

## The numerical instantiation

We pick concrete rational payoffs so that the equilibrium conditions are decidable and the
optimality margins are clearly positive. Named abbreviations encode the `Fin 2` codes:

* types: `low = 0`, `high = 1` (productivities `1` and `3`);
* messages: `noDegree = 0`, `degree = 1` (education costs `0`, and `4` for the low type / `1` for
  the high type);
* actions: `lowWage = 0`, `highWage = 1` (wage values `1` and `3`).

The sender's payoff is `wage(a) - cost(θ, m)`. The receiver's payoff is the negative quadratic loss
`-(wage(a) - productivity(θ))^2`. The single-crossing condition
`cost(low, degree) > cost(high, degree)` (4 vs. 1) is what makes the separating equilibrium
possible: At the equilibrium wages, the low type loses 2 by getting a degree, while the high type
gains 1.

## Main results

* `spence` — the signaling game itself.
* `spenceSeparating` — the candidate separating assessment (point-mass strategies and on-path-Bayes
  beliefs).
* `spence_separating_isSignalingPBE` — `spenceSeparating` is a Perfect Bayesian Equilibrium of
  `spence`.
* `spence_isSeparating` — `spenceSeparating` is a *separating* assessment (structural).
* `spence_separating_PBE_exists` — the existence corollary: an assessment that is both a PBE and
  separating.

The proof of `spence_separating_isSignalingPBE` works through the three side conditions of
`IsSignalingPBE`:

1. **Bayes consistency.** On-path posteriors are degenerate point masses at the signaling type. The
   two messages are both on-path here, so off-path beliefs do not enter.
2. **Sender optimality.** Each type's pure-strategy message maximizes expected payoff against the
   receiver's fixed strategy (no deviation pays more). Reduces to real arithmetic on `Fin 2` once
   `expect` is unfolded.
3. **Receiver optimality.** At each on-path belief (a point mass), the receiver's pure action
   minimizes the quadratic loss. Same argument.

## References

Spence, Michael. 1973. “Job Market Signaling.” The Quarterly Journal of Economics 87 (3): 355.
https://doi.org/10.2307/1882010.
-/

open Econlib.GameTheory Econlib.Probability

namespace EconlibExamples.GameTheory.SpenceSignaling

noncomputable section

/-! ## Numerical Primitives -/

/-- The low-productivity worker type: Produces `1`, finds education expensive. -/
abbrev low : Fin 2 := 0
/-- The high-productivity worker type: Produces `3`, finds education cheap. -/
abbrev high : Fin 2 := 1
/-- The no-degree message: The worker skips the credential. -/
abbrev noDegree : Fin 2 := 0
/-- The degree message: The worker acquires the credential. -/
abbrev degree : Fin 2 := 1
/-- The firm pays the low wage. -/
abbrev lowWage : Fin 2 := 0
/-- The firm pays the high wage. -/
abbrev highWage : Fin 2 := 1

/-- Productivity of the worker as a function of type: The low type produces `1`, the high type
produces `3`. -/
def productivity (θ : Fin 2) : ℝ :=
  if θ = low then 1 else 3

/-- Wage attached to each receiver action: `1` for the low wage, `3` for the high wage. -/
def wage (a : Fin 2) : ℝ :=
  if a = lowWage then 1 else 3

/-- Cost of education. A degree costs the low type `4` but the high type only `1`; skipping the
credential is free for both. The single-crossing differential `4 - 1 = 3` is what sustains the
separating equilibrium below. -/
def educationCost (θ m : Fin 2) : ℝ :=
  if m = degree then (if θ = low then 4 else 1) else 0

/-- Sender's payoff: Wage received minus the cost of the chosen credential. -/
def spenceSenderPayoff : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun θ m a => wage a - educationCost θ m

/-- Receiver's payoff: Negative quadratic loss between paid wage and the worker's true
productivity. With the chosen wage values, the receiver's optimal action at a point-mass belief on
`θ` is to pay the wage that matches `productivity θ`. -/
def spenceReceiverPayoff : Fin 2 → Fin 2 → Fin 2 → ℝ :=
  fun θ _ a => -(wage a - productivity θ) ^ 2

/-! ## The Signaling Game -/

/-- Uniform 50/50 prior over `{low, high}`. Lifted from the legacy `FinDist` API to a generic
`FinDist (Fin 2)`. The exact split plays no role in the separating-equilibrium verification (the
on-path posteriors are degenerate point masses determined by the pure sender strategy), but the
prior's *full support* is load-bearing: Bayes consistency invokes
`posterior_eq_pure_of_unique_sender`, whose hypothesis is that the prior puts positive mass on the
signaling type, which holds here because the uniform prior is strictly positive. -/
def spencePrior : FinDist (Fin 2) :=
  FinDist.uniform (α := Fin 2)

/-- The Spence signaling game. Built via `SignalingGame.mkFin` and marked `abbrev` so the carrier
types `spence.{Theta,Msg,Act}` reduce to `Fin 2`. The upstream `mkFin_Theta`/`_Msg`/ `_Act` simp
lemmas replace the per-game carrier-unfolding workaround. -/
abbrev spence : SignalingGame :=
  SignalingGame.mkFin 2 2 2 spencePrior fun
    | .sender, θ, m, a => spenceSenderPayoff θ m a
    | .receiver, θ, m, a => spenceReceiverPayoff θ m a

/-! ## The Separating Assessment -/

/-- Sender's pure strategy: The low type sends `noDegree`, the high type sends `degree`. Since the
codes coincide (`low = noDegree`, `high = degree`), the strategy is the diagonal `pure θ`, encoded
as point-mass distributions. -/
def spenceSenderStrategy : spence.SenderMixedStrategy :=
  fun θ => FinDist.pure (α := Fin 2) θ  -- the diagonal: low ↦ noDegree, high ↦ degree

/-- Receiver's pure strategy: Pay `lowWage` on observing `noDegree`, `highWage` on observing
`degree`. Again the diagonal `pure m`, since the codes coincide. -/
def spenceReceiverStrategy : spence.ReceiverMixedStrategy :=
  fun m => FinDist.pure (α := Fin 2) m

/-- Receiver's belief: At message `m`, believe the type is `m`. Both messages are on-path here
(each is sent by exactly one type), so these beliefs are also the unique Bayes-consistent
posteriors. -/
def spenceBelief : spence.ReceiverBelief :=
  fun m => FinDist.pure (α := Fin 2) m

/-- The candidate separating assessment. -/
def spenceSeparating : spence.SignalingAssessment where
  senderStrategy := spenceSenderStrategy
  receiverStrategy := spenceReceiverStrategy
  belief := spenceBelief

/-! ## Bayes Consistency

Point-mass and `Fin 2` mass-evaluation facts live upstream: `FinDist.pure_pmf`,
`FinDist.pure_apply_ne`, `FinDist.sum_pmf_two`. -/

/-- Bayes consistency for the separating assessment, via `posterior_eq_pure_of_unique_sender`: Each
message `m` is sent only by type `m` (the diagonal strategy), so the posterior at `m` is `pure m` —
exactly `spenceBelief m`. -/
lemma spenceSeparating_bayesConsistent :
    spence.signalingBayesConsistent spenceSeparating := by
  intro m _hm
  have hpost : spence.posterior spenceSeparating.senderStrategy m = FinDist.pure m :=
    spence.posterior_eq_pure_of_unique_sender (θ₀ := m)
      (by rw [show spencePrior.pmf m = (Fintype.card (Fin 2) : ℝ)⁻¹ from
            FinDist.uniform_apply m]; norm_num [Fintype.card_fin])
      (by rw [show (spenceSeparating.senderStrategy m).pmf m = 1 from
        FinDist.pure_apply_self m]; norm_num)
      (fun θ hθ => FinDist.pure_apply_ne hθ)
  rw [hpost]
  rfl

/-! ## Sender Optimality -/

/-- Pure receiver play is `pure m`, so the action drawn at message `m` is `m` itself. The sender's
expected payoff at type `θ` and message `m` is therefore the deterministic table entry
`wage m - educationCost θ m`. -/
private lemma sender_expected_payoff_value (θ m : Fin 2) :
    spence.senderExpectedPayoff spenceSeparating.receiverStrategy θ m =
      wage m - educationCost θ m :=
  spence.senderExpectedPayoff_pure_receiver rfl θ

/-- Sender optimality for the separating assessment, via pure-deviation sufficiency
(`senderOptimal_of_pure`): Each type's diagonal message maximizes the deterministic payoff table —
the single-crossing cost differential prices the low type out of the degree. -/
lemma spenceSeparating_senderOptimal
    (θ : spence.Theta) (a' : spence.SignalingAssessment)
    (hswap : spence.signalingSwap (.sender θ) spenceSeparating a') :
    spence.signalingValue (.sender θ) spenceSeparating ≥
      spence.signalingValue (.sender θ) a' := by
  refine spence.senderOptimal_of_pure spenceSeparating θ ?_ a' hswap
  intro m hm m'
  -- The diagonal strategy is on-support only at m = θ.
  have hmθ : m = θ := by
    by_contra hne
    rw [show (spenceSeparating.senderStrategy θ).pmf m = 0 from
      FinDist.pure_apply_ne fun h => hne h.symm] at hm
    exact lt_irrefl _ hm
  subst hmθ
  -- Payoff-table check: wage m - cost θ m, maximized at the diagonal. (After `subst`, the type
  -- variable is spelled `m`.)
  simp only [sender_expected_payoff_value]
  fin_cases m <;> fin_cases m' <;>
    norm_num [wage, educationCost, low, high, noDegree, degree, lowWage, highWage]

/-! ## Receiver Optimality -/

/-- Receiver optimality for the separating assessment, via pure-deviation sufficiency
(`receiverOptimal_of_pure`): At each on-path point belief `pure m`, paying the type-matching wage
minimizes the quadratic loss. -/
lemma spenceSeparating_receiverOptimal
    (m : spence.Msg) (a' : spence.SignalingAssessment)
    (hswap : spence.signalingSwap (.receiver m) spenceSeparating a') :
    spence.signalingValue (.receiver m) spenceSeparating ≥
      spence.signalingValue (.receiver m) a' := by
  refine spence.receiverOptimal_of_pure spenceSeparating m ?_ a' hswap
  intro act hact act'
  -- The diagonal receiver strategy is on-support only at act = m.
  have hactm : act = m := by
    by_contra hne
    rw [show (spenceSeparating.receiverStrategy m).pmf act = 0 from
      FinDist.pure_apply_ne fun h => hne h.symm] at hact
    exact lt_irrefl _ hact
  subst hactm
  -- The belief is the point mass `pure act` (after `subst`, the message is spelled `act`);
  -- posterior payoffs are table entries.
  rw [show spenceSeparating.belief act = FinDist.pure (α := Fin 2) act from rfl]
  simp_rw [SignalingGame.receiverPosteriorPayoff_eq_expect, FinDist.expect_pure]
  fin_cases act <;> fin_cases act' <;>
    norm_num [spenceReceiverPayoff, wage, productivity, low, lowWage, highWage]

/-! ## The Main Theorem -/

/-- The separating assessment is a Perfect Bayesian Equilibrium of `spence`. -/
theorem spence_separating_isSignalingPBE :
    spence.IsSignalingPBE spenceSeparating := by
  refine ⟨spenceSeparating_bayesConsistent, ?_⟩
  intro dev a' hswap
  cases dev with
  | sender θ => exact spenceSeparating_senderOptimal θ a' hswap
  | receiver m => exact spenceSeparating_receiverOptimal m a' hswap

/-- `spenceSeparating` is a *separating* assessment in the formal sense: Distinct types never both
assign positive probability to the same message. -/
theorem spence_isSeparating : spence.IsSeparating spenceSeparating := by
  intro θ₁ θ₂ hne m ⟨h1, h2⟩
  -- (pure θᵢ).pmf m > 0 forces θᵢ = m; factor the identical argument.
  have key : ∀ th : Fin 2, 0 < (spenceSeparating.senderStrategy th).pmf m → th = m := by
    intro th hpos
    by_contra hθ
    rw [show (spenceSeparating.senderStrategy th).pmf m = 0 from
      FinDist.pure_apply_ne hθ] at hpos
    exact lt_irrefl _ hpos
  exact hne (key θ₁ h1 ▸ key θ₂ h2 ▸ rfl)

/-- A *separating* PBE exists for the Spence signaling game: There is an assessment that is both a
Perfect Bayesian Equilibrium and a separating assessment (distinct types send distinct messages). -/
theorem spence_separating_PBE_exists :
    ∃ a : spence.SignalingAssessment, spence.IsSignalingPBE a ∧ spence.IsSeparating a :=
  ⟨spenceSeparating, spence_separating_isSignalingPBE, spence_isSeparating⟩

end

end EconlibExamples.GameTheory.SpenceSignaling
