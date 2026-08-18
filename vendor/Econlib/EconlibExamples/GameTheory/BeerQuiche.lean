/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Beer-Quiche (Cho-Kreps 1987): The Pooling Equilibrium Fails the Intuitive Criterion

The Beer-Quiche signaling game is the classical motivating example for the **intuitive criterion**
refinement of Cho and Kreps (1987). It is a two-type, two-message, two-action signaling game in
which two distinct pooling perfect Bayesian equilibria (PBE) coexist — all-quiche and all-beer —
with no separating equilibrium. Of these two pooling equilibria, the all-quiche one fails the
intuitive criterion while the all-beer one survives it (we verify each directly; we do not formalize
a classification ruling out every other conceivable surviving equilibrium). The all-quiche pooling
equilibrium is sustained by an unreasonable off-path belief that
the receiver puts probability one on the sender being the "weak" type whenever the off-path message
*beer* is observed, which is exactly the inference the intuitive criterion rules out; the all-beer
equilibrium's off-path belief (weak at *quiche*) is precisely the inference the criterion endorses.

## The story

A sender (the *patron*) is one of two types — **weak** or **strong** — drawn from a known prior.
The patron walks into a saloon and orders breakfast: Either a **quiche** or a **beer**. A receiver
(the *bully*) observes the order but not the patron's type, and decides whether to **fight** the
patron or **not fight**.

* The weak patron prefers quiche for breakfast (intrinsic `+1`); the strong patron prefers beer
  (intrinsic `+1`). Both lose `2` if they are fought.
* The bully wants to fight the weak type (`+1`) and not fight the strong type (`-1`); not fighting
  yields zero in both cases.

So both types want most of all to avoid a fight, secondarily to get their preferred breakfast.

## The two equilibria

In the **all-quiche pooling PBE**, both types order quiche, the bully does not fight quiche-eaters,
and on the off-path message *beer* the bully threatens to fight. The threat is sustained by the
off-path belief μ(weak | beer) = 1 — i.e., the bully insists, against all reason, that anyone who
orders beer must be weak. Given this belief, fighting is the bully's best response at *beer*, and
the threat of being fought deters the strong type from ordering their preferred drink.

In the **all-beer pooling PBE**, both types order beer, the bully does not fight beer-drinkers and
on the off-path message *quiche* the bully fights, sustained by the belief μ(weak | quiche) = 1.
Here the off-path inference is the reasonable one: Only the weak type could ever gain from
deviating to quiche.

There is no separating PBE: If the order revealed the type, the bully would fight whichever message
marked the weak patron, and the weak patron would profitably defect to the strong type's unfought
order. The symmetric case also fails by the same argument.

## What the intuitive criterion says

Cho and Kreps' intuitive criterion eliminates exactly the unreasonable inference above. At an
off-path message `m`, a sender type `θ` is **equilibrium-dominated** if `θ`'s equilibrium payoff
strictly exceeds the *best-case* payoff `θ` could possibly achieve from deviating to `m`. The
criterion demands that beliefs at `m` assign zero weight to such types: A type who can never
benefit from a deviation should not be blamed for it.

In Beer-Quiche the weak type is equilibrium-dominated at beer (their equilibrium payoff of `+1`
beats their best-case beer payoff of `0`), but the strong type is not (their equilibrium payoff of
`0` does not exceed their best-case beer payoff of `+1`). So the criterion forces μ(weak | beer) =
0. Combined with the requirement that beliefs sum to one, this forces μ(strong | beer) = 1 — which
makes not fighting the bully's best response at beer, undoing the threat that sustained the pooling
equilibrium.

## What this file proves

We construct the Beer-Quiche game `beerQuiche` and both pooling assessments directly, then prove
the full Cho-Kreps story:

* `beerQuichePooling_isSignalingPBE` — the all-quiche pooling assessment is a PBE…
* `beerQuichePooling_fails_IC` — …that does not pass the intuitive criterion.
* `beerQuicheBeerPooling_isSignalingPBE` — the all-beer pooling assessment is a PBE…
* `beerQuicheBeerPooling_passes_IC` — …that does pass the intuitive criterion.
* `beerQuiche_not_isSeparatingPBE` — no separating PBE exists.

Both pooling assessments share one structure: A pure pooling sender at the on-path message `m₀`, a
receiver that does not fight `m₀` and fights the off-path message, and a belief that holds the prior
at `m₀` and puts mass one on *weak* off path. The two are therefore *near-instantiations* of one
another: The PBE proof, the equilibrium payoffs, and the best-response payoffs are all established
once as game-level lemmas parameterized by `m₀` (the `beerQuiche_pooling_*` and
`beerQuiche_bestResponsePayoff_eq` lemmas below), and each named assessment discharges the
structural hypotheses by `rfl`. Only the *intuitive-criterion* conclusions differ between the two,
because the dominated type flips with the off-path message.

The IC-failure argument is short and entirely local: The criterion at message `beer` and type
`weak` would demand `(belief beer).pmf weak = 0`; but the all-quiche assessment has
`(belief beer).pmf weak = 1`; the two are inconsistent. The IC-pass argument is dual: At the
all-beer equilibrium's off-path message `quiche`, the *strong* type is the dominated one and the
belief already assigns it zero mass.

## Main definitions and theorems

* `beerQuiche : SignalingGame` — the Cho-Kreps Beer-Quiche game on `Fin 2 × Fin 2 × Fin 2`.
* `beerQuichePooling : beerQuiche.SignalingAssessment` — the all-quiche pooling assessment.
* `beerQuichePooling_isPooling` — `beerQuichePooling` is a pooling assessment.
* `beerQuichePooling_beer_isOffPath` — *beer* is off-path under `beerQuichePooling`.
* `beerQuichePooling_isSignalingPBE`, `beerQuichePooling_isPoolingPBE` — the all-quiche pooling
  assessment is a perfect Bayesian equilibrium.
* `beerQuichePooling_weak_dominated_at_beer` — the weak type is equilibrium-dominated at *beer*.
* `beerQuichePooling_strong_not_dominated_at_beer` — the strong type is not
  equilibrium-dominated at *beer*.
* `beerQuichePooling_fails_IC` — the Cho-Kreps headline: The all-quiche pooling PBE fails the
  intuitive criterion.
* `beerQuicheBeerPooling : beerQuiche.SignalingAssessment` — the all-beer pooling assessment.
* `beerQuicheBeerPooling_isSignalingPBE`, `beerQuicheBeerPooling_isPoolingPBE` — the all-beer
  pooling assessment is a perfect Bayesian equilibrium.
* `beerQuicheBeerPooling_passes_IC` — the all-beer pooling PBE passes the intuitive criterion.
* `beerQuiche_not_isSeparatingPBE` — the Beer-Quiche game has no separating PBE.

## References

Cho, In-Koo, and David M. Kreps. 1987. “Signaling Games and Stable Equilibria.” The Quarterly
Journal of Economics 102 (2): 179. https://doi.org/10.2307/1885060.
-/

noncomputable section

namespace EconlibExamples.GameTheory.BeerQuiche

open Econlib.GameTheory Econlib.Probability

/-! ## The Beer-Quiche Signaling Game -/

/-- The weak patron type: Would prefer quiche, gets fought (`+1` to the bully). -/
abbrev weak : Fin 2 := 0
/-- The strong patron type: Would prefer beer, hurts the bully (`-1` to the bully) if fought. -/
abbrev strong : Fin 2 := 1
/-- The quiche message. -/
abbrev quiche : Fin 2 := 0
/-- The beer message. -/
abbrev beer : Fin 2 := 1
/-- The bully does not fight. -/
abbrev notFight : Fin 2 := 0
/-- The bully fights. -/
abbrev fight : Fin 2 := 1

/-- The Beer-Quiche prior: 1/10 weak, 9/10 strong. The exact split is immaterial for the
intuitive-criterion *failure* (`beerQuichePooling_fails_IC`), which is computed entirely from the
prior-independent equilibrium and best-response payoffs. The split is not immaterial for the
pooling assessment to be a PBE: receiver optimality at the on-path message requires the weak
type's prior mass to be at most `1/2` (so that fighting, worth `2·p_weak − 1`, is suboptimal), which
the `1/10` weight comfortably satisfies. -/
def beerQuichePrior : FinDist (Fin 2) :=
  ⟨fun θ => if θ = weak then (1 : ℝ) / 10 else 9 / 10,
    fun θ => by
      change 0 ≤ if θ = weak then (1 : ℝ) / 10 else 9 / 10
      split_ifs <;> norm_num,
    by
      change ∑ θ, (if θ = weak then (1 : ℝ) / 10 else 9 / 10) = 1
      simp [Fin.sum_univ_two, weak]
      norm_num⟩

/-- Sender's payoff in the Beer-Quiche game.

* Intrinsic breakfast preference: `+1` if a strong patron orders beer or a weak patron orders
  quiche; otherwise `0`.
* Fight penalty: `-2` if the bully fights, else `0`.

Total payoff is intrinsic plus fight-penalty. -/
def beerQuicheSenderPayoff (θ : Fin 2) (m : Fin 2) (a : Fin 2) : ℝ :=
  let intrinsic : ℝ := if (θ = strong ∧ m = beer) ∨ (θ = weak ∧ m = quiche) then 1 else 0
  let fightCost : ℝ := if a = fight then -2 else 0
  intrinsic + fightCost

/-- Receiver's payoff in the Beer-Quiche game. The bully gains `+1` for fighting the weak type,
loses `1` for fighting the strong type, and gets `0` for not fighting. -/
def beerQuicheReceiverPayoff (θ : Fin 2) (_m : Fin 2) (a : Fin 2) : ℝ :=
  if a = fight then (if θ = weak then 1 else -1) else 0

/-- The Cho-Kreps Beer-Quiche signaling game. Built via `SignalingGame.mkFin` and marked `abbrev`
so that the carrier types `beerQuiche.{Theta,Msg,Act}` reduce to `Fin 2` for instance synthesis;
downstream proofs can use `FinDist.pure_apply_self` directly without `change` casts. -/
abbrev beerQuiche : SignalingGame :=
  SignalingGame.mkFin 2 2 2 beerQuichePrior fun
    | .sender,   θ, m, a => beerQuicheSenderPayoff θ m a
    | .receiver, θ, m, a => beerQuicheReceiverPayoff θ m a

/-! ## Game-Specific Helper Lemmas

Point-mass and `Fin 2` mass-evaluation facts live upstream: `FinDist.pure_apply_self`,
`FinDist.pure_apply_ne`, `FinDist.pure_pmf`, `FinDist.sum_pmf_two`. -/

/-- The two prior masses: Weak gets `1/10`, strong gets `9/10`. -/
private lemma bq_prior_val (θ : Fin 2) :
    (beerQuichePrior : FinDist (Fin 2)).pmf θ = if θ = weak then (1 : ℝ) / 10 else 9 / 10 := rfl

/-- The fight penalty caps the sender's payoff under *fight*: Intrinsic is at most `1` and the `-2`
fight penalty drops it to at most `-1`. -/
private lemma beerQuicheSenderPayoff_fight_le (θ m : Fin 2) :
    beerQuicheSenderPayoff θ m fight ≤ -1 := by
  simp only [beerQuicheSenderPayoff, if_true]
  split_ifs <;> norm_num

/-- Under *not fight* the sender's payoff is nonnegative: The intrinsic reward is in `{0, 1}` and
there is no fight penalty. -/
private lemma beerQuicheSenderPayoff_notFight_nonneg (θ m : Fin 2) :
    0 ≤ beerQuicheSenderPayoff θ m notFight := by
  simp only [beerQuicheSenderPayoff, show (notFight : Fin 2) ≠ fight from by decide, if_false]
  split_ifs <;> norm_num

/-! ## Best-Response Payoffs: The Cho-Kreps Simplification

Because the receiver's payoff is message-independent and both pure actions are best responses to
*some* belief (`fight` to `pure weak`, `notFight` to `pure strong`), the receiver's best-response
set is the full action set at every message. The sender's best-case deviation payoff is then the
maximum payoff-table entry over both receiver actions, which — since fighting costs `2` — is always
the *not fight* entry. This recovers the textbook Cho-Kreps reduction once and for all. -/

/-- Both receiver actions are best responses to *some* belief on `Θ` at every message: `fight` is a
best response to `pure weak` (receiver gains `1` vs `0`), and `notFight` is a best response to
`pure strong` (receiver gains `0` vs `-1`). Therefore `BR(univ, m)` is the full action set. -/
private lemma beerQuiche_possibleReceiverActions_eq_univ (m : beerQuiche.Msg) :
    beerQuiche.possibleReceiverActions Set.univ m = Set.univ := by
  ext a
  refine ⟨fun _ => Set.mem_univ _, fun _ => ?_⟩
  fin_cases a
  · -- `a = notFight`. Witness: belief `pure strong` (not fighting the strong type is optimal).
    refine beerQuiche.mem_possibleReceiverActions_of_pure_belief (Set.mem_univ strong)
      (beerQuiche.isReceiverBestResponse_pure_iff.mpr fun a' => ?_)
    fin_cases a' <;> norm_num [beerQuicheReceiverPayoff, strong, weak, notFight, fight]
  · -- `a = fight`. Witness: belief `pure weak` (fighting the weak type is optimal).
    refine beerQuiche.mem_possibleReceiverActions_of_pure_belief (Set.mem_univ weak)
      (beerQuiche.isReceiverBestResponse_pure_iff.mpr fun a' => ?_)
    fin_cases a' <;> norm_num [beerQuicheReceiverPayoff, weak, notFight, fight]

/-- The sender's best-response payoff at any message is the *not fight* payoff-table entry: With the
receiver best-response set equal to the full action set, the best-case deviation is the supremum
`max (payoff … notFight) (payoff … fight)`, and fighting always costs `2`, so *not fight* wins. -/
private lemma beerQuiche_bestResponsePayoff_eq (θ m : Fin 2) :
    beerQuiche.bestResponsePayoff Set.univ θ m = beerQuicheSenderPayoff θ m notFight := by
  rw [beerQuiche.bestResponsePayoff_eq_iSup_of_univ
      (beerQuiche_possibleReceiverActions_eq_univ m) θ,
    iSup_fin_two (fun act => beerQuiche.payoff .sender θ m act),
    max_eq_left (by
      -- `fight` is never the better message-response: it costs `2` relative to `notFight`.
      have h1 := beerQuicheSenderPayoff_fight_le θ m
      have h2 := beerQuicheSenderPayoff_notFight_nonneg θ m
      change beerQuicheSenderPayoff θ m fight ≤ beerQuicheSenderPayoff θ m notFight
      linarith)]

/-! ## The Shared Pooling Pattern

Both Beer-Quiche pooling equilibria fit one template, parameterized by the pooling message `m₀`:

* the sender pools on `m₀` (`hσ`);
* the receiver does not fight `m₀` and fights every other message (`hR`);
* the belief is the prior at `m₀` and the point mass on *weak* everywhere else (`hbel`).

The following lemmas prove the equilibrium payoff, the deterministic payoff evaluation, and the PBE
property *once* for any assessment matching this template. Each named assessment then discharges
`hσ`, `hR`, `hbel` by `rfl`. -/

/-- Against the templated receiver, the sender's expected payoff at message `m` is a single
payoff-table entry, taken at the receiver's pure action there (`notFight` at `m₀`, else `fight`). -/
private lemma beerQuiche_pooling_senderExpectedPayoff
    {m₀ : Fin 2} {a : beerQuiche.SignalingAssessment}
    (hR : ∀ m, a.receiverStrategy m =
      if m = m₀ then FinDist.pure notFight else FinDist.pure fight)
    (θ m : Fin 2) :
    beerQuiche.senderExpectedPayoff a.receiverStrategy θ m =
      beerQuicheSenderPayoff θ m (if m = m₀ then notFight else fight) := by
  by_cases hm : m = m₀
  · rw [beerQuiche.senderExpectedPayoff_pure_receiver
        (show a.receiverStrategy m = FinDist.pure notFight by rw [hR m, if_pos hm]) θ, if_pos hm]
  · rw [beerQuiche.senderExpectedPayoff_pure_receiver
        (show a.receiverStrategy m = FinDist.pure fight by rw [hR m, if_neg hm]) θ, if_neg hm]

/-- A pooling type's equilibrium payoff is its on-path (`notFight`) payoff-table entry at `m₀`. -/
private lemma beerQuiche_pooling_equilibriumPayoff
    {m₀ : Fin 2} {a : beerQuiche.SignalingAssessment}
    (hσ : ∀ θ, a.senderStrategy θ = FinDist.pure m₀)
    (hR : ∀ m, a.receiverStrategy m =
      if m = m₀ then FinDist.pure notFight else FinDist.pure fight)
    (θ : Fin 2) :
    beerQuiche.equilibriumPayoff a θ = beerQuicheSenderPayoff θ m₀ notFight := by
  rw [beerQuiche.equilibriumPayoff_pooling hσ θ,
    beerQuiche_pooling_senderExpectedPayoff hR θ m₀, if_pos rfl]

/-- **The shared pooling PBE.** Any assessment fitting the Beer-Quiche pooling template is a perfect
Bayesian equilibrium.

* *Bayes consistency.* `m₀` is the only on-path message and its posterior is the prior — exactly the
  templated belief. Off-path beliefs are unconstrained.
* *Sender optimality.* On-support is `m₀` (not fought, payoff `≥ 0`); any other message is fought
  (payoff `≤ -1`), so no deviation helps.
* *Receiver optimality.* At `m₀` (belief = prior): Fighting loses `2·p_weak − 1 = -4/5 < 0`, so not
  fighting is optimal. Off path (belief = pure weak): Fighting the weak type gains `1 > 0`. -/
private lemma beerQuiche_pooling_isSignalingPBE
    {m₀ : Fin 2} {a : beerQuiche.SignalingAssessment}
    (hσ : ∀ θ, a.senderStrategy θ = FinDist.pure m₀)
    (hR : ∀ m, a.receiverStrategy m =
      if m = m₀ then FinDist.pure notFight else FinDist.pure fight)
    (hbel : ∀ m, a.belief m = if m = m₀ then beerQuichePrior else FinDist.pure weak) :
    beerQuiche.IsSignalingPBE a := by
  have hbel₀ : a.belief m₀ = beerQuichePrior := by rw [hbel m₀, if_pos rfl]
  refine beerQuiche.isSignalingPBE_of_pure a
    (beerQuiche.pooling_bayesConsistent hσ hbel₀) ?_ ?_
  · -- Sender optimality: the on-support message is `m₀`; deviations are fought.
    intro θ m hm m'
    have hmm : m = m₀ := by
      by_contra hne
      rw [hσ θ, FinDist.pure_apply_ne (fun h => hne h.symm)] at hm
      exact lt_irrefl _ hm
    rw [hmm, beerQuiche_pooling_senderExpectedPayoff hR θ m',
      beerQuiche_pooling_senderExpectedPayoff hR θ m₀, if_pos rfl]
    rcases eq_or_ne m' m₀ with hm' | hm'
    · subst hm'; exact le_of_eq (by rw [if_pos rfl])
    · rw [if_neg hm']
      calc beerQuicheSenderPayoff θ m' fight ≤ (-1 : ℝ) := beerQuicheSenderPayoff_fight_le θ m'
        _ ≤ 0 := by norm_num
        _ ≤ beerQuicheSenderPayoff θ m₀ notFight := beerQuicheSenderPayoff_notFight_nonneg θ m₀
  · -- Receiver optimality: at `m₀` not fighting beats fighting against the prior; off path the
    -- point belief on weak makes fighting optimal.
    intro m act hact act'
    by_cases hm : m = m₀
    · have hbelm : a.belief m = beerQuichePrior := by rw [hbel m, if_pos hm]
      have hactnf : act = notFight := by
        by_contra hne
        rw [hR m, if_pos hm, FinDist.pure_apply_ne (fun h => hne h.symm)] at hact
        exact lt_irrefl _ hact
      subst hactnf
      simp only [SignalingGame.receiverPosteriorPayoff_eq_expect, hbelm]
      rw [FinDist.expect_eq_sum, FinDist.expect_eq_sum, Fin.sum_univ_two, Fin.sum_univ_two,
        bq_prior_val, bq_prior_val]
      fin_cases act' <;> norm_num [beerQuicheReceiverPayoff, weak, strong, notFight, fight]
    · have hbelm : a.belief m = FinDist.pure (α := Fin 2) weak := by rw [hbel m, if_neg hm]
      have hactf : act = fight := by
        by_contra hne
        rw [hR m, if_neg hm, FinDist.pure_apply_ne (fun h => hne h.symm)] at hact
        exact lt_irrefl _ hact
      subst hactf
      simp only [SignalingGame.receiverPosteriorPayoff_eq_expect, hbelm, FinDist.expect_pure]
      fin_cases act' <;> norm_num [beerQuicheReceiverPayoff, weak, strong, notFight, fight]

/-! ## The All-Quiche Pooling Assessment -/

/-- The pooling sender strategy: Both types deterministically order quiche. -/
def beerQuichePoolingSender : beerQuiche.SenderMixedStrategy :=
  fun _ => FinDist.pure quiche

/-- The receiver's mixed strategy: Do not fight after quiche; fight after beer. The bully threatens
to fight any off-path beer order, which is what sustains the pooling. -/
def beerQuichePoolingReceiver : beerQuiche.ReceiverMixedStrategy :=
  fun m => if m = quiche then FinDist.pure notFight else FinDist.pure fight

/-- The off-path belief: At the on-path message quiche, the receiver retains the prior; at the
off-path message beer, the receiver assigns probability one to the *weak* type. This is the
"unreasonable" belief that the intuitive criterion rejects. -/
def beerQuichePoolingBelief : beerQuiche.ReceiverBelief :=
  fun m => if m = quiche then beerQuichePrior else FinDist.pure weak

/-- The candidate pooling assessment: Pooling sender strategy, threatening receiver strategy, and
the unreasonable off-path belief. -/
def beerQuichePooling : beerQuiche.SignalingAssessment where
  senderStrategy   := beerQuichePoolingSender
  receiverStrategy := beerQuichePoolingReceiver
  belief           := beerQuichePoolingBelief

/-! ## Basic Properties of the Pooling Assessment -/

/-- Both types order quiche with probability one — i.e. `beerQuichePooling` is a pooling assessment
in the sense of `SignalingGame.IsPooling`. -/
theorem beerQuichePooling_isPooling :
    beerQuiche.IsPooling beerQuichePooling :=
  beerQuiche.isPooling_of_pure fun _ => rfl

/-- *Beer* is off-path under the pooling assessment: Neither type orders beer. -/
theorem beerQuichePooling_beer_isOffPath :
    beerQuiche.isOffPath beerQuichePooling beer :=
  beerQuiche.isOffPath_pooling (fun _ => rfl) (by decide)

/-! ## Equilibrium Payoffs and Best-Response Payoffs at Beer -/

/-- The weak type's equilibrium payoff under pooling is `+1`: Weak orders quiche (intrinsic `+1`)
and is not fought (no penalty). -/
theorem beerQuichePooling_equilibriumPayoff_weak :
    beerQuiche.equilibriumPayoff beerQuichePooling weak = 1 := by
  rw [beerQuiche_pooling_equilibriumPayoff (m₀ := quiche) (fun _ => rfl) (fun _ => rfl)]
  norm_num [beerQuicheSenderPayoff, weak, quiche, notFight, fight]

/-- The strong type's equilibrium payoff under pooling is `0`: Strong orders quiche (intrinsic `0`)
and is not fought (no penalty). -/
theorem beerQuichePooling_equilibriumPayoff_strong :
    beerQuiche.equilibriumPayoff beerQuichePooling strong = 0 := by
  rw [beerQuiche_pooling_equilibriumPayoff (m₀ := quiche) (fun _ => rfl) (fun _ => rfl)]
  norm_num [beerQuicheSenderPayoff, strong, quiche, notFight, fight]

/-- The weak type's best-response payoff at beer is `0`: This is the *best payoff the weak deviator
could obtain* by ordering beer. Weak's intrinsic payoff from beer is zero and fighting only lowers
it, so the supremum is the *not fight* entry `0`. -/
theorem beerQuiche_bestResponsePayoff_weak_beer :
    beerQuiche.bestResponsePayoff Set.univ weak beer = 0 := by
  rw [beerQuiche_bestResponsePayoff_eq]
  norm_num [beerQuicheSenderPayoff, weak, beer, notFight, fight]

/-- The strong type's best-response payoff at beer is `+1`: Strong's intrinsic payoff from beer is
`+1`, preserved by the *not fight* best response; the supremum is `1`. -/
theorem beerQuiche_bestResponsePayoff_strong_beer :
    beerQuiche.bestResponsePayoff Set.univ strong beer = 1 := by
  rw [beerQuiche_bestResponsePayoff_eq]
  norm_num [beerQuicheSenderPayoff, strong, beer, notFight, fight]

/-- The weak type is equilibrium-dominated at beer: Equilibrium payoff `1 > 0 =` best-response
payoff. The weak type can never improve by deviating to beer. -/
theorem beerQuichePooling_weak_dominated_at_beer :
    beerQuiche.equilibriumDominated beerQuichePooling beer weak := by
  unfold SignalingGame.equilibriumDominated
  rw [beerQuichePooling_equilibriumPayoff_weak, beerQuiche_bestResponsePayoff_weak_beer]
  norm_num

/-- The strong type is not equilibrium-dominated at beer: Equilibrium payoff `0` does not
exceed the best-response payoff `1`. The strong type has a potential incentive to deviate. -/
theorem beerQuichePooling_strong_not_dominated_at_beer :
    ¬ beerQuiche.equilibriumDominated beerQuichePooling beer strong := by
  unfold SignalingGame.equilibriumDominated
  rw [beerQuichePooling_equilibriumPayoff_strong, beerQuiche_bestResponsePayoff_strong_beer]
  -- `¬ (0 > 1)`, just numerical.
  norm_num

/-! ## Belief Evaluation Simp Lemma (All-Quiche Assessment) -/

/-- The all-quiche pooling belief at *beer* is the point mass on *weak*: Beer is off-path, so the
belief is the unreasonable off-path belief `FinDist.pure weak`. -/
@[simp]
lemma beerQuichePooling_belief_beer :
    beerQuichePooling.belief beer = FinDist.pure (α := Fin 2) weak := by
  change (if (beer : Fin 2) = quiche then beerQuichePrior else FinDist.pure weak) = _
  rw [if_neg (by decide : (beer : Fin 2) ≠ quiche)]

/-! ## The Headline Theorem: Failure of the Intuitive Criterion -/

/-- **Cho-Kreps (1987).** The candidate pooling assessment for Beer-Quiche does not survive the
intuitive criterion.

*Proof.* The criterion's belief restriction at the off-path message *beer*, applied to the weak
type, would demand `(belief beer).pmf weak = 0` (since weak is equilibrium-dominated at beer). But
by construction the off-path belief assigns probability one to weak: `(belief beer).pmf weak = 1`.
These cannot both hold, so the belief restriction fails — and with it the bundled refinement,
regardless of whether the assessment is a PBE. -/
theorem beerQuichePooling_fails_IC :
    ¬ beerQuiche.SurvivesIntuitiveCriterion beerQuichePooling := by
  intro hic
  -- Apply the belief restriction at off-path message `beer`, supplying the strong type as the
  -- non-dominated witness, and apply to the dominated weak type.
  have h_nonempty : ∃ θ, ¬ beerQuiche.equilibriumDominated beerQuichePooling beer θ :=
    ⟨strong, beerQuichePooling_strong_not_dominated_at_beer⟩
  -- Use the named API: the intuitive criterion assigns zero belief to dominated types.
  have h_zero : (beerQuichePooling.belief beer).pmf weak = 0 :=
    beerQuiche.intuitiveCriterion_eliminates_dominated_types
      beerQuichePooling beer beerQuichePooling_beer_isOffPath h_nonempty hic.2
      weak beerQuichePooling_weak_dominated_at_beer
  -- But our pooling belief is `pure weak` at beer, so its mass at weak is one.
  have h_one : (beerQuichePooling.belief beer).pmf weak = 1 := by
    simp
  -- `0 = 1` from the two equalities, impossible.
  linarith [h_zero, h_one]

/-! ## The All-Quiche Pooling Assessment Is a PBE -/

/-- **The all-quiche pooling assessment is a perfect Bayesian equilibrium.** The intuitive
criterion story needs this: The point of `beerQuichePooling_fails_IC` is that an *actual PBE* dies
under the refinement. The proof is one instantiation of the shared pooling template
`beerQuiche_pooling_isSignalingPBE` at `m₀ = quiche`; the three structural hypotheses (pure pooling,
templated receiver, templated belief) hold by `rfl`.

* *Bayes consistency.* Quiche is the only on-path message and its posterior is the prior. Beer has
  marginal probability `0`, so its belief is unconstrained.
* *Sender optimality.* Weak: Equilibrium `1` (quiche, not fought) vs. beer deviation `0 - 2 = -2`.
  Strong: Equilibrium `0` vs. beer deviation `1 - 2 = -1`.
* *Receiver optimality.* At quiche (belief = prior): Fighting loses
  `1/10 · 1 + 9/10 · (-1) = -4/5 < 0`. At beer (belief = pure weak): Fighting gains `1 > 0`. -/
theorem beerQuichePooling_isSignalingPBE :
    beerQuiche.IsSignalingPBE beerQuichePooling :=
  beerQuiche_pooling_isSignalingPBE (m₀ := quiche) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- The all-quiche pooling assessment is a pooling PBE (bundled form). -/
theorem beerQuichePooling_isPoolingPBE :
    beerQuiche.IsPoolingPBE beerQuichePooling :=
  ⟨beerQuichePooling_isSignalingPBE, beerQuichePooling_isPooling⟩

/-! ## The All-Beer Pooling Assessment: The PBE That Survives the Criterion -/

/-- The all-beer pooling sender strategy: Both types deterministically order beer. -/
def beerQuicheBeerPoolingSender : beerQuiche.SenderMixedStrategy :=
  fun _ => FinDist.pure beer

/-- The all-beer receiver strategy: Do not fight after beer; fight after the off-path quiche. -/
def beerQuicheBeerPoolingReceiver : beerQuiche.ReceiverMixedStrategy :=
  fun m => if m = beer then FinDist.pure notFight else FinDist.pure fight

/-- The all-beer belief system: The prior at the on-path message beer; probability one on *weak* at
the off-path message quiche. Unlike the all-quiche assessment's off-path belief, this is the
inference the intuitive criterion endorses: Only the weak type could gain from quiche. -/
def beerQuicheBeerPoolingBelief : beerQuiche.ReceiverBelief :=
  fun m => if m = beer then beerQuichePrior else FinDist.pure weak

/-- The all-beer pooling assessment: Both types order beer, the bully fights only the off-path
quiche-eater, believing them weak. -/
def beerQuicheBeerPooling : beerQuiche.SignalingAssessment where
  senderStrategy   := beerQuicheBeerPoolingSender
  receiverStrategy := beerQuicheBeerPoolingReceiver
  belief           := beerQuicheBeerPoolingBelief

/-- The all-beer pooling belief at *quiche* is the point mass on *weak*: Quiche is off-path, so
the belief is the off-path belief `FinDist.pure weak`. -/
@[simp]
lemma beerQuicheBeerPooling_belief_quiche :
    beerQuicheBeerPooling.belief quiche = FinDist.pure (α := Fin 2) weak := by
  change (if (quiche : Fin 2) = beer then beerQuichePrior else FinDist.pure weak) = _
  rw [if_neg (by decide : (quiche : Fin 2) ≠ beer)]

/-- *Quiche* is off-path under the all-beer pooling assessment: Neither type orders quiche. -/
theorem beerQuicheBeerPooling_quiche_isOffPath :
    beerQuiche.isOffPath beerQuicheBeerPooling quiche :=
  beerQuiche.isOffPath_pooling (fun _ => rfl) (by decide)

/-- The weak type's equilibrium payoff under all-beer pooling is `0`: Weak orders beer (intrinsic
`0`) and is not fought (no penalty). -/
theorem beerQuicheBeerPooling_equilibriumPayoff_weak :
    beerQuiche.equilibriumPayoff beerQuicheBeerPooling weak = 0 := by
  rw [beerQuiche_pooling_equilibriumPayoff (m₀ := beer) (fun _ => rfl) (fun _ => rfl)]
  norm_num [beerQuicheSenderPayoff, weak, beer, notFight, fight]

/-- The strong type's equilibrium payoff under all-beer pooling is `+1`: Strong orders beer
(intrinsic `+1`) and is not fought (no penalty). -/
theorem beerQuicheBeerPooling_equilibriumPayoff_strong :
    beerQuiche.equilibriumPayoff beerQuicheBeerPooling strong = 1 := by
  rw [beerQuiche_pooling_equilibriumPayoff (m₀ := beer) (fun _ => rfl) (fun _ => rfl)]
  norm_num [beerQuicheSenderPayoff, strong, beer, notFight, fight]

/-- The weak type's best-response payoff at quiche is `+1`: Weak's intrinsic payoff from quiche is
`+1`, preserved by the *not fight* best response; the supremum is `1`. -/
theorem beerQuiche_bestResponsePayoff_weak_quiche :
    beerQuiche.bestResponsePayoff Set.univ weak quiche = 1 := by
  rw [beerQuiche_bestResponsePayoff_eq]
  norm_num [beerQuicheSenderPayoff, weak, quiche, notFight, fight]

/-- The strong type's best-response payoff at quiche is `0`: Strong's intrinsic payoff from quiche
is `0`, preserved by not fight; the supremum is `0`. -/
theorem beerQuiche_bestResponsePayoff_strong_quiche :
    beerQuiche.bestResponsePayoff Set.univ strong quiche = 0 := by
  rw [beerQuiche_bestResponsePayoff_eq]
  norm_num [beerQuicheSenderPayoff, strong, quiche, notFight, fight]

/-- The strong type is equilibrium-dominated at quiche under all-beer pooling: Equilibrium
payoff `1 > 0 =` best-response payoff. The strong patron can never gain by ordering quiche. -/
theorem beerQuicheBeerPooling_strong_dominated_at_quiche :
    beerQuiche.equilibriumDominated beerQuicheBeerPooling quiche strong := by
  unfold SignalingGame.equilibriumDominated
  rw [beerQuicheBeerPooling_equilibriumPayoff_strong, beerQuiche_bestResponsePayoff_strong_quiche]
  norm_num

/-- The weak type is not equilibrium-dominated at quiche under all-beer pooling: Equilibrium
payoff `0` does not exceed the best-response payoff `1`. The weak type is the one who could
conceivably gain from quiche — which is exactly why believing `weak` at quiche is reasonable. -/
theorem beerQuicheBeerPooling_weak_not_dominated_at_quiche :
    ¬ beerQuiche.equilibriumDominated beerQuicheBeerPooling quiche weak := by
  unfold SignalingGame.equilibriumDominated
  rw [beerQuicheBeerPooling_equilibriumPayoff_weak, beerQuiche_bestResponsePayoff_weak_quiche]
  -- `¬ (0 > 1)`, just numerical.
  norm_num

/-- **The all-beer pooling assessment is a perfect Bayesian equilibrium.** Like the all-quiche
assessment, this is one instantiation of the shared pooling template
`beerQuiche_pooling_isSignalingPBE`, here at `m₀ = beer`.

* *Bayes consistency.* Beer is the only on-path message; the posterior there is the prior. Quiche is
  off-path, so its belief is unconstrained.
* *Sender optimality.* Weak: Equilibrium `0` (beer, not fought) vs. quiche deviation `1 - 2 = -1`.
  Strong: Equilibrium `1` vs. quiche deviation `0 - 2 = -2`.
* *Receiver optimality.* At beer (belief = prior): Fighting loses `-4/5 < 0`. At quiche (belief =
  pure weak): Fighting gains `1 > 0`. -/
theorem beerQuicheBeerPooling_isSignalingPBE :
    beerQuiche.IsSignalingPBE beerQuicheBeerPooling :=
  beerQuiche_pooling_isSignalingPBE (m₀ := beer) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

/-- Both types order beer with probability one — the all-beer assessment is pooling. -/
theorem beerQuicheBeerPooling_isPooling :
    beerQuiche.IsPooling beerQuicheBeerPooling :=
  beerQuiche.isPooling_of_pure fun _ => rfl

/-- The all-beer pooling assessment is a pooling PBE (bundled form). -/
theorem beerQuicheBeerPooling_isPoolingPBE :
    beerQuiche.IsPoolingPBE beerQuicheBeerPooling :=
  ⟨beerQuicheBeerPooling_isSignalingPBE, beerQuicheBeerPooling_isPooling⟩

/-- **Cho-Kreps (1987), the surviving equilibrium.** The all-beer pooling assessment survives the
intuitive criterion: it is a PBE (`beerQuicheBeerPooling_isSignalingPBE`) whose off-path beliefs
satisfy the criterion's belief restriction. Its only off-path message is quiche, where the strong
type is equilibrium-dominated and the belief `pure weak` already assigns the strong type zero mass.
The weak type is not dominated at quiche, so the restriction does not apply to it. Receiver
optimality on the non-dominated set (Cho-Kreps part 2) is then automatic via
`SurvivesIntuitiveCriterion.receiver_optimal_on_nonDominated`. -/
theorem beerQuicheBeerPooling_passes_IC :
    beerQuiche.SurvivesIntuitiveCriterion beerQuicheBeerPooling := by
  refine ⟨beerQuicheBeerPooling_isSignalingPBE, ?_⟩
  -- Belief restriction. Quantify over messages: beer is on-path (vacuous); at quiche only the
  -- strong type is dominated, and `(pure weak).pmf strong = 0`.
  intro m h_offPath _h_exists θ h_dom
  by_cases hm : m = beer
  · -- beer is ON-path under all-beer pooling: its marginal is `1`, contradicting the off-path
    -- hypothesis `isOffPath beer`, which by definition says the marginal is `0`.
    subst hm
    rw [SignalingGame.isOffPath,
      beerQuiche.marginalProb_pooling (σ := beerQuicheBeerPooling.senderStrategy)
      (m₀ := beer) (fun _ => rfl) beer, FinDist.pure_apply_self] at h_offPath
    norm_num at h_offPath
  · -- m = quiche: the off-path message. Only the strong type is dominated there.
    have hmquiche : m = quiche := by fin_cases m <;> simp_all
    subst hmquiche
    -- The belief at quiche is `pure weak`.
    rw [beerQuicheBeerPooling_belief_quiche]
    -- Split on the dominated type: weak is not dominated (contradiction), strong has zero mass.
    fin_cases θ
    · -- θ = weak: contradicts `weak is not dominated at quiche`.
      exact absurd h_dom beerQuicheBeerPooling_weak_not_dominated_at_quiche
    · -- θ = strong: `(pure weak).pmf strong = 0`.
      exact FinDist.pure_apply_ne (by decide : (weak : Fin 2) ≠ strong)

/-! ## No Separating PBE Exists -/

/-- **Beer-Quiche has no separating equilibrium.** In a separating assessment each type sends a
distinct pure message, so Bayes consistency forces the receiver to learn the type: The belief at
the weak type's message is `pure weak`, making *fight* the receiver's unique best response there,
while the belief at the strong type's message is `pure strong`, forcing *not fight*. But then the
weak type earns `breakfast - 2 ≤ 1 - 2 = -1` in equilibrium and could instead mimic the strong
type's message for a payoff of at least `0 > -1` — contradicting sender optimality. -/
theorem beerQuiche_not_isSeparatingPBE (a : beerQuiche.SignalingAssessment) :
    ¬ beerQuiche.IsSeparatingPBE a := by
  rintro ⟨hPBE, hSep⟩
  have hBayes := hPBE.1
  -- Sender strategies of the two types, as `FinDist (Fin 2)`.
  set dw : FinDist (Fin 2) := a.senderStrategy weak with hdw
  set ds : FinDist (Fin 2) := a.senderStrategy strong with hds
  -- Separation forces each type pure on a distinct message
  -- (`FinDist.eq_pure_pair_of_disjoint_fin_two`).
  obtain ⟨mw, ms, hmne, hdw_pure, hds_pure⟩ :=
    FinDist.eq_pure_pair_of_disjoint_fin_two (d₁ := dw) (d₂ := ds)
      (fun m => hSep weak strong (by decide) m)
  have hdw_mw : dw.pmf mw = 1 := by rw [hdw_pure]; exact FinDist.pure_apply_self mw
  have hds_ms : ds.pmf ms = 1 := by rw [hds_pure]; exact FinDist.pure_apply_self ms
  have hdw_ms : dw.pmf ms = 0 := by rw [hdw_pure]; exact FinDist.pure_apply_ne hmne
  have hds_mw : ds.pmf mw = 0 := by rw [hds_pure]; exact FinDist.pure_apply_ne (Ne.symm hmne)
  -- Bayes consistency, in usable form.
  have hBC : beerQuiche.signalingBayesConsistent a := hBayes
  -- The prior has full support, so each type's message is on-path.
  have hprior_w : 0 < beerQuiche.prior.pmf weak := by rw [bq_prior_val]; norm_num
  have hprior_s : 0 < beerQuiche.prior.pmf strong := by
    rw [bq_prior_val]
    norm_num [show (strong : Fin 2) ≠ weak from by decide]
  -- Bayes fixes the belief at mw to `pure weak` and at ms to `pure strong`
  -- (`IsSeparating.belief_eq_pure` — the receiver learns the type).
  have hbel_mw : a.belief mw = FinDist.pure (α := Fin 2) weak :=
    hSep.belief_eq_pure hBC hprior_w (by rw [← hdw, hdw_mw]; norm_num)
  have hbel_ms : a.belief ms = FinDist.pure (α := Fin 2) strong :=
    hSep.belief_eq_pure hBC hprior_s (by rw [← hds, hds_ms]; norm_num)
  -- The PBE receiver best-responds to the point belief `pure weak` at mw
  -- (`IsSignalingPBE.receiver_bestResponse`), where fighting pays 1 and not fighting 0 —
  -- so the fight mass must be full.
  have hrecv_mw_fight : (a.receiverStrategy mw).pmf fight = 1 := by
    have hbr := hPBE.receiver_bestResponse mw fight
    rw [hbel_mw] at hbr
    unfold SignalingGame.receiverPosteriorPayoff at hbr
    simp_rw [FinDist.expect_pure] at hbr
    rw [FinDist.expect_eq_sum, Fin.sum_univ_two] at hbr
    -- hbr : 1 ≤ e₀ · payoff_R(weak, notFight) + e₁ · payoff_R(weak, fight) = e₁.
    norm_num [beerQuicheReceiverPayoff, weak, fight] at hbr
    exact le_antisymm ((a.receiverStrategy mw).prob_le_one fight) hbr
  -- Dually, the point belief `pure strong` at ms makes fighting pay `-1` against
  -- not-fighting's `0`, so the fight mass must vanish and sum-one fills notFight.
  have hrecv_ms_notFight : (a.receiverStrategy ms).pmf notFight = 1 := by
    have hbr := hPBE.receiver_bestResponse ms notFight
    rw [hbel_ms] at hbr
    unfold SignalingGame.receiverPosteriorPayoff at hbr
    simp_rw [FinDist.expect_pure] at hbr
    rw [FinDist.expect_eq_sum, Fin.sum_univ_two] at hbr
    -- hbr : 0 ≤ e₀ · 0 + e₁ · (-1), i.e. the fight mass is nonpositive.
    norm_num [beerQuicheReceiverPayoff, strong, weak, notFight, fight] at hbr
    have hf0 : (a.receiverStrategy ms).pmf 1 = 0 :=
      le_antisymm (by linarith) ((a.receiverStrategy ms).nonneg 1)
    have hsum := FinDist.sum_pmf_two (a.receiverStrategy ms)
    change (a.receiverStrategy ms).pmf 0 = 1
    linarith
  -- `IsSignalingPBE.sender_bestResponse` bounds the weak type's ms-deviation payoff by
  -- its equilibrium payoff. Both collapse along point masses: the equilibrium payoff is the
  -- mw-payoff under fight (≤ -1), the deviation payoff is the ms-payoff under notFight (≥ 0).
  have hbr := hPBE.sender_bestResponse weak ms
  have heq_val : beerQuiche.equilibriumPayoff a weak = beerQuicheSenderPayoff weak mw fight := by
    unfold SignalingGame.equilibriumPayoff
    rw [← hdw, FinDist.expect_of_pmf_eq_one hdw_mw]
    unfold SignalingGame.senderExpectedPayoff
    -- `rw` closes the residue by rfl: `payoff .sender` is definitionally the sender table.
    rw [FinDist.expect_of_pmf_eq_one hrecv_mw_fight]
  have hdev_val : beerQuiche.senderExpectedPayoff a.receiverStrategy weak ms =
      beerQuicheSenderPayoff weak ms notFight := by
    unfold SignalingGame.senderExpectedPayoff
    rw [FinDist.expect_of_pmf_eq_one hrecv_ms_notFight]
  rw [heq_val, hdev_val] at hbr
  -- deviation ≥ 0 > -1 ≥ equilibrium, contradicting the best-response bound.
  have h1 := beerQuicheSenderPayoff_fight_le weak mw
  have h2 := beerQuicheSenderPayoff_notFight_nonneg weak ms
  linarith

end EconlibExamples.GameTheory.BeerQuiche

end
