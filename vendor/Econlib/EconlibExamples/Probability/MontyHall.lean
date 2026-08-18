/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# The Monty Hall Problem: A Tour of the Finite-Distribution Toolkit

A contestant faces three doors. Behind one is a valuable prize; behind the others nothing. The
contestant picks **door 0**. The host — who knows where the prize is — opens one of the two other
doors to reveal nothing, then offers a switch. The classical conclusion is that switching wins with
probability `2/3` against the `1/3` of standing pat.

The probability content is elementary, which is exactly why the problem makes a good tutorial: it is
small enough to compute by hand, so every step can be checked, yet it touches most of the finite
probability toolkit. We deliberately solve it several ways, each exercising a different part of the
`FinDist` API, and we close by connecting the finite computation to the measure-theoretic carrier it
embeds into. The point is not the answer — it is to see the pieces fit together.

The toolkit on display:

* `FinDist.uniform` and the `finDist% ![...]` literal for building distributions with no side
  conditions to discharge;
* `FinDist.posterior` / `FinDist.posterior_apply`, the dedicated finite Bayes operator;
* `FinDist.expect`, recasting the contestant's choice as expected-payoff maximization;
* `FinDist.bind` and `FinDist.map`, assembling the joint distribution compositionally, with
  `FinDist.conditionalOn` recovering the posterior by conditioning that joint — so the Bayes
  operator is exhibited as a composition of generic operations rather than a black box;
* `FinDist.total_probability`, the consistency check that the posterior beliefs average back to the
  prior;
* `FinDist.expect_eq_probDist_expect`, identifying the finite-sum expectation with the Bochner
  integral against the `ProbDist` that the carrier embeds into.

## The model

The hidden state is the prize's location, an element of `Fin 3`. The prior is uniform. The signal is
which door the host opens, also an element of `Fin 3`. The host's behavior is the likelihood
`hostOpens : Fin 3 → FinDist (Fin 3)`:

* Prize behind **0** (the contestant's door): the host may open either door `1` or `2`, each with
  probability `1/2`;
* Prize behind **1**: the host must open door `2`;
* Prize behind **2**: the host must open door `1`.

We condition throughout on the observation that the host opens **door 2**.
-/

noncomputable section

namespace EconlibExamples.Probability.MontyHall

open Econlib.Probability

/-! ## The model

The model definitions below are marked `@[simp]` so that the evaluation proofs reduce to plain
arithmetic. Together with the library's `findist_eval` simp set (which carries the `FinDist`
evaluation lemmas such as `uniform_apply` and `expect_eq_sum`) and the `@[simp]` `Matrix.cons_val_*`
lemmas that evaluate `finDist% ![...]` vectors coordinatewise, `simp [findist_eval] <;> norm_num`
unfolds each distribution and discharges the resulting rational arithmetic. -/

/-- The uniform prior over the car's location in `Fin 3`. -/
@[simp] def prior : FinDist (Fin 3) := FinDist.uniform

/-- The host's behavior when the car is behind the contestant's door `0`: open either goat door
(`1` or `2`) with equal probability. -/
@[simp] def hostCar0 : FinDist (Fin 3) :=
  finDist% ![0, 1/2, 1/2]

/-- The host's behavior when the car is behind door `1`: forced to open door `2`. -/
@[simp] def hostCar1 : FinDist (Fin 3) :=
  finDist% ![0, 0, 1]

/-- The host's behavior when the car is behind door `2`: forced to open door `1`. -/
@[simp] def hostCar2 : FinDist (Fin 3) :=
  finDist% ![0, 1, 0]

/-- The host's door-opening likelihood as a function of the car's location. -/
@[simp] def hostOpens : Fin 3 → FinDist (Fin 3) := ![hostCar0, hostCar1, hostCar2]

/-! ## The marginal probability of the observed signal -/

/-- The probability that the host opens door `2`, marginalized over the uniform prior, equals
`1/2`. This is the denominator in Bayes' rule, named by `FinDist.signalMarginal`. -/
lemma marginal_opens2 :
    prior.signalMarginal hostOpens 2 = 1 / 2 := by
  simp [Fin.sum_univ_three, findist_eval]
  norm_num

/-- The marginal is strictly positive, so Bayes' rule applies. -/
lemma marginal_opens2_pos :
    0 < prior.signalMarginal hostOpens 2 := by
  rw [marginal_opens2]; norm_num

/-! ## First solution: the dedicated Bayes operator

`FinDist.posterior` takes a prior, a likelihood kernel, an observed signal, and a proof that the
signal has positive marginal probability, and returns the posterior distribution. Its pointwise
formula `FinDist.posterior_apply` is exactly Bayes' rule, `prior · likelihood / marginal`. -/

/-- **Staying loses two-thirds of the time.** Conditional on the host opening door `2`, the car is
behind the contestant's original door `0` with probability only `1/3`. -/
theorem posterior_stay :
    (prior.posterior hostOpens 2 marginal_opens2_pos).pmf 0 = 1 / 3 := by
  simp [Fin.sum_univ_three, findist_eval]
  norm_num

/-- **Switching wins two-thirds of the time.** Conditional on the host opening door `2`, the car is
behind door `1` — the one the contestant would switch to — with probability `2/3`. -/
theorem posterior_switch :
    (prior.posterior hostOpens 2 marginal_opens2_pos).pmf 1 = 2 / 3 := by
  simp [Fin.sum_univ_three, findist_eval]
  norm_num

/-- The posterior strictly favors switching: the probability the car is behind the switch door (`1`)
exceeds the probability it is behind the stay door (`0`). -/
theorem switching_wins :
    (prior.posterior hostOpens 2 marginal_opens2_pos).pmf 0
      < (prior.posterior hostOpens 2 marginal_opens2_pos).pmf 1 := by
  rw [posterior_stay, posterior_switch]; norm_num

/-! ## Second solution: the choice as an expected payoff

A decision maker does not rank doors by posterior probability directly; they maximize expected
payoff. Suppose the prize is a car worth `30000` and a goat is worth `0`. The switching strategy
collects the prize exactly when the car is behind door `1`, and the staying strategy when it is
behind door `0`, so each strategy's value is the expectation of its payoff under the posterior.
`FinDist.expect` computes these as posterior-weighted sums. -/

/-- Payoff to switching to door `1`: the car (worth `30000`) is there, or nothing. -/
@[simp] def switchPayoff : Fin 3 → ℝ := fun car => if car = 1 then 30000 else 0

/-- Payoff to staying on door `0`. -/
@[simp] def stayPayoff : Fin 3 → ℝ := fun car => if car = 0 then 30000 else 0

/-- Switching has expected value `20000`. -/
theorem expected_value_switch :
    (prior.posterior hostOpens 2 marginal_opens2_pos).expect switchPayoff = 20000 := by
  simp [FinDist.expect_eq_sum, Fin.sum_univ_three, findist_eval]
  norm_num

/-- Staying has expected value only `10000`. -/
theorem expected_value_stay :
    (prior.posterior hostOpens 2 marginal_opens2_pos).expect stayPayoff = 10000 := by
  simp [FinDist.expect_eq_sum, Fin.sum_univ_three, findist_eval]
  norm_num

/-- Expected-payoff maximization recommends switching. -/
theorem switching_is_optimal :
    (prior.posterior hostOpens 2 marginal_opens2_pos).expect stayPayoff
      < (prior.posterior hostOpens 2 marginal_opens2_pos).expect switchPayoff := by
  rw [expected_value_stay, expected_value_switch]; norm_num

/-! ## Third solution: building the joint and conditioning it

The dedicated Bayes operator is convenient, but it is not primitive: it is what you get by forming
the joint distribution of (state, signal) and conditioning on the observed signal. This section
builds the joint from the prior and the likelihood with `FinDist.bind` and `FinDist.map`, recovers
the signal marginal as the pushforward `map Prod.snd`, and recovers the posterior over states by
conditioning the joint on the event "door 2 was opened" and pushing forward to the state coordinate.
That the result agrees with `posterior` is the coherence between the generic operations and the
special-purpose one. -/

/-- The joint distribution of (car location, door opened), assembled monadically: draw the car from
the prior, then draw the opened door from the host's likelihood and pair it with the car. -/
@[simp] def joint : FinDist (Fin 3 × Fin 3) :=
  prior.bind (fun car => (hostOpens car).map (Prod.mk car))

/-- The event that the host opened door `2`, as a subset of the joint outcome space. -/
def opened2 : Set (Fin 3 × Fin 3) := {p | p.2 = 2}

instance : DecidablePred (· ∈ opened2) := fun p => decEq p.2 2

/-- The signal marginal recovered from the joint by pushing forward to the door coordinate agrees
with the hand-computed marginal: door `2` is opened with probability `1/2`. -/
theorem joint_signal_marginal :
    (joint.map Prod.snd).pmf 2 = 1 / 2 := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, findist_eval]
  norm_num

/-- The event "door 2 opened" has positive probability under the joint, so conditioning is valid. -/
theorem joint_opened2_pos : 0 < joint.probEvent opened2 := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, opened2, Set.mem_setOf_eq, findist_eval]
  norm_num

/-- **Coherence.** Conditioning the joint on "door 2 opened" and pushing forward to the car
coordinate reproduces, state by state, the posterior delivered by the dedicated Bayes operator. -/
theorem posterior_from_joint (θ : Fin 3) :
    ((joint.conditionalOn opened2 joint_opened2_pos).map Prod.fst).pmf θ
      = (prior.posterior hostOpens 2 marginal_opens2_pos).pmf θ := by
  fin_cases θ <;>
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, opened2, Set.mem_setOf_eq, findist_eval] <;>
    norm_num

/-! ## A consistency check: the law of total probability

Averaging the posterior beliefs over all possible signals, weighted by each signal's marginal
probability, must return the prior. `FinDist.total_probability` is this identity, available for free
on any finite prior and likelihood. -/

/-- The signal-weighted posteriors average back to the uniform prior: each car location is recovered
with its prior probability `1/3`. -/
theorem total_probability_recovers_prior (θ : Fin 3) :
    (∑ s : Fin 3, prior.signalMarginal hostOpens s * (prior.posteriorOrPrior hostOpens s).pmf θ)
      = prior.pmf θ :=
  FinDist.total_probability_signalMarginal prior hostOpens θ

/-! ## Coherence with the measure-theoretic carrier

The whole computation lives on the finite-sum surface, but `FinDist` is not a separate track: it
embeds into `ProbDist`, Mathlib's `ProbabilityMeasure`, via `toProbDist`, and the finite expectation
agrees with the Bochner integral against that measure. `FinDist.expect_eq_probDist_expect` is that
identity, so the `20000` we computed by summing three rationals is literally the integral of the
payoff against the posterior measure — the finite carrier is a specialization of the general one,
not a parallel construction. -/

/-- The expected value of switching, computed in finite sums, equals the Bochner integral of the
payoff against the posterior viewed as a `ProbDist`. -/
theorem expect_switch_eq_integral :
    (prior.posterior hostOpens 2 marginal_opens2_pos).expect switchPayoff
      = (prior.posterior hostOpens 2 marginal_opens2_pos).toProbDist.expect switchPayoff :=
  FinDist.expect_eq_probDist_expect _ _

end EconlibExamples.Probability.MontyHall

end
