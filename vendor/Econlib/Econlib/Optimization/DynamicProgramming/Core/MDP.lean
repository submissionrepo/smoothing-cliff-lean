/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Markov Decision Processes

Defines the core structures for discrete-time infinite-horizon MDPs used in dynamic programing. We
provide three variants: Deterministic (`DetMDP`), finite-state stochastic (`FinMDP`), and general
measure-valued stochastic (`StochMDP`).

## Main definitions

* `DetMDP`: Deterministic MDP with generic state and action types
* `FinMDP`: Finite-state stochastic MDP with `FinDist`-valued transitions
* `StochMDP`: General stochastic MDP with `Measure ℝ`-valued transitions
* `DetPolicy`: Deterministic policy for `DetMDP`
* `FinPolicy`: Stationary policy for `FinMDP`

## Notes

Following Econlib conventions, these are structures, not typeclasses — MDPs are passed explicitly.
`StochMDP` remains specialized to `ℝ`-valued states and actions because `Measure S` requires
`[MeasurableSpace S]` and the integration lemmas in `Stochastic.lean` are built around
Lebesgue/Bochner integrals on `ℝ`; generalizing to arbitrary measurable spaces is a separate effort.

## References

* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press. [https://doi.org/10.2307/j.ctvjnrt76](https://doi.org/10.2307/j.ctvjnrt76).

## Tags

markov decision process, dynamic programing, bellman equation, stochastic control
-/

@[expose] public section

open Econlib.Probability

namespace Econlib.Optimization.DynamicProgramming

/-- A deterministic Markov Decision Process **without** a boundedness assumption on the reward.

This is the carrier for the unbounded principle of optimality (`UnboundedOptimality`), where the
tail term is controlled by an explicit transversality hypothesis rather than a uniform reward
bound. The bounded `DetMDP` extends it by adding `reward_bounded`, so the bounded layer reuses this
data and the operator/plan machinery defined on it.

* `Γ` is the feasibility correspondence: Given state `s`, the set of available actions.
* `reward` is the per-period payoff `u(s, a) : ℝ`.
* `transition` is the deterministic law of motion `s' = f(s, a)`.
* `β` is the discount factor in `[0, 1)`. -/
structure UnboundedDetMDP (S : Type*) (A : Type*) [Nonempty S] where
  /-- Feasibility correspondence: Available actions given state -/
  Γ : S → Set A
  /-- Per-period reward function -/
  reward : S → A → ℝ
  /-- Deterministic transition function: Next state given (state, action) -/
  transition : S → A → S
  /-- Discount factor -/
  β : ℝ
  /-- Discount factor is nonneg -/
  β_nonneg : 0 ≤ β
  /-- Discount factor is strictly less than 1 -/
  β_lt_one : β < 1
  /-- Feasible sets are nonempty -/
  Γ_nonempty : ∀ s, (Γ s).Nonempty

/-- A deterministic Markov Decision Process with state space `S` and action space `A`.

Extends `UnboundedDetMDP` with a uniform reward bound, enabling the Banach (sup-norm) fixed-point
theory and the bounded principle of optimality. -/
structure DetMDP (S : Type*) (A : Type*) [Nonempty S] extends UnboundedDetMDP S A where
  /-- Reward is bounded -/
  reward_bounded : ∃ B : ℝ, ∀ s a, |reward s a| ≤ B

/-- A bounded MDP is in particular an unbounded one (forgetting the reward bound). -/
instance {S A : Type*} [Nonempty S] : Coe (DetMDP S A) (UnboundedDetMDP S A) :=
  ⟨DetMDP.toUnboundedDetMDP⟩

/-- A stochastic MDP with finite state space `Fin n` and generic action space `A`. Transitions are
`FinDist (Fin n)`-valued. -/
structure FinMDP (n : ℕ) (A : Type*) where
  /-- Feasibility correspondence: Available actions given state -/
  Γ : Fin n → Set A
  /-- Per-period reward function -/
  reward : Fin n → A → ℝ
  /-- Stochastic transition: Distribution over next states given (state, action) -/
  transition : Fin n → A → FinDist (Fin n)
  /-- Discount factor -/
  β : ℝ
  /-- Discount factor is nonneg -/
  β_nonneg : 0 ≤ β
  /-- Discount factor is strictly less than 1 -/
  β_lt_one : β < 1
  /-- Feasible sets are nonempty -/
  Γ_nonempty : ∀ s, (Γ s).Nonempty
  /-- Reward is bounded -/
  reward_bounded : ∃ B : ℝ, ∀ (s : Fin n) (a : A), |reward s a| ≤ B

/-- A general stochastic MDP with `ℝ`-valued states and actions and measure-valued transitions. The
deterministic and finite cases embed into this via Dirac measures and `FinDist.toPMF`. -/
structure StochMDP where
  /-- Feasibility correspondence -/
  Γ : ℝ → Set ℝ
  /-- Per-period reward (assumed bounded) -/
  reward : ℝ → ℝ → ℝ
  /-- Stochastic transition kernel -/
  transition : ℝ → ℝ → MeasureTheory.Measure ℝ
  /-- Discount factor -/
  β : ℝ
  /-- Discount factor is nonneg -/
  β_nonneg : 0 ≤ β
  /-- Discount factor is strictly less than 1 -/
  β_lt_one : β < 1
  /-- Feasible sets are nonempty -/
  Γ_nonempty : ∀ s, (Γ s).Nonempty
  /-- Reward is bounded -/
  reward_bounded : ∃ M : ℝ, ∀ s a, |reward s a| ≤ M
  /-- Transitions are probability measures -/
  transition_prob : ∀ s a, MeasureTheory.IsProbabilityMeasure (transition s a)

/-- A deterministic policy: Maps states to feasible actions. -/
def DetPolicy {S : Type*} {A : Type*} [Nonempty S] (M : DetMDP S A) :=
  (s : S) → {a : A // a ∈ M.Γ s}

/-- A stationary stochastic policy for the finite MDP. -/
def FinPolicy (n : ℕ) {A : Type*} (M : FinMDP n A) :=
  (s : Fin n) → {a : A // a ∈ M.Γ s}

end Econlib.Optimization.DynamicProgramming
