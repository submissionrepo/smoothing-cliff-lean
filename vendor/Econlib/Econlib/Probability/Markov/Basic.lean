/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Basic
public import Econlib.Probability.FinDist.Expect
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Finite Markov chains

A **finite Markov chain** on an arbitrary finite state space `α` is a transition kernel assigning
to each state a `FinDist α` over next states. This module provides the one-step and `k`-step
evolution of a distribution, the stationarity predicate, and the one-step conditional expectation
of a payoff.

## Main definitions

* `FiniteMarkovChain α` — finite Markov chain on a finite state space `α`
* `FiniteMarkovChain.step` — one-step evolution of a distribution
* `FiniteMarkovChain.nStep` — `k`-step evolution of a distribution
* `FiniteMarkovChain.IsStationary` — a distribution is left fixed by one step
* `FiniteMarkovChain.StationaryDist` — the subtype of stationary distributions
* `FiniteMarkovChain.IidRows` — all transition rows are equal
* `FiniteMarkovChain.condExp` — conditional expectation of a payoff after one transition

## Main statements

* `FiniteMarkovChain.isStationary_iff` — stationarity expressed as coordinate equations

## Tags

markov chain, transition kernel, stationary distribution
-/

@[expose] public section

open Finset BigOperators

namespace Econlib.Probability

/-- A Markov chain on an arbitrary finite state space. -/
structure FiniteMarkovChain (α : Type*) [Fintype α] [DecidableEq α] where
  /-- Transition kernel: `transition s` is the distribution of next states given state `s`. -/
  transition : α → FinDist α

namespace FiniteMarkovChain

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : FiniteMarkovChain α)

/-- One-step evolution of a distribution: `(step P d)(s') = Σ_s d(s) · Π(s, s')`. -/
noncomputable def step (d : FinDist α) : FinDist α where
  pmf s' := ∑ s, d s * P.transition s s'
  nonneg s' := Finset.sum_nonneg fun s _ =>
      mul_nonneg (d.nonneg s) ((P.transition s).nonneg s')
  sum_one := by
    -- Sum over s' first: each transition row sums to 1, leaving Σ_s d(s) = 1.
    have hrow : ∀ s, ∑ s', P.transition s s' = 1 := fun s => (P.transition s).sum_one
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hrow, mul_one]
    exact d.sum_one

/-- k-step evolution of a distribution. -/
noncomputable def nStep (k : ℕ) (d : FinDist α) : FinDist α :=
  Nat.iterate P.step k d

/-- Zero steps leave the distribution unchanged. -/
@[simp] lemma nStep_zero (d : FinDist α) :
    P.nStep 0 d = d := rfl

/-- One more step is a single `step` applied to the `k`-step evolution. -/
@[simp] lemma nStep_succ (k : ℕ) (d : FinDist α) :
    P.nStep (k + 1) d = P.step (P.nStep k d) :=
  Function.iterate_succ_apply' P.step k d

/-- Conditional expectation of a payoff after one transition from state `s`. -/
noncomputable def condExp (s : α) (f : α → ℝ) : ℝ :=
  (P.transition s).expect f

/-- A distribution is stationary if one step leaves it fixed. -/
def IsStationary (μ : FinDist α) : Prop :=
  P.step μ = μ

/-- The subtype of stationary distributions. -/
def StationaryDist :=
  {μ : FinDist α // P.IsStationary μ}

/-- All transition rows are equal. -/
def IidRows : Prop :=
  ∀ s t, P.transition s = P.transition t

/-- Stationarity as coordinate equations. -/
lemma isStationary_iff (μ : FinDist α) :
    P.IsStationary μ ↔ ∀ s', ∑ s, μ s * P.transition s s' = μ s' := by
  constructor
  · intro h s'
    have := congr_arg (fun d : FinDist α => d s') h
    simpa [IsStationary, step] using this
  · intro h
    ext s'
    simpa [IsStationary, step] using h s'

end FiniteMarkovChain

end Econlib.Probability
