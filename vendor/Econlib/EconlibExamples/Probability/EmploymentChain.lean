/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# A Two-State Employment Chain: Ergodicity and the Long-Run Unemployment Rate

A worker's labor-market status follows a two-state Markov chain: *employed* workers separate into
unemployment at rate `1/10` each period, and *unemployed* workers find jobs at rate `3/10`. This is
the textbook reduced-form model behind the steady-state unemployment rate. We compute the
stationary distribution explicitly and prove the three ergodic facts that make it the long-run
description of the economy: It is stationary, it is the unique stationary distribution, and every
initial distribution converges to it geometrically.

This is the worked tutorial for `Econlib.Probability.FiniteMarkovChain` and the ergodic theorems in
`Econlib.Probability.Markov.Ergodic`.

## The model

States are `Fin 2`: `0 = employed`, `1 = unemployed`. The transition kernel is

* from **employed**: Stay employed `9/10`, separate to unemployment `1/10`;
* from **unemployed**: Find a job `3/10`, stay unemployed `7/10`.

## The mathematics

The steady-state unemployment rate solves the flow-balance equation
`u·(find rate) = (1-u)·(separation rate)`, giving
`u* = separation / (separation + find) = (1/10) / (1/10 + 3/10) = 1/4`. So the stationary
distribution is `(employed, unemployed) = (3/4, 1/4)`. Because every transition probability is
strictly positive, Doeblin's condition holds: The step operator is a total-variation contraction,
so the stationary law is unique and globally attracting at a geometric rate.

## Main definitions and theorems

* `chain`, `stationary` — the chain and its stationary distribution `(3/4, 1/4)`.
* `stationary_unemployment_rate` — the long-run unemployment rate is `1/4`.
* `stationary_isStationary` — `(3/4, 1/4)` is invariant under one step.
* `stationary_unique` — it is the only stationary distribution.
* `converges_to_stationary` — from any start, `chain.nStep k d₀ → (3/4, 1/4)` geometrically.
-/

noncomputable section

namespace EconlibExamples.Probability.EmploymentChain

open Econlib.Probability

/-! ## The chain and its stationary distribution -/

/-- The employment chain on `Fin 2` (`0 = employed`, `1 = unemployed`): Separation rate `1/10`,
job-finding rate `3/10`. -/
def chain : FiniteMarkovChain (Fin 2) where
  transition := ![finDist% ![9/10, 1/10], finDist% ![3/10, 7/10]]

/-- The stationary distribution: `3/4` employed, `1/4` unemployed. -/
def stationary : FinDist (Fin 2) := finDist% ![3/4, 1/4]

/-- The long-run unemployment rate is `1/4`. -/
theorem stationary_unemployment_rate : stationary.pmf 1 = 1 / 4 := by
  simp [stationary]

/-! ## Strict positivity (Doeblin's condition) -/

/-- Every transition probability is strictly positive, which is the hypothesis the ergodic theorems
need (it gives a uniform minorization / Doeblin contraction). -/
lemma chain_pos : ∀ s s', 0 < chain.transition s s' := by
  intro s s'
  fin_cases s <;> fin_cases s' <;> simp [chain]

/-! ## The stationary distribution is invariant -/

/-- **`(3/4, 1/4)` is stationary.** Verified through the coordinate balance equations
`∑ₛ μ(s)·Π(s, s') = μ(s')`: At each state the inflow equals the outflow. -/
theorem stationary_isStationary : chain.IsStationary stationary := by
  rw [FiniteMarkovChain.isStationary_iff]
  intro s'
  fin_cases s' <;> simp [chain, stationary, Fin.sum_univ_two] <;> norm_num

/-! ## Uniqueness and global geometric convergence -/

/-- **Uniqueness.** Strict positivity makes the step operator a total-variation contraction, so
`(3/4, 1/4)` is the only stationary distribution. -/
theorem stationary_unique (μ : FinDist (Fin 2)) (hμ : chain.IsStationary μ) :
    μ = stationary :=
  chain.unique_stationary chain_pos μ stationary hμ stationary_isStationary

/-- **Global geometric convergence (ergodicity).** From any initial distribution `d₀`, the `k`-step
distribution converges to the stationary `(3/4, 1/4)` at a geometric rate: There are constants
`C > 0` and `0 ≤ ρ < 1` with `|(chain.nStep k d₀)(s) - stationary(s)| ≤ C · ρᵏ` for every state. -/
theorem converges_to_stationary (d₀ : FinDist (Fin 2)) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ k : ℕ, ∀ s : Fin 2,
        |(chain.nStep k d₀).pmf s - stationary.pmf s| ≤ C * ρ ^ k :=
  chain.geometric_convergence_to chain_pos stationary_isStationary d₀

end EconlibExamples.Probability.EmploymentChain

end
