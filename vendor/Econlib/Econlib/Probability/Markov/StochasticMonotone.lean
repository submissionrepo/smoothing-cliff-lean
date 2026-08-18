/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Markov.Basic
public import Econlib.Probability.Order.FOSD.FinDist

/-!
# Stochastically monotone Markov chains

A chain is **stochastically monotone** if higher current states lead to FOSD-higher next-step
distributions. We work over an arbitrary finite linear order `α`.

## Main definitions

* `StochMonotoneFiniteMarkovChain` — a finite Markov chain whose transition is FOSD-monotone in the
  current state.
* `StochMonotoneFiniteMarkovChain.ofIidRows` — a chain with equal transition rows, viewed as
  stochastically monotone.

## Main statements

* `StochMonotoneFiniteMarkovChain.monotone_expect` — a monotone integrand has conditional
  expectation monotone in the state.
* `StochMonotoneFiniteMarkovChain.antitone_expect` — an antitone integrand has antitone conditional
  expectation.
* `StochMonotoneFiniteMarkovChain.step_preserves_FOSD` — the one-step evolution preserves FOSD.
* `StochMonotoneFiniteMarkovChain.nStep_monotone` — the iterated chain is stochastically monotone.

## Tags

markov chain, stochastically monotone, first-order stochastic dominance, fosd
-/

@[expose] public section

open Finset BigOperators

namespace Econlib.Probability

/-- A stochastically monotone finite Markov chain over a finite linear order: Higher current states
lead to FOSD-higher distributions over next-period states. -/
structure StochMonotoneFiniteMarkovChain (α : Type*) [Fintype α] [DecidableEq α]
    [LinearOrder α] extends FiniteMarkovChain α where
  /-- Stochastic monotonicity: `s₁ ≤ s₂ ⟹ transition(s₂)` FOSD-dominates `transition(s₁)`.
  Equivalently, higher current states shift the next-period distribution upward. -/
  monotone : ∀ s₁ s₂ : α, s₁ ≤ s₂ →
    FinDist.FOSD (transition s₂) (transition s₁)

namespace StochMonotoneFiniteMarkovChain

variable {α : Type*} [Fintype α] [DecidableEq α] [LinearOrder α]
variable (P : StochMonotoneFiniteMarkovChain α)

/-- **Monotone expectation transfer.** If `f : α → ℝ` is monotone non-decreasing and `Π` is
stochastically monotone, then `s ↦ 𝔼_{Π(s)}[f]` is monotone non-decreasing. -/
theorem monotone_expect {f : α → ℝ} (hf : Monotone f) :
    Monotone (fun s => (P.transition s).expect f) := by
  intro s₁ s₂ hs
  exact FinDist.FOSD_expect_mono (P.monotone s₁ s₂ hs) hf

/-- **Antitone expectation transfer.** If `g : α → ℝ` is antitone and `Π` is stochastically
monotone, then `s ↦ 𝔼_{Π(s)}[g]` is antitone. -/
theorem antitone_expect {g : α → ℝ} (hg : Antitone g) :
    Antitone (fun s => (P.transition s).expect g) := by
  intro s₁ s₂ hs
  exact FinDist.FOSD_expect_antitone (P.monotone s₁ s₂ hs) hg

/-- **Stochastic monotonicity of the one-step evolution.** If `d₁ ≤_FOSD d₂` and `Π` is
stochastically monotone, then `P.step d₁ ≤_FOSD P.step d₂`. -/
theorem step_preserves_FOSD {d₁ d₂ : FinDist α}
    (hd : FinDist.FOSD d₁ d₂) :
    FinDist.FOSD (P.toFiniteMarkovChain.step d₁)
      (P.toFiniteMarkovChain.step d₂) := by
  intro a
  change ∑ s' ∈ Finset.univ.filter (· ≤ a),
      (∑ s, d₁ s * P.transition s s') ≤
    ∑ s' ∈ Finset.univ.filter (· ≤ a),
      (∑ s, d₂ s * P.transition s s')
  simp_rw [Finset.sum_comm (s := Finset.univ.filter (· ≤ a)), ← Finset.mul_sum]
  have hg_anti : Antitone (fun s => ∑ s' ∈ Finset.univ.filter (· ≤ a),
      P.transition s s') := by
    intro s₁ s₂ hs
    exact P.monotone s₁ s₂ hs a
  simpa [FinDist.expect, FinDist.cdf] using
    FinDist.FOSD_expect_antitone hd hg_anti

/-- Iterated kernels of a stochastically monotone chain are stochastically monotone. -/
theorem nStep_monotone (k : ℕ) (s₁ s₂ : α) (hs : s₁ ≤ s₂) :
    FinDist.FOSD
      (P.toFiniteMarkovChain.nStep k (FinDist.pure s₂))
      (P.toFiniteMarkovChain.nStep k (FinDist.pure s₁)) := by
  induction k with
  | zero =>
      simp only [FiniteMarkovChain.nStep]
      exact FinDist.FOSD_pure hs
  | succ k ih =>
      simp only [FiniteMarkovChain.nStep_succ]
      exact P.step_preserves_FOSD ih

/-- Iid transition rows are stochastically monotone. -/
def ofIidRows (P : FiniteMarkovChain α) (hrows : P.IidRows) :
    StochMonotoneFiniteMarkovChain α where
  transition := P.transition
  monotone := by
    intro s₁ s₂ hs a
    rw [hrows s₂ s₁]

end StochMonotoneFiniteMarkovChain

end Econlib.Probability
