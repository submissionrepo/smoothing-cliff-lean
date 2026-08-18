/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Expect
public import Econlib.Probability.Markov.Basic

/-!
# Expected-Value Convergence for Finite-State Supermartingales

Discrete-time supermartingale theory for finite-state Markov chains. This provides the
expected-value convergence results needed for the Euler inequality argument without the full
measure-theoretic overhead of Mathlib's `MeasureTheory.Supermartingale`. The convergence
established here is of the *sequence of expectations* `𝔼[Xₜ]` (monotone + bounded below) — not
pathwise / almost-sure / L¹ convergence of the process.

## Main definitions

* `FinSupermartingale` — a non-negative supermartingale adapted to a finite Markov chain.
* `eulerSupermartingale` — the rescaled marginal utility sequence `(βR)ᵗ μₜ`.

## Main statements

* `FinSupermartingale.expect_step_le` — the expected value is non-increasing under one step.
* `FinSupermartingale.bounded_in_L1` — the evolved expectation is bounded by `𝔼_d[X₀]`.
* `FinSupermartingale.expect_converges` — the sequence of expected values converges (monotone +
  bounded below); this is convergence of expectations, not of the process.
* `euler_forces_divergence` — under `βR > 1`, the rescaled marginal utility has expectation bounded
  by `𝔼_d[μ₀]` along the evolved distribution.

## Notes

We work with explicit sequences `X : ℕ → α → ℝ` adapted to a Markov chain, rather than
filtration-adapted processes. This avoids measurability issues entirely: On a finite type, every
function is measurable.

## Tags

supermartingale, markov chain, expected-value convergence, euler equation, transversality
-/

@[expose] public section

namespace Econlib.Probability

open Finset BigOperators

/-! ## Tower Property -/

/-- **Fubini / tower property** for the Markov step operator: `𝔼_{P·d}[f] = 𝔼_d[𝔼_{P(·)}[f]]`. -/
lemma FiniteMarkovChain.fubini_step {α : Type*} [Fintype α] [DecidableEq α]
    (P : FiniteMarkovChain α) (d : FinDist α) (f : α → ℝ) :
    FinDist.expect (P.step d) f =
      FinDist.expect d
        (fun s => FinDist.expect (P.transition s) f) := by
  simp only [FinDist.expect, FiniteMarkovChain.step]
  -- LHS: Σ_{s'} (Σ_s d(s) P(s,s')) · f(s')
  -- RHS: Σ_s d(s) · (Σ_{s'} P(s,s') · f(s'))
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext s'; congr 1; ext s; ring

/-! ## Finite-State Supermartingale -/

/-- A non-negative supermartingale adapted to a Markov chain on a finite type `α`. The process
`X : ℕ → α → ℝ` satisfies:

* Non-negativity: `X t s ≥ 0` for all `t, s`
* Supermartingale property: `𝔼[X_{t+1} | s] ≤ X_t(s)` where the expectation is over the transition
  `P(s, ·)` -/
structure FinSupermartingale {α : Type*} [Fintype α] [DecidableEq α]
    (P : FiniteMarkovChain α) where
  /-- The process: `X t s` is the value at time `t` in state `s`. -/
  X : ℕ → α → ℝ
  /-- Non-negativity. -/
  nonneg : ∀ t s, 0 ≤ X t s
  /-- Supermartingale property: Conditional expectation ≤ current. -/
  superMG : ∀ t s, FinDist.expect (P.transition s) (X (t + 1)) ≤ X t s

namespace FinSupermartingale

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {P : FiniteMarkovChain α} (M : FinSupermartingale P)

/-- **Supermartingale inequality.** The conditional expectation of `X_{t+1}` over the transition
`P(s, ·)` is at most the current value `X_t(s)`. -/
theorem condExpect_le (t : ℕ) (s : α) :
    FinDist.expect (P.transition s) (M.X (t + 1)) ≤
      M.X t s :=
  M.superMG t s

/-- **Expected value under one-step evolution is non-increasing.** `𝔼_{P·d}[X_{t+1}] ≤ 𝔼_d[X_t]`
where `P·d` is the one-step evolved distribution. -/
theorem expect_step_le (d : FinDist α) (t : ℕ) :
    FinDist.expect d
      (fun s => FinDist.expect (P.transition s)
        (M.X (t + 1))) ≤
      FinDist.expect d (M.X t) := by
  unfold FinDist.expect
  apply Finset.sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left (M.superMG t s)
    (d.nonneg s)

/-- **One-step decrease under the evolved distribution.**
`𝔼_{P^{t+1} d}[X_{t+1}] ≤ 𝔼_{P^t d}[X_t]`. -/
theorem expect_nStep_succ_le (d : FinDist α) (t : ℕ) :
    FinDist.expect (P.nStep (t + 1) d) (M.X (t + 1)) ≤
      FinDist.expect (P.nStep t d) (M.X t) := by
  rw [FiniteMarkovChain.nStep_succ]
  calc FinDist.expect (P.step (P.nStep t d)) (M.X (t + 1))
      = FinDist.expect (P.nStep t d)
          (fun s => FinDist.expect (P.transition s) (M.X (t + 1))) :=
        P.fubini_step (P.nStep t d) (M.X (t + 1))
    _ ≤ FinDist.expect (P.nStep t d) (M.X t) :=
        M.expect_step_le (P.nStep t d) t

/-- **L¹ bounded.** `𝔼_{P^t d}[X_t] ≤ 𝔼_d[X_0]` for all `t`, where `P^t d` is the t-step evolved
distribution. -/
theorem bounded_in_L1 (d : FinDist α) (t : ℕ) :
    FinDist.expect (P.nStep t d) (M.X t) ≤
      FinDist.expect d (M.X 0) := by
  induction t with
  | zero => simp [FiniteMarkovChain.nStep]
  | succ t ih => exact (M.expect_nStep_succ_le d t).trans ih

/-- **Convergence of the expected value (monotone + bounded below).** The sequence of expected
values `𝔼_{P^t d}[X_t]` converges as `t → ∞` for any initial distribution `d`, by antitonicity and
lower-boundedness. This is convergence of expectations, not pathwise / almost-sure / L¹ convergence
of the process (Doob's supermartingale convergence theorem). -/
theorem expect_converges (d : FinDist α) :
    ∃ l, Filter.Tendsto
      (fun t => FinDist.expect (P.nStep t d) (M.X t))
      Filter.atTop (nhds l) := by
  refine ⟨⨅ t, FinDist.expect (P.nStep t d) (M.X t), ?_⟩
  apply tendsto_atTop_ciInf
  · -- Antitone: the sequence is non-increasing
    intro s t hst
    induction hst with
    | refl => rfl
    | step hst ih => exact (M.expect_nStep_succ_le d _).trans ih
  · -- BddBelow: each term is ≥ 0 (non-negative supermartingale)
    exact ⟨0, by rintro _ ⟨t, rfl⟩; exact FinDist.expect_nonneg _ _ (M.nonneg t)⟩

end FinSupermartingale

/-! ## Euler Inequality Application -/

/-- **Euler supermartingale.** Given the Euler inequality `μ_t(s) ≥ βR · 𝔼[μ_{t+1} | s]` where
`μ_t = u'(c_t)`, the rescaled process `Y_t(s) = (βR)^t · μ_t(s)` is a non-negative
supermartingale. -/
noncomputable def eulerSupermartingale {α : Type*} [Fintype α] [DecidableEq α]
    (P : FiniteMarkovChain α) (μ : ℕ → α → ℝ)
    (βR : ℝ) (hβR : 0 < βR)
    (hμ_pos : ∀ t s, 0 < μ t s)
    (hEuler : ∀ t s,
      βR * FinDist.expect (P.transition s) (μ (t + 1)) ≤
        μ t s) :
    FinSupermartingale P where
  X t s := βR ^ t * μ t s
  nonneg t s := mul_nonneg (pow_nonneg hβR.le t)
    (hμ_pos t s).le
  superMG t s := by
    -- 𝔼[Y_{t+1}] = (βR)^{t+1} · 𝔼[μ_{t+1}] = (βR)^t · (βR · 𝔼[μ_{t+1}]) ≤ (βR)^t · μ_t(s).
    -- Factor (βR)^t out of the sum, leaving βR · 𝔼[μ_{t+1}] ≤ μ_t(s), which is `hEuler`.
    unfold FinDist.expect
    have hfactor : ∑ s', P.transition s s' * (βR ^ (t + 1) * μ (t + 1) s') =
        βR ^ t * (βR * ∑ s', P.transition s s' * μ (t + 1) s') := by
      rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun s' _ => by ring
    rw [hfactor]
    exact mul_le_mul_of_nonneg_left (hEuler t s) (pow_nonneg hβR.le t)

/-- **Euler inequality bound when `βR > 1`.** If `μ_t ≥ βR · 𝔼[μ_{t+1} | s_t]` with `βR > 1` and
`μ_t > 0`, then `(βR)^t · μ_t` is a non-negative supermartingale, so its expectation along the
evolved distribution `P^t d` stays bounded by `𝔼_d[μ₀]`.

This is the L¹ bound underlying the transversality argument ruling out `βR > 1` in the credit
certification model: Since `(βR)^t → ∞`, a bounded `𝔼[(βR)^t μ_t]` pushes `μ_t` toward zero. The
downstream consequences (via the Inada condition) are not established here. -/
theorem euler_forces_divergence {α : Type*} [Fintype α] [DecidableEq α]
    (P : FiniteMarkovChain α)
    (μ : ℕ → α → ℝ) (βR : ℝ) (hβR : 1 < βR)
    (hμ_pos : ∀ t s, 0 < μ t s)
    (hEuler : ∀ t s,
      βR * FinDist.expect (P.transition s) (μ (t + 1)) ≤
        μ t s)
    (d : FinDist α) :
    -- The rescaled process (βR)^t μ_t has bounded expectation
    -- under the EVOLVED distribution P^t d
    ∀ t, FinDist.expect (P.nStep t d)
      (fun s => βR ^ t * μ t s) ≤
      FinDist.expect d (μ 0) := by
  intro t
  set SM := eulerSupermartingale P μ βR (by linarith)
    hμ_pos hEuler
  have hL1 := SM.bounded_in_L1 d t
  -- Y_0 = (βR)^0 · μ_0 = 1 · μ_0 = μ_0
  have hY0 : SM.X 0 = μ 0 := by
    ext s; simp [SM, eulerSupermartingale]
  rw [hY0] at hL1
  exact hL1

end Econlib.Probability
