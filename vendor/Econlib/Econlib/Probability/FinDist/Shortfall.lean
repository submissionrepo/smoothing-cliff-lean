/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.CDF
public import Econlib.Probability.FinDist.Expect

/-!
# Expected shortfall of a finite distribution

The **expected shortfall** of a payoff `y : α → ℝ` below a cutoff `t` is the expected lower hinge
`E[(t − Y)⁺] = E[max (t − y, 0)]`. It is the dispersion statistic of the Rothschild–Stiglitz
characterization of mean-preserving spreads: A spread is detected exactly when, at every cutoff,
the expected shortfall is weakly larger. It coincides with the **integrated CDF** — the area under
the payoff CDF up to `t`:

`E[(t − Y)⁺] = ∑_{a : y a < t} (t − y a) · d a = ∫_{−∞}^t F_Y`.

## Main definitions

* `FinDist.expectedShortfall` — `E[(t − Y)⁺] = E[max (t − y, 0)]`.

## Main statements

* `FinDist.expectedShortfall_nonneg` — the expected shortfall is nonnegative.
* `FinDist.expectedShortfall_eq_sum_lt` — the integrated-CDF identity: The expected shortfall is
  the mass-weighted sum of cutoff gaps over the states strictly below the cutoff.

## Notes

This file uses the **lower** hinge `max (t − y, 0)` (shortfall below the cutoff `t`), matching the
Rothschild–Stiglitz characterization. The continuous
`MeasureTheory.Measure.stopLoss μ z =
∫ max (x − z) 0` uses the **upper** hinge (expected excess
above `z`); the two are reflections of each other (`E_d[(t − Y)⁺] = E_{−d}[((−t) − (−Y))_-]`, i.e.
negate the payoff and the cutoff). The lower-hinge convention here lets the `FinDist` dispersion
test read off directly.

## Tags

expected shortfall, integrated CDF, lower hinge, mean-preserving spread, Rothschild-Stiglitz,
dispersion, stop-loss
-/

@[expose] public section

open Finset BigOperators

namespace Econlib.Probability

namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **Expected shortfall below the cutoff** `t`: The expected lower hinge
`E[(t − Y)⁺] = E[max (t − y, 0)]` of the payoff `y` under `d`. This is the dispersion statistic of
the Rothschild–Stiglitz characterization of mean-preserving spreads, equivalently the discrete
integrated CDF (`expectedShortfall_eq_sum_lt`). -/
noncomputable def expectedShortfall (d : FinDist α) (y : α → ℝ) (t : ℝ) : ℝ :=
  d.expect (fun a => max (t - y a) 0)

@[simp] lemma expectedShortfall_eq (d : FinDist α) (y : α → ℝ) (t : ℝ) :
    d.expectedShortfall y t = d.expect (fun a => max (t - y a) 0) := rfl

/-- The expected shortfall is nonnegative: Each hinge `max (t − y a) 0` is nonnegative. -/
lemma expectedShortfall_nonneg (d : FinDist α) (y : α → ℝ) (t : ℝ) :
    0 ≤ d.expectedShortfall y t :=
  d.expect_nonneg _ (fun _ => le_max_right _ _)

/-- **The integrated-CDF identity.** The expected shortfall is the mass-weighted sum of the cutoff
gaps `t − y a` over exactly the states whose payoff lies strictly below the cutoff `t`; the states
at or above the cutoff contribute zero. This is the area under the payoff step-CDF up to `t`. -/
lemma expectedShortfall_eq_sum_lt (d : FinDist α) (y : α → ℝ) (t : ℝ) :
    d.expectedShortfall y t = ∑ a ∈ univ.filter (fun a => y a < t), (t - y a) * d a := by
  rw [expectedShortfall_eq, expect_eq_sum, ← Finset.sum_filter_add_sum_filter_not univ
    (fun a => y a < t)]
  -- States at or above the cutoff contribute zero (`max (t − y a) 0 = 0` when `t ≤ y a`).
  have h_ge_zero : ∑ a ∈ univ.filter (fun a => ¬ y a < t), d.pmf a * max (t - y a) 0 = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [mem_filter, not_lt] at ha
    rw [max_eq_right (by linarith [ha.2] : t - y a ≤ 0), mul_zero]
  -- Below the cutoff `max (t − y a) 0 = t − y a`; reorder the product into `(t − y a) · d a`.
  rw [h_ge_zero, add_zero]
  apply Finset.sum_congr rfl
  intro a ha
  rw [mem_filter] at ha
  rw [max_eq_left (by linarith [ha.2] : 0 ≤ t - y a), pmf_eq_coe, mul_comm]

end FinDist

end Econlib.Probability
