/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# First-Order Stochastic Dominance: A Dominant Lottery Is Preferred by Everyone

First-order stochastic dominance (FOSD) is the strongest of the classical stochastic orders — it
implies second-order dominance and the concave/convex orders, a standard fact we take for context
rather than formalize here — and it is characterized by unanimity: Lottery `dHi` dominates lottery
`dLo` exactly when every decision maker with a monotone (weakly increasing) valuation prefers `dHi`,
without any further assumptions on risk attitude, concavity, or the shape of the utility function.
This file exhibits a concrete dominant pair over three ordered prizes, proves the
universal-preference conclusion, and records the full equivalence.

We work entirely with the finite stochastic-dominance API: Dominance is the pointwise comparison of
cumulative distribution functions (`FinDist.cdf`), the payoff conclusion is the discrete
`FinDist.FOSD_expect_mono`, and the equivalence is `FinDist.FOSD_iff_expect_mono` — the converse
direction recovers each CDF comparison from the monotone threshold payoff at that cutoff.

## The model

States are three ordered prizes, `Fin 3` (i.e. `0 < 1 < 2`). Two lotteries:

* `dLo` places mass `(1/2, 1/4, 1/4)` — weight concentrated on the worst prize;
* `dHi` places mass `(1/4, 1/4, 1/2)` — weight shifted to the best prize.

## The mathematics

The cumulative distribution functions are `F_dHi = (1/4, 1/2, 1)` and `F_dLo = (1/2, 3/4, 1)`, so
`F_dHi ≤ F_dLo` pointwise: `dHi` puts less mass at or below every cutoff. That pointwise CDF
inequality is FOSD (`FinDist.FOSD_iff`) and `FinDist.FOSD_expect_mono` turns it into the statement
that the dominated lottery never yields a higher expectation of any monotone payoff. The dominance
here is *strict* at the cutoffs `0` and `1` (`dHi_cdf_lt_dLo_cutoffs`), and the strictness is
visible in the payoffs: the strictly increasing prize valuation (`prize_strictMono`) gives a
strictly higher mean under `dHi` (`3/4 < 5/4`).

## Main definitions and theorems

* `dLo`, `dHi` — the two lotteries.
* `dHi_fosd_dLo` — `dHi` first-order stochastically dominates `dLo`;
  `dHi_cdf_lt_dLo_cutoffs` — the CDF gap is *strict* at the cutoffs `0` and `1`.
* `everyone_prefers_dHi` — for every monotone `f`, `dLo.expect f ≤ dHi.expect f`.
* `fosd_iff_everyone_prefers` — the characterization: Dominance holds exactly when every monotone
  valuation weakly prefers `dHi`.
* `dHi_has_higher_mean` — the dominant lottery's mean prize (`5/4`) strictly exceeds the dominated
  one's (`3/4`): The strictly monotone prize valuation strictly prefers `dHi`.
-/

noncomputable section

namespace EconlibExamples.Probability.FirstOrderDominance

open Econlib.Probability

/-! ## Two lotteries over three ordered prizes -/

/-- The dominated lottery: Mass `(1/2, 1/4, 1/4)`, concentrated on the worst prize. -/
def dLo : FinDist (Fin 3) :=
  finDist% ![1/2, 1/4, 1/4]

/-- The dominant lottery: Mass `(1/4, 1/4, 1/2)`, shifted toward the best prize. -/
def dHi : FinDist (Fin 3) :=
  finDist% ![1/4, 1/4, 1/2]

/-! ## `dHi` first-order stochastically dominates `dLo` -/

/-- **`dHi` FOSD-dominates `dLo`.** The CDF of `dHi` lies weakly below that of `dLo` at every
cutoff: `(1/4, 1/2, 1) ≤ (1/2, 3/4, 1)`. The library's `FinDist.cdf_eq_sum_ite` turns each finite
CDF into a sum of indicators that `Fin.sum_univ_three` expands and `norm_num` evaluates cutoff by
cutoff. -/
theorem dHi_fosd_dLo : FinDist.FOSD dHi dLo := by
  rw [FinDist.FOSD_iff]
  intro a
  rw [FinDist.cdf_eq_sum_ite, FinDist.cdf_eq_sum_ite, Fin.sum_univ_three, Fin.sum_univ_three]
  fin_cases a <;> simp [dHi, dLo] <;> norm_num

/-- **The dominance is strict at the interior cutoffs.** The CDF gap `F_dHi < F_dLo` is strict at
the cutoffs `0` (`1/4 < 1/2`) and `1` (`1/2 < 3/4`); it closes only at the top cutoff `2`, where
both CDFs reach `1`. This is the strict mass-shift the strict mean comparison below reflects. -/
theorem dHi_cdf_lt_dLo_cutoffs : dHi.cdf 0 < dLo.cdf 0 ∧ dHi.cdf 1 < dLo.cdf 1 := by
  constructor <;>
    · rw [FinDist.cdf_eq_sum_ite, FinDist.cdf_eq_sum_ite, Fin.sum_univ_three, Fin.sum_univ_three]
      simp [dHi, dLo]; norm_num

/-! ## Every monotone agent prefers the dominant lottery -/

/-- **Main theorem.** For any monotone valuation `f`, the dominated lottery `dLo` yields a weakly
lower expected payoff than the dominant lottery `dHi`. This is the defining economic content of
first-order stochastic dominance: It ranks lotteries for all monotone decision makers
simultaneously, with no further assumptions on preferences. -/
theorem everyone_prefers_dHi (f : Fin 3 → ℝ) (hf : Monotone f) :
    dLo.expect f ≤ dHi.expect f :=
  FinDist.FOSD_expect_mono dHi_fosd_dLo hf

/-- **The characterization.** Dominance is not merely sufficient for unanimous preference — it is
equivalent to it: `dHi` FOSD-dominates `dLo` exactly when every monotone valuation weakly prefers
`dHi`. The converse direction is the library's `FinDist.FOSD_of_expect_mono`, which recovers the
CDF comparison at each cutoff from the monotone threshold payoff `x ↦ if x ≤ a then 0 else 1`. -/
theorem fosd_iff_everyone_prefers :
    FinDist.FOSD dHi dLo ↔ ∀ f : Fin 3 → ℝ, Monotone f → dLo.expect f ≤ dHi.expect f :=
  FinDist.FOSD_iff_expect_mono dHi dLo

/-! ## A concrete instance: The dominant lottery has the higher mean prize -/

/-- The prize value: State `i` is worth `i` units. Weakly increasing in the state. -/
def prize : Fin 3 → ℝ := fun i => (i : ℝ)

lemma prize_monotone : Monotone prize := by
  intro i j hij
  simp only [prize]
  exact_mod_cast Fin.val_le_of_le hij

/-- The prize value is strictly increasing in the state: `prize i = i` and the cast `Fin 3 → ℝ`
preserves strict order. This is the decision-maker witness behind the strict mean comparison. -/
lemma prize_strictMono : StrictMono prize := by
  intro i j hij
  simp only [prize]
  exact_mod_cast hij

/-- The dominated lottery's mean prize is `3/4`. -/
lemma dLo_mean : dLo.expect prize = 3 / 4 := by
  simp only [FinDist.expect, Fin.sum_univ_three, dLo, prize, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num [Fin.val_zero, Fin.val_one, Fin.val_two]

/-- The dominant lottery's mean prize is `5/4`. -/
lemma dHi_mean : dHi.expect prize = 5 / 4 := by
  simp only [FinDist.expect, Fin.sum_univ_three, dHi, prize, FinDist.ofVec_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num [Fin.val_zero, Fin.val_one, Fin.val_two]

/-- Instantiating at the strictly increasing prize value shows the dominance is not degenerate: The
mean comparison `3/4 < 5/4` is strict. A strictly monotone decision maker strictly prefers the
dominant lottery here, reflecting that the CDF gap is strict at the cutoffs `0` and `1`. -/
theorem dHi_has_higher_mean : dLo.expect prize < dHi.expect prize := by
  rw [dLo_mean, dHi_mean]; norm_num

end EconlibExamples.Probability.FirstOrderDominance

end
