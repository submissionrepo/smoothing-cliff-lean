/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Rothschild–Stiglitz: A Mean-Preserving Spread Is Disliked by Every Risk Averter

A *mean-preserving spread* (MPS) takes a distribution and scatters its mass outward while holding
the mean fixed — the formal notion of "more risk, same average." Rothschild and Stiglitz (1970)
characterized this increase in risk by its effect on expected utility: `ds` is a mean-preserving
spread of `d` exactly when every risk-averse (concave-utility) agent weakly prefers `d`. This file
runs both sides of that characterization on the simplest case — adding fair noise to a sure thing —
using the library's Rothschild–Stiglitz equivalence `FinDist.shortfall_iff_concave_expect_le`: The
*dispersion* side is verified directly (the spread has weakly larger expected shortfall
`E[(t - y)⁺]` at every cutoff `t`, i.e. a weakly larger integrated CDF), and the *preference* side
then follows from the equivalence rather than by definition.

This is the worked tutorial for `Econlib.Probability.FinDist.IsMPS` and
`Econlib.Probability.Order.Convex.MPSCharacterization`.

## The model

Outcomes are three states `Fin 3` carrying payoffs `y = (-1, 0, 1)`. There are two distributions:

* `sure` — the Dirac mass on state `1`: Payoff `0` with certainty;
* `risky` — mass `1/2` on each of states `0` and `2`: A fair `±1` gamble.

Both have mean `0`, and `risky` scatters the mass of `sure` outward: At every cutoff `t` its
expected shortfall `E[(t - y)⁺]` is weakly larger (`risky_shortfall_ge`), strictly so on the
interior `-1 < t < 1` (`risky_shortfall_gt`) and with equality outside
(`risky_shortfall_eq_outside`). So `risky` is a mean-preserving spread of `sure` — by the dispersion
test, not by fiat.

## The mathematics

The dispersion condition is a four-region computation: `E_sure[(t - y)⁺] = max t 0` while
`E_risky[(t - y)⁺] = ½·max (t+1) 0 + ½·max (t-1) 0`, and the claimed inequality is an instance of
convexity of the hinge — checked here directly by cases on `t ≤ -1`, `-1 ≤ t ≤ 0`, `0 ≤ t ≤ 1`,
`1 ≤ t`. Feeding it into the Rothschild–Stiglitz equivalence (`FinDist.isMPS_iff_shortfall`) yields
`risky_is_mps`, whence every concave utility weakly prefers `sure`
(`risk_averse_prefers_certainty`) — e.g. `u(x) = -x²` strictly so — and the variance rises from `0`
to `1`. The full biconditional for this pair is `mps_iff_all_risk_averse_prefer`.

## Main definitions and theorems

* `sure`, `risky`, `y` — the two distributions and the payoff map.
* `same_mean` — both have mean `0`.
* `risky_shortfall_ge` — the dispersion condition: `risky` has weakly larger expected shortfall at
  every cutoff; `risky_shortfall_gt` — strictly larger on the interior `-1 < t < 1`;
  `risky_shortfall_eq_outside` — equality for `t ≤ -1` or `1 ≤ t`.
* `risky_is_mps` — hence `risky` is a mean-preserving spread of `sure`, via the Rothschild–Stiglitz
  characterization `FinDist.isMPS_iff_shortfall`.
* `mps_iff_all_risk_averse_prefer` — the headline biconditional for this pair: `risky` is a
  mean-preserving spread of `sure` exactly when every risk averter weakly prefers `sure`.
* `risk_averse_prefers_certainty` — every concave utility weakly prefers `sure`.
* `spread_increases_variance` — the spread weakly increases variance.
* `sure_variance`, `risky_variance` — the concrete variances `0` and `1`.
* `risk_averse_strictly_prefers` — with concave `u(x) = -x²`, the preference is strict (`-1 < 0`).
-/

noncomputable section

namespace EconlibExamples.Probability.RothschildStiglitz

open Econlib.Probability

/-! ## The payoffs, the sure thing, and the fair gamble -/

/-- The monetary payoff in each of the three states: `(-1, 0, 1)`. -/
def y : Fin 3 → ℝ := ![-1, 0, 1]

/-- The certain outcome: A point mass on state `1`, paying `0` for sure. -/
def sure : FinDist (Fin 3) := FinDist.pure 1

/-- The fair gamble: Payoff `-1` or `+1`, each with probability `1/2`. -/
def risky : FinDist (Fin 3) :=
  finDist% ![1/2, 0, 1/2]

/-! ## Equal means -/

/-- The fair gamble has mean `0`. -/
lemma risky_mean : risky.expect y = 0 := by
  simp only [FinDist.expect, risky, y, FinDist.ofVec_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num

/-- The sure thing has mean `0`. -/
lemma sure_mean : sure.expect y = 0 := by
  simp only [sure, FinDist.expect_pure, y, Matrix.cons_val_one, Matrix.cons_val_zero]

/-- The spread preserves the mean. -/
lemma same_mean : risky.expect y = sure.expect y := by rw [risky_mean, sure_mean]

/-! ## The dispersion condition: `risky` has weakly larger expected shortfall -/

/-- The sure thing's expected shortfall in closed form: `E_sure[(t - y)⁺] = max t 0`. -/
lemma sure_shortfall_eq (t : ℝ) : sure.expectedShortfall y t = max t 0 := by
  simp only [FinDist.expectedShortfall_eq, sure, FinDist.expect_pure, y, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  norm_num

/-- The fair gamble's expected shortfall in closed form:
`E_risky[(t - y)⁺] = ½·max (t+1) 0 + ½·max (t-1) 0`. -/
lemma risky_shortfall_eq (t : ℝ) :
    risky.expectedShortfall y t = 1 / 2 * max (t + 1) 0 + 1 / 2 * max (t - 1) 0 := by
  simp only [FinDist.expectedShortfall_eq, FinDist.expect, risky, y, FinDist.ofVec_apply,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num [sub_neg_eq_add]

/-- **The Rothschild–Stiglitz dispersion condition.** At every cutoff `t`, the expected shortfall
`E[(t - y)⁺]` — the discrete integrated CDF — is weakly larger under `risky` than under `sure`:
`max t 0 ≤ ½·max (t+1) 0 + ½·max (t-1) 0`. This is the formal content of "scatters its mass
outward" — the strict interior gap (`risky_shortfall_gt`) and the equality outside
(`risky_shortfall_eq_outside`) are recorded separately below. -/
lemma risky_shortfall_ge (t : ℝ) :
    sure.expectedShortfall y t ≤ risky.expectedShortfall y t := by
  rw [sure_shortfall_eq, risky_shortfall_eq]
  -- Four regions split by the kinks at `-1`, `0`, `1`.
  rcases le_total t (-1) with ht1 | ht1
  · -- `t ≤ -1`: all three hinges are flat, `0 ≤ 0`.
    rw [max_eq_right (by linarith : t ≤ 0), max_eq_right (by linarith : t + 1 ≤ 0),
      max_eq_right (by linarith : t - 1 ≤ 0)]
    norm_num
  · rcases le_total t 0 with ht2 | ht2
    · -- `-1 ≤ t ≤ 0`: the gamble's lower tail is already exposed, `0 ≤ ½(t+1)`.
      rw [max_eq_right ht2, max_eq_left (by linarith : 0 ≤ t + 1),
        max_eq_right (by linarith : t - 1 ≤ 0)]
      linarith
    · rcases le_total t 1 with ht3 | ht3
      · -- `0 ≤ t ≤ 1`: `t ≤ ½(t+1)` exactly because `t ≤ 1`.
        rw [max_eq_left ht2, max_eq_left (by linarith : 0 ≤ t + 1),
          max_eq_right (by linarith : t - 1 ≤ 0)]
        linarith
      · -- `1 ≤ t`: both sides equal `t`.
        rw [max_eq_left ht2, max_eq_left (by linarith : 0 ≤ t + 1),
          max_eq_left (by linarith : 0 ≤ t - 1)]
        linarith

/-- **Strict dispersion on the interior.** At every interior cutoff `-1 < t < 1`, the gamble's
expected shortfall is strictly larger than the sure thing's: both `±1` tails contribute, so
`max t 0 < ½(t+1)`. This is where "scatters its mass outward" bites. -/
lemma risky_shortfall_gt {t : ℝ} (ht : -1 < t) (ht' : t < 1) :
    sure.expectedShortfall y t < risky.expectedShortfall y t := by
  rw [sure_shortfall_eq, risky_shortfall_eq,
    max_eq_left (by linarith : 0 ≤ t + 1), max_eq_right (by linarith : t - 1 ≤ 0)]
  -- The right tail is flat; the strict gap is `max t 0 < ½(t+1)`.
  rcases le_total t 0 with ht0 | ht0
  · rw [max_eq_right ht0]; linarith
  · rw [max_eq_left ht0]; linarith

/-- **Equality outside the support gap.** For `t ≤ -1` or `1 ≤ t` the two shortfalls coincide: below
both kinks both sides are `0`/flat, above both kinks both equal `t`. So the dispersion inequality is
strict exactly on the interior. -/
lemma risky_shortfall_eq_outside {t : ℝ} (ht : t ≤ -1 ∨ 1 ≤ t) :
    sure.expectedShortfall y t = risky.expectedShortfall y t := by
  rw [sure_shortfall_eq, risky_shortfall_eq]
  rcases ht with ht | ht
  · rw [max_eq_right (by linarith : t ≤ 0), max_eq_right (by linarith : t + 1 ≤ 0),
      max_eq_right (by linarith : t - 1 ≤ 0)]
    norm_num
  · rw [max_eq_left (by linarith : 0 ≤ t), max_eq_left (by linarith : 0 ≤ t + 1),
      max_eq_left (by linarith : 0 ≤ t - 1)]
    ring

/-! ## `risky` is a mean-preserving spread of `sure` — by the characterization -/

/-- **`risky` is a mean-preserving spread of `sure`**, derived from the Rothschild–Stiglitz
characterization `FinDist.isMPS_iff_shortfall`: Equal means plus the dispersion condition. The
universal concave-preference property is a conclusion here, not a hypothesis. -/
theorem risky_is_mps : FinDist.IsMPS sure risky y :=
  (FinDist.isMPS_iff_shortfall sure risky y).mpr ⟨same_mean, risky_shortfall_ge⟩

/-! ## The Rothschild–Stiglitz preference and variance consequences -/

/-- **The headline biconditional, instantiated.** `risky` is a mean-preserving spread of `sure`
exactly when every risk-averse agent (concave utility) weakly prefers the sure thing —
Rothschild–Stiglitz (1970) for this pair, both directions. Composes the dispersion characterization
`FinDist.isMPS_iff_shortfall` (`IsMPS` ⟺ equal means + the shortfall condition) with the
shortfall/concave equivalence `FinDist.shortfall_iff_concave_expect_le`, discharging the equal-means
clause via `same_mean`. -/
theorem mps_iff_all_risk_averse_prefer :
    FinDist.IsMPS sure risky y
      ↔ ∀ f : ℝ → ℝ, ConcaveOn ℝ Set.univ f → risky.expect (f ∘ y) ≤ sure.expect (f ∘ y) := by
  rw [FinDist.isMPS_iff_shortfall sure risky y,
    FinDist.shortfall_iff_concave_expect_le sure risky y same_mean]
  exact and_iff_right same_mean

/-- **Main theorem.** Every risk-averse agent (i.e. with concave utility `f`) weakly prefers the
sure outcome to the fair gamble — obtained from the dispersion condition through the
Rothschild–Stiglitz equivalence. -/
theorem risk_averse_prefers_certainty (f : ℝ → ℝ) (hf : ConcaveOn ℝ Set.univ f) :
    risky.expect (f ∘ y) ≤ sure.expect (f ∘ y) :=
  risky_is_mps.concave_expect_le f hf

/-- The mean-preserving spread weakly increases variance. The concrete jump (`0` to `1`) is
recorded by `sure_variance` and `risky_variance` below. -/
theorem spread_increases_variance : sure.variance y ≤ risky.variance y :=
  risky_is_mps.variance_ge

/-- The sure thing has zero variance (it is a point mass). -/
lemma sure_variance : sure.variance y = 0 := by simp [sure]

/-- The fair gamble has variance `1`: `E[y²] - (E y)² = 1 - 0`. -/
lemma risky_variance : risky.variance y = 1 := by
  simp only [FinDist.variance, FinDist.expect, risky, y, FinDist.ofVec_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num

/-! ## A concrete risk averter strictly prefers certainty -/

/-- A strictly concave utility, `u(x) = -x²`. -/
def u : ℝ → ℝ := fun x => -x ^ 2

lemma u_concave : ConcaveOn ℝ Set.univ u := concaveOn_neg_sq

/-- The fair gamble's expected utility under `u` is `-1` (i.e. `E[u(y)]`, not a money amount). -/
lemma risky_expect_u : risky.expect (u ∘ y) = -1 := by
  simp only [FinDist.expect, Function.comp_apply, risky, u, y, FinDist.ofVec_apply,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- The sure outcome's expected utility under `u` is `0` (here `u(0) = 0`). -/
lemma sure_expect_u : sure.expect (u ∘ y) = 0 := by
  simp only [sure, FinDist.expect_pure, Function.comp_apply, u, y, Matrix.cons_val_one,
    Matrix.cons_val_zero]
  norm_num

/-- Under the quadratic utility `u(x) = -x²`, the risk averter strictly prefers the sure `0`
(expected utility `0`) to the fair gamble (expected utility `-1`). -/
theorem risk_averse_strictly_prefers : risky.expect (u ∘ y) < sure.expect (u ∘ y) := by
  rw [risky_expect_u, sure_expect_u]; norm_num

end EconlibExamples.Probability.RothschildStiglitz

end
