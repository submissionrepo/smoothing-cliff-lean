/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Data.Real.Basic

/-!
# Risk-attitude predicates

This file defines the concavity-based predicates for risk attitudes under expected utility: A
utility function is risk averse, risk neutral, or risk loving on a set according to whether it is
concave, affine, or convex there. The lottery content of these predicates — their consequences for
certainty equivalents and risk premia — is developed in
`Econlib.Preferences.Risk.CertaintyEquivalent`.

## Main definitions

* `RiskAverse` — concavity of the utility function on a set.
* `StrictlyRiskAverse` — strict concavity on a set.
* `RiskNeutral` — affinity on a set.
* `RiskLoving` — convexity on a set.

## References

* Pratt, John W. 1964. “Risk Aversion in the Small and in the Large.” *Econometrica* 32 (1/2): 122.
  [https://doi.org/10.2307/1913738](https://doi.org/10.2307/1913738).

## Tags

risk aversion, risk neutrality, risk loving, concavity, expected utility
-/

@[expose] public section

namespace Econlib.Preferences

/-- A utility function `u : ℝ → ℝ` is **risk averse** on a set `S ⊆ ℝ` when it is concave on `S`:
For any `x, y ∈ S` and `t ∈ [0, 1]`, `u(t·x + (1-t)·y) ≥ t·u(x) + (1-t)·u(y)`.

The lottery content — a risk-averse agent values a gamble at most as much as its expected value
(`RiskAverse.le_map_sum`) — together with the certainty-equivalent and risk-premium consequences
(`RiskAverse.certainty_equivalent_le_expected_value`, `RiskAverse.risk_premium_nonneg`) lives in
`Econlib.Preferences.Risk.CertaintyEquivalent`. -/
def RiskAverse (u : ℝ → ℝ) (S : Set ℝ) : Prop := ConcaveOn ℝ S u

/-- A utility function is **strictly risk averse** on `S` when it is strictly concave on `S`: The
concavity inequality is strict for `x ≠ y` and `t ∈ (0, 1)`.

The strict Jensen gap — the certainty equivalent falls below the expected value for a
non-degenerate lottery — is `StrictlyRiskAverse.risk_premium_pos`. -/
def StrictlyRiskAverse (u : ℝ → ℝ) (S : Set ℝ) : Prop := StrictConcaveOn ℝ S u

/-- A utility function is **risk neutral** on `S` when it is affine on `S`: There exist `a, b : ℝ`
with `u(x) = a·x + b` for all `x ∈ S`. An affine agent is indifferent between a lottery and its
expected value (`RiskNeutral.map_sum_eq`). -/
def RiskNeutral (u : ℝ → ℝ) (S : Set ℝ) : Prop := ∃ a b : ℝ, ∀ x ∈ S, u x = a * x + b

/-- A utility function is **risk loving** on `S` when it is convex on `S`. A risk-loving agent
values a gamble at least as much as its expected value (`RiskLoving.le_map_sum`). -/
def RiskLoving (u : ℝ → ℝ) (S : Set ℝ) : Prop := ConvexOn ℝ S u

end Econlib.Preferences
