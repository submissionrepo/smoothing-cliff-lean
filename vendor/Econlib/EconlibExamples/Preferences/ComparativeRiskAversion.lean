/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Comparative Risk Aversion: A More Risk-Averse CARA Agent Demands a Lower Certainty Equivalent

Constant-absolute-risk-aversion (CARA) utility `u_α(x) = -exp(-α x)` is the textbook family for
isolating the Arrow–Pratt coefficient of absolute risk aversion: Its coefficient is *constant* and
equal to `α` everywhere. This file instantiates the comparative-risk-aversion API on two concrete
CARA agents — a low-aversion agent (`α = 1`) and a high-aversion agent (`α = 2`) — and shows the
two classic consequences of `α_hi > α_lo`:

* the high-α agent's Arrow–Pratt coefficient dominates the low-α agent's pointwise, so it is *more
  risk averse* in Pratt's sense; and
* over a common fair-coin lottery, the more-risk-averse agent's certainty equivalent is no higher
  (`cu ≤ cv`) — it would accept no more sure money in place of the gamble. (The Pratt comparison
  delivers the weak inequality; we do not claim strictness.)

We do not develop any new theory: Every conclusion is an application of an existing Econlib theorem
to concrete data.

## The model

Two agents differ only in their CARA parameter:

* `caraLo` has `α_lo = 1` (less risk averse);
* `caraHi` has `α_hi = 2` (more risk averse).

Each is built as a `TwiceDiffUtility` on `domain = Set.univ` with

`u_α(x) = -exp(-α x)`, `u'_α(x) = α exp(-α x)`, `u''_α(x) = -α² exp(-α x)`.

The common lottery is the fair coin with outcomes `(0, 1)` and probabilities `(1/2, 1/2)`, bundled
as a `FinLottery 2`.

## The mathematics

For CARA, the Arrow–Pratt coefficient `-u''/u'` collapses to `α exp(-α x) · α / (α exp(-α x)) = α`,
constant in `x` (using `exp ≠ 0`). Since `α_hi = 2 ≥ 1 = α_lo`, the high agent's coefficient
dominates pointwise, which by `more_risk_averse_iff_absoluteRiskAversion_ge` is exactly the Pratt
relation `MoreRiskAverseOn`. Feeding that relation, the shared `domain = Set.univ`, and certainty
equivalents obtained from `certainty_equivalent_exists` (both `u_α` are continuous) into
`MoreRiskAverseOn.le_certaintyEquivalent` gives `cu ≤ cv`: The more risk-averse agent's
certainty equivalent is no larger.

## Main definitions and theorems

* `caraUtility` — the `TwiceDiffUtility` for `CARA(α)` on `Set.univ`, given `0 < α`.
* `caraLo`, `caraHi` — the two agents, `α = 1` and `α = 2`.
* `ara_lo_eq`, `ara_hi_eq` — each agent's Arrow–Pratt coefficient equals its `α` at every point.
* `hi_more_risk_averse` — `caraHi` is more risk averse than `caraLo` on the common domain.
* `lottery` — the common fair-coin lottery over `Fin 2`, bundled as a `FinLottery 2`.
* `caraHi_certainty_equivalent_exists` / `caraLo_certainty_equivalent_exists` — each agent has a
  certainty equivalent over the lottery.
* `hi_lower_certainty_equivalent` — over the fair-coin lottery, every certainty equivalent of
  `caraHi` is `≤` every certainty equivalent of `caraLo` (universal form).
-/

noncomputable section

namespace EconlibExamples.Preferences.ComparativeRiskAversion

open Econlib.Preferences

/-! ## The CARA utility as a `TwiceDiffUtility` -/

/-- The CARA agent with coefficient `α > 0`: `u(x) = -exp(-α x)` on all of `ℝ`. We do not rebuild
the derivative structure by hand: This is the library `ConstantAbsoluteRiskAversionUtility α`
packaged as a `TwiceDiffUtility` through its `toTwiceDiffUtility` bridge, so the closed-form
derivative fields (`u' = α exp(-α x)`, `u'' = -α² exp(-α x)`), the exponential chain-rule
obligations, and `u' > 0` all come from the library construction. -/
def caraUtility (α : ℝ) (hα : 0 < α) : TwiceDiffUtility :=
  (ConstantAbsoluteRiskAversionUtility.mk α hα).toTwiceDiffUtility

/-- The continuity of `caraUtility α hα`'s utility, needed to obtain certainty equivalents. -/
lemma continuous_caraUtility_u (α : ℝ) (hα : 0 < α) :
    Continuous (caraUtility α hα).u :=
  (ConstantAbsoluteRiskAversionUtility.mk α hα).continuous_u

/-! ## The two agents -/

/-- The less risk-averse agent: `CARA(1)`. -/
def caraLo : TwiceDiffUtility := caraUtility 1 one_pos

/-- The more risk-averse agent: `CARA(2)`. -/
def caraHi : TwiceDiffUtility := caraUtility 2 two_pos

/-! ## Arrow–Pratt coefficients are constant and equal to `α` -/

/-- The Arrow–Pratt coefficient of any CARA agent is its parameter `α`, at every point. This is the
library lemma `ConstantAbsoluteRiskAversionUtility.absoluteRiskAversion_eq_alpha` read off the
bridged utility — the `-u''/u' = α² exp(-α x) / (α exp(-α x)) = α` cancellation lives there. -/
lemma ara_caraUtility_eq (α : ℝ) (hα : 0 < α) (x : ℝ)
    (hx : x ∈ (caraUtility α hα).domain) :
    (caraUtility α hα).absoluteRiskAversion x hx = α :=
  (ConstantAbsoluteRiskAversionUtility.mk α hα).absoluteRiskAversion_eq_alpha x hx

/-- `caraLo`'s Arrow–Pratt coefficient is `1` everywhere. -/
lemma ara_lo_eq (x : ℝ) (hx : x ∈ caraLo.domain) :
    caraLo.absoluteRiskAversion x hx = 1 :=
  ara_caraUtility_eq 1 one_pos x hx

/-- `caraHi`'s Arrow–Pratt coefficient is `2` everywhere. -/
lemma ara_hi_eq (x : ℝ) (hx : x ∈ caraHi.domain) :
    caraHi.absoluteRiskAversion x hx = 2 :=
  ara_caraUtility_eq 2 two_pos x hx

/-! ## `caraHi` is more risk averse -/

/-- The two agents share the same domain `Set.univ`. -/
lemma hi_lo_same_domain : caraHi.domain = caraLo.domain := rfl

/-- **`caraHi` is more risk averse than `caraLo`.** Pointwise the high agent's Arrow–Pratt
coefficient (`2`) dominates the low agent's (`1`), which is exactly Pratt's `MoreRiskAverseOn`
relation by `more_risk_averse_iff_absoluteRiskAversion_ge`. -/
theorem hi_more_risk_averse : MoreRiskAverseOn caraHi.u caraLo.u caraLo.domain := by
  rw [more_risk_averse_iff_absoluteRiskAversion_ge caraHi caraLo hi_lo_same_domain]
  intro x hx_hi hx_lo
  rw [ara_hi_eq x hx_hi, ara_lo_eq x hx_lo]
  norm_num

/-! ## The common fair-coin lottery -/

/-- The common fair-coin lottery, bundled as a `FinLottery 2`: prizes `![0, 1]` under the fair coin
`![1/2, 1/2]`. The probabilities are supplied through the `finDist%` literal builder, so the
distribution axioms are discharged automatically and invalid weights are inexpressible. -/
def lottery : FinLottery 2 where
  outcome := ![0, 1]
  prob := finDist% ![1 / 2, 1 / 2]

/-! ## The more risk-averse agent has a lower certainty equivalent -/

/-- A certainty equivalent of `caraHi` over the fair-coin lottery exists (the utility is
continuous). -/
theorem caraHi_certainty_equivalent_exists :
    ∃ cu : ℝ, IsCertaintyEquivalent caraHi.u lottery cu :=
  certainty_equivalent_exists (u := caraHi.u) (L := lottery)
    (continuous_caraUtility_u 2 two_pos)

/-- A certainty equivalent of `caraLo` over the fair-coin lottery exists. -/
theorem caraLo_certainty_equivalent_exists :
    ∃ cv : ℝ, IsCertaintyEquivalent caraLo.u lottery cv :=
  certainty_equivalent_exists (u := caraLo.u) (L := lottery)
    (continuous_caraUtility_u 1 one_pos)

/-- **The more risk-averse agent's certainty equivalent is lower.** Over the common fair-coin
lottery, every certainty equivalent `cu` of the more risk-averse `caraHi` is `≤` every certainty
equivalent `cv` of `caraLo` — a universal statement, not merely an existence witness. (Existence of
each is `caraHi_certainty_equivalent_exists` / `caraLo_certainty_equivalent_exists`.) It is a direct
application of `MoreRiskAverseOn.le_certaintyEquivalent`; the `domain = Set.univ` makes
every membership obligation trivial. -/
theorem hi_lower_certainty_equivalent {cu cv : ℝ}
    (hcu : IsCertaintyEquivalent caraHi.u lottery cu)
    (hcv : IsCertaintyEquivalent caraLo.u lottery cv) :
    cu ≤ cv :=
  MoreRiskAverseOn.le_certaintyEquivalent caraHi caraLo hi_lo_same_domain
    lottery (fun _ => Set.mem_univ _) hi_more_risk_averse
    cu cv (Set.mem_univ _) (Set.mem_univ _) hcu hcv

end EconlibExamples.Preferences.ComparativeRiskAversion
