/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import EconlibExamples.Optimization.BudgetMaximumTheorem
import EconlibExamples.Optimization.ConstrainedQP
import EconlibExamples.Optimization.DiscreteCakeEating
import EconlibExamples.Optimization.EndogenousChainOptimalPolicy
import EconlibExamples.Optimization.EnvelopeGrowth
import EconlibExamples.Optimization.EqualityConstrainedQP
import EconlibExamples.Optimization.HotellingProfit
import EconlibExamples.Optimization.MonopolyPricing
import EconlibExamples.Optimization.MonotoneComparativeStatics
import EconlibExamples.Optimization.OptimalGrowth
import EconlibExamples.Optimization.SlaterDuality
import EconlibExamples.Optimization.StateDependentEnvelope

/-!
# EconlibExamples.Optimization

Worked examples of canonical optimization results, formalized against the `Econlib.Optimization`
API. Each example file is a self-contained tutorial: It constructs a textbook problem, names the
claim, and proves it using theorems that already exist in the library.

Per-file index:

* `MonopolyPricing` — linear-demand monopolist: The optimal price `p* = (a+bc)/(2b)` globally
  maximizes profit (exact gap `b·(p*−p)²`), with the first-order condition `π′(p*) = 0` and the
  second-order condition `π″(p*) ≤ 0` read off via the unconstrained optimization API
* `SlaterDuality` — a one-variable convex program (`max x` s.t. `x ≤ 1` on `[0,2]`): Slater's
  condition holds, so `strongDuality_scalar_of_isSlater` gives zero duality gap; the common optimal
  value is `1`
* `ConstrainedQP` — `max −(x−a)²` s.t. `x ≤ b` (binding, `b ≤ a`): An explicit `MaxKKT` certificate
  with multiplier `2(a−b)` and exact Lagrangian gap `(y−b)²`, closed by `MaxKKT.isMaxOn`
* `EqualityConstrainedQP` — `max −(x₀−a)²−(x₁−d)²` s.t. the *equality* `x₀+x₁=s`: the projection
  `x* = ((a−d+s)/2,(d−a+s)/2)` is globally optimal over the feasible line via a `MaxKKTEq`
  certificate with sign-unrestricted multiplier `μ = a+d−s`, closed by `MaxKKTEq.isMaxOn` —
  the full equality-and-inequality KKT form the inequality-only `MaxKKT` cannot reach
* `DiscreteCakeEating` — a concrete finite deterministic MDP: The closed-form value function is the
  unique Bellman fixed point, the stationary policy attains it (`stationary_plan_payoff_eq`), and
  the value equals the supremum of discounted feasible-plan payoffs (`principle_of_optimality`)
* `HotellingProfit` — a single-output firm with quadratic cost: At interior prices the supply is
  unique, so Hotelling's lemma (`hasGradientAt_profitFunction`) gives `∇Π(p) = y*(p)` — the supply
  equals the gradient of the profit function
* `BudgetMaximumTheorem` — Berge's maximum theorem on a consumer's budget correspondence as the
  price varies: Indirect utility is continuous and the demand correspondence is upper
  hemicontinuous and compact-valued, reusing the budget-set hemicontinuity lemmas from `Equilibrium`
* `EndogenousChainOptimalPolicy` — the optimal-policy interface end to end: A strictly concave,
  state-dependent objective on `[0,1] × Fin 2` yields (via Berge + strict concavity + continuous
  selection) a continuous optimal policy, hence an `EndogenousMarkovChain`, hence a stationary
  distribution of the optimally controlled economy (`exists_stationary_under_optimal_policy`)
* `MonotoneComparativeStatics` — Topkis monotone comparative statics via the ordered-policy
  certificate: an effort payoff `θ·a − a²` with strictly increasing differences yields (through
  `OrderedPolicyCertificate.ofStrictIncreasingDifferences`) an optimal effort policy monotone in
  productivity (`optimalEffort_monotone`), pinned to `0` at `θ = 0` and `1` at `θ = 2` so the
  comparative static is genuinely non-constant (`optimalEffort_strictMono_witness`)
* `CollateralLogUtility` — a collateral/credit DP with the canonical **log** Inada utility
  (`InadaUtility.log`, unbounded): The model is constructible (log is in scope), receives a genuine
  value function via the *weighted* fixed-point core (`weightedValueFunction`), and discharges the
  economic theorem `feasible_value_le` with the weighted `BddAbove` certificate a uniform bound
  could not supply
* `CollateralSqrtUtility` — the same collateral DP with **`√c`** utility (`InadaUtility.sqrt`, CRRA
  `γ = 1/2`), which *is* closed-ray concave and continuous at zero consumption: It discharges the
  `RegularCollateralDP` regularity fields outright (both Bewley/Aiyagari hard points are derived at
  the source, in `CollateralStrictConcavity` and `CollateralErgodicCeiling`) and reaches the
  endogenous-chain payoff **unconditionally** — a stationary wealth distribution under the optimal
  savings policy (`sqrtModel_exists_stationary`)
* `OptimalGrowth` — an unbounded-value deterministic growth/extraction program (linear
  cake-eating): The closed-form value is the Bellman fixed point and the consume-now policy is
  optimal via the *transversality* principle of optimality (`…_of_transversality`), which the
  unbounded value function genuinely requires (the bounded theory does not apply, as
  `vStar_unbounded` records)
* `EnvelopeGrowth` — a bounded `arctan` accumulation program in the "next state as control"
  formulation: The closed-form value `arctan w + 3π/4` is the Bellman fixed point, and the
  *derived* Benveniste-Scheinkman envelope condition (`envelope_deriv_dp_of_transition_indep`)
  yields `(v*)′(w₀) = 1/(1+w₀²)` on `(0,1)` with no successor-differentiability assumed — value
  differentiability is a conclusion, obtained from concavity, `C¹` reward, and the
  state-independent transition
* `StateDependentEnvelope` — the companion with a genuinely **state-dependent** transition
  `f(w,a) = (w+a)/2` on `[1,2]`: The closed-form value `arctan w` is the Bellman fixed point (a
  reward compensator `−½·arctan((w+2)/2)` cancels the continuation at the optimal policy), and the
  general Benveniste-Scheinkman envelope (`envelope_deriv_dp_of_diffSucc`) yields
  `(v*)′(w₀) = 1/(1+w₀²)` with a **nonzero** continuation chain term (`∂f/∂w = 1/2`) that cancels
  the compensator's marginal contribution — exercising the live multiplier `EnvelopeGrowth`'s
  vanishing-chain-term collapse never reaches
-/
