/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Optimal Growth with Unbounded Value: The Transversality Principle of Optimality

A worked example exercising the **unbounded-reward** principle of optimality
(`Econlib.Optimization.DynamicProgramming.Core.UnboundedOptimality`) on a concrete deterministic
dynamic program whose value function is unbounded, so the bounded Banach-fixed-point theory of
`Optimality.lean` (which needs a uniform bound `|v*| ≤ B`) does not apply. The tail term
`β^N · v*(s_N)` is instead killed by an explicit **transversality** condition, discharged here from
the model fact that feasible resource stocks stay bounded by the initial stock.

This file proves no new general-purpose theorem: The transversality principle of optimality lives
upstream (`value_ge_payoff_of_transversality`, `principle_of_optimality_of_transversality`,
`stationary_plan_payoff_eq_of_transversality`). Here we supply a concrete `UnboundedDetMDP`, solve
its Bellman equation in closed form, and check that the transversality / summability hypotheses
hold.

## The model

A textbook **exhaustible-resource / linear cake-eating** program, the simplest deterministic growth
model with an unbounded value function:

* State `x : ℝ≥0` — the resource stock on hand.
* Action `c : ℝ≥0` — how much to consume this period, feasible iff `c ∈ [0, x]`.
* Reward `u(x, c) = (c : ℝ)` — linear utility of consumption.
* Transition `f(x, c) = x - c` — the unconsumed stock carries over (truncated subtraction is honest
  here because every feasible action satisfies `c ≤ x`).
* Discount `β = 1/2 ∈ [0, 1)`.

This is a simplification of the canonical log/Cobb–Douglas Brock–Mirman model: That model's Bellman
operator violates the weighted-Blackwell discounting axiom of `Regularity.lean` (the weight blows
up as consumption tends to the whole stock), so it cannot route through the weighted fixed point;
and solving its one-step maximization in closed form is a `Real.log`-concavity / FOC argument. The
linear model keeps the value function unbounded — the whole point of the transversality layer —
while making the one-step Bellman supremum an order-only computation, so the file stays fully
proved.

## The mathematics

Because `β < 1`, waiting strictly wastes discounting, so it is optimal to **consume the entire
stock immediately**. The closed-form value is therefore `v*(x) = (x : ℝ)`, the optimal stationary
policy is `σ(x) = x`, and the optimal trajectory is `x, 0, 0, …`. The Bellman supremum

`sup_{c ∈ [0,x]} [ c + β·(x - c) ]`

is greatest at `c = x` (giving `x`) and bounded above by `x` everywhere (since `β ≤ 1` and
`x - c ≥ 0`), so `IsGreatest.csSup_eq` closes the fixed-point identity `v* = T v*` without calculus.

Transversality holds along *every* feasible plan, not just the optimum: The stock is monotone
nonincreasing along any feasible trajectory, so `0 ≤ stateSeq … N ≤ x`, whence
`0 ≤ β^N · v*(stateSeq … N) = β^N · stateSeq … N ≤ β^N · x → 0` by squeezing against the vanishing
geometric tail. Summability of the discounted reward stream follows from the same bound by
comparison with a geometric series.

## Main definitions and theorems

* `M : UnboundedDetMDP ℝ≥0 ℝ≥0` — the linear cake-eating program.
* `vStar : ℝ≥0 → ℝ` — the closed-form value function `x ↦ (x : ℝ)`.
* `σ : ℝ≥0 → ℝ≥0` — the optimal stationary policy `x ↦ x` (consume everything).
* `vStar_eq_bellman : ∀ s, vStar s = M.bellmanOperator vStar s` — the Bellman fixed-point identity.
* `vStar_unbounded : ¬ UniformBounded vStar` — the value is unbounded (bounded theory
  inapplicable).
* `value_ge_payoff : ∀ s π, M.isFeasible s π → M.discountedPayoff s π ≤ vStar s`.
* `vStar_eq_iSup_payoff` — **principle of optimality**: `v*` is the supremum of feasible payoffs.
* `stationary_optimal : ∀ s, M.discountedPayoff s (extractPlan σ M.transition s) = vStar s`.
-/

noncomputable section

namespace EconlibExamples.Optimization.OptimalGrowth

open Econlib.Optimization Econlib.Optimization.DynamicProgramming
open Filter Topology UnboundedDetMDP Blackwell
open scoped NNReal

/-- The discount factor `β = 1/2 ∈ [0, 1)`. -/
def β : ℝ := 1 / 2

/-- The **linear cake-eating** program as an unbounded-reward deterministic MDP: State and action
are nonnegative reals, the feasible consumption set is `[0, x]`, reward is linear consumption
`(c : ℝ)`, and the stock evolves by `x ↦ x - c`. There is no uniform reward bound — consumption can
be arbitrarily large from a large stock — so this is honestly an `UnboundedDetMDP`. -/
def M : UnboundedDetMDP ℝ≥0 ℝ≥0 where
  Γ x := Set.Icc 0 x
  reward _ c := (c : ℝ)
  transition x c := x - c
  β := β
  β_nonneg := by norm_num [β]
  β_lt_one := by norm_num [β]
  Γ_nonempty x := ⟨0, by simp⟩

/-- The closed-form value function: Consume the whole stock now, so `v*(x) = (x : ℝ)`. This is
unbounded over the state space `ℝ≥0`. -/
def vStar : ℝ≥0 → ℝ := fun x => (x : ℝ)

/-- The optimal stationary policy: Consume the entire current stock. -/
def σ : ℝ≥0 → ℝ≥0 := fun x => x

/-- **Bellman fixed-point identity.** The closed-form value `v*(x) = x` solves the Bellman
equation. The one-step problem `sup_{c ∈ [0,x]} [c + β(x - c)]` has greatest element `x`, attained
at `c = x` (eat everything) and dominated by `x` everywhere because `β ≤ 1` makes
`c + β(x-c) ≤ c + (x-c) = x`. -/
theorem vStar_eq_bellman : ∀ s, vStar s = M.bellmanOperator vStar s := by
  intro s
  -- The Bellman set has greatest element `(s : ℝ)`: attained at `c = s`, dominated by `s` else.
  have hgreatest : IsGreatest (M.bellmanSet vStar s) (s : ℝ) := by
    constructor
    · -- Membership: consume the entire stock, `c = s`, leaving `s - s = 0`.
      refine ⟨s, ⟨by simp, le_refl s⟩, ?_⟩
      simp only [M, vStar, β, tsub_self, NNReal.coe_zero, mul_zero, add_zero]
    · -- Upper bound: for `0 ≤ c ≤ s`, `c + β(s - c) ≤ c + (s - c) = s` since `β ≤ 1`, `s - c ≥ 0`.
      rintro r ⟨a, ⟨_, ha_le⟩, rfl⟩
      have hsub : ((s - a : ℝ≥0) : ℝ) = (s : ℝ) - (a : ℝ) := NNReal.coe_sub ha_le
      have hsub_nonneg : (0 : ℝ) ≤ (s : ℝ) - (a : ℝ) := by
        rw [← hsub]; exact NNReal.coe_nonneg _
      simp only [M, vStar, β, hsub]
      linarith
  rw [vStar, UnboundedDetMDP.bellmanOperator_eq, hgreatest.csSup_eq]

/-- The value function is **unbounded**, so the bounded principle of optimality
(`Optimality.lean`), which requires `|v*| ≤ B`, cannot be used: The transversality layer is
necessary. -/
theorem vStar_unbounded : ¬ UniformBounded vStar := by
  rintro ⟨B, hB⟩
  -- Evaluate the claimed bound at the stock `B + 1` (clamped to `ℝ≥0`): `|B + 1| ≤ B` is false.
  have hpos : (0 : ℝ) ≤ |B| + 1 := by positivity
  have := hB (Real.toNNReal (|B| + 1))
  rw [vStar, Real.coe_toNNReal _ hpos, abs_of_nonneg hpos] at this
  linarith [le_abs_self B]

/-- The Bellman set is bounded above at `v*` for every state — needed for the supremum identity to
be meaningful and for the transversality theorems' `hbdd` hypothesis. -/
theorem bellmanSet_bddAbove (s : ℝ≥0) :
    BddAbove (M.bellmanSet vStar s) := by
  -- `(s : ℝ)` is an upper bound, by the same `c + β(s - c) ≤ s` computation as the fixed point.
  refine ⟨(s : ℝ), ?_⟩
  rintro r ⟨a, ⟨_, ha_le⟩, rfl⟩
  have hsub : ((s - a : ℝ≥0) : ℝ) = (s : ℝ) - (a : ℝ) := NNReal.coe_sub ha_le
  have hsub_nonneg : (0 : ℝ) ≤ (s : ℝ) - (a : ℝ) := by rw [← hsub]; exact NNReal.coe_nonneg _
  simp only [M, vStar, β, hsub]
  linarith

/-- Along any plan the stock is monotone nonincreasing, so it never exceeds the initial stock:
`stateSeq s π N ≤ s`. (No feasibility needed — `ℝ≥0` truncated subtraction only ever shrinks.) -/
theorem stateSeq_le (s : ℝ≥0) (π : Plan ℝ≥0) (N : ℕ) :
    M.stateSeq s π N ≤ s := by
  induction N with
  | zero => simp
  | succ n ih =>
    -- `stateSeq (n+1) = stateSeq n - π n ≤ stateSeq n ≤ s`; NNReal subtraction only shrinks.
    rw [stateSeq_succ]
    exact le_trans (tsub_le_self) ih

/-- **Transversality holds along every feasible plan.** Since `0 ≤ stateSeq … N ≤ s`, the
discounted value tail `β^N · v*(stateSeq … N)` is squeezed between `0` and the geometric
`β^N · s → 0`. -/
theorem transversality (s : ℝ≥0) (π : Plan ℝ≥0) (_hπ : M.isFeasible s π) :
    Tendsto (fun N ↦ M.β ^ N * vStar (M.stateSeq s π N)) atTop (𝓝 0) := by
  -- Squeeze `0 ≤ β^N · stateSeq N ≤ β^N · s`; the geometric upper bound vanishes.
  have hgeom : Tendsto (fun N ↦ M.β ^ N * (s : ℝ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun N ↦ M.β ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one M.β_nonneg M.β_lt_one
    simpa using h0.mul_const (s : ℝ)
  refine squeeze_zero (fun N ↦ ?_) (fun N ↦ ?_) hgeom
  · -- nonnegativity: `β^N ≥ 0` and `vStar (…) = (stateSeq … : ℝ) ≥ 0`.
    exact mul_nonneg (pow_nonneg M.β_nonneg N) (NNReal.coe_nonneg _)
  · -- upper bound from `stateSeq N ≤ s`.
    have hle : (vStar (M.stateSeq s π N)) ≤ (s : ℝ) := by
      rw [vStar]; exact_mod_cast stateSeq_le s π N
    exact mul_le_mul_of_nonneg_left hle (pow_nonneg M.β_nonneg N)

/-- **Summability of the discounted reward stream along every feasible plan.** Each term is
squeezed between `0` and the geometric `β^t · s`, so the series converges by comparison. -/
theorem summable_reward (s : ℝ≥0) (π : Plan ℝ≥0) (hπ : M.isFeasible s π) :
    Summable fun t ↦ M.β ^ t * M.reward (M.stateSeq s π t) (π t) := by
  -- Comparison with the geometric `β^t · s`: feasibility gives `π t ≤ stateSeq t ≤ s`.
  have hgeom : Summable fun t ↦ M.β ^ t * (s : ℝ) :=
    (summable_geometric_of_lt_one M.β_nonneg M.β_lt_one).mul_right (s : ℝ)
  refine Summable.of_nonneg_of_le (fun t ↦ ?_) (fun t ↦ ?_) hgeom
  · -- nonnegativity: `β^t ≥ 0` and reward `= (π t : ℝ) ≥ 0`.
    exact mul_nonneg (pow_nonneg M.β_nonneg t) (NNReal.coe_nonneg _)
  · -- `reward (stateSeq t) (π t) = (π t : ℝ) ≤ (s : ℝ)` from `π t ≤ stateSeq t ≤ s`.
    have hπt : π t ≤ M.stateSeq s π t := (hπ t).2
    have hπt_s : π t ≤ s := le_trans hπt (stateSeq_le s π t)
    have hle : M.reward (M.stateSeq s π t) (π t) ≤ (s : ℝ) := by
      simp only [M]; exact_mod_cast hπt_s
    exact mul_le_mul_of_nonneg_left hle (pow_nonneg M.β_nonneg t)

/-- **Principle of optimality (≥ direction).** The value `v*` dominates the discounted payoff of
any feasible plan, by `value_ge_payoff_of_transversality`. -/
theorem value_ge_payoff (s : ℝ≥0) (π : Plan ℝ≥0) (hπ : M.isFeasible s π) :
    M.discountedPayoff s π ≤ vStar s :=
  M.value_ge_payoff_of_transversality vStar vStar_eq_bellman bellmanSet_bddAbove s π hπ
    (summable_reward s π hπ) (transversality s π hπ)

/-- **Principle of optimality (transversality form).** The value function equals the supremum of
discounted payoffs over all feasible plans, via `principle_of_optimality_of_transversality`. -/
theorem vStar_eq_iSup_payoff (s : ℝ≥0) :
    vStar s = sSup {p : ℝ | ∃ π : Plan ℝ≥0, M.isFeasible s π ∧ p = M.discountedPayoff s π} :=
  M.principle_of_optimality_of_transversality vStar vStar_eq_bellman bellmanSet_bddAbove s
    (fun π hπ => summable_reward s π hπ) (fun π hπ => transversality s π hπ)

/-- The optimal stationary policy `σ x = x` achieves the Bellman value identity at every state:
`v*(x) = u(x, x) + β·v*(x - x) = x + β·0 = x`. -/
theorem σ_opt : ∀ s, vStar s = M.reward s (σ s) + M.β * vStar (M.transition s (σ s)) := by
  intro s
  -- `σ s = s`, so `transition s (σ s) = s - s = 0` and `v*(0) = 0`: RHS = `s + β·0 = s`.
  simp only [M, σ, vStar, β, tsub_self, NNReal.coe_zero, mul_zero, add_zero]

/-- The plan extracted from the stationary policy `σ` is feasible: Every action
`σ(stateSeq …) =
stateSeq …` lies in `Γ(stateSeq …) = [0, stateSeq …]`. -/
theorem extractPlan_σ_feasible (s : ℝ≥0) : M.isFeasible s (extractPlan σ M.transition s) := by
  intro t
  -- The action is `σ (state) = state`, which lies in `Γ (state) = [0, state]`.
  rw [extractPlan_eq_σ, M.stateSeq_eq_extractState]
  exact ⟨by simp, le_refl _⟩

/-- **The optimal stationary policy attains the value.** By
`stationary_plan_payoff_eq_of_transversality`, consuming the entire stock immediately yields a
discounted payoff equal to `v*`. -/
theorem stationary_optimal (s : ℝ≥0) :
    M.discountedPayoff s (extractPlan σ M.transition s) = vStar s :=
  M.stationary_plan_payoff_eq_of_transversality vStar σ σ_opt s
    (summable_reward s _ (extractPlan_σ_feasible s))
    (transversality s _ (extractPlan_σ_feasible s))

end EconlibExamples.Optimization.OptimalGrowth
