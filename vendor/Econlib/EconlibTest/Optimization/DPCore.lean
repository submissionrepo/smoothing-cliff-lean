/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import EconlibExamples.Optimization.DiscreteCakeEating
import EconlibExamples.Optimization.OptimalGrowth
import Mathlib

/-!
# Dynamic-programming core non-vacuity witnesses (deterministic + stochastic Bellman)

Compile-time semantic witnesses for the *bounded* and *unbounded* deterministic Bellman layer
(`Bellman`, `BellmanOperator`, `Optimality`, `UnboundedOptimality`) and the *finite/stochastic*
layer (`Stochastic`, `MDP`) of `Econlib.Optimization.DynamicProgramming`. Every abstract
sup-over-actions / contraction / value-vs-payoff statement is forced through a concrete MDP whose
value function and optimal policy are hand-solved, so a silent reversal — sup↔inf in the Bellman
operator, payoff↔value inequality, contraction modulus `β`↔`βμ`, or a transition row/column
transpose — would fail to typecheck.

## Anchoring models

* **Chunk 1 (deterministic):** the growing-cake `DetMDP (Fin 2) (Fin 2)` of
  `EconlibExamples.Optimization.DiscreteCakeEating` (value `v* = (8/3, 16/3)`, policy *wait when
  small / eat when large*) for the bounded Banach layer, and the linear cake-eating
  `UnboundedDetMDP ℝ≥0 ℝ≥0` of `EconlibExamples.Optimization.OptimalGrowth` (value `v*(x) = x`,
  consume-everything) for the unbounded transversality layer.
* **Chunk 2 (finite/stochastic):** a fresh hand-solved **explore-or-stay** `FinMDP 2 (Fin 2)`. Two
  states (`0` = low, `1` = high) and two actions (`0` = *stay*, Dirac transition keeping the state;
  `1` = *explore*, a genuine `50/50` transition over `{0,1}`). Rewards `r(0,0)=0`, `r(1,0)=6`,
  `r(s,1)=1`, discount `β = 1/2`. Solving the coupled `max`-system gives the **closed-form value**
  `v* = (16/3, 12)` with the optimal action **flipping** with the state: At low it is best to
  *explore* (`16/3 > 8/3`), at high it is best to *stay* (`12 > 16/3`). The `50/50` continuation
  `E[v*] = 26/3` is genuinely averaged, so the witness exercises a real `FinDist.expect`, not a
  point mass.

## What each block catches

* **Operator structure** — `bellmanOperator_monotone` / `_discounting` / `_bounded` /
  `_apply_abs_sub_le` / `bellmanSet_bddAbove` are run on the concrete cake operator. The orientation
  and modulus are pinned by exact-value witnesses: `cake_bellmanOperator_apply_zero`
  (`T v* 0 = 8/3`, the *sup* — an inf-Bellman flip gives `7/3`),
  `cake_bellmanOperator_discounting_eq` (the discounting
  bound is *attained with equality*, gap exactly `β·c = 1`, not `β²·c`), and
  `cake_bellmanSet_eq_distinct_pair` (the Bellman set is the genuinely two-point `{8/3, 7/3}`).
* **Fixed point / value iteration** — `existsUnique_fixedPoint`,
  `value_iteration_converges_to_valueFunction` (limit written against the hand-computed `cakeV`, not
  the abstract `valueFunction`), `valueFunction_ge_payoff`,
  `stationary_plan_payoff_eq_valueFunction`, `stationary_policy_optimal_valueFunction`,
  `exists_optimalPolicy_valueFunction` are exercised on the cake `M`, where `v*` is known in closed
  form; a payoff↔value inequality reversal would contradict `valueFunction_ge_payoff`.
* **Unbounded transversality** — `value_ge_partialPayoff_add_tail` (on the unbounded growth model),
  with the companion `growth_value_gt_partialPayoff_add_tail_suboptimal` showing the bound is
  *strict* for a suboptimal (never-consume) plan, so the `≥` direction is genuinely tested;
  `summable_discountedPayoff` / `tendsto_pow_beta_mul` on the cake model where `reward_bounded`
  is available.
* **Finite / stochastic** — `FinMDP.bellmanOperator_existsUnique_fixedPoint`,
  `FinMDP.exists_optimalAction` (selecting the hand-computed argmax *and* confirming the
  alternative is strictly worse), the `finiteBellmanSet_*` / `finiteBellmanOperator_*` structural
  stack, `stochBellmanOperator_contraction` with modulus exactly the stated `β` (pinned by
  `detR_stoch_gap_eq_beta`, where the contraction bound is *attained with equality* on `v ≡ 1`,
  `w ≡ 0`), and `bellman_dirac_eq` collapsing the stochastic operator to the deterministic one on a
  Dirac kernel (the row/column transpose catch).
-/

noncomputable section

namespace EconlibTest.Optimization.DPCore

open Econlib.Optimization Econlib.Optimization.DynamicProgramming
open Econlib.Probability
open Blackwell UnboundedDetMDP

/-! ## Chunk 1 — Bounded deterministic Bellman (growing-cake model)

We reuse the fully hand-solved growing-cake `DetMDP (Fin 2) (Fin 2)` of `DiscreteCakeEating`,
whose value function is `cake.value = (8/3, 16/3)`. Each abstract endpoint below is anchored on
it. -/

/-- The growing-cake bounded MDP, value, and Bellman-fixed-point fact, abbreviated. -/
private abbrev cakeM : DetMDP (Fin 2) (Fin 2) := EconlibExamples.Optimization.DiscreteCakeEating.M
private abbrev cakeV : Fin 2 → ℝ := EconlibExamples.Optimization.DiscreteCakeEating.value

open EconlibExamples.Optimization.DiscreteCakeEating
  (value value_is_bellman_fixedPoint value_bounded value_eq_banach_fixedPoint optimalPolicy
    optimalPolicy_opt bellmanSet_eq_pair)

/-! ### Operator structure -/

/-- **The cake operator at state `0` is the *supremum* `8/3`, not the infimum `7/3`.** The two
one-step candidates at the small state are *wait* (`0 + ½·v(1) = 8/3`) and
*eat* (`1 + ½·v(0) = 7/3`),
so `T v* 0 = max (8/3) (7/3) = 8/3`. This is the direct value test that a sup↔inf flip in
`bellmanOperator` would fail — an inf-Bellman operator gives `7/3` here. -/
theorem cake_bellmanOperator_apply_zero : cakeM.bellmanOperator cakeV 0 = 8 / 3 := by
  rw [bellmanOperator_eq, bellmanSet_eq_pair, csSup_pair]
  have h0 : cakeM.reward 0 0 + cakeM.β * cakeV (cakeM.transition 0 0) = 8 / 3 := by
    norm_num [EconlibExamples.Optimization.DiscreteCakeEating.M, cakeV, value]
  have h1 : cakeM.reward 0 1 + cakeM.β * cakeV (cakeM.transition 0 1) = 7 / 3 := by
    norm_num [EconlibExamples.Optimization.DiscreteCakeEating.M, cakeV, value]
  rw [h0, h1, sup_eq_left.mpr (by norm_num : (7 : ℝ) / 3 ≤ 8 / 3)]

/-- **`bellmanOperator_monotone` is non-vacuous and oriented correctly.** Bumping the continuation
from `v*` to `v* + 1` (pointwise larger) weakly raises the Bellman image at every state. A sup↔inf
flip in `bellmanOperator` would reverse this; `cake_bellmanOperator_apply_zero`
(sup = `8/3`, not the
inf `7/3`) is the accompanying direct value test that orientation is correct. -/
theorem cake_bellmanOperator_monotone (s : Fin 2) :
    cakeM.bellmanOperator cakeV s ≤ cakeM.bellmanOperator (fun s' => cakeV s' + 1) s :=
  bellmanOperator_monotone cakeM cakeV (fun s' => cakeV s' + 1)
    ⟨16 / 3 + 1, fun s' => by fin_cases s' <;> norm_num [cakeV, value]⟩
    (fun s' => by linarith) s

/-- **The discounting modulus is *exactly* `β`, attained with equality at state `0`.**
Adding `c = 2`
to the continuation raises the operator image at the small state from `T v* 0 = 8/3` to
`T(v* + 2) 0 = 11/3` — a gap of *exactly* `β · c = ½ · 2 = 1`, not merely `≤ 1`. A continuation
underweighted by `β²` instead of `β` would give a strictly smaller gap and fail this equality.
(The two candidates of `T(v* + 2) 0` are *wait* `½·(16/3 + 2) = 11/3` and *eat* `1 + ½·(8/3 + 2) =
10/3`, with sup `11/3`.) -/
theorem cake_bellmanOperator_discounting_eq :
    cakeM.bellmanOperator (fun s' => cakeV s' + 2) 0 =
      cakeM.bellmanOperator cakeV 0 + cakeM.β * 2 := by
  rw [cake_bellmanOperator_apply_zero, bellmanOperator_eq, bellmanSet_eq_pair, csSup_pair]
  have h0 : cakeM.reward 0 0 + cakeM.β *
      (fun s' => cakeV s' + 2) (cakeM.transition 0 0) = 11 / 3 := by
    norm_num [EconlibExamples.Optimization.DiscreteCakeEating.M, cakeV, value]
  have h1 : cakeM.reward 0 1 + cakeM.β *
      (fun s' => cakeV s' + 2) (cakeM.transition 0 1) = 10 / 3 := by
    norm_num [EconlibExamples.Optimization.DiscreteCakeEating.M, cakeV, value]
  rw [h0, h1, sup_eq_left.mpr (by norm_num : (10 : ℝ) / 3 ≤ 11 / 3)]
  norm_num [EconlibExamples.Optimization.DiscreteCakeEating.M]

/-- **`bellmanOperator_discounting` pins the modulus to `β`.** Adding a constant `c = 2 ≥ 0` to the
continuation raises the Bellman image by at most `β · c = 1`. This is the discounting half of
Blackwell's sufficient conditions; the bound is `β·c`, not `c`. The companion
`cake_bellmanOperator_discounting_eq` shows the bound is *attained with equality* at state `0`, so
the modulus is exactly `β` (not `β²`). -/
theorem cake_bellmanOperator_discounting (s : Fin 2) :
    cakeM.bellmanOperator (fun s' => cakeV s' + 2) s ≤
      cakeM.bellmanOperator cakeV s + cakeM.β * 2 :=
  bellmanOperator_discounting cakeM cakeV 2
    ⟨16 / 3, fun s' => by fin_cases s' <;> norm_num [cakeV, value]⟩ (by norm_num) s

/-- **`bellmanOperator_bounded` preserves boundedness.** The Bellman image of the bounded `v*` is
again uniformly bounded — the precondition behind every fixed-point and value-iteration step. -/
theorem cake_bellmanOperator_bounded : UniformBounded (cakeM.bellmanOperator cakeV) :=
  bellmanOperator_bounded cakeM cakeV
    ⟨16 / 3, fun s' => by fin_cases s' <;> norm_num [cakeV, value]⟩

/-- **`bellmanOperator_apply_abs_sub_le` is the pointwise sup-norm contraction estimate.** With the
two continuations `v*` and `v* + 1`, the pointwise gap of the Bellman images is at most
`β · sup|v* - (v*+1)| = β · 1`. The contraction modulus is `β`, not `1`. -/
theorem cake_bellmanOperator_apply_abs_sub_le (s : Fin 2) :
    |cakeM.bellmanOperator cakeV s - cakeM.bellmanOperator (fun s' => cakeV s' + 1) s| ≤
      cakeM.β * ⨆ s, |cakeV s - (cakeV s + 1)| :=
  bellmanOperator_apply_abs_sub_le cakeM cakeV (fun s' => cakeV s' + 1)
    ⟨16 / 3, fun s' => by fin_cases s' <;> norm_num [cakeV, value]⟩
    ⟨16 / 3 + 1, fun s' => by fin_cases s' <;> norm_num [cakeV, value]⟩ s

/-- **`bellmanSet_bddAbove` is satisfied by the concrete *two-candidate* Bellman set.** At the small
state the Bellman set is exactly `{8/3, 7/3}` (one value per action, via `bellmanSet_eq_pair`), and
the two candidates are *distinct* (`8/3 ≠ 7/3`) — so this is genuinely a two-point set whose two
actions give different one-step values, not a collapsed singleton. It is bounded above; the abstract
lemma's `v*`-bounded hypothesis is discharged from the concrete model. -/
theorem cake_bellmanSet_bddAbove (s : Fin 2) : BddAbove (cakeM.bellmanSet cakeV s) :=
  bellmanSet_bddAbove cakeM cakeV
    ⟨16 / 3, fun s' => by fin_cases s' <;> norm_num [cakeV, value]⟩ s

/-- The Bellman set at the small state is the **distinct** two-candidate set `{8/3, 7/3}`: *wait*
gives `8/3`, *eat* gives `7/3`, and `8/3 ≠ 7/3`. Dropping or duplicating an action would collapse
this to a singleton and be caught here. -/
theorem cake_bellmanSet_eq_distinct_pair :
    cakeM.bellmanSet cakeV 0 = {8 / 3, 7 / 3} ∧ (8 / 3 : ℝ) ≠ 7 / 3 := by
  refine ⟨?_, by norm_num⟩
  rw [bellmanSet_eq_pair]
  have h0 : cakeM.reward 0 0 + cakeM.β * cakeV (cakeM.transition 0 0) = 8 / 3 := by
    norm_num [EconlibExamples.Optimization.DiscreteCakeEating.M, cakeV, value]
  have h1 : cakeM.reward 0 1 + cakeM.β * cakeV (cakeM.transition 0 1) = 7 / 3 := by
    norm_num [EconlibExamples.Optimization.DiscreteCakeEating.M, cakeV, value]
  rw [h0, h1]

/-! ### Fixed point, value iteration, optimality -/

/-- **`DetMDP.bellmanOperator_existsUnique_fixedPoint` on a concrete model.** The Bellman operator
has a *unique* bounded fixed point; the hand-computed `cake.value` is that unique witness, so the
`∃!` is non-vacuous and its uniqueness clause forces `cake.value` to be `cakeM.valueFunction`. -/
theorem cake_existsUnique_fixedPoint :
    cakeM.valueFunction = cakeV ∧
      (∃! v : Fin 2 → ℝ, UniformBounded v ∧ ∀ s, v s = cakeM.bellmanOperator v s) := by
  refine ⟨value_eq_banach_fixedPoint, ?_⟩
  exact cakeM.bellmanOperator_existsUnique_fixedPoint

/-- **`value_iteration_converges_to_valueFunction` is non-vacuous — converging to the
*hand-computed*
`cakeV = (8/3, 16/3)`.** From the zero start `v₀ ≡ 0`, the Bellman iterates `Tⁿ 0` converge in the
sup norm to `cakeV s` at every state. The limit is written against the explicit closed form
`cakeV`, not the abstract `cakeM.valueFunction` (the two coincide by `value_eq_banach_fixedPoint`),
so this checks genuine convergence to `(8/3, 16/3)`, not merely to whatever fixed point the plumbing
produces. -/
theorem cake_value_iteration_converges :
    Filter.Tendsto
      (fun n => ⨆ s, |bellmanIterate cakeM (fun _ => 0) n s - cakeV s|)
      Filter.atTop (nhds 0) := by
  have h := cakeM.value_iteration_converges_to_valueFunction (fun _ => 0) ⟨0, fun s => by simp⟩
  rwa [value_eq_banach_fixedPoint] at h

/-- **`DetMDP.valueFunction_ge_payoff`: Value dominates payoff (correct direction).** Every
feasible plan from any state earns a discounted payoff *no greater than* the value function. A
reversed inequality (`value ≤ payoff`) would be false here since `value` is the supremum. -/
theorem cake_valueFunction_ge_payoff (s : Fin 2) (π : Plan (Fin 2))
    (hπ : cakeM.isFeasible s π) :
    cakeM.discountedPayoff s π ≤ cakeM.valueFunction s :=
  cakeM.valueFunction_ge_payoff s π hπ

/-- **`DetMDP.stationary_plan_payoff_eq_valueFunction`: The optimal policy attains the value.** The
*wait-small / eat-large* policy is Bellman-consistent with `cakeM.valueFunction` (transported from
`optimalPolicy_opt` through `value_eq_banach_fixedPoint`), so its discounted payoff equals the
value function at every state. -/
theorem cake_stationary_plan_payoff_eq_valueFunction (s : Fin 2) :
    cakeM.discountedPayoff s (extractPlan optimalPolicy cakeM.transition s) =
      cakeM.valueFunction s :=
  cakeM.stationary_plan_payoff_eq_valueFunction optimalPolicy
    (fun s' => by rw [value_eq_banach_fixedPoint]; exact optimalPolicy_opt s') s

/-- **`DetMDP.stationary_policy_optimal_valueFunction`: Full optimality of the policy.** The
optimal policy is feasible, attains `cakeM.valueFunction`, and weakly dominates the discounted
payoff of *every* feasible plan — the genuine optimality statement, not mere value-attainment. -/
theorem cake_stationary_policy_optimal_valueFunction (s : Fin 2) :
    cakeM.isFeasible s (extractPlan optimalPolicy cakeM.transition s) ∧
      cakeM.discountedPayoff s (extractPlan optimalPolicy cakeM.transition s) =
        cakeM.valueFunction s ∧
      ∀ π : Plan (Fin 2), cakeM.isFeasible s π →
        cakeM.discountedPayoff s π ≤
          cakeM.discountedPayoff s (extractPlan optimalPolicy cakeM.transition s) :=
  cakeM.stationary_policy_optimal_valueFunction optimalPolicy (fun _ => Set.mem_univ _)
    (fun s' => by rw [value_eq_banach_fixedPoint]; exact optimalPolicy_opt s') s

/-- **`DetMDP.exists_optimalPolicy_valueFunction` produces a genuine policy function.** With
`Fin 2` state/action spaces (discrete, hence every `Γ s = univ` is compact and every map is
continuous, including `cakeM.valueFunction`), an optimal stationary policy *function* exists that
is feasible and weakly dominates every feasible plan from every state. -/
theorem cake_exists_optimalPolicy_valueFunction :
    ∃ σ : Fin 2 → Fin 2, (∀ s, σ s ∈ cakeM.Γ s) ∧
      ∀ s, cakeM.isFeasible s (extractPlan σ cakeM.transition s) ∧
        cakeM.discountedPayoff s (extractPlan σ cakeM.transition s) = cakeM.valueFunction s ∧
        ∀ π : Plan (Fin 2), cakeM.isFeasible s π →
          cakeM.discountedPayoff s π ≤
            cakeM.discountedPayoff s (extractPlan σ cakeM.transition s) :=
  cakeM.exists_optimalPolicy_valueFunction (fun _ => isCompact_univ)
    (fun _ => continuous_of_discreteTopology.continuousOn)
    (fun _ => continuous_of_discreteTopology.continuousOn)
    (continuous_of_discreteTopology)

/-! ### Bounded-layer decay lemmas (cake model)

`summable_discountedPayoff` and `tendsto_pow_beta_mul` require `reward_bounded`, so they are
exercised on the bounded cake `M`, not the unbounded growth model. -/

/-- **`summable_discountedPayoff`: The discounted reward stream converges.** Along any plan from
state `0`, the discounted rewards `β^t · r_t` form a summable series (bounded rewards,
`β = 1/2`). -/
theorem cake_summable_discountedPayoff (π : Plan (Fin 2)) :
    Summable (fun t => cakeM.β ^ t * cakeM.reward (cakeM.stateSeq 0 π t) (π t)) :=
  summable_discountedPayoff cakeM 0 π

/-- **`tendsto_pow_beta_mul`: The geometric value tail vanishes.** `β^N · 16/3 → 0` since
`β = 1/2 < 1`; this is the tail term killed in the telescoping principle-of-optimality argument. -/
theorem cake_tendsto_pow_beta_mul :
    Filter.Tendsto (fun N => cakeM.β ^ N * (16 / 3 : ℝ)) Filter.atTop (nhds 0) :=
  tendsto_pow_beta_mul cakeM (16 / 3)

/-! ### Unbounded transversality (linear-growth model)

`value_ge_partialPayoff_add_tail` lives on `UnboundedDetMDP`; we anchor it on the linear
cake-eating growth model whose value `v*(x) = x` is unbounded. -/

private abbrev growthM : UnboundedDetMDP NNReal NNReal :=
  EconlibExamples.Optimization.OptimalGrowth.M
private abbrev growthV : NNReal → ℝ := EconlibExamples.Optimization.OptimalGrowth.vStar

open EconlibExamples.Optimization.OptimalGrowth (vStar_eq_bellman bellmanSet_bddAbove σ
  extractPlan_σ_feasible)

/-- **`value_ge_partialPayoff_add_tail`: The telescoped lower bound.** For the optimal
consume-everything plan from any stock `s`, the value `v*(s) = s` dominates the partial discounted
payoff plus the discounted value tail at every horizon `N`. The inequality is `≥` (value bounds the
truncated return-plus-tail from above); a reversed direction would be false. -/
theorem growth_value_ge_partialPayoff_add_tail (s : NNReal) (N : ℕ) :
    growthV s ≥ ∑ t ∈ Finset.range N,
        growthM.β ^ t *
          growthM.reward (growthM.stateSeq s (extractPlan σ growthM.transition s) t)
            (extractPlan σ growthM.transition s t) +
      growthM.β ^ N *
        growthV (growthM.stateSeq s (extractPlan σ growthM.transition s) N) :=
  growthM.value_ge_partialPayoff_add_tail growthV vStar_eq_bellman bellmanSet_bddAbove s
    (extractPlan σ growthM.transition s) (extractPlan_σ_feasible s) N

/-- The **never-consume** plan `π ≡ 0` (a feasible but *suboptimal* alternative to the optimal
consume-everything `extractPlan σ`). It keeps the stock constant (`transition x 0 = x - 0 = x`). -/
private def nullPlan : Plan NNReal := fun _ => 0

/-- The never-consume plan is feasible from any stock: `0 ∈ Γ (anything) = Icc 0 (·)`. -/
private theorem nullPlan_feasible (s : NNReal) : growthM.isFeasible s nullPlan :=
  fun _ => by
    simp only [nullPlan, EconlibExamples.Optimization.OptimalGrowth.M]
    exact ⟨le_refl 0, zero_le⟩

/-- **The telescoped bound is *strict* for a suboptimal plan** — the reversed direction the optimal
plan cannot detect. Anchored on the never-consume plan `π ≡ 0` from stock `s = 1`
at horizon `N = 1`:
the value `v*(1) = 1` *strictly* exceeds the partial discounted payoff plus the tail
`0 + β·v*(stateSeq) = 0 + ½·v*(1) = 1/2`, i.e. `1 > 1/2`. (Never consuming wastes the entire first
period's return, so the bound is slack.) The optimal consume-everything plan makes this an equality
at every horizon, so only a genuinely suboptimal plan exhibits the strict gap. -/
theorem growth_value_gt_partialPayoff_add_tail_suboptimal :
    growthV 1 > ∑ t ∈ Finset.range 1,
        growthM.β ^ t * growthM.reward (growthM.stateSeq 1 nullPlan t) (nullPlan t) +
      growthM.β ^ 1 * growthV (growthM.stateSeq 1 nullPlan 1) := by
  -- `stateSeq 1 nullPlan 1 = transition 1 0 = 1`; `reward 1 0 = 0`; `v*(1) = 1`; `β = 1/2`.
  have hstate : growthM.stateSeq 1 nullPlan 1 = 1 := by
    rw [stateSeq_succ, stateSeq_zero]
    simp only [nullPlan, EconlibExamples.Optimization.OptimalGrowth.M]
    simp
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, pow_one, one_mul, hstate]
  simp only [nullPlan, growthV, EconlibExamples.Optimization.OptimalGrowth.M,
    EconlibExamples.Optimization.OptimalGrowth.vStar, EconlibExamples.Optimization.OptimalGrowth.β,
    stateSeq_zero]
  norm_num

/-! ## Chunk 2 — Finite / stochastic Bellman (explore-or-stay model)

The hand-solved `FinMDP 2 (Fin 2)`: States `{0 = low, 1 = high}`, actions
`{0 = stay, 1 = explore}`, rewards `r(0,0)=0, r(1,0)=6, r(s,1)=1`, discount `β = 1/2`. Action `0`
(stay) is a Dirac transition keeping the state; action `1` (explore) is a genuine `50/50` over
`{0,1}`. The closed-form value is `v* = (16/3, 12)` and the optimal action **flips**: Explore at
low, stay at high. -/

/-- The `50/50` exploration kernel over `{0, 1}` (a genuine two-point distribution, not a Dirac). -/
private def half : FinDist (Fin 2) :=
  FinDist.ofVec ![1 / 2, 1 / 2] (fun i => by fin_cases i <;> norm_num)
    (by rw [Fin.sum_univ_two]; norm_num)

/-- The **explore-or-stay** finite stochastic MDP. *Stay* (`a = 0`) keeps the current state via a
Dirac kernel; *explore* (`a = 1`) draws the next state uniformly. Rewards `r(0,0)=0`, `r(1,0)=6`,
`r(s,1)=1`; discount `β = 1/2`; reward bound `6`. -/
private def fmdp : FinMDP 2 (Fin 2) where
  Γ := fun _ => Set.univ
  reward := fun s a => (![![0, 1], ![6, 1]] : Fin 2 → Fin 2 → ℝ) s a
  transition := fun s a => if a = 0 then FinDist.pure s else half
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  Γ_nonempty := fun _ => Set.univ_nonempty
  reward_bounded := ⟨6, fun s a => by fin_cases s <;> fin_cases a <;> norm_num⟩

/-- The closed-form **value function** of the explore-or-stay model: `v* = (16/3, 12)`. -/
private def fval : Fin 2 → ℝ := ![16 / 3, 12]

/-- The exploration continuation `E_{s' ~ half}[v*(s')] = (16/3 + 12)/2 = 26/3` — a genuine average
of the two state values, not a point evaluation. -/
private theorem fmdp_explore_expect : FinDist.expect half fval = 26 / 3 := by
  simp [FinDist.expect_eq_sum, half, fval, Fin.sum_univ_two]
  norm_num

/-- The finite Bellman set at a state is the **two-candidate set** of one-step values, one per
action: `{r(s,0) + β·E[v|stay], r(s,1) + β·E[v|explore]}`. Naming it lets the fixed-point and
argmax proofs evaluate the supremum as an honest `max` (`csSup_pair`). -/
private theorem fmdp_bellmanSet_eq_pair (v : Fin 2 → ℝ) (s : Fin 2) :
    {r : ℝ | ∃ a ∈ fmdp.Γ s,
      r = fmdp.reward s a + fmdp.β * FinDist.expect (fmdp.transition s a) (fun s' => v s')} =
    {fmdp.reward s 0 + fmdp.β * FinDist.expect (fmdp.transition s 0) (fun s' => v s'),
     fmdp.reward s 1 + fmdp.β * FinDist.expect (fmdp.transition s 1) (fun s' => v s')} := by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, -, rfl⟩
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, Set.mem_univ _, rfl⟩
    · exact ⟨1, Set.mem_univ _, rfl⟩

/-- **The closed form solves the finite Bellman equation.** At low (`s = 0`) *explore* (`16/3`)
beats *stay* (`8/3`); at high (`s = 1`) *stay* (`12`) beats *explore* (`16/3`). So `v* = T v*` with
the supremum realized by the *flipping* argmax. -/
private theorem fmdp_value_is_fixedPoint (s : Fin 2) :
    fval s = finiteBellmanOperator fmdp fval s := by
  -- Split into the two states with clean `0`/`1` literals (avoids `fin_cases` index artifacts).
  revert s
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · -- low: max(stay 0+½·v(0)=8/3, explore 1+½·26/3=16/3) = 16/3
    rw [finiteBellmanOperator, fmdp_bellmanSet_eq_pair, csSup_pair]
    have hstay : fmdp.reward 0 0 + fmdp.β * FinDist.expect (fmdp.transition 0 0) fval = 8 / 3 := by
      simp [fmdp, FinDist.expect_pure, fval]; norm_num
    have hexplore : fmdp.reward 0 1 + fmdp.β * FinDist.expect (fmdp.transition 0 1) fval = 16 / 3 :=
      by simp only [fmdp]; rw [if_neg (by decide), fmdp_explore_expect]; norm_num [fval]
    rw [hstay, hexplore, sup_eq_right.mpr (by norm_num : (8 : ℝ) / 3 ≤ 16 / 3)]; norm_num [fval]
  · -- high: max(stay 6+½·12=12, explore 1+½·26/3=16/3) = 12
    rw [finiteBellmanOperator, fmdp_bellmanSet_eq_pair, csSup_pair]
    have hstay : fmdp.reward 1 0 + fmdp.β * FinDist.expect (fmdp.transition 1 0) fval = 12 := by
      simp [fmdp, FinDist.expect_pure, fval]; norm_num
    have hexplore : fmdp.reward 1 1 + fmdp.β * FinDist.expect (fmdp.transition 1 1) fval = 16 / 3 :=
      by simp only [fmdp]; rw [if_neg (by decide), fmdp_explore_expect]; norm_num [fval]
    rw [hstay, hexplore, sup_eq_left.mpr (by norm_num : (16 : ℝ) / 3 ≤ 12)]; norm_num [fval]

/-! ### Finite operator structure -/

/-- **`finiteBellmanSet_nonempty`** on the concrete model. -/
private theorem fmdp_finiteBellmanSet_nonempty (s : Fin 2) :
    {r : ℝ | ∃ a ∈ fmdp.Γ s,
        r = fmdp.reward s a +
          fmdp.β * FinDist.expect (fmdp.transition s a) (fun s' => fval s')}.Nonempty :=
  finiteBellmanSet_nonempty fmdp fval s

/-- **`finiteBellmanSet_bddAbove`** on the concrete model (rewards bounded by `6`). -/
private theorem fmdp_finiteBellmanSet_bddAbove (s : Fin 2) :
    BddAbove {r : ℝ | ∃ a ∈ fmdp.Γ s,
      r = fmdp.reward s a + fmdp.β * FinDist.expect (fmdp.transition s a) (fun s' => fval s')} :=
  finiteBellmanSet_bddAbove fmdp fval s fmdp.reward_bounded

/-- **`finiteBellmanOperator_monotone` is oriented correctly.** Raising the continuation from `v*`
to `v* + 1` weakly raises the operator image at every state. -/
private theorem fmdp_finiteBellmanOperator_monotone (s : Fin 2) :
    finiteBellmanOperator fmdp fval s ≤ finiteBellmanOperator fmdp (fun s' => fval s' + 1) s :=
  finiteBellmanOperator_monotone fmdp fmdp.reward_bounded fval (fun s' => fval s' + 1)
    (fun _ => by linarith) s

/-- **`finiteBellmanOperator_discounting` pins the modulus to `β`.** Adding `c = 2 ≥ 0` to the
continuation raises the operator image by at most `β · c = 1`. -/
private theorem fmdp_finiteBellmanOperator_discounting (s : Fin 2) :
    finiteBellmanOperator fmdp (fun s' => fval s' + 2) s ≤
      finiteBellmanOperator fmdp fval s + fmdp.β * 2 :=
  finiteBellmanOperator_discounting fmdp fmdp.reward_bounded fval 2 (by norm_num) s

/-- **`finiteBellmanOperator_apply_abs_sub_le` is the sup-norm contraction estimate.** The
pointwise gap of the operator images at `v*` and `v* + 1` is at most
`β · sup|v* - (v*+1)| = β · 1`; the modulus is `β`, not `1`. -/
private theorem fmdp_finiteBellmanOperator_apply_abs_sub_le (s : Fin 2) :
    |finiteBellmanOperator fmdp fval s - finiteBellmanOperator fmdp (fun s' => fval s' + 1) s| ≤
      fmdp.β * ⨆ t, |fval t - (fval t + 1)| :=
  finiteBellmanOperator_apply_abs_sub_le fmdp fval (fun s' => fval s' + 1) s

/-! ### Finite fixed point and optimal action -/

/-- **`FinMDP.bellmanOperator_existsUnique_fixedPoint` on a concrete model.** The finite Bellman
operator has a unique fixed point; the hand-computed `fval = (16/3, 12)` is *the* witness, so the
uniqueness clause forces every fixed point to equal it. -/
private theorem fmdp_existsUnique_fixedPoint :
    (∃! v : Fin 2 → ℝ, ∀ s, v s = finiteBellmanOperator fmdp v s) ∧
      (∀ v : Fin 2 → ℝ, (∀ s, v s = finiteBellmanOperator fmdp v s) → v = fval) := by
  obtain ⟨v₀, hv₀_fp, hv₀_uniq⟩ := fmdp.bellmanOperator_existsUnique_fixedPoint
  refine ⟨⟨v₀, hv₀_fp, hv₀_uniq⟩, fun v hv => ?_⟩
  -- both `v` and `fval` are fixed points, so each equals the canonical `v₀`.
  rw [hv₀_uniq v hv, hv₀_uniq fval fmdp_value_is_fixedPoint]

/-- **`FinMDP.exists_optimalAction` selects the hand-computed argmax — and the flip is real.** At
every state an optimizing feasible action attains the Bellman supremum at `v*`. We additionally
record the *negative* checks: At low, *stay* (`a = 0`) is strictly worse than the optimum; at high,
*explore* (`a = 1`) is strictly worse. So the selected argmax genuinely flips with the state. -/
private theorem fmdp_exists_optimalAction :
    (∀ s, ∃ a ∈ fmdp.Γ s,
        fval s = fmdp.reward s a + fmdp.β * FinDist.expect (fmdp.transition s a) fval) ∧
      -- low: staying is strictly suboptimal (explore is the argmax)
      fmdp.reward 0 0 + fmdp.β * FinDist.expect (fmdp.transition 0 0) fval < fval 0 ∧
      -- high: exploring is strictly suboptimal (stay is the argmax)
      fmdp.reward 1 1 + fmdp.β * FinDist.expect (fmdp.transition 1 1) fval < fval 1 := by
  refine ⟨fmdp.exists_optimalAction (fun _ => isCompact_univ) fval
      fmdp_value_is_fixedPoint (fun _ => continuous_of_discreteTopology.continuousOn), ?_, ?_⟩
  · -- stay at low: `0 + ½·v(0) = 8/3 < 16/3 = v(0)`
    simp only [fmdp, fval, ↓reduceIte, FinDist.expect_pure]
    norm_num
  · -- explore at high: `1 + ½·26/3 = 16/3 < 12 = v(1)`
    simp only [fmdp]
    rw [if_neg (by decide), fmdp_explore_expect]
    norm_num [fval]

/-! ### Stochastic operator: Contraction modulus and the Dirac reduction

`stochBellmanOperator_contraction` and `bellman_dirac_eq` are stated for the `ℝ`-valued
`StochMDP`. We embed a concrete deterministic `DetMDP ℝ ℝ` (linear stay-put dynamics) as a Dirac
`StochMDP` and exercise both endpoints on it. -/

/-- A concrete bounded deterministic `DetMDP ℝ ℝ`: A single feasible action, reward `1`, and the
*stay-put* transition `f(s,a) = s`. Its Dirac embedding is the carrier for `bellman_dirac_eq` and
`stochBellmanOperator_contraction`. -/
private def detR : DetMDP ℝ ℝ where
  Γ := fun _ => Set.univ
  reward := fun _ _ => 1
  transition := fun s _ => s
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  Γ_nonempty := fun _ => Set.univ_nonempty
  reward_bounded := ⟨1, fun _ _ => by norm_num⟩

/-- **`bellman_dirac_eq`: The stochastic operator collapses to the deterministic one on a Dirac
kernel.** For any continuation `v` and state `s`, the `StochMDP` Bellman image of the Dirac
embedding equals the `DetMDP` Bellman image — the integral against `δ_{f(s,a)}` is the point
evaluation `v (f s a)`. This catches a transition row/column transpose: If the embedding swapped
the transition argument the two operators would disagree. -/
private theorem detR_bellman_dirac_eq (v : ℝ → ℝ) (s : ℝ) :
    stochBellmanOperator detR.toStochMDP v s = detR.bellmanOperator v s :=
  bellman_dirac_eq detR v s

/-- The deterministic operator of `detR` at `v` and `s` is exactly `1 + (1/2)·v s`:
the reward is the
constant `1`, the transition `f(s,a) = s` keeps the state, and the only feasible action set is
`univ`, so the Bellman set is the singleton `{1 + (1/2)·v s}`. -/
private theorem detR_bellman_apply (v : ℝ → ℝ) (s : ℝ) :
    detR.bellmanOperator v s = 1 + (1 / 2) * v s := by
  rw [bellmanOperator_eq]
  have hset : detR.bellmanSet v s = {1 + (1 / 2) * v s} := by
    ext r
    simp only [UnboundedDetMDP.mem_bellmanSet, Set.mem_singleton_iff]
    constructor
    · rintro ⟨a, -, rfl⟩; rfl
    · rintro rfl; exact ⟨0, Set.mem_univ _, rfl⟩
  rw [hset, csSup_singleton]

/-- **The stochastic-operator gap is *exactly* `β`, not `β²` and not `1`.** With the constant
continuations `v ≡ 1` and `w ≡ 0` (sup-distance `1`), the Dirac-embedded stochastic operator gives
`T v s = 1 + ½·1 = 3/2` and `T w s = 1 + ½·0 = 1` at every state (via `bellman_dirac_eq`), so the
pointwise gap is `|3/2 − 1| = 1/2 = β · sup|v − w|`. A continuation underweighted by `β²` would give
a gap of `1/4`, failing this equality — so the contraction modulus is pinned to exactly `β`. -/
private theorem detR_stoch_gap_eq_beta (s : ℝ) :
    |stochBellmanOperator detR.toStochMDP (fun _ => 1) s -
        stochBellmanOperator detR.toStochMDP (fun _ => 0) s| = detR.toStochMDP.β * 1 := by
  rw [detR_bellman_dirac_eq, detR_bellman_dirac_eq, detR_bellman_apply, detR_bellman_apply,
    show detR.toStochMDP.β = (1 / 2 : ℝ) from rfl]
  norm_num

/-- **`stochBellmanOperator_contraction` with modulus exactly the stated `β`.** On the Dirac
embedding (where every bounded function is trivially integrable against the Dirac measures), the
stochastic Bellman operator contracts the sup-norm gap by the factor `β = 1/2`. The companion
`detR_stoch_gap_eq_beta` shows the bound is *attained with equality* on `v ≡ 1`, `w ≡ 0`, so the
modulus is `β`, not `1` and not `β²`. -/
private theorem detR_stochBellmanOperator_contraction
    (v w : ℝ → ℝ) (hBv : UniformBounded v) (hBw : UniformBounded w) :
    ⨆ s, |stochBellmanOperator detR.toStochMDP v s - stochBellmanOperator detR.toStochMDP w s| ≤
      detR.toStochMDP.β * ⨆ s, |v s - w s| :=
  stochBellmanOperator_contraction detR.toStochMDP
    (fun u _hu s a => by
      -- every function is integrable against the Dirac transition `δ_{f s a}`
      simp only [DetMDP.toStochMDP]
      exact MeasureTheory.integrable_dirac enorm_lt_top)
    v w hBv hBw

/-- **`StochMDP.bellmanOperator_existsUnique_fixedPoint` on the Dirac embedding.** The stochastic
Bellman operator has a unique bounded fixed point. (Here the stay-put deterministic model has
constant value `v* ≡ 2 = 1 / (1 - β)`; we record only the existence/uniqueness endpoint, the
contraction having been confirmed above.) -/
private theorem detR_stoch_existsUnique_fixedPoint :
    ∃! v : ℝ → ℝ, UniformBounded v ∧ ∀ s, v s = stochBellmanOperator detR.toStochMDP v s :=
  detR.toStochMDP.bellmanOperator_existsUnique_fixedPoint
    (fun u _hu s a => by
      simp only [DetMDP.toStochMDP]
      exact MeasureTheory.integrable_dirac enorm_lt_top)

end EconlibTest.Optimization.DPCore
