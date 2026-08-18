/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# A growing cake: a state-dependent dynamic program, end to end

The textbook **cake-eating** lesson is the tension between impatience and growth: a small cake left
uneaten *ripens* into a large one, but the future is discounted, so it is not obvious whether to eat
now or wait. This file builds the smallest dynamic program that makes the tradeoff concrete — the
optimal action **depends on the state** — and runs it through every component of the bounded
dynamic-programming layer in `Econlib.Optimization.DynamicProgramming` on a fully concrete finite
deterministic MDP:

* the **Bellman operator** has a unique bounded fixed point (Banach / contraction);
* that fixed point is the closed-form **value function** `v* = (8/3, 16/3)`;
* the **optimal stationary policy flips with the state** — *wait* when the cake is small,
  *eat* when it is large — and we prove each choice **strictly** beats the alternative, so the model
  is not a one-action degeneracy;
* the optimal policy **attains** the value as its discounted payoff and is **optimal**: it weakly
  dominates every feasible plan;
* the value equals the **supremum of discounted payoffs over feasible plans** — the *principle of
  optimality*;
* and **value iteration converges**: from any bounded initial guess the Bellman iterates approach
  `v*` in the sup norm; from `v₀ ≡ 0` the first iterate is already the one-step `max`,
  `T0 = (1, 4)`.

## The model

Two cake sizes — state `0` = "small", state `1` = "large" (`S := Fin 2`) — and two actions,
`0` = "wait" and `1` = "eat" (`A := Fin 2`). Both actions are always available (`Γ s = univ`).

| state         | action | reward | next state            |
|---------------|--------|--------|-----------------------|
| `0` (small)   | wait   | `0`    | `1` (grows to large)  |
| `0` (small)   | eat    | `1`    | `0` (eat, regrows small) |
| `1` (large)   | wait   | `0`    | `1` (stays large)     |
| `1` (large)   | eat    | `4`    | `0` (eat, regrows small) |

The discount factor is `β = 1/2`. Eating a large cake is worth four small ones, but you must wait a
discounted period for a small cake to grow.

## The mathematics

With two feasible actions per state, the Bellman set at each state is the **two-candidate set**
`{u(s,0) + β·v(f(s,0)), u(s,1) + β·v(f(s,1))}` — one value per action — so the Bellman operator is
an honest `max` over the two actions via `csSup_pair`, not the `csSup_singleton` collapse of a
one-action model. (At the fixed point `v*` the two candidates are strictly distinct, witnessed
below; for a general continuation `v` they could of course coincide.) Solving `v = T v` (a coupled
`2×2` system of `max`-equations) under the conjectured policy "wait when small, eat when large"
gives

`v*(small) = β·v*(large)`,   `v*(large) = 4 + β·v*(small)`   ⟹   `v* = (8/3, 16/3)`.

We verify directly that `v* = (8/3, 16/3)` satisfies `v* = T v*` and is bounded; the uniqueness
lemma `DetMDP.eq_valueFunction` then identifies it with the Banach fixed point
`DetMDP.valueFunction`. Crucially, at `small` waiting (`8/3`) strictly beats eating (`7/3`), while
at `large` eating (`16/3`) strictly beats waiting (`8/3`): the optimal action is not the same at
both states (`eat_strictly_better_when_large`, `wait_strictly_better_when_small`). The optimal plan
therefore cycles small ⟶ large ⟶ small ⟶ … harvesting the large cake every other period — the
two transition steps of this cycle are exported as `optimalPolicy_cycle`.

## Main definitions and theorems

* `M : DetMDP (Fin 2) (Fin 2)` — the concrete growing-cake MDP.
* `value : Fin 2 → ℝ` — the closed-form value function `(8/3, 16/3)`.
* `value_bounded` — `value` is bounded (needed by the upstream bridge lemmas).
* `bellmanSet_eq_pair` — the Bellman set is the two-candidate set of one-step values (one per
  action); for a general `v` the two may coincide, at `v = value` they are strictly distinct.
* `value_is_bellman_fixedPoint : ∀ s, value s = M.bellmanOperator value s` — `v*` solves Bellman.
* `value_eq_banach_fixedPoint` — `value` is `M.valueFunction`, the unique bounded Bellman fixed
  point.
* `optimalPolicy : Fin 2 → Fin 2` — the state-dependent policy "wait when small, eat when large".
* `eat_strictly_better_when_large` / `wait_strictly_better_when_small` — the optimal choice
  **strictly** dominates the alternative and **flips** with the state.
* `optimalPolicy_cycle` — the optimal transitions small ⟶ large ⟶ small (the harvest cycle).
* `optimalPolicy_payoff_eq_value` — its discounted payoff equals `value`.
* `optimalPolicy_optimal` — its payoff weakly dominates that of every feasible plan.
* `value_eq_sup_payoff` — the principle of optimality: `value s = sSup {feasible-plan payoffs}`.
* `value_iteration` — value iteration converges to `value` from any bounded start.
* `bellmanIterate_one` — the first iterate from `v₀ ≡ 0` is the one-step `max`, `(1, 4)`.
-/

noncomputable section

namespace EconlibExamples.Optimization.DiscreteCakeEating

open Econlib.Optimization Econlib.Optimization.DynamicProgramming
open Blackwell UnboundedDetMDP

/-- The concrete **growing-cake** MDP. Two cake sizes (`small = 0`, `large = 1`) and two actions
(`wait = 0`, `eat = 1`), both always available. Waiting on a small cake grows it to large; eating a
small cake pays `1` and a large cake pays `4`, after which a small cake regrows. Discount `β = 1/2`,
reward bound `4`. -/
def M : DetMDP (Fin 2) (Fin 2) where
  Γ := fun _ => Set.univ
  reward := fun s a => (![![0, 1], ![0, 4]] : Fin 2 → Fin 2 → ℝ) s a
  transition := fun s a => (![![1, 0], ![1, 0]] : Fin 2 → Fin 2 → Fin 2) s a
  β := 1 / 2
  β_nonneg := by norm_num
  β_lt_one := by norm_num
  Γ_nonempty := fun _ => Set.univ_nonempty
  reward_bounded := ⟨4, fun s a => by fin_cases s <;> fin_cases a <;> norm_num⟩

/-- The closed-form **value function** `v* = (8/3, 16/3)`: the small-cake value is `8/3`, the
large-cake value `16/3`, the unique bounded solution of the coupled Bellman system. -/
def value : Fin 2 → ℝ := ![8 / 3, 16 / 3]

/-- The value function is bounded, with explicit bound `16/3`. The upstream uniqueness and
policy/plan-bridge lemmas all take boundedness of `v*` as a hypothesis. -/
lemma value_bounded : UniformBounded value :=
  ⟨16 / 3, fun s => by fin_cases s <;> norm_num [value]⟩

/-- The Bellman set at a state is the **two-candidate set** of one-step values, one per action:
`{u(s,0) + β·v(f(s,0)), u(s,1) + β·v(f(s,1))}`. With two feasible actions the existential over
`a ∈ Γ s` ranges over exactly `{0, 1}`, so the supremum defining the Bellman operator is an honest
`max` over the two actions (`csSup_pair`), not the singleton collapse of a one-action model. (For a
general `v` the two candidates may coincide; at `v = value` they are strictly distinct.) -/
lemma bellmanSet_eq_pair (v : Fin 2 → ℝ) (s : Fin 2) :
    M.bellmanSet v s = {M.reward s 0 + M.β * v (M.transition s 0),
                        M.reward s 1 + M.β * v (M.transition s 1)} := by
  ext r
  simp only [UnboundedDetMDP.mem_bellmanSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, -, rfl⟩
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, Set.mem_univ _, rfl⟩
    · exact ⟨1, Set.mem_univ _, rfl⟩

/-- **The closed form solves the Bellman equation.** For every state, `value s = (T value) s`.

`bellmanOperator` is the supremum of the two-candidate Bellman set, so `csSup_pair` evaluates it to
the `max` of the two one-step values. At `small`, waiting yields `8/3` and eating `7/3`, so the max
is `8/3 = value small`; at `large`, waiting yields `8/3` and eating `16/3`, so the max is
`16/3 = value large`. -/
theorem value_is_bellman_fixedPoint : ∀ s, value s = M.bellmanOperator value s := by
  -- Split into the two states with clean `0`/`1` literals (avoids `fin_cases` index artifacts).
  refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
  · -- small: `(8/3) ⊔ (7/3) = 8/3`
    rw [bellmanOperator_eq, bellmanSet_eq_pair, csSup_pair]
    have h0 : M.reward 0 0 + M.β * value (M.transition 0 0) = 8 / 3 := by norm_num [M, value]
    have h1 : M.reward 0 1 + M.β * value (M.transition 0 1) = 7 / 3 := by norm_num [M, value]
    rw [h0, h1, sup_eq_left.mpr (by norm_num : (7 : ℝ) / 3 ≤ 8 / 3)]
    norm_num [value]
  · -- large: `(8/3) ⊔ (16/3) = 16/3`
    rw [bellmanOperator_eq, bellmanSet_eq_pair, csSup_pair]
    have h0 : M.reward 1 0 + M.β * value (M.transition 1 0) = 8 / 3 := by norm_num [M, value]
    have h1 : M.reward 1 1 + M.β * value (M.transition 1 1) = 16 / 3 := by norm_num [M, value]
    rw [h0, h1, sup_eq_right.mpr (by norm_num : (8 : ℝ) / 3 ≤ 16 / 3)]
    norm_num [value]

/-- **The value function is the Banach fixed point.** `DetMDP.valueFunction` is the unique bounded
solution of the Bellman equation delivered by Banach's fixed-point theorem; `value` is bounded and
solves it, so the uniqueness lemma `DetMDP.eq_valueFunction` identifies the two. -/
theorem value_eq_banach_fixedPoint : M.valueFunction = value :=
  (M.eq_valueFunction value_bounded value_is_bellman_fixedPoint).symm

/-- The **optimal stationary policy** "wait when small, eat when large": `σ(small) = wait`,
`σ(large) = eat`. Unlike a one-action model, this is a state-dependent choice. -/
def optimalPolicy : Fin 2 → Fin 2 := ![0, 1]

/-- The stationary policy achieves the Bellman argmax at every state: its action realizes
`value s = reward s (σ s) + β · value (transition s (σ s))`. At `small` the optimal action is *wait*
(`0`), at `large` it is *eat* (`1`). -/
lemma optimalPolicy_opt (s : Fin 2) :
    value s = M.reward s (optimalPolicy s) + M.β * value (M.transition s (optimalPolicy s)) := by
  fin_cases s <;> norm_num [M, value, optimalPolicy]

/-- **The optimal action flips with the state, part 1.** When the cake is **large**, *eating*
(payoff `16/3`) strictly beats *waiting* (payoff `8/3`). -/
theorem eat_strictly_better_when_large :
    M.reward 1 0 + M.β * value (M.transition 1 0) <
      M.reward 1 1 + M.β * value (M.transition 1 1) := by
  norm_num [M, value]

/-- **The optimal action flips with the state, part 2.** When the cake is **small**, *waiting* for
it to grow (continuation value `8/3`) strictly beats *eating* it now (payoff `7/3`). Together with
`eat_strictly_better_when_large` this shows the optimal policy is state-dependent: no
single action is optimal at both states. -/
theorem wait_strictly_better_when_small :
    M.reward 0 1 + M.β * value (M.transition 0 1) <
      M.reward 0 0 + M.β * value (M.transition 0 0) := by
  norm_num [M, value]

/-- **The optimal cycle small ⟶ large ⟶ small.** Under the optimal policy the small cake is grown
to large (waiting), and the large cake is harvested back to small (eating): the two transitions
`f(small, σ small) = large` and `f(large, σ large) = small`. Iterating gives the two-period harvest
cycle described in the module header. -/
theorem optimalPolicy_cycle :
    M.transition 0 (optimalPolicy 0) = 1 ∧ M.transition 1 (optimalPolicy 1) = 0 := by
  constructor <;> norm_num [M, optimalPolicy]

/-- **The optimal policy attains the value.** Its discounted payoff equals `v*` at every state, via
the upstream policy/plan bridge `stationary_plan_payoff_eq`. From `large`, the payoff is the
geometric harvest `4 + (1/2)²·4 + (1/2)⁴·4 + … = 16/3`. -/
theorem optimalPolicy_payoff_eq_value (s : Fin 2) :
    M.discountedPayoff s (extractPlan optimalPolicy M.transition s) = value s :=
  stationary_plan_payoff_eq value value_bounded optimalPolicy optimalPolicy_opt s

/-- **Principle of optimality on this model.** The value function equals the supremum of discounted
payoffs over all feasible plans. Demonstrates the canonical-value-function corollary
`DetMDP.valueFunction_eq_sup_payoff`: after `value_eq_banach_fixedPoint` identifies `value` with
`M.valueFunction`, the general principle of optimality applies with no fixed-point triple to
thread. -/
theorem value_eq_sup_payoff (s : Fin 2) :
    value s = sSup {p : ℝ | ∃ π : Plan (Fin 2),
      M.isFeasible s π ∧ p = M.discountedPayoff s π} := by
  rw [← value_eq_banach_fixedPoint]; exact M.valueFunction_eq_sup_payoff s

/-- **The policy is optimal**, not merely value-attaining: its discounted payoff weakly dominates
that of *every* feasible plan (the `≥` direction of the principle of optimality, `value_ge_payoff`,
combined with attainment). -/
theorem optimalPolicy_optimal (s : Fin 2) (π : Plan (Fin 2)) (hπ : M.isFeasible s π) :
    M.discountedPayoff s π ≤
      M.discountedPayoff s (extractPlan optimalPolicy M.transition s) :=
  (stationary_policy_optimal value value_is_bellman_fixedPoint value_bounded
    optimalPolicy (fun _ => Set.mem_univ _) optimalPolicy_opt s).2.2 π hπ

/-! ### Value iteration -/

/-- **Value iteration converges on this model**: starting from any bounded initial guess, the
Bellman iterates `Tⁿv₀` approach `v* = (8/3, 16/3)` in the sup norm (`value_iteration_converges`
instantiated at `value`). -/
theorem value_iteration (v₀ : Fin 2 → ℝ) (hv₀ : ∃ B : ℝ, ∀ s, |v₀ s| ≤ B) :
    Filter.Tendsto (fun n => ⨆ s, |bellmanIterate M v₀ n s - value s|)
      Filter.atTop (nhds 0) :=
  value_iteration_converges M v₀ hv₀ value value_is_bellman_fixedPoint value_bounded

/-- The first Bellman iterate from `v₀ ≡ 0` is the one-step `max` of the immediate rewards:
`T0 = (max(0,1), max(0,4)) = (1, 4)`. Already nontrivial — the `max` selects *eat* at both states
when the future is valued at `0`, the myopic optimum — and `value_iteration` then drives the
iterates to the farsighted `v* = (8/3, 16/3)`. -/
lemma bellmanIterate_one : bellmanIterate M (fun _ => 0) 1 = ![1, 4] := by
  funext s
  fin_cases s
  · -- small: `T0(small) = max(reward 0, reward 1) = max(0, 1) = 1`
    change M.bellmanOperator (fun _ => 0) 0 = (1 : ℝ)
    rw [bellmanOperator_eq, bellmanSet_eq_pair, csSup_pair]
    simp only [M, mul_zero, add_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [sup_eq_right.mpr (by norm_num : (0 : ℝ) ≤ 1)]
  · -- large: `T0(large) = max(reward 0, reward 1) = max(0, 4) = 4`
    change M.bellmanOperator (fun _ => 0) 1 = (4 : ℝ)
    rw [bellmanOperator_eq, bellmanSet_eq_pair, csSup_pair]
    simp only [M, mul_zero, add_zero, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [sup_eq_right.mpr (by norm_num : (0 : ℝ) ≤ 4)]

end EconlibExamples.Optimization.DiscreteCakeEating
