/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Stationary distribution under an optimal policy, end to end

This worked example instantiates the model-agnostic optimal-policy interface
`Econlib.Optimization.EndogenousPolicyProblem` on a concrete, state-dependent
optimization, and runs the full pipeline to its payoff: **a stationary distribution of the
optimally controlled economy exists.**

It is the acceptance test for the optimality interface — it exercises every stage:

* Berge's maximum theorem makes the optimal-choice correspondence upper hemicontinuous;
* strict concavity of the objective makes the maximizer unique;
* the single-valued continuous-selection lemma upgrades these to a **continuous** optimal policy;
* the policy stays in the state interval, so it induces an `EndogenousMarkovChain`;
* Krylov–Bogolyubov (via the chain's Feller property) gives an invariant probability measure.

## The model

Two exogenous shock states (`Fin 2`) following a symmetric `1/2`–`1/2` Markov chain. The endogenous
state `w` lives in `[0, 1]`. At each state the agent chooses the next continuous state `w'` from the
whole interval to maximize the strictly concave, state-dependent objective

`obj(w, s, s', w') = -(w')² + w · w'`,

whose unique maximizer `w' = w / 2` varies continuously with `w` and is interior for every strictly
positive state (at the boundary state `w = 0` it is the boundary point `0`) — so the optimal policy
is a non-constant continuous function, not a degenerate constant. The interface delivers
existence, continuity, and optimality of the policy *abstractly*; on top of that we exhibit the
maximizer in closed form to certify the model is non-degenerate:

* `policyFun_eq_half` — the optimal policy the interface selects is `w' = w / 2` on the
  state interval `[0, 1]` (proved from `policyFun_mem` + uniqueness of the maximizer, not assumed);
* `policyFun_mem_Ioo` — that maximizer is **interior** to `[0, 1]` for every strictly positive state
  `w ∈ (0, 1]` (at `w = 0` the optimum is the boundary point `0`, see `policyFun_zero`);
* `policyFun_not_constant` — and **non-constant** (value `0` at `w = 0`, `1/2` at
  `w = 1`), so the induced Markov chain is not a disguised constant map;
* `chain_policy_eq_half` — the chain's continuous policy component is therefore `w ↦ w / 2` on
  `[0, 1]` (this identifies the policy map only, not the full Markov kernel, which also carries the
  `Fin 2` shock transition).

The payoff `exists_stationary_under_optimal_policy` then runs the abstract pipeline to a stationary
distribution of this state-dependent optimal control.
-/

namespace EconlibExamples.Optimization.EndogenousChainOptimalPolicy

open Set MeasureTheory
open Econlib.Optimization Econlib.Probability

/-- The concrete optimization problem: a symmetric two-state shock, the unit interval as the
endogenous state space, and a strictly concave state-dependent objective. -/
noncomputable def problem : EndogenousPolicyProblem 2 where
  w_min := 0
  w_max := 1
  hw := by norm_num
  discrete_trans := fun _ => finDist% ![(1 : ℝ) / 2, 1 / 2]
  feasible := fun _ _ _ => Icc 0 1
  obj := fun w _ _ w' => -(w') ^ 2 + w * w'
  feasible_subset := fun _ _ _ => subset_rfl
  feasible_nonempty := fun _ _ _ => nonempty_Icc.mpr (by norm_num)
  feasible_compact := fun _ _ _ => isCompact_Icc
  feasible_uhc := fun _ _ => UpperHemicontinuous.const
  feasible_lhc := fun _ _ => LowerHemicontinuous.const
  obj_cont := fun _ _ => by fun_prop
  obj_strictConcave := fun w _ _ => by
    -- `-(w')² + w·w'` is (strictly concave `-(w')²`) + (concave linear `w·w'`).
    have hsq : StrictConvexOn ℝ (univ : Set ℝ) (fun x : ℝ => x ^ 2) :=
      Even.strictConvexOn_pow (by norm_num) (by norm_num)
    have hneg : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) (fun x : ℝ => -(x ^ 2)) :=
      (hsq.subset (subset_univ _) (convex_Icc 0 1)).neg
    have hlin : ConcaveOn ℝ (Icc (0 : ℝ) 1) (fun x : ℝ => w * x) :=
      (LinearMap.lsmul ℝ ℝ w).concaveOn (convex_Icc 0 1)
    exact hneg.add_concaveOn hlin

/-- **The interface's optimal policy is exactly `w' = w / 2` on the state interval.** The objective
`-(w')² + w·w'` is a downward parabola in `w'` peaking at `w' = w / 2`, which lies in `[0, 1]`
whenever `w ∈ [0, 1]`. So `w / 2` is the (unique) maximizer over the feasible interval; since
`policyFun` is a selection from that single-valued argmax (`policyFun_mem`,
`argmaxCorr_subsingleton`), it must equal `w / 2`. We *derive* the closed form rather than assume
it. -/
theorem policyFun_eq_half (s s' : Fin 2) {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) :
    problem.policyFun s s' w = w / 2 := by
  -- `w / 2` is a maximizer of the objective over the feasible interval `[0, 1]`.
  have hhalf : w / 2 ∈ problem.argmaxCorr s s' w := by
    obtain ⟨hw0, hw1⟩ := hw
    -- Membership in `Icc 0 1`, then `obj w'' ≤ obj (w/2)` for every feasible `w''`.
    have hmemIcc : w / 2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    refine ⟨hmemIcc, fun w'' _ => ?_⟩
    -- `obj` is the concrete parabola; the gap is the perfect square `-(w'' - w/2)² ≤ 0`.
    change -(w'') ^ 2 + w * w'' ≤ -(w / 2) ^ 2 + w * (w / 2)
    nlinarith [sq_nonneg (w'' - w / 2)]
  -- The argmax is a singleton, so the selected policy value coincides with `w / 2`.
  exact problem.argmaxCorr_subsingleton s s' w (problem.policyFun_mem s s' w) hhalf

/-- The optimal choice at `w = 0` is `0`. -/
theorem policyFun_zero (s s' : Fin 2) : problem.policyFun s s' 0 = 0 := by
  simpa using policyFun_eq_half s s' (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1)

/-- The optimal choice at `w = 1` is `1 / 2`. -/
theorem policyFun_one (s s' : Fin 2) : problem.policyFun s s' 1 = 1 / 2 := by
  simpa using policyFun_eq_half s s' (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)

/-- **The optimal policy is non-constant** in the endogenous state: it takes value `0` at
`w = 0` and `1 / 2` at `w = 1`. This is what makes the example a real test of the state-dependent
machinery rather than a constant-policy degeneracy. -/
theorem policyFun_not_constant (s s' : Fin 2) :
    problem.policyFun s s' 0 ≠ problem.policyFun s s' 1 := by
  rw [policyFun_zero, policyFun_one]; norm_num

/-- **The optimal choice is interior** to the state interval for every strictly positive state:
`w / 2 ∈ (0, 1)` whenever `w ∈ (0, 1]`. So the optimum is never a corner solution. -/
theorem policyFun_mem_Ioo (s s' : Fin 2) {w : ℝ} (hw : w ∈ Ioc (0 : ℝ) 1) :
    problem.policyFun s s' w ∈ Ioo (0 : ℝ) 1 := by
  obtain ⟨hw0, hw1⟩ := hw
  rw [policyFun_eq_half s s' ⟨le_of_lt hw0, hw1⟩]
  exact ⟨by linarith, by linarith⟩

/-- **The induced Markov chain's continuous policy component is `w ↦ w / 2`** on the state interval:
the policy field of `toEndogenousMarkovChain` evolves the endogenous state by halving it, the
closed form of the optimal policy. (This identifies the policy map only; the full Markov kernel also
carries the exogenous `Fin 2` shock transition.) -/
theorem chain_policy_eq_half (s s' : Fin 2) {w : ℝ} (hw : w ∈ Icc (0 : ℝ) 1) :
    problem.toEndogenousMarkovChain.policy w s s' = w / 2 :=
  policyFun_eq_half s s' hw

/-- **Acceptance test / payoff.** The optimally controlled economy admits a stationary
distribution: there is an invariant probability measure on `[0, 1] × Fin 2` for the kernel induced
by the (continuous, optimal) policy. -/
theorem exists_stationary_under_optimal_policy :
    ∃ μ : ProbDist (Icc problem.w_min problem.w_max × Fin 2),
      ProbabilityTheory.Kernel.Invariant problem.toEndogenousMarkovChain.toKernel μ.toMeasure :=
  problem.exists_stationary

end EconlibExamples.Optimization.EndogenousChainOptimalPolicy
