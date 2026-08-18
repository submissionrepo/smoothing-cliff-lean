/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.DynamicProgramming.Core.BellmanOperator
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Bellman fixed point and optimal policy

The contraction property of the **Bellman operator**, the value function as the unique bounded
fixed point via Banach's fixed-point theorem, and optimal policy existence. The contraction relies
on the discount factor `β < 1` together with boundedness of the rewards. The contraction estimate
and the fixed-point plumbing both come from the shared core in `Econlib.Math.Analysis.Blackwell`.

## Main definitions

* `DetMDP.valueFunction`: The value function — the unique bounded solution of the Bellman equation.

## Main statements

* `bellmanOperator_contraction`: The Bellman operator is a contraction with modulus `β`.
* `DetMDP.valueFunction_isFixedPt` / `DetMDP.eq_valueFunction`: The value function satisfies the
  Bellman equation and is the unique bounded function doing so.
* `DetMDP.bellmanOperator_existsUnique_fixedPoint`: The same packaged as `∃!`.
* `DetMDP.exists_optimalAction`: Under compactness and continuity, an optimizing action exists at
  each state (pointwise). The optimal-policy-function existence is `DetMDP.exists_optimalPolicy` in
  `Optimality.lean`.

## References

* Bellman, Richard. 1957. *Dynamic Programing*. Princeton University Press.
* Blackwell, David. 1965. “Discounted Dynamic Programing.” *The Annals of Mathematical Statistics*
  36 (1): 226–35. [https://doi.org/10.1214/aoms/1177700285](https://doi.org/10.1214/aoms/1177700285).
* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press. [https://doi.org/10.2307/j.ctvjnrt76](https://doi.org/10.2307/j.ctvjnrt76).

## Tags

bellman equation, dynamic programing, value function, fixed point, contraction mapping
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

open Blackwell UnboundedDetMDP

open Econlib.Optimization

universe u_S
variable {S : Type u_S} {A : Type*} [Nonempty S]

/-! ## Fixed Point = Value Function -/

/-- Pointwise bound: `|Tv(s) - Tw(s)| ≤ β * sup|v-w|` for each state `s`. -/
lemma bellmanOperator_apply_abs_sub_le (M : DetMDP S A)
    (v w : S → ℝ) (hBv : UniformBounded v) (hBw : UniformBounded w)
    (s : S) :
    |M.bellmanOperator v s - M.bellmanOperator w s| ≤ M.β * ⨆ s, |v s - w s| :=
  Blackwell.abs_sub_le_of_monotone_discounting
    (fun v w _ hw hvw => bellmanOperator_monotone M v w hw hvw)
    (bellmanOperator_discounting M) hBv hBw s

/-- The Bellman operator is a contraction with modulus `β` under the sup norm. -/
theorem bellmanOperator_contraction (M : DetMDP S A) :
    ∀ v w : S → ℝ,
      UniformBounded v →
      UniformBounded w →
      ⨆ s, |M.bellmanOperator v s - M.bellmanOperator w s| ≤
        M.β * ⨆ s, |v s - w s| :=
  fun v w hBv hBw => ciSup_le fun s => bellmanOperator_apply_abs_sub_le M v w hBv hBw s

/-- The lifted Bellman operator is a Banach contraction with modulus `β`. -/
theorem DetMDP.contractingWith_bellmanOperatorBddFun (M : DetMDP S A) :
    ContractingWith ⟨M.β, M.β_nonneg⟩ (bellmanOperatorBddFun M) :=
  Blackwell.contractingWith_liftBddFun M.β_nonneg M.β_lt_one
    (bellmanOperator_apply_abs_sub_le M)

/-- The **value function** of a deterministic MDP: The unique bounded solution of the Bellman
equation, obtained from Banach's fixed-point theorem via the shared core in
`Econlib.Math.Analysis.Blackwell`. -/
noncomputable def DetMDP.valueFunction (M : DetMDP S A) : S → ℝ :=
  Blackwell.bddFixedPoint M.contractingWith_bellmanOperatorBddFun

/-- The value function is uniformly bounded. -/
theorem DetMDP.valueFunction_bounded (M : DetMDP S A) :
    UniformBounded M.valueFunction :=
  Blackwell.bddFixedPoint_bounded _

/-- The value function satisfies the Bellman equation. -/
theorem DetMDP.valueFunction_isFixedPt (M : DetMDP S A) (s : S) :
    M.valueFunction s = M.bellmanOperator M.valueFunction s :=
  Blackwell.bddFixedPoint_isFixedPt _ s

/-- Uniqueness: Any bounded solution of the Bellman equation is the value function. -/
theorem DetMDP.eq_valueFunction (M : DetMDP S A) {v : S → ℝ}
    (hv_bdd : UniformBounded v) (hv_fp : ∀ s, v s = M.bellmanOperator v s) :
    v = M.valueFunction :=
  Blackwell.eq_bddFixedPoint _ hv_bdd hv_fp

/-- **Existence and uniqueness of the value function** (Blackwell 1965): There exists a unique
bounded function `v*` satisfying `v* = Tv*` (the Bellman equation), namely
`DetMDP.valueFunction`. -/
theorem DetMDP.bellmanOperator_existsUnique_fixedPoint (M : DetMDP S A) :
    ∃! v : S → ℝ, UniformBounded v ∧
      ∀ s, v s = M.bellmanOperator v s :=
  ⟨M.valueFunction, ⟨M.valueFunction_bounded, M.valueFunction_isFixedPt⟩,
    fun _ ⟨hw_bdd, hw_eq⟩ => M.eq_valueFunction hw_bdd hw_eq⟩

/-! ## Optimal Action (pointwise)

Pointwise maximizer existence: At each state an optimizing action exists. For the selection of
a stationary policy function see `DetMDP.exists_optimalPolicy` in `Optimality.lean`. -/

/-- **Optimal action existence (pointwise).** If `Γ(s)` is compact and the reward and transition
are continuous, then at each state `s` there is a feasible action `a ∈ Γ(s)` attaining the supremum
defining `(T v_star) s`, i.e., `v_star s = reward s a + β · v_star (transition s a)`. This is a
`∀ s, ∃ a …` statement; the policy-function selection is `DetMDP.exists_optimalPolicy` in
`Optimality.lean`. -/
theorem DetMDP.exists_optimalAction [TopologicalSpace A] [TopologicalSpace S]
    (M : DetMDP S A)
    (h_compact : ∀ s, IsCompact (M.Γ s))
    (h_cont_reward : ∀ s, ContinuousOn (M.reward s) (M.Γ s))
    (h_cont_trans : ∀ s, ContinuousOn (M.transition s) (M.Γ s))
    (v_star : S → ℝ) (hv : ∀ s, v_star s = M.bellmanOperator v_star s)
    (h_v_cont : Continuous v_star) :
    ∀ s, ∃ a ∈ M.Γ s,
      v_star s = M.reward s a + M.β * v_star (M.transition s a) := by
  intro s
  set obj : A → ℝ := fun a => M.reward s a + M.β * v_star (M.transition s a) with obj_def
  have h_cont_obj : ContinuousOn obj (M.Γ s) :=
    (h_cont_reward s).add ((continuousOn_const).mul
      (h_v_cont.continuousOn.comp (h_cont_trans s) (Set.mapsTo_univ _ _)))
  obtain ⟨a, ha, hmax⟩ := (h_compact s).exists_isMaxOn (M.Γ_nonempty s) h_cont_obj
  refine ⟨a, ha, ?_⟩
  rw [hv s]; unfold bellmanOperator
  -- `obj a` is the maximum of the Bellman set, hence its supremum.
  exact IsGreatest.csSup_eq
    ⟨⟨a, ha, rfl⟩, fun r hr => by obtain ⟨a', ha', rfl⟩ := hr; exact hmax ha'⟩

end Econlib.Optimization.DynamicProgramming
