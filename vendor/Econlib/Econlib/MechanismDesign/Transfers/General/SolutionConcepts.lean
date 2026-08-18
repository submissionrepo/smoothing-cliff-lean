/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.General.DirectMechanism

/-!
# Solution concepts for direct mechanisms

The properties a direct mechanism may satisfy: Dominant-strategy incentive compatibility (Gibbard
1973) and Bayesian incentive compatibility (Myerson 1979), ex-post and interim individual
rationality, efficiency, and budget conditions. These are `Prop`s on a `DirectMechanism`, not
type-level constraints, because they are exactly what the VCG/Groves theorems establish.

The sign convention is shared library-wide: `transfer` is money received, so individual rationality
normalizes the outside option to `0` and budget conditions read off the sum of transfers.
No-deficit is `∑ transfer ≤ 0` (the mechanism never pays out on net).

## Main definitions

* `IsDSIC`: Truth-telling is a dominant strategy (for every profile of others' reports).
* `IsBIC`: Truth-telling is a Bayes–Nash equilibrium under the common prior.
* `interimUtility`: Interim expected utility of a report under truthful reporting by others.
* `IsExPostIR`, `IsInterimIR`: Participation is individually rational ex post / in expectation.
* `IsEfficient`: The allocation maximizes total value at every reported profile.
* `IsBudgetBalanced`, `IsNoDeficit`: Transfers sum to zero / are nonpositive.

## Main statements

* `isEfficient_iff_isMaxOn`: Efficiency is the allocation maximizing total value over the outcome
  space at each profile.

## References

* Gibbard, Allan. 1973. “Manipulation of Voting Schemes: A General Result.” *Econometrica* 41 (4):
  587. [https://doi.org/10.2307/1914083](https://doi.org/10.2307/1914083).
* Myerson, Roger B. 1979. “Incentive Compatibility and the Bargaining Problem.” *Econometrica* 47
  (1): 61. [https://doi.org/10.2307/1912346](https://doi.org/10.2307/1912346).

## Tags

incentive compatibility, dsic, bic, individual rationality, efficiency, budget balance
-/

@[expose] public section

open Function BigOperators

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

variable {E : QuasilinearEnvironment}

namespace DirectMechanism

variable (M : DirectMechanism E)

/-- **Dominant-strategy incentive compatibility.** Truthful reporting weakly dominates every
misreport, for every agent, every true type, and every fixed profile of others' reports. -/
def IsDSIC : Prop :=
  ∀ (i : E.Agent) (r : E.TypeProfile) (θ_i θ_i' : E.Theta i),
    M.exPostUtility i (update r i θ_i') θ_i ≤ M.exPostUtility i (update r i θ_i) θ_i

/-- Interim expected utility of agent `i` with true type `θ_i` who reports `θ_i'`, assuming all
other agents report truthfully. The expectation is over the others' types under the prior
conditional on `θ i = θ_i`. -/
def interimUtility (i : E.Agent) (θ_i θ_i' : E.Theta i) : ℝ :=
  ∑ θ ∈ Finset.univ.filter (fun θ : E.TypeProfile => θ i = θ_i),
    E.prior.condProbD i θ_i θ * M.exPostUtility i (update θ i θ_i') (θ i)

/-- Interim utility vanishes when the marginal probability of `θ_i` is zero. -/
lemma interimUtility_eq_zero_of_marginal_not_pos (i : E.Agent) (θ_i θ_i' : E.Theta i)
    (h : ¬ 0 < E.prior.marginalD i θ_i) :
    M.interimUtility i θ_i θ_i' = 0 := by
  unfold interimUtility
  refine Finset.sum_eq_zero fun θ _ => ?_
  rw [E.prior.condProbD_eq_zero_of_not_pos i θ_i θ h, zero_mul]

/-- **Bayesian incentive compatibility.** Truthful reporting is a Bayes–Nash equilibrium: Each
agent-type weakly prefers reporting its true type to any misreport, in interim expectation. -/
def IsBIC : Prop :=
  ∀ (i : E.Agent) (θ_i θ_i' : E.Theta i),
    M.interimUtility i θ_i θ_i' ≤ M.interimUtility i θ_i θ_i

/-- **Ex-post individual rationality.** With the outside option normalized to `0`, every agent gets
nonnegative utility under truthful reporting at every type profile. -/
def IsExPostIR : Prop :=
  ∀ (i : E.Agent) (θ : E.TypeProfile), 0 ≤ M.exPostUtility i θ (θ i)

/-- **Interim individual rationality.** Every agent-type gets nonnegative expected utility from
truthful participation. -/
def IsInterimIR : Prop :=
  ∀ (i : E.Agent) (θ_i : E.Theta i), 0 ≤ M.interimUtility i θ_i θ_i

/-- **Efficiency.** The allocation maximizes total value at every reported profile. -/
def IsEfficient : Prop :=
  ∀ (θ : E.TypeProfile) (o : E.Outcome), E.totalValue o θ ≤ E.totalValue (M.alloc θ) θ

/-- `IsEfficient` is equivalent to the allocation being a maximizer of total value over the outcome
space at each profile. -/
lemma isEfficient_iff_isMaxOn :
    M.IsEfficient ↔ ∀ θ, IsMaxOn (fun o => E.totalValue o θ) Set.univ (M.alloc θ) := by
  simp only [IsEfficient, isMaxOn_iff, Set.mem_univ, forall_const]

/-- **(Strong) budget balance.** Transfers sum to zero at every profile. -/
def IsBudgetBalanced : Prop :=
  ∀ (θ : E.TypeProfile), ∑ i, M.transfer i θ = 0

/-- **No deficit (feasibility).** The mechanism never pays out on net: Transfers (money received by
agents) sum to at most zero, so the designer collects a nonnegative amount. -/
def IsNoDeficit : Prop :=
  ∀ (θ : E.TypeProfile), ∑ i, M.transfer i θ ≤ 0

end DirectMechanism

end Econlib.MechanismDesign.Transfers.General
end
