/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.Transfers.General.IndirectMechanism

/-!
# The revelation principle

The **revelation principle** (Myerson 1979): Every Bayes–Nash equilibrium of an indirect mechanism
is replicated by an incentive-compatible direct mechanism that yields the same outcomes and
transfers. The replicating direct mechanism is `directify`, which plays the equilibrium strategy
`σ` on the agents' behalf, so truthful reporting reproduces the equilibrium play. A
dominant-strategy analog is also provided.

## Main statements

* `IndirectMechanism.directify_interimUtility`: Reporting `θ_i'` in `directify σ` gives the same
  interim utility as sending message `σ i θ_i'` in the indirect mechanism.
* `IndirectMechanism.directify_isBIC`: A Bayes–Nash equilibrium of an indirect mechanism induces a
  Bayesian incentive-compatible direct mechanism (the revelation principle).
* `IndirectMechanism.directify_isDSIC`: The dominant-strategy version — a dominant-strategy
  equilibrium induces a dominant-strategy incentive-compatible direct mechanism.
* `IndirectMechanism.directify_alloc`, `IndirectMechanism.directify_transfer`: The direct mechanism
  reproduces the equilibrium outcome and transfers.

## References

* Myerson, Roger B. 1979. “Incentive Compatibility and the Bargaining Problem.” *Econometrica* 47
  (1): 61. [https://doi.org/10.2307/1912346](https://doi.org/10.2307/1912346).

## Tags

revelation principle, incentive compatibility, bayes-nash equilibrium
-/

@[expose] public section

open Function BigOperators

noncomputable section
namespace Econlib.MechanismDesign.Transfers.General

variable {E : QuasilinearEnvironment} (Γ : IndirectMechanism E)

namespace IndirectMechanism

@[simp] lemma directify_alloc (σ : Γ.Strategy) (θ : E.TypeProfile) :
    (Γ.directify σ).alloc θ = Γ.outcome (Γ.msgProfile σ θ) := rfl

@[simp] lemma directify_transfer (σ : Γ.Strategy) (i : E.Agent) (θ : E.TypeProfile) :
    (Γ.directify σ).transfer i θ = Γ.pay i (Γ.msgProfile σ θ) := rfl

/-- Reporting type `θ_i'` in the direct mechanism `directify σ` yields exactly the interim utility
of sending the message `σ i θ_i'` in the indirect mechanism (others playing `σ`). -/
lemma directify_interimUtility (σ : Γ.Strategy) (i : E.Agent) (θ_i θ_i' : E.Theta i) :
    (Γ.directify σ).interimUtility i θ_i θ_i' = Γ.interimUtility σ i θ_i (σ i θ_i') := by
  unfold DirectMechanism.interimUtility interimUtility
  refine Finset.sum_congr rfl fun θ _ => ?_
  rw [DirectMechanism.exPostUtility_def, directify_alloc, directify_transfer,
    Γ.msgProfile_update σ i θ θ_i']

/-- **The revelation principle** (Myerson 1979). If `σ` is a Bayes–Nash equilibrium of the indirect
mechanism `Γ`, then the direct mechanism `directify σ` is Bayesian incentive compatible:
Truth-telling is a Bayes–Nash equilibrium. -/
theorem directify_isBIC {σ : Γ.Strategy} (h : Γ.IsBNE σ) : (Γ.directify σ).IsBIC := by
  rw [Γ.IsBNE_iff] at h
  intro i θ_i θ_i'
  rw [directify_interimUtility, directify_interimUtility]
  by_cases hpos : 0 < E.prior.marginalD i θ_i
  · exact h i θ_i hpos (σ i θ_i')
  · -- At zero-marginal types both interim utilities vanish, so the inequality is `0 ≤ 0`.
    rw [Γ.interimUtility_eq_zero_of_marginal_not_pos σ i θ_i (σ i θ_i') hpos]
    exact (Γ.interimUtility_eq_zero_of_marginal_not_pos σ i θ_i (σ i θ_i) hpos).ge

/-- **The dominant-strategy revelation principle.** If `σ` is a dominant-strategy equilibrium of
the indirect mechanism `Γ`, then the direct mechanism `directify σ` is DSIC: Truth-telling is a
(weakly) dominant strategy for every agent and every type. -/
theorem directify_isDSIC {σ : Γ.Strategy} (h : Γ.IsDominantStrategy σ) :
    (Γ.directify σ).IsDSIC := by
  rw [Γ.IsDominantStrategy_iff] at h
  intro i r θ_i θ_i'
  simp only [DirectMechanism.exPostUtility_def, directify_alloc, directify_transfer,
    Γ.msgProfile_update]
  simpa using h i (update r i θ_i) (Γ.msgProfile σ r) (σ i θ_i')

end IndirectMechanism

end Econlib.MechanismDesign.Transfers.General
end
