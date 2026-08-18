/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Markov.PresentValue

/-!
# Limited-enforcement participation constraints

This file defines participation constraints for finite-state dynamic contracts with limited
enforcement. A `DefaultValue` is a history-adapted outside option. `Participates V D` says that the
continuation value process `V` weakly dominates that outside option at every date and history.

`LimitedEnforcementFeasible P β X D` packages a payoff process `X`, a continuation-value process
`V`, the Bellman recursion for `V` under the Markov chain `P`, and the participation constraint
against `D`. The main uniqueness statement identifies any bounded feasible continuation value with
the canonical present value of `X`.

## Main definitions

* `DefaultValue`: History-adapted lower bound on continuation values (outside option).
* `Participates`: Continuation values dominate the default at every history.
* `LimitedEnforcementFeasible`: Contract payoff and continuation-value data satisfying the Bellman
  recursion and participation constraint against a given default value.

## Main statements

* `participates_iff`: Pointwise characterization of `Participates`.
* `Participates.of_bellman_residual_nonneg`: Sufficient condition for participation via
  state-contingent dominance.
* `LimitedEnforcementFeasible.V_eq_presentValue`: Bounded continuation values equal the canonical
  present value.

## References

* Kehoe, T. J., and D. K. Levine. 1993. “Debt-Constrained Asset Markets.” *The Review of Economic
  Studies* 60 (4): 865–88. [https://doi.org/10.2307/2298103](https://doi.org/10.2307/2298103).
* Kocherlakota, N. R. 1996. “Implications of Efficient Risk Sharing Without Commitment.” *The
  Review of Economic Studies* 63 (4): 595–609. [https://doi.org/10.2307/2297795](https://doi.org/10.2307/2297795).

## Tags

limited enforcement, participation constraint, continuation value, Bellman equation, present value,
sovereign default
-/

@[expose] public section

open BigOperators Finset

namespace Econlib

namespace Equilibrium

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- History-adapted lower bound on continuation values (agent's outside option). -/
abbrev DefaultValue (α : Type*) := Probability.AdaptedProcess α

/-- Continuation values respect the default at every history. -/
def Participates (V : Probability.AdaptedProcess α) (D : DefaultValue α) : Prop :=
  ∀ t h, D.val t h ≤ V.val t h

/-- Contract feasible under limited enforcement against default `D`: Continuation values `V`
satisfy the Bellman recursion and dominate `D` at every history. -/
structure LimitedEnforcementFeasible (P : Probability.FiniteMarkovChain α)
    (β : ℝ) (X : Probability.AdaptedProcess α)
    (D : DefaultValue α) where
  /-- Continuation values realized by the contract. -/
  V : Probability.AdaptedProcess α
  /-- The contract's continuation value satisfies the Bellman recursion. -/
  bellman :
    ∀ t h, V.val t h = X.val t h
                  + β * ∑ s' : α, (P.transition h.lastNode) s' *
                      V.val (t + 1) (h.extend s')
  /-- The contract participates in every history. -/
  participates : Participates V D

omit [Fintype α] [DecidableEq α] in
/-- `Participates V D` iff `D.val t h ≤ V.val t h` for all `t`, `h`. -/
lemma participates_iff
    (V D : Probability.AdaptedProcess α) :
    Participates V D ↔ ∀ t (h : Probability.History α t), D.val t h ≤ V.val t h :=
  Iff.rfl

/-- If `X` dominates the default's Bellman residual at every history and successor continuation
values dominate the default, then the contract participates. -/
lemma Participates.of_bellman_residual_nonneg
    (P : Probability.FiniteMarkovChain α) (β : ℝ) (hβ_nonneg : 0 ≤ β)
    (X : Probability.AdaptedProcess α) (D : DefaultValue α)
    (V : Probability.AdaptedProcess α)
    (hV_bell : ∀ t h, V.val t h = X.val t h
                  + β * ∑ s' : α, (P.transition h.lastNode) s' *
                      V.val (t + 1) (h.extend s'))
    (hX_dominates_default :
      ∀ t h, D.val t h ≤ X.val t h
                  + β * ∑ s' : α, (P.transition h.lastNode) s' *
                      D.val (t + 1) (h.extend s'))
    (hSucc : ∀ t (h : Probability.History α t) (s' : α),
      D.val (t + 1) (h.extend s') ≤ V.val (t + 1) (h.extend s')) :
    Participates V D := by
  intro t h
  rw [hV_bell t h]
  have hsum_le :
      ∑ s' : α, (P.transition h.lastNode) s' * D.val (t + 1) (h.extend s')
        ≤ ∑ s' : α, (P.transition h.lastNode) s' * V.val (t + 1) (h.extend s') := by
    refine Finset.sum_le_sum fun s' _ => ?_
    exact mul_le_mul_of_nonneg_left (hSucc t h s') ((P.transition h.lastNode).nonneg s')
  linarith [hX_dominates_default t h, mul_le_mul_of_nonneg_left hsum_le hβ_nonneg]

/-- Uniformly bounded continuation values of a feasible contract equal the canonical present value
of `X`. -/
theorem LimitedEnforcementFeasible.V_eq_presentValue
    (P : Probability.FiniteMarkovChain α) (β : ℝ)
    (hβ_nonneg : 0 ≤ β) (hβ_lt : β < 1)
    (X : Probability.AdaptedProcess α) (D : DefaultValue α)
    {M : ℝ} (hX : X.Bounded M)
    (F : LimitedEnforcementFeasible P β X D)
    (hV_bdd : ∃ K : ℝ, ∀ t h, |F.V.val t h| ≤ K) :
    ∀ t h, F.V.val t h = Probability.presentValue P β X t h :=
  Probability.presentValue_unique P β hβ_nonneg hβ_lt X hX F.V.val hV_bdd F.bellman

end Equilibrium

end Econlib
