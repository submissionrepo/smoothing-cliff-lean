/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Constrained optimization: Core problem type

`ConstrainedProblem X ι κ` packages an objective with inequality and equality constraints, indexed
by arbitrary types `ι` and `κ`. The associated Lagrangian and two KKT sufficiency lemmas live here:
`isMaxOn_of_kkt_eq` handles the full mixed problem (optimality over `feasibleSet`, using the
equality multipliers), and `isMaxOn_of_kkt` is the inequality-only specialization (optimality over
the larger `feasibleSetIneq`, ignoring the equality data). Neither subsumes the other — see the
note on `isMaxOn_of_kkt_eq`.

## Main definitions

* `ConstrainedProblem`: An inequality- and equality-constrained scalar program over a domain `X`.
* `ConstrainedProblem.feasibleSet`: Points satisfying every inequality and equality constraint.
* `ConstrainedProblem.feasibleSetIneq`: Points satisfying the inequality constraints only.
* `lagrangian`: The Lagrangian `f x - Σ lamᵢ gᵢ x - Σ muⱼ hⱼ x`.

## Main statements

* `ConstrainedProblem.isMaxOn_of_kkt_eq`: **Full KKT sufficiency** — an equality-feasible point
  with dual-feasible inequality multipliers (complementary slackness) and sign-unrestricted
  equality multipliers that maximizes the full Lagrangian over the whole domain is a global
  maximizer of the objective over the full feasible set `feasibleSet`.
* `ConstrainedProblem.isMaxOn_of_kkt`: Inequality-only KKT sufficiency — drops the equality data
  and concludes maximality over the larger inequality-feasible set `feasibleSetIneq`.

## References

* Boyd, Stephen P. 2006. *Convex Optimization*. Cambridge University Press. Chapter 5.

## Tags

constrained optimization, lagrangian, kkt, feasible set
-/

@[expose] public section

namespace Econlib.Optimization

/-- Inequality- and equality-constrained scalar program over an arbitrary domain `X`. `g i x ≤ 0`
encodes the `i`-th inequality; `h j x = 0` the `j`-th equality. -/
structure ConstrainedProblem (X : Type*) (ι κ : Type*) where
  f : X → ℝ
  g : ι → X → ℝ
  h : κ → X → ℝ

namespace ConstrainedProblem

variable {X : Type*} {ι κ : Type*}

/-- Points satisfying both inequality and equality constraints. -/
def feasibleSet (P : ConstrainedProblem X ι κ) : Set X :=
  {x | (∀ i, P.g i x ≤ 0) ∧ ∀ j, P.h j x = 0}

/-- Points satisfying the inequality constraints only. -/
def feasibleSetIneq (P : ConstrainedProblem X ι κ) : Set X :=
  {x | ∀ i, P.g i x ≤ 0}

end ConstrainedProblem

/-- Lagrangian of an inequality- and equality-constrained program. -/
noncomputable def lagrangian {X ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ConstrainedProblem X ι κ) (x : X) (lam : ι → ℝ) (mu : κ → ℝ) : ℝ :=
  P.f x - ∑ i, lam i * P.g i x - ∑ j, mu j * P.h j x

/-- The defining unfold of `lagrangian` as `f x − ∑ lamᵢ gᵢ x − ∑ muⱼ hⱼ x`, exposed as a `simp`
lemma so KKT certificates over concrete index types can rewrite the Lagrangian to its sum form. -/
@[simp] lemma lagrangian_apply {X ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ConstrainedProblem X ι κ) (x : X) (lam : ι → ℝ) (mu : κ → ℝ) :
    lagrangian P x lam mu = P.f x - ∑ i, lam i * P.g i x - ∑ j, mu j * P.h j x :=
  rfl

/-- With no inequality constraints (`ι` empty) the inequality sum drops out:
`lagrangian P x lam mu = f x − ∑ muⱼ hⱼ x`. -/
@[simp] lemma lagrangian_of_isEmpty_ineq {X ι κ : Type*} [Fintype ι] [Fintype κ] [IsEmpty ι]
    (P : ConstrainedProblem X ι κ) (x : X) (lam : ι → ℝ) (mu : κ → ℝ) :
    lagrangian P x lam mu = P.f x - ∑ j, mu j * P.h j x := by
  rw [lagrangian, Fintype.sum_empty (fun i => lam i * P.g i x), sub_zero]

/-- With no equality constraints (`κ` empty) the equality sum drops out:
`lagrangian P x lam mu = f x − ∑ lamᵢ gᵢ x`. -/
@[simp] lemma lagrangian_of_isEmpty_eq {X ι κ : Type*} [Fintype ι] [Fintype κ] [IsEmpty κ]
    (P : ConstrainedProblem X ι κ) (x : X) (lam : ι → ℝ) (mu : κ → ℝ) :
    lagrangian P x lam mu = P.f x - ∑ i, lam i * P.g i x := by
  rw [lagrangian, Fintype.sum_empty (fun j => mu j * P.h j x), sub_zero]

/-- A single inequality constraint (`ι` a `Unique` type, e.g. `Unit`) collapses the inequality sum
to its one term: `lagrangian P x lam mu = f x − lam default · g default x − ∑ muⱼ hⱼ x`. -/
@[simp] lemma lagrangian_unique_ineq {X ι κ : Type*} [Unique ι] [Fintype ι] [Fintype κ]
    (P : ConstrainedProblem X ι κ) (x : X) (lam : ι → ℝ) (mu : κ → ℝ) :
    lagrangian P x lam mu
      = P.f x - lam default * P.g default x - ∑ j, mu j * P.h j x := by
  rw [lagrangian, Fintype.sum_unique (fun i => lam i * P.g i x)]

/-- A single equality constraint (`κ` a `Unique` type, e.g. `Unit`) collapses the equality sum to
its one term: `lagrangian P x lam mu = f x − ∑ lamᵢ gᵢ x − mu default · h default x`. -/
@[simp] lemma lagrangian_unique_eq {X ι κ : Type*} [Fintype ι] [Unique κ] [Fintype κ]
    (P : ConstrainedProblem X ι κ) (x : X) (lam : ι → ℝ) (mu : κ → ℝ) :
    lagrangian P x lam mu
      = P.f x - ∑ i, lam i * P.g i x - mu default * P.h default x := by
  rw [lagrangian, Fintype.sum_unique (fun j => mu j * P.h j x)]

/-- **KKT sufficiency for the mixed equality-and-inequality problem** (Boyd and Vandenberghe 2004,
§5.5.3): If a point `x` is equality-feasible (`h j x = 0`), carries dual-feasible inequality
multipliers `lam` with complementary slackness together with sign-unrestricted equality multipliers
`mu`, and maximizes the full Lagrangian `f y - ∑ lamᵢ gᵢ y - ∑ muⱼ hⱼ y` over the whole domain,
then `x` is a global maximizer of `P.f` over the full feasible set
`feasibleSet = {y | (∀ i, P.g i y ≤ 0) ∧ ∀ j, P.h j y = 0}`.

No convexity or affineness of the constraints is needed for this saddle-point form: Convexity is
what lets one establish the Lagrangian-maximality hypothesis from stationarity (see
`MaxKKT.ofFOC`), not what makes sufficiency hold. Equality feasibility of `x` is load-bearing here
(unlike inequality feasibility, which goes unused) — it forces the equality term of the Lagrangian
to vanish at `x`, there being no complementary-slackness analog for the free `mu`.

This does not subsume `isMaxOn_of_kkt`: That lemma concludes over the larger set `feasibleSetIneq`
from the inequality Lagrangian alone and takes no equality-feasibility hypothesis, so neither
statement implies the other. -/
lemma ConstrainedProblem.isMaxOn_of_kkt_eq {X ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ConstrainedProblem X ι κ) (x : X) (lam : ι → ℝ) (mu : κ → ℝ)
    -- Unused in the proof (`IsMaxOn` does not require `x` itself to be feasible); kept so the
    -- hypotheses are the standard KKT-point data.
    (_h_primal_feas_ineq : ∀ i, P.g i x ≤ 0)
    (h_primal_feas_eq : ∀ j, P.h j x = 0)
    (h_dual_feas : ∀ i, 0 ≤ lam i)
    (h_comp_slack : ∀ i, lam i * P.g i x = 0)
    (h_max_lagrangian : IsMaxOn (fun y => lagrangian P y lam mu) Set.univ x) :
    IsMaxOn P.f P.feasibleSet x := by
  intro y hy
  simp only [ConstrainedProblem.feasibleSet, Set.mem_setOf_eq] at hy
  obtain ⟨hy_ineq, hy_eq⟩ := hy
  have hL := h_max_lagrangian (Set.mem_univ y)
  simp only [Set.mem_setOf_eq, lagrangian] at hL
  -- Complementary slackness kills the inequality term at `x`...
  have hcs : ∑ i, lam i * P.g i x = 0 := Finset.sum_eq_zero (fun i _ => h_comp_slack i)
  -- ...and equality feasibility kills the equality term at both `x` and the feasible `y`.
  have hmu_x : ∑ j, mu j * P.h j x = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [h_primal_feas_eq j, mul_zero])
  have hmu_y : ∑ j, mu j * P.h j y = 0 :=
    Finset.sum_eq_zero (fun j _ => by rw [hy_eq j, mul_zero])
  -- At the feasible `y` the inequality term is nonpositive.
  have hsum_nonpos : ∑ i, lam i * P.g i y ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (h_dual_feas i) (hy_ineq i))
  rw [hcs, hmu_x, hmu_y] at hL
  simp only [sub_zero] at hL
  -- `P.f y ≤ P.f y - ∑ λᵢ gᵢ y ≤ P.f x` since the subtracted sum is nonpositive at `y`.
  change P.f y ≤ P.f x
  linarith [hL, hsum_nonpos]

/-- **Inequality-constrained KKT sufficiency** (Boyd and Vandenberghe 2004): If a point `x` with
multipliers `lam` satisfies dual feasibility and complementary slackness and maximizes the
inequality Lagrangian `f y - ∑ lamᵢ gᵢ y` over the whole domain, then `x` is a global maximizer of
`P.f` over the inequality-feasible set `{y | ∀ i, P.g i y ≤ 0}`. The equality data of `P` is not
handled: The equality constraints `P.h` and any equality multipliers play no role here (the
equality index type `κ` is unrestricted, no equality-feasibility hypothesis is taken, and the
equality term of `lagrangian` does not appear in `h_max_lagrangian` or the conclusion). For the
full mixed problem see `isMaxOn_of_kkt_eq`. -/
lemma ConstrainedProblem.isMaxOn_of_kkt {X ι κ : Type*} [Fintype ι] (P : ConstrainedProblem X ι κ)
    (x : X) (lam : ι → ℝ)
    -- Unused in the proof (`IsMaxOn` does not require `x` itself to be feasible); kept for the
    -- standard KKT signature
    (_h_primal_feas : ∀ i, P.g i x ≤ 0)
    (h_dual_feas : ∀ i, 0 ≤ lam i)
    (h_comp_slack : ∀ i, lam i * P.g i x = 0)
    (h_max_lagrangian : IsMaxOn (fun y => P.f y - ∑ i, lam i * P.g i y) Set.univ x) :
    IsMaxOn P.f {y | ∀ i, P.g i y ≤ 0} x := by
  intro y hy
  simp only [Set.mem_setOf_eq] at hy
  have hL := h_max_lagrangian (Set.mem_univ y)
  simp only [Set.mem_setOf_eq] at hL
  have hcs : ∑ i, lam i * P.g i x = 0 := Finset.sum_eq_zero (fun i _ => h_comp_slack i)
  have hsum_nonpos : ∑ i, lam i * P.g i y ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (h_dual_feas i) (hy i))
  -- `P.f y ≤ P.f y - ∑ λᵢ gᵢ y ≤ P.f x` since the subtracted sum is nonpositive at `x`
  rw [hcs, sub_zero] at hL
  change P.f y ≤ P.f x
  linarith [hL, hsum_nonpos]

end Econlib.Optimization
