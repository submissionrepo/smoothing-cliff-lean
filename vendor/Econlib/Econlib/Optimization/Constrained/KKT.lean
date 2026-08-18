/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.Constrained.Problem

/-!
# Reusable KKT and complementarity certificates

Model-independent KKT wrappers turn finite-dimensional first-order systems into economic Euler
equalities and inequalities. Once nonnegative multipliers and complementary slackness are
available, the certificates here expose the interior Euler equality, the boundary inequality, and a
global maximality statement for concave maximization problems.

## Main definitions

* `NonnegComplementarity`: Nonnegativity/complementary-slackness data for a family of inequality
  constraints in the economic convention.
* `EulerComplementarity`: Euler/KKT system coupling a common LHS price to indexed
  scale–marginal–slack triples.
* `MaxKKT`: Finite-dimensional KKT certificate for a maximization problem with inequality
  constraints.
* `MaxKKTEq`: Finite-dimensional KKT certificate for the full mixed problem (inequalities and
  equalities), carrying sign-unrestricted equality multipliers.

## Main statements

* `NonnegComplementarity.multiplier_eq_zero_of_choice_pos`: Strictly positive primal choice forces
  multiplier to zero.
* `EulerComplementarity.equality_of_choice_pos`: Euler equality at interior choices.
* `EulerComplementarity.scaled_marginal_le_lhs`: Euler inequality at every index.
* `MaxKKT.isMaxOn`: Inequality-constrained KKT sufficiency — certified point globally maximizes the
  objective on the inequality-feasible set `{y | ∀ i, P.g i y ≤ 0}` (equality constraints are not
  handled).
* `MaxKKTEq.isMaxOn`: Full KKT sufficiency — certified point globally maximizes the objective on
  the full feasible set `P.feasibleSet` (both inequalities and equalities).

## References

* Karush, William. 1939. “Minima of Functions of Several Variables with Inequalities as Side
  Conditions.” University of Chicago.
* Kuhn, H. W., and A. W. Tucker. 1951. “Nonlinear Programing.” In *Proceedings of the Second
  Berkeley Symposium on Mathematical Statistics and Probability*, edited by Jerzy Neyman.
  University of California Press.

## Tags

kkt, complementarity, euler, lagrangian, constrained optimization
-/

@[expose] public section

namespace Econlib.Optimization

/-- Nonnegativity/complementarity data for a family of inequality constraints written in the
economic convention `choice i ≥ 0`, `multiplier i ≥ 0`, `multiplier i * choice i = 0`. -/
structure NonnegComplementarity (ι : Type*) where
  /-- The constrained primal quantity. -/
  choice : ι → ℝ
  /-- The associated nonnegative multiplier. -/
  multiplier : ι → ℝ
  /-- Primal nonnegativity. -/
  choice_nonneg : ∀ i, 0 ≤ choice i
  /-- Dual nonnegativity. -/
  multiplier_nonneg : ∀ i, 0 ≤ multiplier i
  /-- Complementary slackness. -/
  complementarity : ∀ i, multiplier i * choice i = 0

namespace NonnegComplementarity

variable {ι : Type*} (C : NonnegComplementarity ι)

/-- A strictly positive primal choice forces the associated multiplier to vanish. -/
lemma multiplier_eq_zero_of_choice_pos {i : ι} (hi : 0 < C.choice i) :
    C.multiplier i = 0 :=
  (mul_eq_zero.mp (C.complementarity i)).resolve_right (ne_of_gt hi)

/-- A strictly positive multiplier forces the primal choice to bind at zero. -/
lemma choice_eq_zero_of_multiplier_pos {i : ι} (hi : 0 < C.multiplier i) :
    C.choice i = 0 :=
  (mul_eq_zero.mp (C.complementarity i)).resolve_left (ne_of_gt hi)

/-- A strictly positive primal choice annihilates any scalar multiple of the multiplier:
`x * multiplier i = 0`. -/
lemma multiplier_mul_eq_zero_of_choice_pos {i : ι} (hi : 0 < C.choice i) (x : ℝ) :
    x * C.multiplier i = 0 := by
  rw [C.multiplier_eq_zero_of_choice_pos hi, mul_zero]

end NonnegComplementarity

/-- A generic Euler/KKT system with one common left-hand side and indexed slack multipliers.

This covers Arrow-claim Euler systems of the form `μ = q i * marginal i + q i * λ i`, where `λ i`
is the multiplier on the nonnegativity constraint for claim `i`. -/
structure EulerComplementarity (ι : Type*) where
  /-- The common marginal value or price on the left-hand side. -/
  lhs : ℝ
  /-- The nonnegative scale multiplying the continuation marginal and slack. -/
  scale : ι → ℝ
  /-- The continuation marginal term. -/
  marginal : ι → ℝ
  /-- The constrained primal choice. -/
  choice : ι → ℝ
  /-- The nonnegative slack multiplier. -/
  slack : ι → ℝ
  /-- Scale nonnegativity, e.g. `β R π_i ≥ 0`. -/
  scale_nonneg : ∀ i, 0 ≤ scale i
  /-- Slack nonnegativity. -/
  slack_nonneg : ∀ i, 0 ≤ slack i
  /-- Primal nonnegativity. -/
  choice_nonneg : ∀ i, 0 ≤ choice i
  /-- Stationarity/Euler equation before complementarity is used. -/
  stationarity : ∀ i, lhs = scale i * marginal i + scale i * slack i
  /-- Complementary slackness. -/
  complementarity : ∀ i, slack i * choice i = 0

namespace EulerComplementarity

variable {ι : Type*} (E : EulerComplementarity ι)

/-- The complementarity sub-system associated with an Euler system. -/
def toNonnegComplementarity : NonnegComplementarity ι where
  choice := E.choice
  multiplier := E.slack
  choice_nonneg := E.choice_nonneg
  multiplier_nonneg := E.slack_nonneg
  complementarity := E.complementarity

/-- Euler equality on an unconstrained/positive-choice index. -/
lemma equality_of_choice_pos {i : ι} (hi : 0 < E.choice i) :
    E.lhs = E.scale i * E.marginal i := by
  have hslack : E.slack i = 0 :=
    E.toNonnegComplementarity.multiplier_eq_zero_of_choice_pos hi
  rw [E.stationarity i, hslack, mul_zero, add_zero]

/-- Euler inequality on every index: Continuation marginal value is weakly below the common
left-hand side once the nonnegative slack term is included. -/
lemma scaled_marginal_le_lhs (i : ι) :
    E.scale i * E.marginal i ≤ E.lhs := by
  rw [E.stationarity i]
  exact le_add_of_nonneg_right (mul_nonneg (E.scale_nonneg i) (E.slack_nonneg i))

/-- If the Euler inequality is strict, the primal choice must bind at zero. -/
lemma choice_eq_zero_of_strict_slack {i : ι}
    (hi : E.scale i * E.marginal i < E.lhs) :
    E.choice i = 0 := by
  rw [E.stationarity i] at hi
  have hscale_slack_pos : 0 < E.scale i * E.slack i := by linarith
  have hslack_pos : 0 < E.slack i :=
    pos_of_mul_pos_right hscale_slack_pos (E.scale_nonneg i)
  exact E.toNonnegComplementarity.choice_eq_zero_of_multiplier_pos hslack_pos

end EulerComplementarity

/-- A finite-dimensional KKT certificate for a maximization problem with inequality constraints
`g i x ≤ 0` (equalities, indexed by `κ`, do not enter the conclusion). Chains to
`ConstrainedProblem.isMaxOn_of_kkt` to expose global optimality as a reusable theorem. -/
structure MaxKKT {X : Type*} {ι κ : Type*} [Fintype ι]
    (P : ConstrainedProblem X ι κ) (x : X) where
  /-- Inequality multipliers. -/
  lambda : ι → ℝ
  /-- Primal feasibility. -/
  primal_feasible : ∀ i, P.g i x ≤ 0
  /-- Dual feasibility. -/
  dual_feasible : ∀ i, 0 ≤ lambda i
  /-- Complementary slackness. -/
  complementarity : ∀ i, lambda i * P.g i x = 0
  /-- Lagrangian maximality. -/
  max_lagrangian :
    IsMaxOn (fun y => P.f y - ∑ i, lambda i * P.g i y) Set.univ x

namespace MaxKKT

variable {X : Type*} {ι κ : Type*} [Fintype ι]
variable {P : ConstrainedProblem X ι κ} {x : X}

/-- **Inequality-constrained KKT sufficiency** (Karush 1939; Kuhn and Tucker 1951): The certified
point globally maximizes the objective over the inequality-feasible set `{y | ∀ i, P.g i y ≤ 0}`.
The equality constraints `P.h` of the underlying `ConstrainedProblem` are not handled: They do not
appear in the conclusion's feasible set, and no equality multipliers enter the certificate. -/
theorem isMaxOn (K : MaxKKT P x) :
    IsMaxOn P.f {y | ∀ i, P.g i y ≤ 0} x :=
  ConstrainedProblem.isMaxOn_of_kkt P x K.lambda K.primal_feasible
    K.dual_feasible K.complementarity K.max_lagrangian

/-- Objective comparison against any inequality-feasible point. -/
lemma objective_le_of_feasible (K : MaxKKT P x) {y : X}
    (hy : ∀ i, P.g i y ≤ 0) :
    P.f y ≤ P.f x :=
  isMaxOn K hy

end MaxKKT

/-- A finite-dimensional KKT certificate for the full mixed problem: Inequality constraints
`g i x ≤ 0` with dual-feasible multipliers and complementary slackness, and equality constraints
`h j x = 0` with sign-unrestricted multipliers `mu`. Chains to
`ConstrainedProblem.isMaxOn_of_kkt_eq` to expose global optimality over the full feasible set as a
reusable theorem. -/
structure MaxKKTEq {X : Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ConstrainedProblem X ι κ) (x : X) where
  /-- Inequality multipliers. -/
  lambda : ι → ℝ
  /-- Equality multipliers (sign-unrestricted). -/
  mu : κ → ℝ
  /-- Inequality primal feasibility. -/
  primal_feasible_ineq : ∀ i, P.g i x ≤ 0
  /-- Equality primal feasibility. -/
  primal_feasible_eq : ∀ j, P.h j x = 0
  /-- Dual feasibility (inequality multipliers). -/
  dual_feasible : ∀ i, 0 ≤ lambda i
  /-- Complementary slackness. -/
  complementarity : ∀ i, lambda i * P.g i x = 0
  /-- Full-Lagrangian maximality. -/
  max_lagrangian :
    IsMaxOn (fun y => lagrangian P y lambda mu) Set.univ x

namespace MaxKKTEq

variable {X : Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {P : ConstrainedProblem X ι κ} {x : X}

/-- **Full KKT sufficiency** (Karush 1939; Kuhn and Tucker 1951): The certified point globally
maximizes the objective over the full feasible set `P.feasibleSet` (both inequality and equality
constraints). -/
theorem isMaxOn (K : MaxKKTEq P x) :
    IsMaxOn P.f P.feasibleSet x :=
  ConstrainedProblem.isMaxOn_of_kkt_eq P x K.lambda K.mu K.primal_feasible_ineq
    K.primal_feasible_eq K.dual_feasible K.complementarity K.max_lagrangian

/-- Objective comparison against any feasible point. -/
lemma objective_le_of_feasible (K : MaxKKTEq P x) {y : X}
    (hy : y ∈ P.feasibleSet) :
    P.f y ≤ P.f x :=
  isMaxOn K hy

end MaxKKTEq

end Econlib.Optimization
