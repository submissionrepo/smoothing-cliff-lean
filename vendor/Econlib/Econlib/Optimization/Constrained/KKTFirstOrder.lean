/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.Constrained.KKT
public import Econlib.Optimization.FirstOrder
public import Optlib.Convex.ConvexFunction

/-!
# First-order constructors for KKT certificates

`MaxKKT` requires a global Lagrangian saddle in its `max_lagrangian` field
(`IsMaxOn (L·) Set.univ x`). For a concave program the natural certificate is instead first-order
stationarity of the Lagrangian together with concavity. These constructors assemble the saddle from
that data, so concave-program KKT examples can supply the first-order condition directly.

## Main definitions

* `MaxKKT.ofFOC` — build a `MaxKKT` certificate over `ℝ` from primal and dual feasibility,
  complementary slackness, concavity of the Lagrangian, and a first-order (`deriv = 0`) condition.
* `MaxKKTEq.ofFOC` — the equality-constraint analog, over a general normed space `E`: Build a
  `MaxKKTEq` certificate from inequality and equality feasibility, dual feasibility, complementary
  slackness, concavity of the *full* Lagrangian, and a Fréchet first-order (`f' = 0`) condition.

## Main statements

* `ConcaveOn.isMaxOn_of_hasGradientAt_eq_zero` — a stationary point (`∇f = 0`) of a function
  concave on a convex set is a global maximizer there. The single-variable `deriv` form is
  `ConcaveOn.isMaxOn_of_deriv_eq_zero`.
* `ConcaveOn.isMaxOn_of_hasFDerivAt_eq_zero` — the Fréchet-derivative version of the same fact over
  a general normed space (no inner product required), the engine behind `MaxKKTEq.ofFOC`.

## References

* Karush, William. 1939. “Minima of Functions of Several Variables with Inequalities as Side
  Conditions.” University of Chicago.
* Kuhn, H. W., and A. W. Tucker. 1951. “Nonlinear Programing.” In *Proceedings of the Second
  Berkeley Symposium on Mathematical Statistics and Probability*, edited by Jerzy Neyman.
  University of California Press.

## Tags

kkt, first-order condition, lagrangian, gradient, concave program
-/

@[expose] public section

namespace Econlib.Optimization

variable {ι κ : Type*} [Fintype ι]

/-- **`MaxKKT` from a first-order condition.** Over `ℝ`, the global Lagrangian saddle required by
`MaxKKT.max_lagrangian` follows from concavity of the Lagrangian plus stationarity at `x`: A
stationary point of a concave function is a global maximizer. `ConcaveOn` suffices — strict
concavity is needed only for uniqueness of the maximizer, not for this certificate. -/
def MaxKKT.ofFOC (P : ConstrainedProblem ℝ ι κ) (x : ℝ) (lambda : ι → ℝ)
    (primal_feasible : ∀ i, P.g i x ≤ 0)
    (dual_feasible : ∀ i, 0 ≤ lambda i)
    (complementarity : ∀ i, lambda i * P.g i x = 0)
    (h_concave : ConcaveOn ℝ Set.univ (fun y => P.f y - ∑ i, lambda i * P.g i y))
    (h_diff : DifferentiableAt ℝ (fun y => P.f y - ∑ i, lambda i * P.g i y) x)
    (h_foc : deriv (fun y => P.f y - ∑ i, lambda i * P.g i y) x = 0) :
    MaxKKT P x where
  lambda := lambda
  primal_feasible := primal_feasible
  dual_feasible := dual_feasible
  complementarity := complementarity
  max_lagrangian :=
    h_concave.isMaxOn_of_deriv_eq_zero isOpen_univ (Set.mem_univ x) h_diff h_foc

section Gradient

open InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **Gradient first-order condition implies global maximum.** A stationary point (`∇f = 0`) of a
function concave on a convex set `s` is a global maximizer on `s`. This is the multi-variable
analog of `ConcaveOn.isMaxOn_of_deriv_eq_zero`. -/
lemma _root_.ConcaveOn.isMaxOn_of_hasGradientAt_eq_zero {f : E → ℝ} {s : Set E} {x : E}
    (h_concave : ConcaveOn ℝ s f) (hx : x ∈ s) (h_grad : HasGradientAt f 0 x) :
    IsMaxOn f s x := by
  -- Work with `-f`, convex with gradient `0`; its first-order condition is global minimality.
  have hconv : ConvexOn ℝ s (-f) := h_concave.neg
  have hgrad_neg : HasGradientAt (-f) (0 : E) x := by
    have := h_grad.neg
    rwa [neg_zero] at this
  -- `Convex_first_order_condition'` with `f' x = 0` collapses to `(-f) x ≤ (-f) y`.
  have hfoc := Convex_first_order_condition' (f' := fun _ => (0 : E)) hgrad_neg hconv hx
  intro y hy
  have h := hfoc y hy
  simp only [Pi.neg_apply, inner_zero_left, add_zero] at h
  -- `(-f) x ≤ (-f) y` is `f y ≤ f x`, i.e. `x` maximizes `f` on `s`.
  simpa only [Set.mem_setOf_eq] using neg_le_neg_iff.mp h

end Gradient

section FDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Fréchet first-order condition implies global maximum.** A stationary point (`f' = 0`, the
zero continuous linear map) of a function concave on a convex set `s` is a global maximizer on `s`.
This is the general normed-space analog of `ConcaveOn.isMaxOn_of_deriv_eq_zero`; unlike
`ConcaveOn.isMaxOn_of_hasGradientAt_eq_zero` it needs no inner product, so it applies on domains
such as `Fin n → ℝ` that carry no canonical `InnerProductSpace`. -/
lemma _root_.ConcaveOn.isMaxOn_of_hasFDerivAt_eq_zero {f : E → ℝ} {s : Set E} {x : E}
    (h_concave : ConcaveOn ℝ s f) (hx : x ∈ s)
    (h_fderiv : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) :
    IsMaxOn f s x := by
  -- Work with `-f`, convex with derivative `0`; its first-order condition is global minimality.
  have hconv : ConvexOn ℝ s (-f) := h_concave.neg
  have hfderiv_neg : HasFDerivAt (-f) (0 : E →L[ℝ] ℝ) x := by
    have := h_fderiv.neg
    rwa [neg_zero] at this
  -- `Convex_first_order_condition` with `f' x = 0` collapses to `(-f) x ≤ (-f) y`.
  have hfoc := Convex_first_order_condition (f' := fun _ => (0 : E →L[ℝ] ℝ)) hfderiv_neg hconv hx
  intro y hy
  have h := hfoc y hy
  simp only [Pi.neg_apply, ContinuousLinearMap.zero_apply, add_zero] at h
  -- `(-f) x ≤ (-f) y` is `f y ≤ f x`, i.e. `x` maximizes `f` on `s`.
  simpa only [Set.mem_setOf_eq] using neg_le_neg_iff.mp h

variable [Fintype κ]

/-- **`MaxKKTEq` from a first-order condition.** The equality-constraint analog of `MaxKKT.ofFOC`:
The global Lagrangian saddle required by `MaxKKTEq.max_lagrangian` follows from concavity of the
*full* Lagrangian `lagrangian P · lambda mu` together with Fréchet stationarity (`f' = 0`) at `x`.
Stated over a general normed space `E`, so it serves both scalar programs over `ℝ` and
finite-dimensional programs over `Fin n → ℝ`. As in `MaxKKT.ofFOC`, `ConcaveOn` suffices — strict
concavity is needed only for uniqueness of the maximizer, not for this certificate. -/
def MaxKKTEq.ofFOC (P : ConstrainedProblem E ι κ) (x : E) (lambda : ι → ℝ) (mu : κ → ℝ)
    (primal_feasible_ineq : ∀ i, P.g i x ≤ 0)
    (primal_feasible_eq : ∀ j, P.h j x = 0)
    (dual_feasible : ∀ i, 0 ≤ lambda i)
    (complementarity : ∀ i, lambda i * P.g i x = 0)
    (h_concave : ConcaveOn ℝ Set.univ (fun y => lagrangian P y lambda mu))
    (h_fderiv : HasFDerivAt (fun y => lagrangian P y lambda mu) (0 : E →L[ℝ] ℝ) x) :
    MaxKKTEq P x where
  lambda := lambda
  mu := mu
  primal_feasible_ineq := primal_feasible_ineq
  primal_feasible_eq := primal_feasible_eq
  dual_feasible := dual_feasible
  complementarity := complementarity
  max_lagrangian :=
    h_concave.isMaxOn_of_hasFDerivAt_eq_zero (Set.mem_univ x) h_fderiv

end FDeriv

end Econlib.Optimization
