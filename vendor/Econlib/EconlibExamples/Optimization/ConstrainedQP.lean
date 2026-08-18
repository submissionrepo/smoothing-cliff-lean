/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# A Constrained Quadratic Program via KKT

This file is a small worked example of Karush-Kuhn-Tucker sufficiency in one dimension. The program
maximizes the strictly concave objective `f(x) = −(x − a)²` subject to the single inequality
constraint `g(x) = x − b ≤ 0`, so the feasible set is the half-line `x ≤ b`.

The unconstrained objective wants to choose `x = a`. When `b < a`, the constraint cuts that point
off, and the constrained solution is forced to the boundary `x* = b`. The KKT multiplier is then
`λ = 2(a − b) > 0`: It is positive exactly because relaxing the upper bound has value. At the
knife-edge `b = a`, the constraint is tight but costless and the multiplier is `0`. When `a < b`,
the constraint is slack and the true value is the unconstrained value `0`.

## The story

Think of `a` as the bliss point and `b` as a policy, budget, or capacity ceiling. The payoff falls
quadratically as the chosen action moves away from `a`. If the ceiling is below the bliss point,
the agent would like to move right but cannot, so the best feasible action is the ceiling itself.

This is the simplest setting in which the KKT multiplier has its usual economic reading as the
marginal value of relaxing the constraint (i.e. as the shadow price).

## The mathematics

The Lagrangian is

`L(y) = −(y − a)² − λ(y − b)`,

with derivative `L′(y) = 2(a − y) − λ`. Stationarity at the candidate solution `x* = b` forces
`λ = 2(a − b)`, and this is dual feasible exactly in the binding range `b ≤ a`.

Since `L″ ≡ −2 < 0`, the Lagrangian is strictly concave, so the stationary point is automatically
its global maximum. Complementary slackness is immediate because the boundary candidate satisfies
`g(b) = 0`. Together, these facts build the `MaxKKT` certificate, and `MaxKKT.isMaxOn` turns the
certificate into global constrained optimality.

## What this file proves

We construct the concrete problem `qp a b`, derive the multiplier from the first-order condition,
and package the KKT certificate at `x* = b` for the binding range `b ≤ a`.

The file also records the economic interpretation:

* In the strict binding case `b < a`, the unconstrained maximizer `a` is infeasible and the
  multiplier is strictly positive.
* On the binding range, the value is `V(b) = f(b) = −(b − a)²`, and the envelope identity
  `V′(b) = λ` holds exactly.
* In the slack region `a ≤ b`, the unconstrained maximizer is feasible, the true value is constant
  `0`, and the shadow price vanishes.

## Main definitions and theorems

* `qp a b` — the constrained problem (`f = −(x−a)²`, one constraint `g = x − b`, no equalities).
* `multiplier a b` — the KKT multiplier `λ = 2(a − b)`, determined by first-order stationarity
  (`multiplier_spec`, `multiplier_unique`).
* `lagrangian a b`, `deriv_lagrangian_eq_zero`, `lagrangian_strictConcaveOn`, `lagrangian_isMaxOn`
  — the first-order route from stationarity to global Lagrangian maximality.
* `kkt a b hab` — the KKT certificate at `x* = b`, using the derived multiplier and Lagrangian
  maximality.
* `qp_isMaxOn` / `qp_isMaxOn_unique` — `x* = b` is the unique global constrained maximizer.
* `unconstrained_isMaxOn`, `unconstrained_infeasible`, `multiplier_pos`, `constraint_binds` — the
  binding-constraint story for `b < a`.
* `valueFn`, `valueFn_isGreatest`, `shadow_price` — the value function and the shadow-price
  identity `V′(b) = λ`, valid on the binding range `b ≤ a`; `slack_value_isGreatest` covers the
  slack region `a ≤ b`, where the value is constant `0` and the shadow price vanishes.
-/

noncomputable section

namespace EconlibExamples.Optimization.ConstrainedQP

open Econlib.Optimization

variable (a b : ℝ)

/-- The constrained quadratic program: Maximize `−(x−a)²` subject to `x − b ≤ 0`. There are no
equality constraints, so the equality index type is `Empty`. -/
def qp : ConstrainedProblem ℝ Unit Empty where
  f := fun x => -(x - a) ^ 2
  g := fun _ x => x - b
  h := fun e => e.elim

@[simp] lemma qp_f_apply (x : ℝ) : (qp a b).f x = -(x - a) ^ 2 := rfl

@[simp] lemma qp_g_apply (i : Unit) (x : ℝ) : (qp a b).g i x = x - b := rfl

/-! ## Deriving the multiplier from the first-order condition -/

/-- The KKT multiplier `λ = 2(a − b)`. This is not an ansatz: `multiplier_spec` shows it solves the
stationarity equation `f′(x*) = λ·g′(x*)` at `x* = b`, and `multiplier_unique` shows it is the only
solution. -/
def multiplier : ℝ := 2 * (a - b)

/-- The objective's derivative: `f′(x) = 2(a − x)`. -/
lemma hasDerivAt_f (x : ℝ) : HasDerivAt (qp a b).f (2 * (a - x)) x := by
  have h := (((hasDerivAt_id x).sub_const a).pow 2).neg
  convert h using 1
  norm_num
  ring

lemma deriv_f (x : ℝ) : deriv (qp a b).f x = 2 * (a - x) :=
  (hasDerivAt_f a b x).deriv

/-- The constraint's derivative: `g′(x) = 1`. -/
lemma hasDerivAt_g (i : Unit) (x : ℝ) : HasDerivAt ((qp a b).g i) 1 x :=
  (hasDerivAt_id x).sub_const b

lemma deriv_g (i : Unit) (x : ℝ) : deriv ((qp a b).g i) x = 1 :=
  (hasDerivAt_g a b i x).deriv

/-- **Stationarity is satisfied**: The multiplier solves the first-order Lagrangian condition
`f′(x*) = λ·g′(x*)` at the candidate solution `x* = b`. -/
theorem multiplier_spec :
    deriv (qp a b).f b = multiplier a b * deriv ((qp a b).g ()) b := by
  rw [deriv_f, deriv_g, multiplier]
  ring

/-- **Stationarity fixes the multiplier**: `λ = 2(a − b)` is the unique solution of the
first-order condition. -/
theorem multiplier_unique (lam : ℝ)
    (hlam : deriv (qp a b).f b = lam * deriv ((qp a b).g ()) b) :
    lam = multiplier a b := by
  rw [deriv_f, deriv_g, mul_one] at hlam
  rw [multiplier, ← hlam]

/-! ## The Lagrangian: Stationary at `x* = b`, strictly concave, hence globally maximized there -/

/-- The Lagrangian `L(y) = f(y) − λ·g(y)` at the derived multiplier. This is the library Lagrangian
`Econlib.Optimization.lagrangian` of `qp a b` at the inequality multiplier `λ` (the equality index
is `Empty`), so the eval lemma below comes straight from the library collapse lemmas. -/
def lagrangian (y : ℝ) : ℝ :=
  Econlib.Optimization.lagrangian (qp a b) y (fun _ => multiplier a b) Empty.elim

/-- The single-constraint Lagrangian in explicit form, obtained from the library collapse lemmas
`lagrangian_unique_ineq` (the `Unit`-indexed inequality sum is one term) and
`lagrangian_of_isEmpty_eq` (no equalities). -/
@[simp] lemma lagrangian_apply (y : ℝ) :
    lagrangian a b y = -(y - a) ^ 2 - multiplier a b * (y - b) := by
  simp [lagrangian]

lemma hasDerivAt_lagrangian (y : ℝ) :
    HasDerivAt (lagrangian a b) (2 * (a - y) - multiplier a b) y := by
  -- Differentiate the explicit form `−(y−a)² − λ(y−b)` and transport along `lagrangian_apply`.
  have hfun : lagrangian a b = fun y => -(y - a) ^ 2 - multiplier a b * (y - b) :=
    funext (lagrangian_apply a b)
  rw [hfun]
  have h := (hasDerivAt_f a b y).sub ((hasDerivAt_g a b () y).const_mul (multiplier a b))
  simpa using h

lemma differentiable_lagrangian : Differentiable ℝ (lagrangian a b) :=
  fun y => (hasDerivAt_lagrangian a b y).differentiableAt

lemma deriv_lagrangian (y : ℝ) :
    deriv (lagrangian a b) y = 2 * (a - y) - multiplier a b :=
  (hasDerivAt_lagrangian a b y).deriv

/-- **First-order condition**: The Lagrangian is stationary at `x* = b`. -/
theorem deriv_lagrangian_eq_zero : deriv (lagrangian a b) b = 0 := by
  rw [deriv_lagrangian, multiplier]
  ring

/-- `L″ ≡ −2 < 0`: The Lagrangian is strictly concave on all of `ℝ`. -/
lemma lagrangian_strictConcaveOn : StrictConcaveOn ℝ Set.univ (lagrangian a b) := by
  apply strictConcaveOn_of_deriv2_neg' convex_univ
    (differentiable_lagrangian a b).continuous.continuousOn
  intro x _
  -- L′ is the affine map `y ↦ 2(a − y) − λ`, whose derivative is the constant `−2`
  have hL' : deriv (lagrangian a b) = fun y => 2 * (a - y) - multiplier a b :=
    funext (deriv_lagrangian a b)
  have h2 : HasDerivAt (fun y : ℝ => 2 * (a - y) - multiplier a b) (-2) x := by
    have h := (((hasDerivAt_id x).const_sub a).const_mul 2).sub_const (multiplier a b)
    simpa using h
  have hiter : deriv^[2] (lagrangian a b) x = deriv (deriv (lagrangian a b)) x := by
    simp [Function.iterate_succ_apply']
  rw [hiter, hL', h2.deriv]
  norm_num

/-- **Global Lagrangian maximality from the FOC.** The stationary point `x* = b` globally maximizes
the strictly concave Lagrangian (via `StrictConcaveOn.isMaxOn_of_deriv_eq_zero`). -/
theorem lagrangian_isMaxOn : IsMaxOn (lagrangian a b) Set.univ b :=
  (lagrangian_strictConcaveOn a b).isMaxOn_of_deriv_eq_zero isOpen_univ (Set.mem_univ b)
    (differentiable_lagrangian a b b) (deriv_lagrangian_eq_zero a b)

/-! ## The KKT certificate and global optimality -/

/-- The Lagrangian in the packaged form `MaxKKT.ofFOC` consumes, `y ↦ f y − ∑ᵢ λᵢ·gᵢ y`, agrees
with the single-constraint `lagrangian a b`. Since `lagrangian a b` is the library Lagrangian and
there are no equality constraints, this is exactly the library collapse lemma
`lagrangian_of_isEmpty_eq`. -/
lemma ofFOC_lagrangian_eq :
    (fun y => (qp a b).f y - ∑ i, (fun _ => multiplier a b) i * (qp a b).g i y)
      = lagrangian a b := by
  funext y
  rw [lagrangian, lagrangian_of_isEmpty_eq]

/-- The **KKT certificate** at the binding solution `x* = b`, assembled by the packaged constructor
`MaxKKT.ofFOC`: primal/dual feasibility and complementary slackness are immediate, and the global
Lagrangian saddle comes from concavity of the Lagrangian plus the first-order condition
`deriv_lagrangian_eq_zero` — no by-hand `max_lagrangian` assembly. (The explicit
`lagrangian_isMaxOn` above shows the same maximality directly, as pedagogy.) -/
def kkt (hab : b ≤ a) : MaxKKT (qp a b) b :=
  MaxKKT.ofFOC (qp a b) b (fun _ => multiplier a b)
    (fun _ => by simp)
    (fun _ => by rw [multiplier]; linarith)
    (fun _ => by simp)
    (by rw [ofFOC_lagrangian_eq]; exact (lagrangian_strictConcaveOn a b).concaveOn)
    (by rw [ofFOC_lagrangian_eq]; exact differentiable_lagrangian a b b)
    (by rw [ofFOC_lagrangian_eq]; exact deriv_lagrangian_eq_zero a b)

/-- **KKT sufficiency.** The certified point `x* = b` globally maximizes the objective over the
feasible set `{x | x ≤ b}`. -/
theorem qp_isMaxOn (hab : b ≤ a) :
    IsMaxOn (qp a b).f {x | ∀ i, (qp a b).g i x ≤ 0} b :=
  (kkt a b hab).isMaxOn

/-! ## Uniqueness of the maximizer -/

/-- The objective is strictly concave on all of `ℝ` (it is the Lagrangian at `b = a`, where the
multiplier vanishes). -/
lemma f_strictConcaveOn : StrictConcaveOn ℝ Set.univ (qp a b).f := by
  have h := lagrangian_strictConcaveOn a a
  have heq : lagrangian a a = (qp a b).f := by
    funext y
    simp [multiplier]
  rwa [heq] at h

/-- The feasible set is the half-line `(-∞, b]`. -/
lemma feasibleSet_eq : {x : ℝ | ∀ i, (qp a b).g i x ≤ 0} = Set.Iic b := by
  ext x
  simp

/-- **Uniqueness.** Any feasible maximizer coincides with `x* = b`: Strict concavity admits at most
one maximizer on the (convex) feasible set. -/
theorem qp_isMaxOn_unique (hab : b ≤ a) {y : ℝ}
    (hy : ∀ i, (qp a b).g i y ≤ 0)
    (hopt : IsMaxOn (qp a b).f {x | ∀ i, (qp a b).g i x ≤ 0} y) :
    y = b := by
  have hconc : StrictConcaveOn ℝ {x : ℝ | ∀ i, (qp a b).g i x ≤ 0} (qp a b).f := by
    rw [feasibleSet_eq]
    exact (f_strictConcaveOn a b).subset (Set.subset_univ _) (convex_Iic b)
  exact hconc.eq_of_isMaxOn hopt (qp_isMaxOn a b hab) hy fun i => by simp

/-! ## The binding case `b < a` -/

/-- The constraint binds at the solution: `g(x*) = 0`. -/
theorem constraint_binds : (qp a b).g () b = 0 := by simp

/-- With the constraint dropped, the unconstrained optimum is `x = a`. -/
theorem unconstrained_isMaxOn : IsMaxOn (qp a b).f Set.univ a := by
  intro y _
  simp only [Set.mem_setOf_eq, qp_f_apply, sub_self]
  nlinarith [sq_nonneg (y - a)]

/-- When `b < a` the unconstrained optimum `x = a` is **infeasible**: The constraint cuts it off,
which is what makes the program constrained. -/
theorem unconstrained_infeasible (hba : b < a) : ¬ (qp a b).g () a ≤ 0 := by
  simp only [qp_g_apply, not_le]
  linarith

/-- **Strict complementary slackness**: When the constraint binds (`b < a`), the derived
multiplier is strictly positive. (At `b = a` it vanishes and the constraint is costless.) -/
theorem multiplier_pos (hba : b < a) : 0 < multiplier a b := by
  rw [multiplier]
  linarith

/-! ## The shadow-price interpretation of the multiplier -/

/-- The **value function** of the program as the constraint level varies: `V(b) = f(b)`, the
objective evaluated at the optimum `x* = b`. That this is the optimal value is
`valueFn_isGreatest`. -/
def valueFn : ℝ → ℝ := fun b' => (qp a b').f b'

/-- `valueFn` is the value of the program: For `b ≤ a`, `V(b)` is the greatest attainable
objective value over the feasible set. -/
theorem valueFn_isGreatest (hab : b ≤ a) :
    IsGreatest ((qp a b).f '' {x | ∀ i, (qp a b).g i x ≤ 0}) (valueFn a b) := by
  constructor
  · exact ⟨b, fun i => by simp, rfl⟩
  · rintro v ⟨x, hx, rfl⟩
    exact qp_isMaxOn a b hab hx

/-- In the **slack region** `a ≤ b` the constraint no longer binds: The program's value is the
unconstrained optimum `f(a) = 0`, attained at the now-feasible interior point `x = a`. The true
value function is therefore *constant* on `[a, ∞)` and the shadow price of the constraint is `0`
there — `valueFn` describes the program only on the binding range `b ≤ a` (`valueFn_isGreatest`). -/
theorem slack_value_isGreatest (hba : a ≤ b) :
    IsGreatest ((qp a b).f '' {x | ∀ i, (qp a b).g i x ≤ 0}) 0 := by
  constructor
  · exact ⟨a, fun i => by simpa using hba, by simp⟩
  · rintro v ⟨x, hx, rfl⟩
    simpa using unconstrained_isMaxOn a b (Set.mem_univ x)

/-- **Shadow price / envelope identity**: On the binding range `b ≤ a` — where `valueFn` is the
program's value (`valueFn_isGreatest`) and `λ` is dual feasible — the derivative of the value
function at constraint level `b` is exactly the KKT multiplier, `V′(b) = λ = 2(a − b)`. Relaxing
the constraint by `db` is worth `λ·db`, the economic content of the multiplier. (The derivative
identity below holds for all `b`, but past `a` it loses this reading: There the constraint is
slack, the program's true value is constant `0` with shadow price `0` — `slack_value_isGreatest` —
matching `λ = 0` exactly at the kink `b = a`.) -/
theorem shadow_price : deriv (valueFn a) b = multiplier a b := by
  have h : HasDerivAt (valueFn a) (2 * (a - b)) b := hasDerivAt_f a b b
  rw [h.deriv, multiplier]

end EconlibExamples.Optimization.ConstrainedQP
