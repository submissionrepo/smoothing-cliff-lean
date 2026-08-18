/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Berge's Maximum Theorem on a Consumer's Budget

Berge's **maximum theorem** is the workhorse continuity result of comparative statics: If an
objective `f : Θ → X → ℝ` is jointly continuous and the constraint correspondence `Φ : Θ → Set X`
is*continuous (upper and lower hemicontinuous), compact-valued, and nonempty-valued, then the value
function `θ ↦ sup_{x ∈ Φ θ} f θ x` is continuous and the argmax correspondence `θ ↦ argmax f (Φ θ)`
is upper hemicontinuous. In consumer theory this is the statement that the indirect utility (value
function) varies continuously and that demand (the argmax) has no sudden jumps as the economic
environment moves.

This file is a worked example that instantiates the general Berge machinery already developed in
`Econlib.Optimization.MaximumTheorem` together with the budget-correspondence hemicontinuity lemmas
in `Econlib.Equilibrium` on a fully concrete single-good consumer.

## The model

A consumer buys a single good, so bundles live in `Fin 1 → ℝ` and consumption is constrained to the
nonnegative orthant. Wealth is fixed at `1` and the price `p > 0` of the good is the varying
environment, ranging over the strictly-positive ray `Price := {p : Fin 1 → ℝ // 0 < p 0}`. At price
`p` the budget set is `budgetSetAt p 1 = {x ≥ 0 | p ⬝ᵥ x ≤ 1}`, which in one good is the interval
`[0, 1/p]` — it shrinks continuously as the good gets more expensive. The consumer maximizes the
strictly concave, continuous utility `u x = √(x 0)`.

## The mathematics

The constraint correspondence is `Φ p = budgetSetAt p.val 1`, i.e. the upstream
wealth-parameterized budget set with the constant wealth function `fun _ => 1`, restricted to
positive prices. The four Berge inputs are discharged from existing API:

* *Compact-valued.* `isCompact_budgetSetAt_of_pos_prices` gives compactness whenever every price is
  positive — guaranteed on the `Price` subtype.
* *Nonempty-valued.* The origin `0` is always affordable (`p ⬝ᵥ 0 = 0 ≤ 1`).
* *Upper hemicontinuous.* `budgetSetAt_upperHemicontinuousAt` (witness point `0`, compactness from
  the previous bullet) gives upper hemicontinuity of the price-varying budget correspondence,
  pulled back to `Price` by `UpperHemicontinuousAt.comp continuousAt_subtype_val`.
* *Lower hemicontinuous.* `budgetSetAt_lowerHemicontinuousAt_of_cheaperPoint` needs a strictly
  cheaper feasible point; the origin works since `p ⬝ᵥ 0 = 0 < 1`. Pulled back to `Price` the same
  way.

The objective is jointly continuous because it ignores the price coordinate: `fun pr => u pr.2`
factors as `u ∘ Prod.snd`. Feeding all of this into `valueFunction_continuous` and
`argmax_upperHemicontinuous` (the latter needs `T2Space (Fin 1 → ℝ)`, automatic) yields the two
conclusions.

## Main definitions and theorems

* `Price` — the strictly-positive single-good prices `{p : Fin 1 → ℝ // 0 < p 0}`.
* `u : (Fin 1 → ℝ) → ℝ` — the consumer's utility `x ↦ √(x 0)`.
* `Φ : Price → Set (Fin 1 → ℝ)` — the budget correspondence `p ↦ budgetSetAt p 1`.
* `indirectUtility_continuous` — the indirect utility `p ↦ valueFunction u (Φ p)` is continuous.
* `demand_upperHemicontinuous` — the demand correspondence `p ↦ argmax u (Φ p)` is upper
  hemicontinuous.
* `demand_isCompact` — the demand correspondence is compact-valued.
* `budget_eq_Icc` — the budget set is the interval `[0, 1/p]`, as the model description promises.
* `demandBundle` / `demand_eq_singleton` — Walrasian demand in closed form: The unique optimal
  bundle is `x*(p) = 1/p` (full expenditure).
* `indirectUtility_eq` / `indirectUtility_closedForm_continuous` — indirect utility in closed form,
  `v(p) = √(1/p)`, with its continuity read off Berge rather than the formula.
* `u_strictConcaveOn` — the utility is strictly concave on the nonnegative orthant (Berge needs
  only continuity; strict concavity is what makes demand single-valued).
-/

noncomputable section

namespace EconlibExamples.Optimization.BudgetMaximumTheorem

open Econlib.Optimization
open Econlib.Equilibrium

/-- The varying economic environment: Strictly-positive single-good prices. As a subtype of the
metric space `Fin 1 → ℝ` it is automatically a Hausdorff topological space. -/
abbrev Price := {p : Fin 1 → ℝ // 0 < p 0}

/-- Fixed consumer wealth, the same at every price. -/
def wealth : ℝ := 1

/-- The consumer's utility over single-good bundles: `u x = √(x 0)`, strictly concave and
continuous. Only its continuity is used by Berge. -/
def u : (Fin 1 → ℝ) → ℝ := fun x => Real.sqrt (x 0)

/-- The wealth-parameterized budget set with the constant wealth function `fun _ => 1`. Written as
a price-indexed family on the full price space so the upstream budget lemmas (which vary the price)
apply directly; the `Price` subtype enters only through composition with `Subtype.val`. -/
def budgetFamily : (Fin 1 → ℝ) → Set (Fin 1 → ℝ) := fun p => budgetSetAt p wealth

/-- The consumer's budget correspondence on the positive-price subtype. By construction this is
`budgetFamily ∘ Subtype.val`. -/
def Φ : Price → Set (Fin 1 → ℝ) := fun p => budgetFamily p.val

/-- The objective as Berge consumes it: A function of environment and bundle that ignores the
environment. -/
def objective : Price → (Fin 1 → ℝ) → ℝ := fun _ x => u x

/-- The utility is continuous. -/
lemma u_continuous : Continuous u :=
  Real.continuous_sqrt.comp (continuous_apply 0)

/-- The constant wealth function is continuous, the form the budget lemmas require. -/
lemma wealth_fun_continuous : Continuous (fun _ : Fin 1 → ℝ => wealth) :=
  continuous_const

/-- The origin is affordable at every price: `p ⬝ᵥ 0 = 0 ≤ 1`. This serves both as the nonemptiness
witness and as the upper-hemicontinuity witness point. -/
lemma zero_mem_budgetFamily (p : Fin 1 → ℝ) : (0 : Fin 1 → ℝ) ∈ budgetFamily p := by
  refine ⟨fun _ => le_refl 0, ?_⟩
  rw [dotProduct_zero]
  norm_num [wealth]

/-- On the positive-price subtype the budget set is compact, by
`isCompact_budgetSetAt_of_pos_prices`: The single price `p 0` is positive, so the budget set sits
in a closed interval. -/
lemma Φ_isCompact (p : Price) : IsCompact (Φ p) :=
  isCompact_budgetSetAt_of_pos_prices
    (fun l => by rw [Fin.fin_one_eq_zero l]; exact p.property) wealth

/-- The budget correspondence is nonempty-valued: The origin is always affordable. -/
lemma Φ_nonempty (p : Price) : (Φ p).Nonempty :=
  ⟨0, zero_mem_budgetFamily p.val⟩

/-- The budget correspondence is upper hemicontinuous in the price. We invoke the upstream
pointwise lemma `budgetSetAt_upperHemicontinuousAt` (origin as the bounded witness point, pointwise
compactness from `Φ_isCompact`) at each underlying price, then pull it back along the continuous
inclusion `Subtype.val` with `UpperHemicontinuousAt.comp`. -/
lemma Φ_upperHemicontinuous : UpperHemicontinuous Φ := by
  rw [upperHemicontinuous_iff]
  intro p
  -- Upper hemicontinuity of the price-varying family at the underlying price `p.val`.
  have hAt : UpperHemicontinuousAt budgetFamily p.val :=
    budgetSetAt_upperHemicontinuousAt (fun _ => wealth) wealth_fun_continuous 0
      zero_mem_budgetFamily (Φ_isCompact p)
  exact hAt.comp continuousAt_subtype_val

/-- The budget correspondence is lower hemicontinuous in the price. We invoke
`budgetSetAt_lowerHemicontinuousAt_of_cheaperPoint` with the origin as the strictly cheaper
feasible point (`p ⬝ᵥ 0 = 0 < 1 = wealth`), then pull back along `Subtype.val`. -/
lemma Φ_lowerHemicontinuous : LowerHemicontinuous Φ := by
  rw [lowerHemicontinuous_iff]
  intro p
  -- A strictly cheaper feasible bundle: the origin costs `0`, below the wealth `1`.
  have hcheap : ∃ z ∈ nonnegOrthant 1, p.val ⬝ᵥ z < wealth := by
    refine ⟨0, fun _ => le_refl 0, ?_⟩
    rw [dotProduct_zero]
    norm_num [wealth]
  have hAt : LowerHemicontinuousAt budgetFamily p.val :=
    budgetSetAt_lowerHemicontinuousAt_of_cheaperPoint (fun _ => wealth) wealth_fun_continuous hcheap
  exact hAt.comp continuousAt_subtype_val

/-- The objective is jointly continuous: It depends only on the bundle, so it factors through
`Prod.snd`. -/
lemma objective_continuous : Continuous (fun pr : Price × (Fin 1 → ℝ) => objective pr.1 pr.2) :=
  u_continuous.comp continuous_snd

/-! ## Berge Part 1: The Indirect Utility (value Function) Is Continuous in Price -/

/-- **Indirect utility is continuous (Berge Part 1).** As the price of the good moves, the
consumer's maximized utility `p ↦ sup_{x ∈ budget} √(x 0)` varies continuously. This is
`valueFunction_continuous` fed the four budget-correspondence facts and the jointly-continuous
objective. -/
theorem indirectUtility_continuous :
    Continuous (fun p : Price => valueFunction (objective p) (Φ p)) :=
  valueFunction_continuous objective_continuous Φ_upperHemicontinuous Φ_lowerHemicontinuous
    Φ_isCompact Φ_nonempty

/-! ## Berge Part 2: The Demand Correspondence Is Upper Hemicontinuous -/

/-- **Demand is upper hemicontinuous (Berge Part 2).** The set of utility-maximizing bundles
`p ↦ argmax (√(· 0)) (budget)` admits no sudden jumps as the price varies. This is
`argmax_upperHemicontinuous`; the required `T2Space (Fin 1 → ℝ)` is automatic. -/
theorem demand_upperHemicontinuous :
    UpperHemicontinuous (fun p : Price => argmax (objective p) (Φ p)) :=
  argmax_upperHemicontinuous objective_continuous Φ_upperHemicontinuous Φ_lowerHemicontinuous
    Φ_isCompact Φ_nonempty

/-! ## Berge Part 3: The Demand Correspondence Is Compact-Valued -/

/-- **Demand is compact-valued (Berge Part 3).** At each price the set of maximizers is compact, by
`argmax_isCompact`. -/
theorem demand_isCompact (p : Price) : IsCompact (argmax (objective p) (Φ p)) :=
  argmax_isCompact objective_continuous Φ_isCompact p

/-! ## Closed forms: Budget interval, demand, and indirect utility

Berge delivers continuity and upper hemicontinuity abstractly. On this one-good instance every
object is also computable in closed form, which is what makes the abstract conclusions concrete:
The budget set is the interval `[0, 1/p]`, demand is the single bundle spending all wealth
(`x*(p) = 1/p`), and the indirect utility is `v(p) = √(1/p)`. In particular the continuity that
Berge delivers lands on a function one can read (`indirectUtility_closedForm_continuous`), and the
upper hemicontinuity of demand is the upper hemicontinuity of a (singleton-valued) demand
function. -/

/-- With one good the dot product collapses to the single coordinate: `p ⬝ᵥ x = p 0 · x 0`. -/
lemma dotProduct_fin_one (p x : Fin 1 → ℝ) : p ⬝ᵥ x = p 0 * x 0 := by
  simp [dotProduct]

/-- **The budget set is the interval `[0, 1/p]`**, read through the single coordinate: Affordable
nonnegative bundles are exactly those consuming between `0` and `1/p`. -/
lemma budget_eq_Icc (p : Price) : Φ p = {x | x 0 ∈ Set.Icc 0 (1 / p.val 0)} := by
  have hp : 0 < p.val 0 := p.property
  ext x
  simp only [Φ, budgetFamily, mem_budgetSetAt, Set.mem_setOf_eq, Set.mem_Icc, wealth]
  constructor
  · rintro ⟨hx_nonneg, hx_afford⟩
    refine ⟨hx_nonneg 0, ?_⟩
    rw [dotProduct_fin_one, mul_comm] at hx_afford
    exact (le_div_iff₀ hp).mpr hx_afford
  · rintro ⟨hx0, hx1⟩
    refine ⟨fun l => by rw [Fin.fin_one_eq_zero l]; exact hx0, ?_⟩
    rw [dotProduct_fin_one, mul_comm]
    exact (le_div_iff₀ hp).mp hx1

/-- The bundle spending all wealth at price `p`: The **Walrasian demand** `x*(p) = 1/p`. -/
def demandBundle (p : Price) : Fin 1 → ℝ := fun _ => 1 / p.val 0

/-- The demand bundle is affordable: It sits at the top of the budget interval. -/
lemma demandBundle_mem (p : Price) : demandBundle p ∈ Φ p := by
  have hp : 0 < p.val 0 := p.property
  rw [budget_eq_Icc]
  exact ⟨le_of_lt (one_div_pos.mpr hp), le_refl _⟩

/-- The utility `u x = √(x 0)` is **strictly concave** on the nonnegative orthant, backing the
adjective in the model description: `√` is strictly concave on `[0, ∞)`
(`Real.strictConcaveOn_sqrt`) and the coordinate map is linear and injective on one-good bundles.
Berge consumes only continuity; strict concavity is what makes demand single-valued
(`demand_eq_singleton`). -/
lemma u_strictConcaveOn : StrictConcaveOn ℝ {x : Fin 1 → ℝ | 0 ≤ x 0} u := by
  constructor
  · -- The nonnegative half-space is convex.
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at *
    have : (a • x + b • y) 0 = a * x 0 + b * y 0 := by simp
    rw [this]
    positivity
  · intro x hx y hy hxy a b ha hb hab
    have hne : x 0 ≠ y 0 := fun h =>
      hxy (funext fun i => by rw [Fin.fin_one_eq_zero i]; exact h)
    have key := Real.strictConcaveOn_sqrt.2 hx hy hne ha hb hab
    simp only [u]
    have : (a • x + b • y) 0 = a * x 0 + b * y 0 := by simp
    rw [this]
    simpa [smul_eq_mul] using key

/-- The objective is strictly concave on the budget set, by restricting `u_strictConcaveOn` (strict
concavity on the whole nonnegative orthant) along `Φ p ⊆ {x | 0 ≤ x 0}` and `Φ p` convex. This is
the input `argmax_eq_singleton` consumes to make demand single-valued. -/
lemma objective_strictConcaveOn (p : Price) :
    StrictConcaveOn ℝ (Φ p) (objective p) :=
  u_strictConcaveOn.subset (fun _ hx => (mem_budgetSetAt.mp hx).1 0) (budgetSetAt_convex _ _)

/-- The demand bundle maximizes utility over the budget set: any affordable bundle consumes at most
`1/p`, and `√` is monotone. -/
lemma demandBundle_isMaxOn (p : Price) : IsMaxOn (objective p) (Φ p) (demandBundle p) := by
  intro y hy
  rw [budget_eq_Icc] at hy
  exact Real.sqrt_le_sqrt hy.2

/-- **Demand in closed form.** At every price the consumer's optimal bundle is *unique* and spends
the whole wealth: `argmax = {1/p}`. Single-valuedness is exactly the library lemma
`argmax_eq_singleton`: strict concavity of the objective (`objective_strictConcaveOn`) makes the
argmax a subsingleton, and the exhibited maximizer `demandBundle_isMaxOn` makes it nonempty. -/
theorem demand_eq_singleton (p : Price) :
    argmax (objective p) (Φ p) = {demandBundle p} :=
  argmax_eq_singleton (objective_strictConcaveOn p) (demandBundle_mem p) (demandBundle_isMaxOn p)

/-- **Indirect utility in closed form**: `v(p) = √(1/p)`, the utility of the unique optimal bundle.
Read off the library lemma `valueFunction_eq_of_mem_isMaxOn` at the attained maximizer
`demandBundle p`, then evaluate `objective p (demandBundle p) = √(1/p)`. -/
theorem indirectUtility_eq (p : Price) :
    valueFunction (objective p) (Φ p) = Real.sqrt (1 / p.val 0) := by
  rw [valueFunction_eq_of_mem_isMaxOn (demandBundle_mem p) (demandBundle_isMaxOn p)]
  simp [objective, u, demandBundle]

/-- **The Berge conclusion, in closed form.** The indirect utility `p ↦ √(1/p)` is continuous on
the positive-price ray — obtained by rewriting `indirectUtility_continuous` along
`indirectUtility_eq`, i.e. delivered by the maximum theorem rather than by differentiating the
formula. -/
theorem indirectUtility_closedForm_continuous :
    Continuous (fun p : Price => Real.sqrt (1 / p.val 0)) :=
  funext indirectUtility_eq ▸ indirectUtility_continuous

end EconlibExamples.Optimization.BudgetMaximumTheorem
