/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib
import Mathlib

/-!
# Additively Separable Utility: A Two-Good Consumer Problem Solved

An additively separable utility aggregates one concave per-good felicity into a total,
`U(c) = Σᵢ βᵢ uᵢ(cᵢ)`, with positive Pareto weights `βᵢ`. This file solves a concrete consumer
problem for such a utility: Maximize `U` over a budget set, exhibit the optimal bundle, prove it is
the unique maximizer, and verify the first-order conditions it satisfies. The economic payoff of
separability is on display throughout: at the common marginal value of wealth `μ* = 1`, the FOC
system decouples into independent scalar equations `βᵢ uᵢ'(cᵢ) = μ*`, one per good, each with a
unique positive solution — reconstructing `c*` coordinate by coordinate.

## The model

* Goods `Fin 2`, both with log felicity `u(x) = log x` on `(0, ∞)` (the canonical Inada witness
  `Econlib.Preferences.InadaUtility.log`), and Pareto weights `β = (1, 2)`, so
  `U(c) = log c₀ + 2 · log c₁`.
* Prices normalized to `(1, 1)` and wealth `m = 3`, so the budget set is
  `{c | c ≫ 0 ∧ c₀ + c₁ ≤ 3}`.

The solution is `c* = (1, 2)` with marginal value of wealth `μ* = 1`: The FOCs `1/c₀ = μ` and
`2/c₁ = μ` plus the budget `c₀ + c₁ = 3` force `3/μ = 3`. Log utility delivers the classical
constant-expenditure-share rule: Good `i` receives the fraction `βᵢ / Σⱼ βⱼ` of wealth — here
`(1/3, 2/3)` of `m = 3`, i.e. `c* = (1, 2)` (`expenditure_shares`).

## The mathematics

Optimality is not re-derived here from a log-specific bound; it is read off the upstream separable
optimization API. The FOC system is verified at `c*` with the common multiplier `μ* = 1` across
both goods (`foc_at_optimum`), and `SeparableUtility.isMaxOn_aggregate_budget_of_foc` certifies that
a positive bundle exhausting the budget with all marginals equalized to a nonnegative multiplier is
a maximizer (`cstar_isMaxOn`). The supporting certificate — the concave tangent-line bound
`uᵢ(cᵢ) ≤ uᵢ(c*ᵢ) + uᵢ'(c*ᵢ)(cᵢ − c*ᵢ)` — lives once, upstream, as `InadaUtility.u_le_tangent`,
specializing to `log z ≤ z − 1` for the logarithm. Uniqueness comes from strict concavity of the
aggregate on the positive orthant (`SeparableUtility.aggregate_strictConcaveOn`), via
`SeparableUtility.eq_of_isMaxOn_aggregate_budget` (`argmax_eq`); strict suboptimality of every other
bundle (`aggregate_lt_cstar`) is then a corollary, not the engine. Separability reduces the FOC
system to per-good scalar equations, each with exactly one positive solution (`foc_unique`) —
necessarily `c* i` (`foc_solution_eq_cstar`).

## Main definitions and theorems

* `U` — the two-good separable utility with log felicities and weights `(1, 2)`.
* `budgetSet`, `cstar` — the budget set (the library's `SeparableUtility.budget 3` at prices
  `(1,1)`, wealth `3`) and the optimum `(1, 2)`.
* `aggregate_eq` / `aggregate_strictConcave` — `U(c) = log c₀ + 2 log c₁`, strictly concave on the
  positive orthant.
* `foc_at_optimum` — the FOC system `βᵢ uᵢ'(c*ᵢ) = μ*` holds at `c*` with common multiplier
  `μ* = 1` for both goods.
* `foc_unique` / `foc_solution_eq_cstar` — given `μ* = 1`, each good's FOC has a unique positive
  solution, and it is `c* i`: Separability decouples the system coordinate-wise.
* `cstar_isMaxOn` / `argmax_eq` — `c*` maximizes `U` on the budget set (derived from the FOC system
  via `isMaxOn_aggregate_budget_of_foc`), and it is the only maximizer
  (`eq_of_isMaxOn_aggregate_budget`): `argmax U budgetSet = {c*}`.
* `aggregate_lt_cstar` — every feasible bundle other than `c*` gives strictly lower utility (a
  corollary of optimality + uniqueness).
* `expenditure_shares` — `c*ᵢ = (βᵢ / Σⱼ βⱼ) · m`: The constant-expenditure-share rule of log
  utility.
* `closedBudgetSet`, `Uext` — the *closed* nonnegative budget set (boundary included) and the
  `EReal`-valued utility that is `-∞` on the boundary and the real aggregate on the interior.
  These make the docstring's "no optimum lost by excluding the boundary" a theorem: `Real.log 0 = 0`
  is a junk value, so the claim requires the `-∞`-on-boundary extension.
* `cstar_isMaxOn_closed` / `argmax_closed_eq` — `c*` maximizes the extended utility `Uext` over the
  closed budget, and is the only maximizer (the boundary scores `-∞`, every interior tie is
  determined by the interior uniqueness `argmax_eq`).
* `closed_optimum_eq_interior` — the closed extended problem and the open real problem have the same
  optimizer set `{c*}`: The formal content of "no optimum is lost by excluding the boundary."
-/

noncomputable section

namespace EconlibExamples.Preferences.SeparableOptimum

open Econlib.Preferences

/-! ## A two-good separable consumer with log felicities -/

/-- The two-good separable utility: Both goods have log felicity, with Pareto weights `(1, 2)`. -/
def U : SeparableUtility (Fin 2) where
  component := fun _ => InadaUtility.log
  weight := ![1, 2]

/-- Both Pareto weights are strictly positive. -/
theorem weights_pos : ∀ i, 0 < U.weight i := by
  intro i
  fin_cases i <;> simp [U]

/-! ## The aggregate and its curvature -/

/-- The aggregate utility is `U(c) = log c₀ + 2 · log c₁`. -/
theorem aggregate_eq (c : Fin 2 → ℝ) :
    U.aggregate c = Real.log (c 0) + 2 * Real.log (c 1) := by
  -- Unfold the two-term sum and read off the weights and the log felicity.
  simp only [SeparableUtility.aggregate, Fin.sum_univ_two, U, InadaUtility.log_u]
  norm_num

/-- **Strict concavity of the aggregate** on the positive orthant: The consumer's objective is
strictly concave, so the budget problem below can have at most one optimum. -/
theorem aggregate_strictConcave :
    StrictConcaveOn ℝ (SeparableUtility.positiveOrthant (Fin 2)) U.aggregate :=
  U.aggregate_strictConcaveOn weights_pos

/-! ## The consumer problem -/

/-- The budget set at prices `(1, 1)` and wealth `m = 3`: Interior bundles costing at most `3`.
Interiority is the right domain for log felicities, because the utility is `-∞` on the
boundary, so no optimum is lost by excluding it. That boundary-exclusion claim is not visible in
the plain real aggregate `U.aggregate`, since in Lean `Real.log 0 = 0` is a junk value rather than
`-∞` — over the closed nonnegative budget, the boundary bundle `(0, 3)` would then beat `c*`. The
claim is made a theorem below via the `EReal`-valued extension `Uext` (which is `-∞` on the
boundary): see `closed_optimum_eq_interior`, proving the closed extended problem and this open real
problem share the optimizer set `{c*}`. This is exactly the library's interior unit-price budget set
`SeparableUtility.budget`, so the upstream FOC-sufficiency and uniqueness API applies directly. -/
abbrev budgetSet : Set (Fin 2 → ℝ) := U.budget 3

/-- Membership in the budget set unfolds to interiority plus the spending constraint `c₀ + c₁ ≤ 3`
(the two-good sum). -/
lemma mem_budgetSet {c : Fin 2 → ℝ} :
    c ∈ budgetSet ↔ (∀ i, 0 < c i) ∧ c 0 + c 1 ≤ 3 := by
  simp only [budgetSet, SeparableUtility.mem_budget, Fin.sum_univ_two]

/-- The optimal bundle `c* = (1, 2)`: Each good receives its expenditure share `βᵢ/Σβ` of wealth. -/
def cstar : Fin 2 → ℝ := ![1, 2]

/-- Both coordinates of the optimum are strictly positive: The optimum is interior. -/
lemma cstar_pos : ∀ i, 0 < cstar i := by
  intro i
  fin_cases i <;> norm_num [cstar]

/-- The optimum is feasible. -/
lemma cstar_mem_budgetSet : cstar ∈ budgetSet :=
  mem_budgetSet.mpr ⟨cstar_pos, by norm_num [cstar]⟩

/-- The optimum exhausts the budget: `1 + 2 = 3` — the spending constraint binds. (That a monotone
utility forces the budget to bind is the textbook Walras's-law argument; here we only record the
arithmetic `∑ cstar = 3`, which is what the FOC-sufficiency theorem consumes.) -/
lemma cstar_budget_binding : ∑ i, cstar i = 3 := by
  simp only [Fin.sum_univ_two]
  norm_num [cstar]

/-- Utility at the optimum: `U(c*) = log 1 + 2 · log 2 = 2 · log 2`. -/
lemma aggregate_cstar : U.aggregate cstar = 2 * Real.log 2 := by
  rw [aggregate_eq]
  norm_num [cstar]

/-! ## The first-order-condition system

Separability turns the joint FOC into per-good scalar equations sharing the single multiplier
`μ* = 1`: The marginal utility of expenditure is equalized across goods at the optimum. The upstream
FOC-sufficiency theorem then certifies `c*` as a maximizer directly from this system — no
log-specific bound required. -/

/-- **The FOC system holds at the optimum with a common multiplier**: `βᵢ uᵢ'(c*ᵢ) = μ* = 1` for
both goods — `1 · (1/1) = 1` and `2 · (1/2) = 1`. Equalized marginal utility per unit of
expenditure is exactly the economic content of an interior consumer optimum. -/
theorem foc_at_optimum (i : Fin 2) : U.marginal i cstar = 1 := by
  fin_cases i <;> norm_num [SeparableUtility.marginal, U, cstar]

/-- **Each good's FOC has a unique positive solution** at the equilibrium marginal value `μ* = 1`.
This is where separability pays: The two-good system decouples into independent scalar equations,
each solvable on its own. -/
theorem foc_unique (i : Fin 2) :
    ∃! c : ℝ, c ∈ Set.Ioi (0 : ℝ) ∧ (U.weight i : ℝ) * (U.component i).u' c = 1 :=
  U.unique_marginal_solution i 1 (weights_pos i) one_pos

/-- **The FOC system recovers the optimum**: Any positive solution of good `i`'s FOC at `μ* = 1` is
the optimal coordinate `c* i`. Solving the decoupled FOCs coordinate-wise reconstructs the
maximizer of the joint budget problem. -/
theorem foc_solution_eq_cstar (i : Fin 2) {c : ℝ} (hc_pos : c ∈ Set.Ioi (0 : ℝ))
    (hc_foc : (U.weight i : ℝ) * (U.component i).u' c = 1) : c = cstar i :=
  (foc_unique i).unique ⟨hc_pos, hc_foc⟩ ⟨cstar_pos i, foc_at_optimum i⟩

/-! ## The optimum, derived from the FOC system

This is the payoff of the upstream separable-optimization API: rather than re-proving optimality by
hand from a log-specific tangent-line bound, `c*` is certified as the maximizer directly from the
FOC system `βᵢ uᵢ'(c*ᵢ) = μ* = 1` plus the binding budget, via
`SeparableUtility.isMaxOn_aggregate_budget_of_foc`. Uniqueness comes from strict concavity of the
aggregate, via `SeparableUtility.eq_of_isMaxOn_aggregate_budget`. -/

/-- **The optimum solves the consumer problem**: `c*` is feasible (`cstar_mem_budgetSet`) and
`IsMaxOn U budgetSet c*`, i.e. it maximizes `U` over the budget set. Derived
from the FOC system with common multiplier `μ* = 1` and the binding budget `∑ c*ᵢ = 3` through the
upstream sufficiency theorem — the tangent-line certificate lives once, upstream, in
`InadaUtility.u_le_tangent`, instead of being re-derived here for the logarithm. -/
theorem cstar_isMaxOn : IsMaxOn U.aggregate budgetSet cstar :=
  U.isMaxOn_aggregate_budget_of_foc (μ := 1) zero_le_one cstar_pos cstar_budget_binding
    foc_at_optimum

/-- **The unique interior optimum.** The argmax of the consumer problem is exactly `{c*}`: An
optimum exists (`cstar_isMaxOn`), and strict concavity of the aggregate makes it the only one. This
is the headline the file's title promises. -/
theorem argmax_eq : Econlib.Optimization.argmax U.aggregate budgetSet = {cstar} := by
  ext c
  simp only [Econlib.Optimization.argmax, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hmem, hmax⟩
    -- Two maximizers of a strictly concave aggregate over the convex budget set must coincide.
    exact U.eq_of_isMaxOn_aggregate_budget weights_pos hmax cstar_isMaxOn hmem cstar_mem_budgetSet
  · rintro rfl
    exact ⟨cstar_mem_budgetSet, cstar_isMaxOn⟩

/-- **Strict suboptimality of every other feasible bundle**, now a corollary of the general
optimum-plus-uniqueness, not the engine: `c*` is the maximizer and the unique one, so any other
feasible bundle scores strictly lower. (The classic log tangent-line bound `log z ≤ z - 1` is the
special-case proof; here it is subsumed by the upstream concave tangent certificate.) -/
theorem aggregate_lt_cstar {c : Fin 2 → ℝ} (hc : c ∈ budgetSet) (hne : c ≠ cstar) :
    U.aggregate c < U.aggregate cstar := by
  -- `c` is feasible but not the unique maximizer `c*`, so it is not a maximizer; with `c*` an upper
  -- bound this gives the strict inequality.
  rcases lt_or_eq_of_le (isMaxOn_iff.mp cstar_isMaxOn c hc) with hlt | heq
  · exact hlt
  · -- Equality of utilities would make `c` a maximizer too, forcing `c = c*` by uniqueness.
    refine absurd ?_ hne
    have hc_max : IsMaxOn U.aggregate budgetSet c := by
      rw [isMaxOn_iff]
      intro d hd
      exact (isMaxOn_iff.mp cstar_isMaxOn d hd).trans heq.ge
    exact U.eq_of_isMaxOn_aggregate_budget weights_pos hc_max cstar_isMaxOn hc cstar_mem_budgetSet

/-! ## Expenditure shares -/

/-- **The expenditure-share identity.** For these log felicities, each good's optimal consumption is
a fixed fraction of wealth equal to its normalized Pareto weight: `c*ᵢ = (βᵢ / Σⱼ βⱼ) · m`. Here the
shares are `(1/3, 2/3)` of `m = 3`. (This is the concrete instance of the classical
constant-expenditure-share rule of Cobb–Douglas / log utility.) -/
theorem expenditure_shares (i : Fin 2) :
    cstar i = (U.weight i : ℝ) / (∑ j, (U.weight j : ℝ)) * 3 := by
  fin_cases i <;> norm_num [U, cstar, Fin.sum_univ_two]

/-! ## Justifying boundary exclusion with an extended utility

The `budgetSet` above is open (strictly positive coordinates), and its docstring claims that the
boundary is dropped "without losing any optimum." That claim is an economic fact — log utility is
`-∞` at a zero coordinate — but it is not visible in the plain real aggregate `U.aggregate`,
because in Lean `Real.log 0 = 0` is a junk value rather than `-∞`. With that junk value the boundary
bundle `(0, 3)` scores `log 0 + 2 log 3 = 2 log 3 > 2 log 2 = U.aggregate c*`, so over the closed
nonnegative budget the interior optimum `c*` would not even be a maximizer of `U.aggregate`.

To make "no optimum lost by excluding the boundary" a theorem rather than a slogan, we extend the
objective to an `EReal`-valued utility `Uext` that equals `-∞ (= ⊥)` off the positive orthant
(in particular on the boundary of the closed budget) and equals the real aggregate on the interior.
We then prove that the closed-budget maximizer of `Uext` is exactly the interior maximizer `c*`
(`cstar_isMaxOn_closed`, `argmax_closed_eq`), and that the closed extended problem and the open real
problem have the same optimizer set (`closed_optimum_eq_interior`). That equality is the formal
content of the boundary-exclusion claim.

Because the library `Econlib.Optimization.argmax` fixes a real codomain, the `Uext`-maximizer set is
written out as `{c ∈ closedBudgetSet | IsMaxOn Uext closedBudgetSet c}`, which is exactly the body
that `Econlib.Optimization.argmax` unfolds to (`Econlib.Optimization.argmax f S = {x ∈ S | IsMaxOn f
S x}`), specialized to the `EReal`-valued objective. -/

/-- The **closed** nonnegative budget set at prices `(1, 1)` and wealth `3`: bundles with all
coordinates `≥ 0` (boundary included) costing at most `3`. This is the interior `budgetSet` together
with its boundary. -/
def closedBudgetSet : Set (Fin 2 → ℝ) := {c | (∀ i, 0 ≤ c i) ∧ c 0 + c 1 ≤ 3}

/-- Membership in the closed budget set: nonnegativity in every coordinate plus the spending
constraint `c₀ + c₁ ≤ 3`. -/
lemma mem_closedBudgetSet {c : Fin 2 → ℝ} :
    c ∈ closedBudgetSet ↔ (∀ i, 0 ≤ c i) ∧ c 0 + c 1 ≤ 3 := Iff.rfl

/-- The interior budget set is contained in the closed one: strict positivity implies
nonnegativity, the spending constraint is identical. -/
lemma budgetSet_subset_closedBudgetSet : budgetSet ⊆ closedBudgetSet := by
  intro c hc
  obtain ⟨hpos, hsum⟩ := mem_budgetSet.mp hc
  exact ⟨fun i => (hpos i).le, hsum⟩

/-- The optimum is feasible for the closed problem (it is feasible for the interior one). -/
lemma cstar_mem_closedBudgetSet : cstar ∈ closedBudgetSet :=
  budgetSet_subset_closedBudgetSet cstar_mem_budgetSet

/-- The **extended utility** on the closed budget: the real aggregate cast to `EReal` on the
strictly positive orthant, and `⊥ = -∞` whenever some coordinate is `≤ 0` — in particular on the
boundary of `closedBudgetSet`. Keeping the objective `EReal`-valued lets the boundary score `-∞`,
unlike the real aggregate where `Real.log 0 = 0` silently. -/
def Uext (c : Fin 2 → ℝ) : EReal :=
  if (∀ i, 0 < c i) then (U.aggregate c : EReal) else ⊥

/-- On the positive orthant `Uext` is the real aggregate, cast to `EReal`. -/
lemma Uext_of_pos {c : Fin 2 → ℝ} (hc : ∀ i, 0 < c i) :
    Uext c = (U.aggregate c : EReal) := if_pos hc

/-- Off the positive orthant (a fortiori on the boundary) `Uext` is `-∞`. -/
lemma Uext_eq_bot_of_boundary {c : Fin 2 → ℝ} (hc : ¬ (∀ i, 0 < c i)) :
    Uext c = ⊥ := if_neg hc

/-- `Uext` at the optimum is the real utility `U.aggregate c*`, since `c*` is interior. -/
lemma Uext_cstar : Uext cstar = (U.aggregate cstar : EReal) := Uext_of_pos cstar_pos

/-- **The closed extended problem is maximized at the interior optimum.** For any closed-feasible
bundle, either it is interior — then `Uext` is the real aggregate, bounded by `U.aggregate c*` via
the interior optimality `cstar_isMaxOn` — or it touches the boundary, where `Uext = ⊥ ≤ Uext c*`. So
`c*` maximizes `Uext` over the closed budget. -/
theorem cstar_isMaxOn_closed : IsMaxOn Uext closedBudgetSet cstar := by
  rw [isMaxOn_iff]
  intro c hc
  by_cases hpos : ∀ i, 0 < c i
  · -- Interior bundle: `Uext` is the cast real aggregate, and `c` is interior-feasible.
    have hc_mem : c ∈ budgetSet := mem_budgetSet.mpr ⟨hpos, (mem_closedBudgetSet.mp hc).2⟩
    rw [Uext_of_pos hpos, Uext_cstar, EReal.coe_le_coe_iff]
    exact isMaxOn_iff.mp cstar_isMaxOn c hc_mem
  · -- Boundary bundle: `Uext c = ⊥` is below everything.
    rw [Uext_eq_bot_of_boundary hpos]
    exact bot_le

/-- **The closed extended optimum is unique and equals `c*`.** The maximizer set of `Uext` over the
closed budget is exactly `{c*}`. Any maximizer `c'` attains
`Uext c' = Uext c* = U.aggregate c* ≠ ⊥`,
so `c'` cannot be on the boundary (where `Uext = ⊥`); hence `c'` is interior, lies in `budgetSet`,
and has `U.aggregate c' = U.aggregate c*`, making it an interior maximizer — so `c' = c*` by the
interior uniqueness `argmax_eq`. -/
theorem argmax_closed_eq :
    {c | c ∈ closedBudgetSet ∧ IsMaxOn Uext closedBudgetSet c} = {cstar} := by
  ext c'
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hc'_mem, hc'_max⟩
    -- The maximizer matches `c*` in `Uext`, which is a finite (`≠ ⊥`) value, forcing interiority.
    have hval : Uext c' = (U.aggregate cstar : EReal) := by
      refine le_antisymm ?_ ?_
      · rw [← Uext_cstar]; exact isMaxOn_iff.mp cstar_isMaxOn_closed c' hc'_mem
      · rw [← Uext_cstar]; exact isMaxOn_iff.mp hc'_max cstar cstar_mem_closedBudgetSet
    have hpos' : ∀ i, 0 < c' i := by
      by_contra hpos
      rw [Uext_eq_bot_of_boundary hpos] at hval
      exact (EReal.coe_ne_bot _) hval.symm
    -- Interior maximizer: transport equality back to the real aggregate and reuse uniqueness.
    have hc'_budget : c' ∈ budgetSet :=
      mem_budgetSet.mpr ⟨hpos', (mem_closedBudgetSet.mp hc'_mem).2⟩
    have hagg : U.aggregate c' = U.aggregate cstar := by
      have : (U.aggregate c' : EReal) = (U.aggregate cstar : EReal) := by
        rw [← Uext_of_pos hpos']; exact hval
      exact EReal.coe_eq_coe_iff.mp this
    -- `c'` ties the optimum, so it is itself an interior maximizer; uniqueness forces `c' = c*`.
    have hc'_argmax : c' ∈ Econlib.Optimization.argmax U.aggregate budgetSet := by
      refine ⟨hc'_budget, ?_⟩
      rw [isMaxOn_iff]
      intro d hd
      rw [hagg]
      exact isMaxOn_iff.mp cstar_isMaxOn d hd
    rw [argmax_eq] at hc'_argmax
    exact hc'_argmax
  · rintro rfl
    exact ⟨cstar_mem_closedBudgetSet, cstar_isMaxOn_closed⟩

/-- **No optimum is lost by excluding the boundary.** The closed `EReal`-extended problem and the
open real problem have the same optimizer set, namely `{c*}`. This is the formal content of the
`budgetSet` docstring's claim: extending the objective to `-∞` on the boundary (`Uext`) and then
solving over the closed budget recovers precisely the interior optimum, so dropping the boundary
costs nothing. The maximizer set on the left is written out as `Econlib.Optimization.argmax` unfolds
(`{x ∈ S | IsMaxOn f S x}`), specialized to the `EReal`-valued `Uext` since the library `argmax`
fixes a real codomain. -/
theorem closed_optimum_eq_interior :
    {c | c ∈ closedBudgetSet ∧ IsMaxOn Uext closedBudgetSet c}
      = Econlib.Optimization.argmax U.aggregate budgetSet := by
  rw [argmax_closed_eq, argmax_eq]

end EconlibExamples.Preferences.SeparableOptimum
