/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.Basic
public import Econlib.Preferences.Utility.Inada

/-!
# N-good Separable Utility and Two-Good Specialization

This file provides a product-domain utility interface for separable preferences. Unlike the
one-dimensional single-peaked and single-crossing APIs, the outcome space here is an indexed bundle
`ι → ℝ`; the finite index type is kept abstract until the two-good specialization.

## Main definitions

* `SeparableUtility` — N-good separable utility with `NNReal` weights
* `SeparableUtility.componentObjective` — the per-good objective `gᵢ(t) = βᵢ uᵢ(t)`
* `SeparableUtility.budget` — the interior unit-price budget set at wealth `m`
* `Good` — `nondurable | durable` for the two-good case
* `TwoGoodUtility` — specialization to two goods

## Main statements

* `SeparableUtility.isMaxOn_aggregate_pi_iff` / `argmax_aggregate_pi` — **separable
  decomposition**: Over a product feasible set, a bundle is jointly optimal iff it is
  coordinatewise optimal.
* `SeparableUtility.isMaxOn_aggregate_budget_of_foc` — **first-order sufficiency under a binding
  budget**: A positive bundle exhausting the budget with all marginals equalized to a common
  `μ ≥ 0` maximizes the aggregate.
* `SeparableUtility.eq_of_isMaxOn_aggregate_budget` — uniqueness of the budget optimum under strict
  component concavity.

## Notes

* `NNReal` weights enforce non-negativity by construction.
* `[Fintype ι]` keeps the index abstract; the two-good case uses `Good` rather than `Fin 2`.
* This is a cardinal utility module: Inada components, marginal utilities, and strict concavity are
  real-analytic statements. Ordinal product-domain results should be phrased using `PreferenceRel`
  plus predicates from `Preferences.Geometry`.
-/

@[expose] public section

namespace Econlib.Preferences

open Set BigOperators NNReal

/-! ## Additively separable real utility -/

/-- Additive separability of a real utility on a finite product domain. -/
structure AdditivelySeparableUtility (ι : Type*) [Fintype ι] where
  /-- Component utility for each coordinate. -/
  component : ι → ℝ → ℝ
  /-- Real-valued weight on each component. -/
  weight : ι → ℝ

namespace AdditivelySeparableUtility

variable {ι : Type*} [Fintype ι] (U : AdditivelySeparableUtility ι)

/-- Aggregate utility on product bundles. -/
noncomputable def aggregate (x : ι → ℝ) : ℝ :=
  ∑ i, U.weight i * U.component i (x i)

end AdditivelySeparableUtility

/-! ## N-good Separable Utility -/

/-- An N-good separable utility: One Inada utility per good, weighted by non-negative `NNReal`
Pareto weights. -/
structure SeparableUtility (ι : Type*) [Fintype ι] where
  /-- One Inada utility per good. -/
  component : ι → InadaUtility
  /-- Non-negative Pareto weight per good. -/
  weight : ι → NNReal

namespace SeparableUtility

variable {ι : Type*} [Fintype ι]
  (U : SeparableUtility ι)

/-- The aggregate utility: `U(c) = Σᵢ βᵢ · uᵢ(cᵢ)`. -/
noncomputable def aggregate (c : ι → ℝ) : ℝ :=
  ∑ i, (U.weight i : ℝ) * (U.component i).u (c i)

/-- The marginal utility of good `i`: `∂U/∂cᵢ(c) = βᵢ · u'ᵢ(cᵢ)`. -/
noncomputable def marginal (i : ι) (c : ι → ℝ) : ℝ :=
  (U.weight i : ℝ) * (U.component i).u' (c i)

/-- The positive orthant: All components strictly positive. -/
def positiveOrthant (ι : Type*) [Fintype ι] : Set (ι → ℝ) :=
  {c | ∀ i, 0 < c i}

/-! ### Component properties -/

/-- Weighted component `βᵢ · uᵢ` is concave on `(0, ∞)`. -/
lemma component_concaveOn (i : ι) :
    ConcaveOn ℝ (Ioi (0 : ℝ))
      (fun c => (U.weight i : ℝ) * (U.component i).u c) :=
  (U.component i).concaveOn.smul (U.weight i).coe_nonneg

/-- Weighted component `βᵢ · uᵢ` is strictly concave when `βᵢ > 0`. -/
lemma component_strictConcaveOn (i : ι)
    (hβ : 0 < U.weight i) :
    StrictConcaveOn ℝ (Ioi (0 : ℝ))
      (fun c => (U.weight i : ℝ) * (U.component i).u c) := by
  have hsc := (U.component i).strictConcaveOn
  have hβ_pos : (0 : ℝ) < U.weight i := NNReal.coe_pos.mpr hβ
  refine ⟨convex_Ioi 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have := hsc.2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at this
  calc a * ((U.weight i : ℝ) * (U.component i).u x) +
        b * ((U.weight i : ℝ) * (U.component i).u y)
      = (U.weight i : ℝ) *
          (a * (U.component i).u x +
            b * (U.component i).u y) := by ring
    _ < (U.weight i : ℝ) *
          (U.component i).u (a * x + b * y) :=
        mul_lt_mul_of_pos_left this hβ_pos

/-! ### Aggregate properties -/

/-- The positive orthant is convex. -/
lemma positiveOrthant_convex :
    Convex ℝ (positiveOrthant ι) := by
  intro c hc d hd a b ha hb hab
  simp only [positiveOrthant, mem_setOf_eq] at *
  intro i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hci := hc i; have hdi := hd i
  have h2 : 0 ≤ b * d i := mul_nonneg hb hdi.le
  by_cases ha0 : a = 0
  · subst ha0
    simp only [zero_add] at hab
    subst hab
    linarith
  · linarith [mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hci]

/-- **Aggregate strict concavity on the positive orthant.**

Each `cᵢ ↦ βᵢ uᵢ(cᵢ)` is strictly concave on `(0,∞)`, and the sum is strictly concave on the
positive orthant. -/
theorem aggregate_strictConcaveOn
    (hβ : ∀ i, 0 < U.weight i) :
    StrictConcaveOn ℝ (positiveOrthant ι) U.aggregate := by
  refine ⟨positiveOrthant_convex, fun c hc d hd hcd a b ha hb hab => ?_⟩
  simp only [aggregate, smul_eq_mul]
  suffices h : ∑ i, (U.weight i : ℝ) *
      (a * (U.component i).u (c i) +
        b * (U.component i).u (d i)) <
    ∑ i, (U.weight i : ℝ) *
      (U.component i).u ((a • c + b • d) i) by
    calc a * ∑ i, _ + b * ∑ i, _
        = ∑ i, (U.weight i : ℝ) *
            (a * (U.component i).u (c i) +
              b * (U.component i).u (d i)) := by
          rw [Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          congr 1; ext i; ring
      _ < _ := h
  have ⟨j, hj⟩ : ∃ j, c j ≠ d j := Function.ne_iff.mp hcd
  apply Finset.sum_lt_sum
  · intro i _
    have hci : 0 < c i := hc i
    have hdi : 0 < d i := hd i
    have hsc := (U.component i).concaveOn
    have hineq := hsc.2 (Set.mem_Ioi.mpr hci)
      (Set.mem_Ioi.mpr hdi) ha.le hb.le hab
    simp only [smul_eq_mul] at hineq
    exact mul_le_mul_of_nonneg_left hineq
      (U.weight i).coe_nonneg
  · exact ⟨j, Finset.mem_univ j, by
      have hcj : 0 < c j := hc j
      have hdj : 0 < d j := hd j
      have hsc := (U.component j).strictConcaveOn
      have hineq := hsc.2 (Set.mem_Ioi.mpr hcj)
        (Set.mem_Ioi.mpr hdj) hj ha hb hab
      simp only [smul_eq_mul] at hineq
      exact mul_lt_mul_of_pos_left hineq
        (NNReal.coe_pos.mpr (hβ j))⟩

/-! ### Marginal solution -/

/-- **Unique marginal solution.** For weight `βᵢ > 0` and `μ > 0`, the equation `βᵢ u'ᵢ(c) = μ` has
a unique solution `c > 0`. -/
theorem unique_marginal_solution (i : ι) (μ : ℝ)
    (hβ : 0 < U.weight i) (hμ : 0 < μ) :
    ∃! c : ℝ, c ∈ Ioi (0 : ℝ) ∧
      (U.weight i : ℝ) * (U.component i).u' c = μ := by
  have hβ_pos : (0 : ℝ) < U.weight i := NNReal.coe_pos.mpr hβ
  set μ' := μ / (U.weight i : ℝ) with hμ'_def
  have hμ' : 0 < μ' := div_pos hμ hβ_pos
  obtain ⟨c, ⟨hc_pos, hc_eq⟩, hc_unique⟩ :=
    (U.component i).unique_marginal_solution μ' hμ'
  refine ⟨c, ⟨hc_pos, ?_⟩, fun d ⟨hd_pos, hd_eq⟩ => ?_⟩
  · rw [hc_eq, hμ'_def]; field_simp
  · refine hc_unique d ⟨hd_pos, ?_⟩
    rw [hμ'_def]; field_simp; linarith

/-! ### Componentwise decomposition over product feasible sets

Over a **product** feasible set `∏ᵢ Sᵢ` the joint maximization of an additively separable
aggregate decouples into independent per-good problems. This decomposition requires a product set:
A shared budget `∑ cᵢ ≤ m` is not one, and the budget-coupled case is handled below via the
multiplier. -/

open Econlib.Optimization in
/-- The per-good objective `gᵢ(t) = βᵢ · uᵢ(t)` — the `i`-th summand of `aggregate`. -/
noncomputable def componentObjective (i : ι) (t : ℝ) : ℝ :=
  (U.weight i : ℝ) * (U.component i).u t

/-- `aggregate` is the coordinate sum of the per-good objectives. -/
lemma aggregate_eq_sum_componentObjective (c : ι → ℝ) :
    U.aggregate c = ∑ i, U.componentObjective i (c i) := rfl

open Econlib.Optimization in
/-- **Separable decomposition (`IsMaxOn` form).** Over a product feasible set `univ.pi S`, a bundle
maximizes the additively separable aggregate iff it maximizes each per-good objective `gᵢ = βᵢ uᵢ`
on its own factor `Sᵢ`. The joint problem decouples coordinate-by-coordinate. -/
theorem isMaxOn_aggregate_pi_iff {S : ι → Set ℝ} {c : ι → ℝ} (hc : c ∈ univ.pi S) :
    IsMaxOn U.aggregate (univ.pi S) c ↔
      ∀ i, IsMaxOn (U.componentObjective i) (S i) (c i) := by
  classical
  simp only [isMaxOn_iff]
  constructor
  · -- Joint ⇒ coordinatewise: vary one coordinate via `Function.update`, holding the rest at `c`.
    intro hjoint i t ht
    have hmem : Function.update c i t ∈ univ.pi S := by
      intro j _
      rcases eq_or_ne j i with rfl | hji
      · simpa using ht
      · simpa [Function.update_of_ne hji] using hc j (mem_univ j)
    have hle := hjoint _ hmem
    -- Only the `i`-th summand changes, so the inequality on sums collapses to the `i`-th term.
    have hsum : ∑ j, U.componentObjective j (Function.update c i t j)
        = U.componentObjective i t
          + ∑ j ∈ Finset.univ.erase i, U.componentObjective j (c j) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Function.update_self]
      congr 1
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    have hsum_c : ∑ j, U.componentObjective j (c j)
        = U.componentObjective i (c i)
          + ∑ j ∈ Finset.univ.erase i, U.componentObjective j (c j) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    rw [aggregate_eq_sum_componentObjective, aggregate_eq_sum_componentObjective, hsum,
      hsum_c] at hle
    linarith
  · intro hcoord d hd
    rw [aggregate_eq_sum_componentObjective, aggregate_eq_sum_componentObjective]
    exact Finset.sum_le_sum fun i _ => hcoord i (d i) (hd i (mem_univ i))

open Econlib.Optimization in
/-- **Separable decomposition (`argmax` form).** Over a product feasible set, the argmax of the
aggregate is the product of the per-good argmaxes: `argmax U.aggregate (∏ Sᵢ) = ∏ᵢ argmax gᵢ Sᵢ`. -/
theorem argmax_aggregate_pi {S : ι → Set ℝ} :
    argmax U.aggregate (univ.pi S)
      = univ.pi (fun i => argmax (U.componentObjective i) (S i)) := by
  ext c
  simp only [argmax, Set.mem_setOf_eq, mem_pi, mem_univ, forall_const]
  constructor
  · rintro ⟨hmem, hmax⟩ i
    have hmem' : c ∈ univ.pi S := fun j _ => hmem j
    exact ⟨hmem i, (U.isMaxOn_aggregate_pi_iff hmem').mp hmax i⟩
  · intro h
    have hmem : c ∈ univ.pi S := fun i _ => (h i).1
    exact ⟨fun i => (h i).1, (U.isMaxOn_aggregate_pi_iff hmem).mpr fun i => (h i).2⟩

/-! ### First-order sufficiency under a binding budget

A coupling budget `∑ cᵢ ≤ m` (unit prices) breaks the product decomposition, but separability
still delivers a clean sufficiency theorem via a single multiplier: A positive bundle exhausting
the budget whose marginal utilities are all equalized to a common `μ ≥ 0` is a maximizer. The
certificate is the concave tangent-line bound on each component — no product structure needed. -/

/-- The interior, unit-price budget set at wealth `m`: Strictly positive bundles costing at most
`m`. Interiority is the right domain for Inada felicities (marginal utility blows up at the
boundary), and unit prices match the canonical two-good consumer problem. Keyed on the utility `U`
(rather than just `ι`) so that the multiplier API below reads via dot notation `U.budget m`; the
set itself depends only on `ι` and `m` at unit prices. -/
def budget (_U : SeparableUtility ι) (m : ℝ) : Set (ι → ℝ) :=
  {c | (∀ i, 0 < c i) ∧ ∑ i, c i ≤ m}

@[simp] lemma mem_budget {m : ℝ} {c : ι → ℝ} :
    c ∈ U.budget m ↔ (∀ i, 0 < c i) ∧ ∑ i, c i ≤ m := Iff.rfl

/-- The budget set is convex: A convex combination of two interior, affordable bundles is interior
and affordable. -/
lemma budget_convex (m : ℝ) : Convex ℝ (U.budget m) := by
  intro c hc d hd a b ha hb hab
  obtain ⟨hc_pos, hc_bud⟩ := hc
  obtain ⟨hd_pos, hd_bud⟩ := hd
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      simp only [hb1, zero_mul, zero_add, one_mul]; exact hd_pos i
    · have := mul_pos ha_pos (hc_pos i)
      have := mul_nonneg hb (hd_pos i).le
      linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    have h1 : a * ∑ i, c i ≤ a * m := by gcongr
    have h2 : b * ∑ i, d i ≤ b * m := by gcongr
    calc a * ∑ i, c i + b * ∑ i, d i
        ≤ a * m + b * m := by linarith
      _ = m := by rw [← add_mul, hab, one_mul]

/-- **First-order sufficiency under a binding budget.** Suppose a strictly positive bundle `cstar`
exhausts the unit-price budget (`∑ cstarᵢ = m`) and equalizes all marginal utilities to a common
nonnegative multiplier `μ` (`βᵢ uᵢ'(cstarᵢ) = μ` for every good). Then `cstar` maximizes the
additively separable aggregate over the whole budget set `{c ≫ 0 ∣ ∑ cᵢ ≤ m}`. Together with
`unique_marginal_solution`, which recovers each `cstarᵢ` from `μ`, this lets a consumer derive the
optimum from the multiplier and the budget. -/
theorem isMaxOn_aggregate_budget_of_foc {cstar : ι → ℝ} {μ m : ℝ}
    (hμ : 0 ≤ μ) (hpos : ∀ i, 0 < cstar i) (hbudget : ∑ i, cstar i = m)
    (hfoc : ∀ i, U.marginal i cstar = μ) :
    IsMaxOn U.aggregate (U.budget m) cstar := by
  rw [isMaxOn_iff]
  intro c hc
  obtain ⟨hc_pos, hc_bud⟩ := hc
  -- Tangent-line bound for each weighted component at `cstar`, summed over goods.
  have h_tangent : ∀ i, (U.weight i : ℝ) * (U.component i).u (c i)
      ≤ (U.weight i : ℝ) * (U.component i).u (cstar i)
        + μ * (c i - cstar i) := by
    intro i
    have hbound := (U.component i).u_le_tangent (hpos i) (hc_pos i)
    have hβ : (0 : ℝ) ≤ U.weight i := (U.weight i).coe_nonneg
    have hmul := mul_le_mul_of_nonneg_left hbound hβ
    have hfoc_i : (U.weight i : ℝ) * (U.component i).u' (cstar i) = μ := hfoc i
    have hkey : (U.weight i : ℝ) *
        ((U.component i).u' (cstar i) * (c i - cstar i)) = μ * (c i - cstar i) := by
      rw [← mul_assoc, hfoc_i]
    calc (U.weight i : ℝ) * (U.component i).u (c i)
        ≤ (U.weight i : ℝ) *
            ((U.component i).u (cstar i)
              + (U.component i).u' (cstar i) * (c i - cstar i)) := hmul
      _ = (U.weight i : ℝ) * (U.component i).u (cstar i) + μ * (c i - cstar i) := by
          rw [mul_add, hkey]
  -- Sum the bounds; the linear part telescopes to `μ (∑cᵢ − ∑c*ᵢ) = μ (∑cᵢ − m) ≤ 0`.
  have h_sum : U.aggregate c
      ≤ U.aggregate cstar + μ * ((∑ i, c i) - ∑ i, cstar i) := by
    simp only [aggregate]
    have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h_tangent i)
    calc ∑ i, (U.weight i : ℝ) * (U.component i).u (c i)
        ≤ ∑ i, ((U.weight i : ℝ) * (U.component i).u (cstar i) + μ * (c i - cstar i)) := this
      _ = (∑ i, (U.weight i : ℝ) * (U.component i).u (cstar i))
            + μ * ((∑ i, c i) - ∑ i, cstar i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  -- `∑cᵢ ≤ m = ∑c*ᵢ` and `μ ≥ 0` make the correction nonpositive; only `h_sum` mentions the sum.
  rw [hbudget] at h_sum
  have hcorr : μ * ((∑ i, c i) - m) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hμ (by linarith)
  linarith [h_sum, hcorr]

/-- **Uniqueness of the budget optimum under strict component concavity.** Given strictly positive
Pareto weights, the aggregate is strictly concave on the positive orthant, so any maximizer over
the convex budget set is unique. -/
theorem eq_of_isMaxOn_aggregate_budget {m : ℝ} {c d : ι → ℝ}
    (hβ : ∀ i, 0 < U.weight i)
    (hc : IsMaxOn U.aggregate (U.budget m) c) (hd : IsMaxOn U.aggregate (U.budget m) d)
    (hc_mem : c ∈ U.budget m) (hd_mem : d ∈ U.budget m) : c = d := by
  have hsub : U.budget m ⊆ positiveOrthant ι := fun e he i => he.1 i
  have hstrict : StrictConcaveOn ℝ (U.budget m) U.aggregate :=
    (U.aggregate_strictConcaveOn hβ).subset hsub (U.budget_convex m)
  exact hstrict.eq_of_isMaxOn hc hd hc_mem hd_mem

end SeparableUtility

/-! ## Two-Good Specialization -/

/-- The two goods: Nondurable consumption and durable stock. -/
inductive Good | nondurable | durable
  deriving DecidableEq, Fintype

/-- A two-good separable utility. -/
abbrev TwoGoodUtility := SeparableUtility Good

namespace TwoGoodUtility

variable (U : TwoGoodUtility)

/-- The nondurable consumption utility component. -/
abbrev nondurableComponent := U.component Good.nondurable

/-- The durable stock utility component. -/
abbrev durableComponent := U.component Good.durable

/-- The aggregate utility as a function of `(c, k)`: `U(c, k) = β_c · u(c) + β_k · g(k)`, where
`β_c = weightNondurable` and `β_k = weightDurable`. -/
noncomputable def aggregateCK (c k : ℝ) : ℝ :=
  U.aggregate (fun i => match i with
    | Good.nondurable => c
    | Good.durable    => k)

/-- The nondurable weight. -/
abbrev weightNondurable := U.weight Good.nondurable

/-- The durable weight. -/
abbrev weightDurable := U.weight Good.durable

/-- The aggregate decomposes as `weightNondurable · u(c) + weightDurable · g(k)`. -/
lemma aggregateCK_eq (c k : ℝ) :
    U.aggregateCK c k =
      (U.weightNondurable : ℝ) * U.nondurableComponent.u c +
      (U.weightDurable : ℝ) * U.durableComponent.u k := by
  simp only [aggregateCK, SeparableUtility.aggregate]
  rw [Fintype.sum_eq_add Good.nondurable Good.durable (by decide)
    (fun x ⟨hn, hd⟩ => by cases x <;> simp_all)]

end TwoGoodUtility

end Econlib.Preferences
