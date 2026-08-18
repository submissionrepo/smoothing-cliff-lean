/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.DynamicProgramming.Budget.StochasticBudgetWeighted
public import Econlib.Optimization.DynamicProgramming.Concavity.BenvenisteScheinkman
public import Econlib.Optimization.MaximumTheorem
public import Econlib.Preferences.Utility.Inada
public import Mathlib.Analysis.Convex.Continuous

/-!
# Consumption–savings dynamic programing

A refinement of the generic `StochBudgetData` to the canonical consumption–savings problem with an
abstract savings instrument. The action is `(c, sav) : ℝ × Sav`: `c ≥ 0` is consumption and
`sav ∈ savings s` is a feasible savings choice (e.g. a vector of Arrow holdings, or a private
margin plus public coverage). Next-period wealth in successor state `s'` is `g sav s'`, the reward
is `u c` for an Inada utility `u`, and the budget at wealth `w` is
`{(c, sav) | 0 ≤ c ∧ sav ∈ savings s ∧ c + cost s sav ≤ w}`.

This sits between `StochBudgetData` (which carries no economic structure on reward / law of motion
/ budget) and a concrete model such as the two-instrument `InsuranceDP`: It packages exactly the
hypotheses under which the **value-level** consumption–savings theory holds — concavity of the
value function, existence of an interior optimal policy, the binding budget, Benveniste–Scheinkman
differentiability, and the envelope identity `v*_w = u'(c*)` — so a concrete model obtains all of
them by instantiation rather than re-derivation.

The interiority argument (`cStar_pos`) is the only place where model-specific structure beyond
affineness is needed: At a binding budget the household must be able to *trade savings for
consumption* along a cost-reducing feasible direction. That direction is supplied abstractly by the
`costReducingDir` field, which a concrete model discharges from its own budget geometry.

## Main definitions

* `ConsumptionSavingsDP n Sav` — the consumption–savings primitives
* `ConsumptionSavingsDP.budget` / `toStochBudgetData` — the budget correspondence and the
  underlying generic stochastic budget DP
* `ConsumptionSavingsDP.valueFunction` — the weighted value function (unbounded-reward layer)
* `ConsumptionSavingsDP.optimalAction` / `cStar` — the selected optimal action and consumption

## Main statements

* `ConsumptionSavingsDP.value_concave` — the value function is concave in wealth on `(0, ∞)`
* `ConsumptionSavingsDP.optimalAction_mem_budget` / `optimalAction_isMaxOn` — Berge existence
* `ConsumptionSavingsDP.cStar_pos` — interiority of consumption (Inada)
* `ConsumptionSavingsDP.budget_binds` — the budget binds: `c* = w − cost s sav*`
* `ConsumptionSavingsDP.value_diff` — Benveniste–Scheinkman differentiability of the value function
* `ConsumptionSavingsDP.value_envelope` — the envelope identity `v*_w(w, s) = u'(c*(w, s))`

## References

* Benveniste, L. M., and J. A. Scheinkman. 1979. “On the Differentiability of the Value Function in
  Dynamic Models of Economics.” *Econometrica* 47 (3): 727. [https://doi.org/10.2307/1910417](https://doi.org/10.2307/1910417).
* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press.

## Tags

dynamic programing, consumption savings, value function, envelope theorem, inada,
benveniste-scheinkman
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

open Set Filter Topology Econlib.Preferences Econlib.Optimization

/-- Primitives of a consumption–savings DP on the mixed state `ℝ × Fin n` with an abstract savings
instrument `Sav` (an `ℝ`-vector space carrying a topology). The action is `(c, sav)`: Consumption
`c` and a savings choice `sav`. -/
structure ConsumptionSavingsDP (n : ℕ) [NeZero n] (Sav : Type*)
    [AddCommGroup Sav] [Module ℝ Sav] [TopologicalSpace Sav] [T2Space Sav] where
  /-- The consumption utility (Inada, hence strictly concave on `(0, ∞)`). -/
  util : Econlib.Preferences.InadaUtility
  /-- **Utility is concave on the closed consumption ray** `[0, ∞)`. Closed-ray concavity (not
  merely the `Ioi 0` concavity that `InadaUtility` provides) makes the per-period reward concave
  over the whole budget, which includes `c = 0`. Satisfied by CRRA `γ ∈ (0, 1)` and `√c`; not by
  `log`. -/
  util_concaveOn : ConcaveOn ℝ (Set.Ici (0 : ℝ)) util.u
  /-- **Utility is continuous on the closed consumption ray** `[0, ∞)`. Makes the Bellman objective
  continuous over the compact budget so Berge's maximum theorem applies up to `c = 0`. -/
  util_continuousOn : ContinuousOn util.u (Set.Ici (0 : ℝ))
  /-- Discount factor. -/
  β : ℝ
  /-- Discount factor is non-negative. -/
  β_nonneg : 0 ≤ β
  /-- Discount factor is strictly less than one. -/
  β_lt_one : β < 1
  /-- Markov transition matrix for the discrete shock. -/
  trans : Fin n → Fin n → ℝ
  /-- Transition entries are non-negative. -/
  trans_nonneg : ∀ s s', 0 ≤ trans s s'
  /-- Each row of the transition matrix sums to one. -/
  trans_sum_one : ∀ s, ∑ s', trans s s' = 1
  /-- Non-consumption budget usage of a savings choice at state `s` (e.g. `R⁻¹ Σ π h`, or `τσ`). -/
  cost : Fin n → Sav → ℝ
  /-- The cost is **continuous** in the savings choice (closedness/continuity input for Berge). -/
  cost_continuous : ∀ s : Fin n, Continuous (cost s)
  /-- Feasible savings at state `s` (independent of wealth: Nonneg/cap/coverage bounds). -/
  savings : Fin n → Set Sav
  /-- The feasible savings set is **convex** (a polytope of linear nonneg/cap constraints). -/
  savings_convex : ∀ s : Fin n, Convex ℝ (savings s)
  /-- The cost is **convex** in the savings choice on the feasible set. The budget constraint
  `c + cost ≤ w` is then convex (a sublevel set of a convex function), which is all the
  value-concavity argument needs — a strictly convex instrument price (e.g. an insurance load `τ`)
  is admissible, not just affine costs. Note `g` must still be affine (`g_affine`): Convexity is
  allowed only in the price, not the law of motion. -/
  cost_convex : ∀ s : Fin n, ConvexOn ℝ (savings s) (cost s)
  /-- The feasible savings set is **compact** (needed for Berge's existence). -/
  savings_isCompact : ∀ s : Fin n, IsCompact (savings s)
  /-- Next-period wealth from a savings choice and realized shock (e.g. `y s' + h s' + σ ρ s'`). -/
  g : Sav → Fin n → ℝ
  /-- Next-period wealth is **affine** in the savings choice for each successor `s'`. With concave
  per-state continuation values, affineness makes the continuation concave in the action. -/
  g_affine : ∀ (a b : Sav) (α : ℝ) (s' : Fin n),
    g (α • a + (1 - α) • b) s' = α * g a s' + (1 - α) * g b s'
  /-- Next-period wealth is **continuous** in the savings choice (continuity input for Berge). -/
  g_continuous : ∀ s' : Fin n, Continuous (fun sav => g sav s')
  /-- Next-period wealth is positive on feasible savings (economic domain). -/
  g_pos : ∀ (s : Fin n) {sav : Sav}, sav ∈ savings s → ∀ s', 0 < g sav s'
  /-- Zero savings is feasible and free (the always-available fallback action). -/
  zero_sav : Fin n → Sav
  /-- Zero savings is feasible. -/
  zero_sav_mem : ∀ s, zero_sav s ∈ savings s
  /-- Zero savings has non-positive cost. -/
  zero_sav_cost : ∀ s, cost s (zero_sav s) ≤ 0
  /-- **Cost-reducing feasible direction** (model-specific kernel of interiority). From feasible
  savings with positive cost, a one-parameter family `move t` (`t ∈ [0, 1]`) staying feasible,
  starting at `sav`, reducing cost *at least* linearly at a positive rate `κ`, and moving
  next-wealth along a concave chord toward a fixed positive `floor` profile (so the continuation
  loss is linear in `t`). The cost conjunct is a one-sided bound `cost (move t) ≤ cost sav − t·κ`
  rather than an equality: A strictly convex instrument price (e.g. an insurance load `τ`) reduces
  cost *super*linearly when its argument is scaled toward zero, which the lower-bound rate `κ`
  captures. The interiority proof needs only this direction (feasibility plus a positive
  consumption gain). -/
  costReducingDir : ∀ (s : Fin n) {sav : Sav}, sav ∈ savings s → 0 < cost s sav →
    ∃ (move : ℝ → Sav) (κ : ℝ) (floor : Fin n → ℝ),
      0 < κ ∧ move 0 = sav ∧ (∀ s', 0 < floor s') ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, move t ∈ savings s) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, cost s (move t) ≤ cost s sav - t * κ) ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, ∀ s', g (move t) s' = (1 - t) * g sav s' + t * floor s')

namespace ConsumptionSavingsDP

variable {n : ℕ} [NeZero n] {Sav : Type*}
  [AddCommGroup Sav] [Module ℝ Sav] [TopologicalSpace Sav] [T2Space Sav]
  (D : ConsumptionSavingsDP n Sav)

/-- The budget set at wealth `w`, shock `s`: Consumption `c ≥ 0`, savings `sav` feasible, and the
budget `c + cost s sav ≤ w`. -/
def budget (w : ℝ) (s : Fin n) : Set (ℝ × Sav) :=
  {a | 0 ≤ a.1 ∧ a.2 ∈ D.savings s ∧ a.1 + D.cost s a.2 ≤ w}

/-- The consumption–savings problem as a generic stochastic budget DP: Reward `u c`, law of motion
`g sav s'`, and the budget correspondence. The Blackwell / concavity / decreasing-differences
theory is inherited from `StochBudgetData`. -/
def toStochBudgetData : StochBudgetData n (ℝ × Sav) where
  β := D.β
  β_nonneg := D.β_nonneg
  β_lt_one := D.β_lt_one
  trans := D.trans
  trans_nonneg := D.trans_nonneg
  trans_sum_one := D.trans_sum_one
  reward := fun a => D.util.u a.1
  f := fun a => D.g a.2
  Γ := D.budget

@[simp] lemma toStochBudgetData_Γ : D.toStochBudgetData.Γ = D.budget := rfl

@[simp] lemma toStochBudgetData_reward (a : ℝ × Sav) :
    D.toStochBudgetData.reward a = D.util.u a.1 := rfl

@[simp] lemma toStochBudgetData_f (a : ℝ × Sav) (s' : Fin n) :
    D.toStochBudgetData.f a s' = D.g a.2 s' := rfl

@[simp] lemma toStochBudgetData_β : D.toStochBudgetData.β = D.β := rfl

@[simp] lemma toStochBudgetData_trans : D.toStochBudgetData.trans = D.trans := rfl

/-- The budget is the generic correspondence. -/
lemma budget_eq_Γ (w : ℝ) (s : Fin n) :
    D.budget w s = D.toStochBudgetData.Γ w s := rfl

/-- The zero action `(0, zero_sav s)` is feasible at non-negative wealth (consumption `0`, the free
fallback savings). -/
lemma zero_action_mem_budget {w : ℝ} (hw : 0 ≤ w) (s : Fin n) :
    ((0, D.zero_sav s) : ℝ × Sav) ∈ D.budget w s :=
  ⟨le_refl 0, D.zero_sav_mem s, by simpa using le_trans (D.zero_sav_cost s) hw⟩

/-- The budget set is nonempty at non-negative wealth. -/
lemma budget_nonempty {w : ℝ} (hw : 0 ≤ w) (s : Fin n) : (D.budget w s).Nonempty :=
  ⟨_, D.zero_action_mem_budget hw s⟩

/-! ### The weighted value function -/

/-- The **value function** of the consumption–savings DP: The unique weighted-bounded fixed point
of the stochastic Bellman operator (unbounded-reward layer). The weight `ω` and the Phase-1
weighted bounds are taken as arguments, exactly as the generic weighted wrappers require. -/
noncomputable def valueFunction (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : D.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        ∑ s', D.trans s s' * ω (D.g a.2 s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        |D.util.u a.1| ≤ C * ω (w, s)) : ℝ × Fin n → ℝ :=
  D.toStochBudgetData.weightedValueFunction ω hμ hβμ h_succ h_reward

/-- The value function solves the stochastic Bellman equation. -/
theorem valueFunction_isFixedPt (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : D.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        ∑ s', D.trans s s' * ω (D.g a.2 s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        |D.util.u a.1| ≤ C * ω (w, s)) (st : ℝ × Fin n) :
    D.valueFunction ω hμ hβμ h_succ h_reward st =
      D.toStochBudgetData.bellmanOp (D.valueFunction ω hμ hβμ h_succ h_reward) st :=
  D.toStochBudgetData.weightedValueFunction_isFixedPt ω hμ hβμ h_succ h_reward st

/-- The value function is weighted-bounded. -/
theorem valueFunction_weightedBounded (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ)
    (hβμ : D.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        ∑ s', D.trans s s' * ω (D.g a.2 s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        |D.util.u a.1| ≤ C * ω (w, s)) :
    WeightedBounded ω (D.valueFunction ω hμ hβμ h_succ h_reward) :=
  D.toStochBudgetData.weightedValueFunction_weightedBounded ω hμ hβμ h_succ h_reward

/-- The per-state `BddAbove` certificate for the value function's Bellman set. -/
lemma valueFunction_bellmanSet_bddAbove (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ)
    (hβμ : D.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        ∑ s', D.trans s s' * ω (D.g a.2 s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        |D.util.u a.1| ≤ C * ω (w, s)) (st : ℝ × Fin n) :
    BddAbove (D.toStochBudgetData.bellmanSet (D.valueFunction ω hμ hβμ h_succ h_reward) st) := by
  obtain ⟨Bv, hBv0, hBv⟩ := D.valueFunction_weightedBounded ω hμ hβμ h_succ h_reward
  exact D.toStochBudgetData.bellmanSet_bddAbove_weighted ω h_succ h_reward hBv0 hBv st

/-! ### Concavity of the value function -/

/-- **Graph-convexity of the budget correspondence across wealth levels.** Mirrors
`CollateralDP.collateralBudget_graphConvex`: The budget is cut out by `c ≥ 0`, `sav ∈ savings s`
(convex), and the affine constraint `c + cost s sav ≤ w`. -/
lemma budget_graphConvex (s : Fin n) ⦃w₁ w₂ : ℝ⦄
    -- `_hw₁`/`_hw₂` are unused (graph-convexity needs no positivity) but fix the shape of the
    -- `bellmanOp_concaveOn` `h_Γ_convex` hypothesis so this lemma plugs in directly.
    (_hw₁ : 0 < w₁) (_hw₂ : 0 < w₂)
    ⦃a₁ a₂ : ℝ × Sav⦄ (ha₁ : a₁ ∈ D.budget w₁ s) (ha₂ : a₂ ∈ D.budget w₂ s)
    ⦃α : ℝ⦄ (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    α • a₁ + (1 - α) • a₂ ∈ D.budget (α • w₁ + (1 - α) • w₂) s := by
  obtain ⟨hca, hsava, hcosta⟩ := ha₁
  obtain ⟨hcb, hsavb, hcostb⟩ := ha₂
  have hβ : (0 : ℝ) ≤ 1 - α := by linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul]
    exact add_nonneg (mul_nonneg hα hca) (mul_nonneg hβ hcb)
  · simp only [Prod.smul_snd, Prod.snd_add]
    exact D.savings_convex s hsava hsavb hα hβ (by ring)
  · -- Cost is convex, so the combination's cost is at most the combination of the costs.
    simp only [Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Prod.fst_add, smul_eq_mul]
    have hconv := (D.cost_convex s).2 hsava hsavb hα hβ (by ring)
    simp only [smul_eq_mul] at hconv
    have h₁ : α * (a₁.1 + D.cost s a₁.2) ≤ α * w₁ := mul_le_mul_of_nonneg_left hcosta hα
    have h₂ : (1 - α) * (a₂.1 + D.cost s a₂.2) ≤ (1 - α) * w₂ := mul_le_mul_of_nonneg_left hcostb hβ
    nlinarith [h₁, h₂, hconv]

/-- **Joint concavity of the stochastic Bellman objective** when the continuation is concave per
state on `(0, ∞)`. Reward `u c` is concave on `[0, ∞)` (`util_concaveOn`), and each continuation
`v(g sav s', s')` is concave in `sav` because `v(·, s')` is concave on `(0, ∞)`, `g(· s')` is
affine (`g_affine`) and lands in `(0, ∞)` (`g_pos`); the affine `g` and non-negative weights `β π`
preserve concavity. -/
lemma objConcave {v : ℝ × Fin n → ℝ}
    (hv : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s)))
    -- `_hw₁`/`_hw₂` are unused (the objective concavity needs only feasibility of the actions) but
    -- fix the shape of the `bellmanOp_concaveOn` `h_obj_concave` hypothesis so this plugs in.
    (s : Fin n) ⦃w₁ w₂ : ℝ⦄ (_hw₁ : 0 < w₁) (_hw₂ : 0 < w₂)
    ⦃a₁ a₂ : ℝ × Sav⦄ (ha₁ : a₁ ∈ D.budget w₁ s) (ha₂ : a₂ ∈ D.budget w₂ s)
    ⦃α : ℝ⦄ (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    α * (D.util.u a₁.1 + D.β * ∑ s', D.trans s s' * v (D.g a₁.2 s', s')) +
      (1 - α) * (D.util.u a₂.1 + D.β * ∑ s', D.trans s s' * v (D.g a₂.2 s', s')) ≤
    D.util.u (α • a₁ + (1 - α) • a₂).1 +
      D.β * ∑ s', D.trans s s' * v (D.g (α • a₁ + (1 - α) • a₂).2 s', s') := by
  obtain ⟨hca, hsava, _⟩ := ha₁
  obtain ⟨hcb, hsavb, _⟩ := ha₂
  have hβ : (0 : ℝ) ≤ 1 - α := by linarith
  have hαβ : α + (1 - α) = 1 := by ring
  have hfst : (α • a₁ + (1 - α) • a₂).1 = α * a₁.1 + (1 - α) * a₂.1 := by
    simp only [Prod.smul_fst, Prod.fst_add, smul_eq_mul]
  -- Reward: concavity of `u` on the closed ray.
  have hu : α * D.util.u a₁.1 + (1 - α) * D.util.u a₂.1 ≤ D.util.u (α • a₁ + (1 - α) • a₂).1 := by
    have h := D.util_concaveOn.2 (Set.mem_Ici.mpr hca) (Set.mem_Ici.mpr hcb) hα hβ hαβ
    simp only [smul_eq_mul] at h
    rw [hfst]; exact h
  -- Continuation: per-state concavity composed with affine `g`.
  have hcont : ∀ s' ∈ Finset.univ,
      α * (D.trans s s' * v (D.g a₁.2 s', s')) + (1 - α) * (D.trans s s' * v (D.g a₂.2 s', s')) ≤
      D.trans s s' * v (D.g (α • a₁ + (1 - α) • a₂).2 s', s') := by
    intro s' _
    have hg1 : (0 : ℝ) < D.g a₁.2 s' := D.g_pos s hsava s'
    have hg2 : (0 : ℝ) < D.g a₂.2 s' := D.g_pos s hsavb s'
    have hvconc := (hv s').2 (Set.mem_Ioi.mpr hg1) (Set.mem_Ioi.mpr hg2) hα hβ hαβ
    simp only [smul_eq_mul] at hvconc
    -- The argument of the combination is the combination of the arguments (`g` affine).
    have harg : D.g (α • a₁ + (1 - α) • a₂).2 s' = α * D.g a₁.2 s' + (1 - α) * D.g a₂.2 s' := by
      simp only [Prod.smul_snd, Prod.snd_add]; exact D.g_affine a₁.2 a₂.2 α s'
    rw [harg]
    have hπ := D.trans_nonneg s s'
    nlinarith [mul_le_mul_of_nonneg_left hvconc hπ]
  have hcont_sum :
      α * (∑ s', D.trans s s' * v (D.g a₁.2 s', s')) +
        (1 - α) * (∑ s', D.trans s s' * v (D.g a₂.2 s', s')) ≤
      ∑ s', D.trans s s' * v (D.g (α • a₁ + (1 - α) • a₂).2 s', s') := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hcont
  have hβcont := mul_le_mul_of_nonneg_left hcont_sum D.β_nonneg
  nlinarith [hu, hβcont]

/-- **The value function is concave in wealth on `(0, ∞)`.** Routed through the weighted iterates
from zero: Each iterate is concave (via `bellmanOp_concaveOn`, discharging budget graph-convexity
and objective concavity), and concavity survives the pointwise limit. -/
theorem value_concave (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : D.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        ∑ s', D.trans s s' * ω (D.g a.2 s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        |D.util.u a.1| ≤ C * ω (w, s)) (s : Fin n) :
    ConcaveOn ℝ (Ioi 0) (fun w => D.valueFunction ω hμ hβμ h_succ h_reward (w, s)) := by
  set M := D.toStochBudgetData with hM
  set H := M.toWeightedBlackwell ω hμ hβμ h_succ h_reward with hH
  -- Each weighted iterate `iterₖ(·, s)` is concave on `(0, ∞)`, by induction on `k`.
  have h_iter_concave : ∀ (k : ℕ) (s : Fin n),
      ConcaveOn ℝ (Ioi 0) (fun w => WeightedBlackwell.iter M.bellmanOp k (w, s)) := by
    intro k
    induction k with
    | zero =>
      intro s
      simpa only [WeightedBlackwell.iter_zero] using concaveOn_const (0 : ℝ) (convex_Ioi (0 : ℝ))
    | succ k ih =>
      intro s
      rw [WeightedBlackwell.iter_succ]
      -- The iterate is weighted bounded, so each Bellman set is bounded above.
      have hbdd_k : WeightedBounded ω (WeightedBlackwell.iter M.bellmanOp k) :=
        WeightedBlackwell.iter_weightedBounded H k
      obtain ⟨Bv, hBv0, hBv⟩ := hbdd_k
      exact M.bellmanOp_concaveOn _ ih
        (fun st => M.bellmanSet_bddAbove_weighted ω h_succ h_reward hBv0 hBv st)
        (fun s' w hw => D.budget_nonempty hw.le s')
        (fun s' => D.budget_graphConvex s')
        (fun s' => D.objConcave ih s') s
  -- The value function is the pointwise limit of the iterates; concavity survives.
  refine ⟨convex_Ioi 0, fun w₁ hw₁ w₂ hw₂ a b ha hb hab => ?_⟩
  have htend : ∀ w : ℝ,
      Filter.Tendsto (fun k => WeightedBlackwell.iter M.bellmanOp k (w, s)) Filter.atTop
        (nhds (D.valueFunction ω hμ hβμ h_succ h_reward (w, s))) :=
    fun w => WeightedBlackwell.iter_tendsto_fixedPoint H (w, s)
  have hk : ∀ k,
      a • WeightedBlackwell.iter M.bellmanOp k (w₁, s) +
        b • WeightedBlackwell.iter M.bellmanOp k (w₂, s) ≤
      WeightedBlackwell.iter M.bellmanOp k (a • w₁ + b • w₂, s) :=
    fun k => (h_iter_concave k s).2 hw₁ hw₂ ha hb hab
  have hlhs :
      Filter.Tendsto
        (fun k => a • WeightedBlackwell.iter M.bellmanOp k (w₁, s) +
          b • WeightedBlackwell.iter M.bellmanOp k (w₂, s))
        Filter.atTop
        (nhds (a • D.valueFunction ω hμ hβμ h_succ h_reward (w₁, s) +
          b • D.valueFunction ω hμ hβμ h_succ h_reward (w₂, s))) :=
    ((htend w₁).const_smul a).add ((htend w₂).const_smul b)
  exact le_of_tendsto_of_tendsto' hlhs (htend (a • w₁ + b • w₂)) hk

/-! ### Berge existence of the optimal action -/

/-- The Bellman objective at wealth `w`, shock `s`, action `a = (c, sav)`:
`u c + β Σ π v(g sav s', s')`. -/
noncomputable def objective (v : ℝ × Fin n → ℝ) (s : Fin n) (a : ℝ × Sav) : ℝ :=
  D.util.u a.1 + D.β * ∑ s', D.trans s s' * v (D.g a.2 s', s')

/-- The budget set is **closed**: An intersection of closed conditions (`c ≥ 0`, `sav ∈ savings s`
closed, and the continuous affine constraint `c + cost ≤ w`). -/
lemma budget_isClosed (w : ℝ) (s : Fin n) : IsClosed (D.budget w s) := by
  have hc : IsClosed {a : ℝ × Sav | 0 ≤ a.1} := isClosed_le continuous_const continuous_fst
  have hsav : IsClosed {a : ℝ × Sav | a.2 ∈ D.savings s} :=
    (D.savings_isCompact s).isClosed.preimage continuous_snd
  have hcost : IsClosed {a : ℝ × Sav | a.1 + D.cost s a.2 ≤ w} :=
    isClosed_le (continuous_fst.add ((D.cost_continuous s).comp continuous_snd)) continuous_const
  have heq : D.budget w s =
      {a : ℝ × Sav | 0 ≤ a.1} ∩ {a | a.2 ∈ D.savings s} ∩ {a | a.1 + D.cost s a.2 ≤ w} := by
    ext a; simp only [budget, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [heq]; exact (hc.inter hsav).inter hcost

/-- The budget set is **compact**: It is closed (`budget_isClosed`) and trapped in the compact box
`[0, w − m] × savings s`, where `m` is the (attained, since `savings s` is compact and `cost s`
continuous) minimum cost. From feasibility `a.1 ≤ w − cost s a.2 ≤ w − m`. -/
lemma budget_isCompact {w : ℝ} (s : Fin n) : IsCompact (D.budget w s) := by
  rcases (D.savings s).eq_empty_or_nonempty with hempty | hne
  · -- Empty savings ⇒ empty budget.
    have : D.budget w s = ∅ := by
      ext a; simp only [budget, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, hsav, _⟩; rw [hempty] at hsav; exact hsav
    rw [this]; exact isCompact_empty
  · -- The continuous `cost s` attains a minimum `m` on the compact `savings s`.
    obtain ⟨sav₀, _, hmin⟩ := (D.savings_isCompact s).exists_isMinOn hne
      (D.cost_continuous s).continuousOn
    set m := D.cost s sav₀ with hm_def
    -- The budget sits inside the compact box `[0, w − m] × savings s`.
    have hbox : IsCompact (Set.Icc (0 : ℝ) (w - m) ×ˢ D.savings s) :=
      isCompact_Icc.prod (D.savings_isCompact s)
    refine hbox.of_isClosed_subset (D.budget_isClosed w s) ?_
    intro a ⟨hca, hsava, hcosta⟩
    refine Set.mem_prod.mpr ⟨⟨hca, ?_⟩, hsava⟩
    -- `a.1 ≤ w − cost s a.2 ≤ w − m`.
    have hm_le : m ≤ D.cost s a.2 := hmin hsava
    linarith

/-- The continuation term is continuous on the open slice where every successor wealth is positive,
since each `v(·, s')` is continuous on `Ioi 0` and `sav ↦ g sav s'` is continuous. -/
lemma continuousOn_continuation {v : ℝ × Fin n → ℝ}
    (hv : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s))) (s : Fin n) :
    ContinuousOn (fun a : ℝ × Sav => D.β * ∑ s', D.trans s s' * v (D.g a.2 s', s'))
      {a : ℝ × Sav | ∀ s', 0 < D.g a.2 s'} := by
  apply continuousOn_const.mul
  apply continuousOn_finset_sum
  intro s' _
  apply continuousOn_const.mul
  have hvcont : ContinuousOn (fun x => v (x, s')) (Ioi 0) :=
    ConcaveOn.continuousOn isOpen_Ioi (hv s')
  have harg : ContinuousOn (fun a : ℝ × Sav => D.g a.2 s')
      {a : ℝ × Sav | ∀ s'', 0 < D.g a.2 s''} :=
    ((D.g_continuous s').comp continuous_snd).continuousOn
  exact hvcont.comp harg (fun a ha => Set.mem_Ioi.mpr (ha s'))

/-- **The Bellman objective is continuous on the budget set.** Reward `u ∘ fst` is continuous on
`{c ≥ 0} ⊇ budget`, and the continuation is continuous on `{a | ∀ s', 0 < g sav s'} ⊇ budget`. -/
lemma objective_continuousOn {v : ℝ × Fin n → ℝ}
    (hv : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s))) (w : ℝ) (s : Fin n) :
    ContinuousOn (D.objective v s) (D.budget w s) := by
  have hu : ContinuousOn (fun a : ℝ × Sav => D.util.u a.1) (D.budget w s) :=
    D.util_continuousOn.comp continuousOn_fst (fun a ha => Set.mem_Ici.mpr ha.1)
  have hcont : ContinuousOn (fun a : ℝ × Sav => D.β * ∑ s', D.trans s s' * v (D.g a.2 s', s'))
      (D.budget w s) :=
    (D.continuousOn_continuation hv s).mono (fun a ha s' => D.g_pos s ha.2.1 s')
  simpa only [objective] using hu.add hcont

/-- The **selected optimal action** `a*(w, s) = (c*, sav*)`: A chosen element of the argmax of the
Bellman objective over the budget set (nonempty at `w ≥ 0` by compactness). -/
noncomputable def optimalAction (v : ℝ × Fin n → ℝ) (w : ℝ) (s : Fin n) : ℝ × Sav :=
  open Classical in
  if h : (argmax (D.objective v s) (D.budget w s)).Nonempty then h.some
  else (0, D.zero_sav s)

/-- **Optimal consumption** `c*(w, s)`. -/
noncomputable def cStar (v : ℝ × Fin n → ℝ) (w : ℝ) (s : Fin n) : ℝ := (D.optimalAction v w s).1

/-- The argmax is nonempty at non-negative wealth (Berge: Continuous objective on compact
budget). -/
lemma argmax_nonempty {v : ℝ × Fin n → ℝ}
    (hv : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s)))
    {w : ℝ} (hw : 0 ≤ w) (s : Fin n) :
    (argmax (D.objective v s) (D.budget w s)).Nonempty :=
  (D.budget_isCompact s).exists_isMaxOn (D.budget_nonempty hw s) (D.objective_continuousOn hv w s)

/-- The optimal action is in the argmax at non-negative wealth. -/
lemma optimalAction_mem_argmax {v : ℝ × Fin n → ℝ}
    (hv : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s)))
    {w : ℝ} (hw : 0 ≤ w) (s : Fin n) :
    D.optimalAction v w s ∈ argmax (D.objective v s) (D.budget w s) := by
  rw [optimalAction, dif_pos (D.argmax_nonempty hv hw s)]
  exact (D.argmax_nonempty hv hw s).some_mem

/-- The optimal action lies in the budget set. -/
lemma optimalAction_mem_budget {v : ℝ × Fin n → ℝ}
    (hv : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s)))
    {w : ℝ} (hw : 0 ≤ w) (s : Fin n) :
    D.optimalAction v w s ∈ D.budget w s :=
  (D.optimalAction_mem_argmax hv hw s).1

/-- The optimal action maximizes the objective over the budget set. -/
lemma optimalAction_isMaxOn {v : ℝ × Fin n → ℝ}
    (hv : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s)))
    {w : ℝ} (hw : 0 ≤ w) (s : Fin n) :
    IsMaxOn (D.objective v s) (D.budget w s) (D.optimalAction v w s) :=
  (D.optimalAction_mem_argmax hv hw s).2

/-! ### The value function as the attained maximum of the objective

These bridge the objective `objective v* s` to the fixed point `v*`: The objective is exactly
the defining expression of the Bellman set, so `v*(w, s)` is its supremum (`feasible_value_le`) and
a maximizing feasible action's objective equals `v*(w, s)`. -/

/-- The objective is the Bellman-set expression of the underlying generic DP. -/
lemma objective_eq (v : ℝ × Fin n → ℝ) (s : Fin n) (a : ℝ × Sav) :
    D.objective v s a =
      D.toStochBudgetData.reward a +
        D.toStochBudgetData.β * ∑ s', D.toStochBudgetData.trans s s' *
          v (D.toStochBudgetData.f a s', s') := rfl

/-- The objective of any feasible action is bounded by the fixed-point value (forward Bellman
inequality). -/
lemma objective_le_value {v : ℝ × Fin n → ℝ} (hv_fp : ∀ p, v p = D.toStochBudgetData.bellmanOp v p)
    (hbdd : ∀ st, BddAbove (D.toStochBudgetData.bellmanSet v st)) {w : ℝ} (s : Fin n)
    {a : ℝ × Sav} (ha : a ∈ D.budget w s) :
    D.objective v s a ≤ v (w, s) :=
  D.toStochBudgetData.feasible_value_le v hv_fp (w, s) (hbdd (w, s)) a ha

/-- A maximizing feasible action's objective equals the fixed-point value. -/
lemma objective_eq_value_of_isMaxOn {v : ℝ × Fin n → ℝ}
    (hv_fp : ∀ p, v p = D.toStochBudgetData.bellmanOp v p)
    (hbdd : ∀ st, BddAbove (D.toStochBudgetData.bellmanSet v st))
    {w : ℝ} (hw : 0 ≤ w) (s : Fin n) {a : ℝ × Sav} (ha : a ∈ D.budget w s)
    (hmax : IsMaxOn (D.objective v s) (D.budget w s) a) :
    D.objective v s a = v (w, s) := by
  refine le_antisymm (D.objective_le_value hv_fp hbdd s ha) ?_
  -- `v*(w,s) = sSup (bellmanSet v* (w,s))`, every element of which is some `objective v* s a'`,
  -- and `objective v* s a' ≤ objective v* s a` because `a` is a maximizer.
  rw [hv_fp (w, s), StochBudgetData.bellmanOp_eq_sSup]
  refine csSup_le (D.toStochBudgetData.bellmanSet_nonempty v (D.budget_nonempty hw s)) ?_
  rintro r ⟨a', ha', rfl⟩
  exact hmax ha'

/-! ### Interiority of the optimal consumption (Inada) -/

/-- **Tangent gain at zero consumption.** From closed-ray concavity of `u`, for `c > 0` the gain
over zero consumption dominates the linear term: `u c − u 0 ≥ c · u'(c)`. (`util_concaveOn` on the
closed ray makes `c = 0` admissible.) -/
lemma tangent_gain_zero {c : ℝ} (hc : 0 < c) : D.util.u c - D.util.u 0 ≥ c * D.util.u' c := by
  have hslope : D.util.u' c ≤ slope D.util.u 0 c :=
    D.util_concaveOn.le_slope_of_hasDerivAt Set.self_mem_Ici (Set.mem_Ici.mpr hc.le) hc
      (D.util.has_deriv c (D.util.domain_eq ▸ hc))
  rw [slope_def_field, sub_zero] at hslope
  have := (le_div_iff₀ hc).mp hslope
  nlinarith [this]

/-- **Interiority of any maximizer (Inada).** At positive wealth, any feasible action attaining the
Bellman value of a concave fixed point has strictly positive consumption. The concave tangent bound
at `c = 0`, `u(c) − u(0) ≥ c · u'(c)`, with `u'(0⁺) = +∞` (Inada), makes `c = 0` strictly
suboptimal: A little wealth moved into consumption gains unbounded marginal utility, outweighing
the bounded loss in continuation value. The binding case (all wealth committed to savings) is
handled by the `costReducingDir` field, which hands over a cost-reducing feasible direction. -/
lemma pos_of_isMaxOn {v : ℝ × Fin n → ℝ}
    (hv_concave : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s)))
    {w : ℝ} (hw : 0 < w) (s : Fin n)
    {a : ℝ × Sav} (ha : a ∈ D.budget w s)
    (hmax : IsMaxOn (D.objective v s) (D.budget w s) a) :
    0 < a.1 := by
  obtain ⟨hc, hsav, hcost⟩ := ha
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  swap
  · exact hcpos
  -- Suppose `a.1 = 0`. Split on whether the budget binds (`cost s a.2 = w`) or has slack.
  exfalso
  set sav := a.2 with hsav_def
  have hcost' : D.cost s sav ≤ w := by rw [← hc0] at hcost; simpa using hcost
  rcases lt_or_eq_of_le hcost' with hslack | hbind
  · -- **Slack case** `cost < w`: the action `(w − cost, sav)` (same savings, residual consumed) is
    -- feasible and strictly better, since `u(w − cost) − u(0) ≥ (w − cost) u'(w − cost) > 0`.
    set c₁ := w - D.cost s sav with hc₁_def
    have hc₁_pos : 0 < c₁ := by rw [hc₁_def]; linarith
    have hfeas : ((c₁, sav) : ℝ × Sav) ∈ D.budget w s :=
      ⟨hc₁_pos.le, hsav, by rw [hc₁_def]; linarith⟩
    -- Concave tangent at `c = 0`: `u(c₁) − u(0) ≥ c₁ u'(c₁) > 0`.
    have hgain : D.util.u 0 < D.util.u c₁ := by
      have hu'pos : 0 < D.util.u' c₁ := D.util.u'_pos_on _ hc₁_pos
      have := D.tangent_gain_zero hc₁_pos
      nlinarith [mul_pos hc₁_pos hu'pos]
    have hmaxle := hmax hfeas
    -- The continuation is unchanged (same savings); `u(a.1) = u(0) < u(c₁)` contradicts optimality.
    simp only [objective, Set.mem_setOf_eq] at hmaxle
    rw [← hc0] at hmaxle
    linarith
  · -- **Binding case** `cost s sav = w > 0`: use the cost-reducing direction to trade savings for
    -- consumption. The trade `(t·κ, move t)` is feasible on `[0, 1]`, with consumption gain
    -- `u(t·κ) − u(0) ≥ t·κ·u'(t·κ)` (Inada `u'(0⁺) = +∞`) dominating the linear continuation loss.
    have hcost_pos : 0 < D.cost s sav := by rw [hbind]; exact hw
    obtain ⟨move, κ, floor, hκ_pos, hmove0, hfloor_pos, hmove_feas, hmove_cost, hmove_g⟩ :=
      D.costReducingDir s hsav hcost_pos
    -- Feasibility of the trade `(t·κ, move t)` for `t ∈ [0, 1]`: cost `c + cost ≤ w` holds since
    -- the consumption gain `t·κ` is bounded by the (at-least-linear) cost drop.
    have hfeas : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
        ((t * κ, move t) : ℝ × Sav) ∈ D.budget w s := by
      intro t ht
      refine ⟨mul_nonneg ht.1 hκ_pos.le, hmove_feas t ht, ?_⟩
      have hcost_le := hmove_cost t ht
      rw [hbind] at hcost_le; simp only; linarith [hcost_le]
    -- The objective at the trade `t`.
    set g : ℝ → ℝ := fun t => D.objective v s (t * κ, move t) with hg_def
    -- `g 0 = objective(a)` (trade nothing): `0·κ = 0`, `move 0 = sav`.
    have hg0_eq : g 0 = D.objective v s a := by
      simp only [hg_def, zero_mul, hmove0]
      congr 1
      exact Prod.ext hc0 hsav_def
    -- Optimality: `g t ≤ g 0` for feasible `t ∈ [0, 1]`.
    have hg_le : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 → g t ≤ g 0 := by
      intro t ht
      rw [hg0_eq]; exact hmax (hfeas t ht)
    -- **Continuation chord bound.** Each successor term moves through `v(·, s')` along the chord
    -- from `g sav s' > 0` to `floor s' > 0`. Concavity gives the linear lower bound in `t`.
    set Cv : ℝ := ∑ s', D.trans s s' * (v (floor s', s') - v (D.g sav s', s')) with hCv_def
    have hcont_chord : ∀ t : ℝ, t ∈ Set.Icc (0:ℝ) 1 →
        (∑ s', D.trans s s' * v (D.g (move t) s', s')) -
          (∑ s', D.trans s s' * v (D.g sav s', s')) ≥ t * Cv := by
      intro t ht
      rw [hCv_def, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_le_sum
      intro s' _
      have hgsav_pos : 0 < D.g sav s' := D.g_pos s hsav s'
      have hfloor_s'_pos : 0 < floor s' := hfloor_pos s'
      -- `v((1-t) g sav s' + t floor s') ≥ (1-t) v(g sav s') + t v(floor s')`.
      have hconc := (hv_concave s').2 (Set.mem_Ioi.mpr hgsav_pos) (Set.mem_Ioi.mpr hfloor_s'_pos)
        (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1 (by ring)
      simp only [smul_eq_mul] at hconc
      rw [hmove_g t ht s']
      have hπ := D.trans_nonneg s s'
      nlinarith [mul_le_mul_of_nonneg_left hconc hπ]
    -- The decomposition of `g t − g 0`.
    have hg_decomp : ∀ t : ℝ, g t - g 0 =
        (D.util.u (t * κ) - D.util.u 0) +
          D.β * ((∑ s', D.trans s s' * v (D.g (move t) s', s')) -
            (∑ s', D.trans s s' * v (D.g sav s', s'))) := by
      intro t
      rw [hg0_eq]
      simp only [hg_def, objective, hsav_def, ← hc0]
      ring
    -- The threshold marginal utility the consumption term must clear.
    set μ₀ : ℝ := (1 - D.β * Cv) / κ + 1 with hμ₀_def
    -- For small `t > 0`: `t·κ > 0`, `t ≤ 1`, and `u'(t·κ) > μ₀` (Inada `u'(0⁺) = +∞`).
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        0 < t ∧ t ≤ 1 ∧ μ₀ < D.util.u' (t * κ) := by
      -- `t ↦ t·κ` maps `𝓝[>] 0` into `𝓝[>] 0`; precompose Inada divergence.
      have hc_cont : Filter.Tendsto (fun t : ℝ => t * κ) (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin 0 (Set.Ioi 0)) := by
        have hc_tendsto : Filter.Tendsto (fun t : ℝ => t * κ) (nhds 0) (nhds 0) := by
          simpa using (continuous_id.mul continuous_const).tendsto (0 : ℝ)
        rw [tendsto_nhdsWithin_iff]
        refine ⟨hc_tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos ht hκ_pos
      have hinada := D.util.inada_zero.eventually_gt_atTop μ₀
      have hpre := hc_cont.eventually hinada
      filter_upwards [hpre, self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds
          (eventually_le_nhds (by norm_num : (0:ℝ) < 1))]
        with t ht hpos htle
      exact ⟨hpos, htle, ht⟩
    -- Extract one such `t` and derive the contradiction.
    obtain ⟨t, ht0, ht1, htμ⟩ : ∃ t, 0 < t ∧ t ≤ 1 ∧ μ₀ < D.util.u' (t * κ) := hev.exists
    have htκ_pos : 0 < t * κ := mul_pos ht0 hκ_pos
    have htmem : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht0.le, ht1⟩
    -- Consumption gain `u(t·κ) − u(0) ≥ t·κ·u'(t·κ) > t·(1 − β Cv)` (the threshold clearing).
    have hgain_t := D.tangent_gain_zero htκ_pos
    have hbig : (t * κ) * D.util.u' (t * κ) > t * (1 - D.β * Cv) := by
      -- `μ₀·κ = (1 − β Cv) + κ`, so `(t·κ)·μ₀ = t·(1 − β Cv) + t·κ`.
      have hμ₀_clear : μ₀ * κ = (1 - D.β * Cv) + κ := by
        rw [hμ₀_def, add_mul, div_mul_cancel₀ _ hκ_pos.ne', one_mul]
      have hcμ : (t * κ) * μ₀ = t * (1 - D.β * Cv) + t * κ := by
        rw [show (t * κ) * μ₀ = t * (μ₀ * κ) by ring, hμ₀_clear]; ring
      have hstep : (t * κ) * D.util.u' (t * κ) > (t * κ) * μ₀ :=
        mul_lt_mul_of_pos_left htμ htκ_pos
      rw [hcμ] at hstep
      linarith [htκ_pos]
    -- Continuation loss `β·(Δcont) ≥ β t Cv`.
    have hcont_lb : D.β * ((∑ s', D.trans s s' * v (D.g (move t) s', s')) -
        (∑ s', D.trans s s' * v (D.g sav s', s'))) ≥ D.β * (t * Cv) :=
      mul_le_mul_of_nonneg_left (hcont_chord t htmem) D.β_nonneg
    -- Therefore `g t − g 0 ≥ t·κ·u'(t·κ) + β t Cv > t(1 − β Cv) + β t Cv = t > 0`. Contradiction.
    have hpos : g t - g 0 > 0 := by
      have hcancel : t * (1 - D.β * Cv) + D.β * (t * Cv) = t := by ring
      rw [hg_decomp t]
      linarith [hgain_t, hcont_lb, hbig, hcancel, ht0]
    linarith [hg_le t htmem, hpos]

/-! ### Headline value-level theorems for the value function -/

/-- **Interiority of optimal consumption (Inada).** On the economic domain `w > 0`, optimal
consumption is strictly positive. -/
theorem cStar_pos (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : D.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        ∑ s', D.trans s s' * ω (D.g a.2 s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        |D.util.u a.1| ≤ C * ω (w, s))
    {w : ℝ} (hw : 0 < w) (s : Fin n) :
    0 < D.cStar (D.valueFunction ω hμ hβμ h_succ h_reward) w s := by
  set v := D.valueFunction ω hμ hβμ h_succ h_reward with hv
  have hv_concave : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s)) :=
    fun s => D.value_concave ω hμ hβμ h_succ h_reward s
  exact D.pos_of_isMaxOn hv_concave hw s (D.optimalAction_mem_budget hv_concave hw.le s)
    (D.optimalAction_isMaxOn hv_concave hw.le s)

/-- **The budget binds at the optimum.** Since `u` is strictly increasing, optimal consumption
exhausts the wealth left after savings: `c* = w − cost s sav*`. -/
theorem budget_binds (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : D.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        ∑ s', D.trans s s' * ω (D.g a.2 s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        |D.util.u a.1| ≤ C * ω (w, s))
    {w : ℝ} (hw : 0 < w) (s : Fin n) :
    D.cStar (D.valueFunction ω hμ hβμ h_succ h_reward) w s =
      w - D.cost s (D.optimalAction (D.valueFunction ω hμ hβμ h_succ h_reward) w s).2 := by
  set v := D.valueFunction ω hμ hβμ h_succ h_reward with hv
  have hv_concave : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s)) :=
    fun s => D.value_concave ω hμ hβμ h_succ h_reward s
  set sav := (D.optimalAction v w s).2 with hsav_def
  have hmax := D.optimalAction_isMaxOn hv_concave hw.le s
  have hcpos : 0 < D.cStar v w s := D.cStar_pos ω hμ hβμ h_succ h_reward hw s
  obtain ⟨hc, hsav, hcost⟩ := D.optimalAction_mem_budget hv_concave hw.le s
  -- `c* + cost ≤ w` so `c* ≤ w − cost`.
  have hcost' : D.cStar v w s + D.cost s sav ≤ w := by simpa only [cStar, hsav_def] using hcost
  have hle : D.cStar v w s ≤ w - D.cost s sav := by linarith
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- If strict, the action `(w − cost, sav)` is feasible and strictly better (`u` increasing).
    exfalso
    set c₁ := w - D.cost s sav with hc₁_def
    have hc₁_pos : 0 < c₁ := lt_of_lt_of_le hcpos hle
    have hfeas : ((c₁, sav) : ℝ × Sav) ∈ D.budget w s :=
      ⟨hc₁_pos.le, hsav, by rw [hc₁_def]; linarith⟩
    have hmono : D.util.u (D.cStar v w s) < D.util.u c₁ :=
      D.util.strictMonoOn_u (D.util.mem_domain_iff.mpr hcpos)
        (D.util.mem_domain_iff.mpr hc₁_pos) hlt
    have hmaxle := hmax hfeas
    -- The continuation term is identical (same savings); only the `u` term differs.
    simp only [objective, Set.mem_setOf_eq, cStar, hsav_def] at hmaxle hmono ⊢
    linarith
  · exact heq

/-! ### Benveniste–Scheinkman differentiability and the envelope identity

Freeze the optimal savings `sav*(w₀, s)` and vary wealth: The support
`φ(w') = u(w' − cost s sav*) + β Σ π v(g sav* s', s')` is the objective at the feasible action
`(w' − cost s sav*, sav*)`. It is differentiable (frozen continuation), lies below `v*` near `w₀`
(`objective_le_value`), and meets it at `w₀` (optimality + binding budget). Benveniste–Scheinkman
(`ConcaveOn.differentiableAt_of_support`) then makes `v*` differentiable at `w₀` with
`v*_w(w₀, s) = φ'(w₀) = u'(c*)`. -/

/-- The Benveniste–Scheinkman support at base wealth `w₀`: Freeze the optimal savings, vary wealth
in the consumption coordinate. Differentiable at `w₀` (consumption residual `w₀ − cost = c* > 0`),
touches `v*` from below, and meets it at `w₀`. Stated as a `∃` so the value-function arguments stay
threaded once. -/
lemma exists_bsSupport (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : D.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        ∑ s', D.trans s s' * ω (D.g a.2 s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        |D.util.u a.1| ≤ C * ω (w, s))
    {w₀ : ℝ} (hw₀ : 0 < w₀) (s : Fin n) :
    ∃ φ : ℝ → ℝ, DifferentiableAt ℝ φ w₀ ∧
      HasDerivAt φ (D.util.u' (D.cStar (D.valueFunction ω hμ hβμ h_succ h_reward) w₀ s)) w₀ ∧
      φ w₀ = D.valueFunction ω hμ hβμ h_succ h_reward (w₀, s) ∧
      ∀ᶠ w' in nhds w₀,
        φ w' ≤ D.valueFunction ω hμ hβμ h_succ h_reward (w', s) := by
  set v := D.valueFunction ω hμ hβμ h_succ h_reward with hv
  have hv_concave : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s)) :=
    fun s => D.value_concave ω hμ hβμ h_succ h_reward s
  have hv_fp : ∀ p, v p = D.toStochBudgetData.bellmanOp v p :=
    fun p => D.valueFunction_isFixedPt ω hμ hβμ h_succ h_reward p
  have hbdd : ∀ st, BddAbove (D.toStochBudgetData.bellmanSet v st) :=
    fun st => D.valueFunction_bellmanSet_bddAbove ω hμ hβμ h_succ h_reward st
  set sav := (D.optimalAction v w₀ s).2 with hsav_def
  set K := D.cost s sav with hK_def
  set cont := D.β * ∑ s', D.trans s s' * v (D.g sav s', s') with hcont_def
  -- The frozen-savings support.
  refine ⟨fun w' => D.util.u (w' - K) + cont, ?_, ?_, ?_, ?_⟩
  · -- Differentiable at `w₀`: residual `w₀ − K = c* > 0`.
    have hres : 0 < w₀ - K := by
      rw [← D.budget_binds ω hμ hβμ h_succ h_reward hw₀ s]
      exact D.cStar_pos ω hμ hβμ h_succ h_reward hw₀ s
    have hu : DifferentiableAt ℝ D.util.u (w₀ - K) :=
      (D.util.has_deriv _ (D.util.domain_eq ▸ hres)).differentiableAt
    exact (hu.comp w₀ (differentiableAt_id.sub (differentiableAt_const _))).add
      (differentiableAt_const _)
  · -- Derivative `u'(c*)` at `w₀`.
    have hbind : w₀ - K = D.cStar v w₀ s := (D.budget_binds ω hμ hβμ h_succ h_reward hw₀ s).symm
    have hres : 0 < w₀ - K := by rw [hbind]; exact D.cStar_pos ω hμ hβμ h_succ h_reward hw₀ s
    have hsub : HasDerivAt (fun w' => w' - K) 1 w₀ := (hasDerivAt_id w₀).sub_const _
    have hu : HasDerivAt D.util.u (D.util.u' (w₀ - K)) (w₀ - K) :=
      D.util.has_deriv _ (D.util.domain_eq ▸ hres)
    have hcomp := hu.comp w₀ hsub
    simp only [mul_one] at hcomp
    have hφ := hcomp.add (hasDerivAt_const w₀ cont)
    rw [add_zero, hbind] at hφ
    exact hφ
  · -- `φ(w₀) = v*(w₀, s)`: optimality + binding budget.
    have hbind : w₀ - K = D.cStar v w₀ s := (D.budget_binds ω hμ hβμ h_succ h_reward hw₀ s).symm
    change D.util.u (w₀ - K) + cont = v (w₀, s)
    rw [hbind]
    -- `u(c*) + cont = objective v s (optimalAction) = v*(w₀, s)`.
    have hobj_eq : D.util.u (D.cStar v w₀ s) + cont = D.objective v s (D.optimalAction v w₀ s) := by
      rw [objective, hcont_def, cStar]
    rw [hobj_eq]
    exact D.objective_eq_value_of_isMaxOn hv_fp hbdd hw₀.le s
      (D.optimalAction_mem_budget hv_concave hw₀.le s)
      (D.optimalAction_isMaxOn hv_concave hw₀.le s)
  · -- `φ(w') ≤ v*(w', s)` near `w₀`: the frozen action `(w' − K, sav)` stays feasible for `w' > K`.
    have hbind : D.cStar v w₀ s = w₀ - K := D.budget_binds ω hμ hβμ h_succ h_reward hw₀ s
    have hres : K < w₀ := by
      have hcpos := D.cStar_pos ω hμ hβμ h_succ h_reward hw₀ s; rw [hbind] at hcpos; linarith
    have hsav_mem : sav ∈ D.savings s := (D.optimalAction_mem_budget hv_concave hw₀.le s).2.1
    filter_upwards [Ioi_mem_nhds hres] with w' hw'
    have hw'mem : K < w' := Set.mem_Ioi.mp hw'
    -- Feasibility of `(w' − K, sav)` at `w'`.
    have hfeas : ((w' - K, sav) : ℝ × Sav) ∈ D.budget w' s :=
      ⟨by linarith, hsav_mem, by rw [hK_def]; linarith⟩
    have hle := D.objective_le_value hv_fp hbdd s hfeas
    -- `objective v s (w' − K, sav) = φ(w')`.
    simpa only [objective, hcont_def] using hle

/-- **The value function is differentiable in wealth on `(0, ∞)`** (Benveniste–Scheinkman). -/
theorem value_diff (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : D.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        ∑ s', D.trans s s' * ω (D.g a.2 s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        |D.util.u a.1| ≤ C * ω (w, s))
    {w : ℝ} (hw : 0 < w) (s : Fin n) :
    DifferentiableAt ℝ (fun x => D.valueFunction ω hμ hβμ h_succ h_reward (x, s)) w := by
  refine ConcaveOn.differentiableAt_of_support isOpen_Ioi (convex_Ioi 0)
    (fun x => D.valueFunction ω hμ hβμ h_succ h_reward (x, s))
    (D.value_concave ω hμ hβμ h_succ h_reward s) (fun w₀ hw₀ => ?_) w (Set.mem_Ioi.mpr hw)
  obtain ⟨φ, hφ_diff, _, hφ_eq, hφ_le⟩ :=
    D.exists_bsSupport ω hμ hβμ h_succ h_reward (Set.mem_Ioi.mp hw₀) s
  exact ⟨φ, hφ_diff, hφ_eq, hφ_le⟩

/-- **Envelope identity** at the optimum: `v*_w(w, s) = u'(c*(w, s))` for `w > 0`
(Benveniste–Scheinkman). -/
theorem value_envelope (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : D.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        ∑ s', D.trans s s' * ω (D.g a.2 s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : ℝ × Sav), a ∈ D.budget w s →
        |D.util.u a.1| ≤ C * ω (w, s))
    {w : ℝ} (hw : 0 < w) (s : Fin n) :
    deriv (fun x => D.valueFunction ω hμ hβμ h_succ h_reward (x, s)) w =
      D.util.u' (D.cStar (D.valueFunction ω hμ hβμ h_succ h_reward) w s) := by
  obtain ⟨φ, hφ_diff, hφ_hasDeriv, hφ_eq, hφ_le⟩ :=
    D.exists_bsSupport ω hμ hβμ h_succ h_reward hw s
  rw [deriv_eq_of_eventuallyLE_of_eq (fun x => D.valueFunction ω hμ hβμ h_succ h_reward (x, s)) w φ
      hφ_diff hφ_eq hφ_le (D.value_diff ω hμ hβμ h_succ h_reward hw s),
    hφ_hasDeriv.deriv]

end ConsumptionSavingsDP

end Econlib.Optimization.DynamicProgramming
