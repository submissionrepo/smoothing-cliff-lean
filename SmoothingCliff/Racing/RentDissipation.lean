import SmoothingCliff.Racing.Spread
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.BigOperators.Field

/-!
# Dissipation bounds and the no-race threshold

This file formalizes the generic analytic and best-response content of
Proposition `prop:rentdissipation` in *Smoothing the Cliff*.  Opponents are
held fixed inside the response function `allocation : ℝ → ℝ`, exactly as in
`Spread.lean`.  Thus every theorem below is uniform over opponent profiles:
the particular response function is arbitrary subject to the paper's
monotonicity, range, and Lipschitz hypotheses.
-/

namespace SmoothingCliff.Racing

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- A global best response over the paper's action set `[0,∞)`. -/
def NonnegativeBestResponse (utility : ℝ → ℝ) (action : ℝ) : Prop :=
  0 ≤ action ∧ IsMaxOn utility (Set.Ici 0) action

/-- A positive best response is an interior maximizer, so its utility
derivative vanishes. -/
theorem positive_bestResponse_has_zero_deriv
    {utility : ℝ → ℝ} {action derivative : ℝ}
    (hAction : 0 < action)
    (hBest : NonnegativeBestResponse utility action)
    (hDeriv : HasDerivAt utility derivative action) :
    derivative = 0 := by
  have hLocal : IsLocalMax utility action :=
    hBest.2.isLocalMax (Ici_mem_nhds hAction)
  exact hLocal.hasDerivAt_eq_zero hDeriv

/-- Proposition `prop:rentdissipation` (i), first-order part.  At every
positive best response, marginal cost is no larger than `(v-r) S`. -/
theorem positive_bestResponse_marginalCost_le
    (allocation cost : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value action : ℝ}
    (hValue : reserve ≤ value) (hAction : 0 < action)
    (hCostDiff : DifferentiableAt ℝ cost action)
    (hBest : NonnegativeBestResponse
      (advantageUtility allocation cost reserve value) action) :
    deriv cost action ≤ (value - reserve) * (sensitivity : ℝ) := by
  have hUtilityDeriv := advantageUtility_hasDerivAt allocation cost
    hLip.continuous (reserve := reserve) (value := value)
      (advantage := action) hCostDiff.hasDerivAt
  have hFirstOrder := positive_bestResponse_has_zero_deriv
    hAction hBest hUtilityDeriv
  have hSpread := allocationSpread_bounds allocation weight sensitivity
    hMono hRange hLip (advantage := action) hValue
  have hSlopeBound :
      allocation (value + action) - allocation (reserve + action) ≤
        (value - reserve) * (sensitivity : ℝ) :=
    hSpread.2.trans (min_le_right _ _)
  linarith

/-- Marginal costs of a differentiable strictly convex cost are strictly
increasing on the feasible action set. -/
theorem strictMonoOn_deriv_of_strictConvexCost
    {cost : ℝ → ℝ}
    (hStrictConvex : StrictConvexOn ℝ (Set.Ici 0) cost)
    (hDifferentiable : ∀ a : ℝ, 0 ≤ a → DifferentiableAt ℝ cost a) :
    StrictMonoOn (deriv cost) (Set.Ici 0) := by
  exact hStrictConvex.strictMonoOn_deriv
    (fun a ha => hDifferentiable a ha)

/-- Under the no-race threshold, truthful utility is strictly decreasing over
all feasible positive investments.  Strict convexity is used exactly where
the paper uses `c'(a) > c'(0)` for `a > 0`. -/
theorem advantageUtility_strictAntiOn_of_threshold
    (allocation cost : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value : ℝ} (hValue : reserve ≤ value)
    (hStrictConvex : StrictConvexOn ℝ (Set.Ici 0) cost)
    (hDifferentiable : ∀ a : ℝ, 0 ≤ a → DifferentiableAt ℝ cost a)
    (hThreshold :
      (value - reserve) * (sensitivity : ℝ) ≤ deriv cost 0) :
    StrictAntiOn (advantageUtility allocation cost reserve value)
      (Set.Ici 0) := by
  have hCostDerivStrict : StrictMonoOn (deriv cost) (Set.Ici 0) :=
    strictMonoOn_deriv_of_strictConvexCost hStrictConvex hDifferentiable
  apply strictAntiOn_of_deriv_neg (convex_Ici 0)
  · intro action hAction
    exact (advantageUtility_hasDerivAt allocation cost hLip.continuous
      (reserve := reserve) (value := value) (advantage := action)
      (hDifferentiable action hAction).hasDerivAt).continuousAt.continuousWithinAt
  · intro action hInterior
    have hAction : 0 < action := by
      simpa only [interior_Ici, Set.mem_Ioi] using hInterior
    have hCostStrict : deriv cost 0 < deriv cost action :=
      hCostDerivStrict (by simp) hAction.le hAction
    have hSpread := allocationSpread_bounds allocation weight sensitivity
      hMono hRange hLip (advantage := action) hValue
    have hSlopeBound :
        allocation (value + action) - allocation (reserve + action) ≤
          (value - reserve) * (sensitivity : ℝ) :=
      hSpread.2.trans (min_le_right _ _)
    rw [deriv_advantageUtility allocation cost hLip.continuous
      (reserve := reserve) (value := value) (advantage := action)
      (hDifferentiable action hAction.le).hasDerivAt]
    linarith

/-- Proposition `prop:rentdissipation` (iii), strict-dominance form.  For
every fixed opponent profile encoded by `allocation`, every positive action
gives strictly less utility than zero. -/
theorem positive_action_utility_lt_zero_of_threshold
    (allocation cost : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value action : ℝ} (hValue : reserve ≤ value)
    (hAction : 0 < action)
    (hStrictConvex : StrictConvexOn ℝ (Set.Ici 0) cost)
    (hDifferentiable : ∀ a : ℝ, 0 ≤ a → DifferentiableAt ℝ cost a)
    (hThreshold :
      (value - reserve) * (sensitivity : ℝ) ≤ deriv cost 0) :
    advantageUtility allocation cost reserve value action <
      advantageUtility allocation cost reserve value 0 := by
  exact (advantageUtility_strictAntiOn_of_threshold allocation cost
    weight sensitivity hMono hRange hLip hValue hStrictConvex
    hDifferentiable hThreshold) (by simp) hAction.le hAction

/-- Hence zero is the unique best response against every opponent profile. -/
theorem bestResponse_iff_zero_of_threshold
    (allocation cost : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value action : ℝ} (hValue : reserve ≤ value)
    (hStrictConvex : StrictConvexOn ℝ (Set.Ici 0) cost)
    (hDifferentiable : ∀ a : ℝ, 0 ≤ a → DifferentiableAt ℝ cost a)
    (hThreshold :
      (value - reserve) * (sensitivity : ℝ) ≤ deriv cost 0) :
    NonnegativeBestResponse
      (advantageUtility allocation cost reserve value) action ↔
      action = 0 := by
  let utility := advantageUtility allocation cost reserve value
  have hStrictAnti : StrictAntiOn utility (Set.Ici 0) :=
    advantageUtility_strictAntiOn_of_threshold allocation cost
      weight sensitivity hMono hRange hLip hValue hStrictConvex
      hDifferentiable hThreshold
  constructor
  · intro hBest
    apply le_antisymm _ hBest.1
    by_contra hNot
    have hPositive : 0 < action := lt_of_not_ge hNot
    have hStrict := hStrictAnti (by simp) hBest.1 hPositive
    have hOptimal := hBest.2 (by simp : (0 : ℝ) ∈ Set.Ici 0)
    exact (not_lt_of_ge hOptimal) hStrict
  · rintro rfl
    refine ⟨le_refl 0, ?_⟩
    intro deviation hDeviation
    have hDeviationNonneg : 0 ≤ deviation := hDeviation
    rcases eq_or_lt_of_le hDeviationNonneg with hZero | hPositive
    · simp [hZero]
    · exact (hStrictAnti (by simp) hDeviation hPositive).le

/-- The displayed PL temperature condition implies the derivative threshold
`(v-r) w₁/(eτ) ≤ c'(0)` for one agent. -/
theorem pl_derivative_threshold_of_temperature_ge
    (weight temperature : NNReal) {premium marginalCostAtZero : ℝ}
    (hTemperature : 0 < temperature) (hMarginalCost : 0 < marginalCostAtZero)
    (hTemperatureThreshold :
      (weight : ℝ) / Real.exp 1 * (premium / marginalCostAtZero) ≤
        (temperature : ℝ)) :
    premium * (plSensitivity weight temperature : ℝ) ≤ marginalCostAtZero := by
  have hExp : 0 < Real.exp 1 := Real.exp_pos 1
  have hTau : 0 < (temperature : ℝ) := by exact_mod_cast hTemperature
  have hFirst :
      ((weight : ℝ) / Real.exp 1 * premium) / marginalCostAtZero ≤
        (temperature : ℝ) := by
    convert hTemperatureThreshold using 1
    field_simp [ne_of_gt hMarginalCost]
  have hSecond :
      (weight : ℝ) / Real.exp 1 * premium ≤
        (temperature : ℝ) * marginalCostAtZero :=
    (div_le_iff₀ hMarginalCost).mp hFirst
  have hThird :
      (weight : ℝ) * premium ≤
        ((temperature : ℝ) * marginalCostAtZero) * Real.exp 1 := by
    apply (div_le_iff₀ hExp).mp
    convert hSecond using 1
    ring
  have hNumerator :
      premium * (weight : ℝ) ≤
        marginalCostAtZero * (Real.exp 1 * (temperature : ℝ)) := by
    calc
      premium * (weight : ℝ) = (weight : ℝ) * premium := by ring
      _ ≤ ((temperature : ℝ) * marginalCostAtZero) * Real.exp 1 := hThird
      _ = marginalCostAtZero * (Real.exp 1 * (temperature : ℝ)) := by ring
  change premium *
      ((weight : ℝ) / (Real.exp 1 * (temperature : ℝ))) ≤
        marginalCostAtZero
  calc
    premium * ((weight : ℝ) / (Real.exp 1 * (temperature : ℝ))) =
        (premium * (weight : ℝ)) /
          (Real.exp 1 * (temperature : ℝ)) := by ring
    _ ≤ marginalCostAtZero :=
      (div_le_iff₀ (mul_pos hExp hTau)).2 hNumerator

/-- PL specialization of the no-race theorem at the paper's displayed
temperature certificate. -/
theorem pl_bestResponse_iff_zero_of_temperature_ge
    (allocation cost : ℝ → ℝ) (weight temperature : NNReal)
    (hTemperature : 0 < temperature)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith (plSensitivity weight temperature) allocation)
    {reserve value action : ℝ} (hValue : reserve ≤ value)
    (hStrictConvex : StrictConvexOn ℝ (Set.Ici 0) cost)
    (hDifferentiable : ∀ a : ℝ, 0 ≤ a → DifferentiableAt ℝ cost a)
    (hMarginalCost : 0 < deriv cost 0)
    (hTemperatureThreshold :
      (weight : ℝ) / Real.exp 1 *
          ((value - reserve) / deriv cost 0) ≤ (temperature : ℝ)) :
    NonnegativeBestResponse
      (advantageUtility allocation cost reserve value) action ↔ action = 0 := by
  apply bestResponse_iff_zero_of_threshold allocation cost weight
    (plSensitivity weight temperature) hMono hRange hLip hValue
    hStrictConvex hDifferentiable
  exact pl_derivative_threshold_of_temperature_ge weight temperature
    hTemperature hMarginalCost hTemperatureThreshold

/-- Quadratic latency cost `a²/(2γ)`. -/
def quadraticAdvantageCost (capacity action : ℝ) : ℝ :=
  action ^ 2 / (2 * capacity)

theorem quadraticAdvantageCost_hasDerivAt
    {capacity action : ℝ} (hCapacity : 0 < capacity) :
    HasDerivAt (quadraticAdvantageCost capacity) (action / capacity) action := by
  have h := ((hasDerivAt_id action).mul
    (hasDerivAt_id action)).div_const (2 * capacity)
  convert h using 1
  · ext x
    simp [quadraticAdvantageCost, id_eq, pow_two]
  · simp only [id_eq, one_mul, mul_one]
    field_simp [ne_of_gt hCapacity]
    ring

/-- Generic version of the paper's generalized action bound.  If marginal
cost is strictly above the spread certificate past `bound`, no best response
can lie past `bound`. -/
theorem bestResponse_le_of_marginalCost_gt_threshold
    (allocation cost : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value action bound : ℝ}
    (hValue : reserve ≤ value) (hBound : 0 ≤ bound)
    (hCostDiff : DifferentiableAt ℝ cost action)
    (hAbove : ∀ a : ℝ, bound < a →
      (value - reserve) * (sensitivity : ℝ) < deriv cost a)
    (hBest : NonnegativeBestResponse
      (advantageUtility allocation cost reserve value) action) :
    action ≤ bound := by
  by_contra hNot
  have hPast : bound < action := lt_of_not_ge hNot
  have hPositive : 0 < action := lt_of_le_of_lt hBound hPast
  have hMarginalCost := positive_bestResponse_marginalCost_le
    allocation cost weight sensitivity hMono hRange hLip hValue
    hPositive hCostDiff hBest
  exact (not_lt_of_ge hMarginalCost) (hAbove action hPast)

/-- If cost is increasing, the abstract action bound immediately gives the
paper's pointwise dissipation bound `c(a) ≤ c(bound)`. -/
theorem bestResponse_cost_le_of_marginalCost_gt_threshold
    (allocation cost : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value action bound : ℝ}
    (hValue : reserve ≤ value) (hBound : 0 ≤ bound)
    (hCostMono : MonotoneOn cost (Set.Ici 0))
    (hCostDiff : DifferentiableAt ℝ cost action)
    (hAbove : ∀ a : ℝ, bound < a →
      (value - reserve) * (sensitivity : ℝ) < deriv cost a)
    (hBest : NonnegativeBestResponse
      (advantageUtility allocation cost reserve value) action) :
    cost action ≤ cost bound := by
  apply hCostMono hBest.1 hBound
  exact bestResponse_le_of_marginalCost_gt_threshold allocation cost
    weight sensitivity hMono hRange hLip hValue hBound hCostDiff hAbove hBest

/-- Finite-agent version of the generic dissipation bound.  `bound i` may be
instantiated by any finite marginal-cost sublevel bound satisfying `hAbove`;
this avoids silently treating an unbounded real supremum as a finite action. -/
theorem sum_bestResponse_cost_le_of_bounds
    {ι : Type*} [Fintype ι]
    (allocation cost : ι → ℝ → ℝ) (weight sensitivity : NNReal)
    (value action bound : ι → ℝ) (reserve : ℝ)
    (hMono : ∀ i, Monotone (allocation i))
    (hRange : ∀ i u,
      0 ≤ allocation i u ∧ allocation i u ≤ (weight : ℝ))
    (hLip : ∀ i, LipschitzWith sensitivity (allocation i))
    (hValue : ∀ i, reserve ≤ value i)
    (hBound : ∀ i, 0 ≤ bound i)
    (hCostMono : ∀ i, MonotoneOn (cost i) (Set.Ici 0))
    (hCostDiff : ∀ i, DifferentiableAt ℝ (cost i) (action i))
    (hAbove : ∀ i a, bound i < a →
      (value i - reserve) * (sensitivity : ℝ) < deriv (cost i) a)
    (hBest : ∀ i, NonnegativeBestResponse
      (advantageUtility (allocation i) (cost i) reserve (value i)) (action i)) :
    ∑ i, cost i (action i) ≤ ∑ i, cost i (bound i) := by
  apply Finset.sum_le_sum
  intro i _
  exact bestResponse_cost_le_of_marginalCost_gt_threshold
    (allocation i) (cost i) weight sensitivity (hMono i) (hRange i)
    (hLip i) (hValue i) (hBound i) (hCostMono i) (hCostDiff i)
    (hAbove i) (hBest i)

/-- For quadratic cost, every best response, including the zero corner,
satisfies `a ≤ γ (v-r) S`. -/
theorem quadratic_bestResponse_action_le
    (allocation : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value capacity action : ℝ}
    (hValue : reserve ≤ value) (hCapacity : 0 < capacity)
    (hBest : NonnegativeBestResponse
      (advantageUtility allocation (quadraticAdvantageCost capacity)
        reserve value) action) :
    action ≤ capacity * (value - reserve) * (sensitivity : ℝ) := by
  by_cases hZero : action = 0
  · subst action
    exact mul_nonneg
      (mul_nonneg hCapacity.le (sub_nonneg.mpr hValue)) sensitivity.coe_nonneg
  · have hPositive : 0 < action :=
      lt_of_le_of_ne hBest.1 (Ne.symm hZero)
    have hMarginalCost := positive_bestResponse_marginalCost_le
      allocation (quadraticAdvantageCost capacity) weight sensitivity
      hMono hRange hLip hValue hPositive
      (quadraticAdvantageCost_hasDerivAt hCapacity).differentiableAt hBest
    rw [(quadraticAdvantageCost_hasDerivAt
      (action := action) hCapacity).deriv] at hMarginalCost
    have hScaled := (div_le_iff₀ hCapacity).mp hMarginalCost
    nlinarith

/-- The per-agent quadratic dissipation bound
`c(a) ≤ γ (v-r)² S² / 2`. -/
theorem quadratic_bestResponse_cost_le
    (allocation : ℝ → ℝ) (weight sensitivity : NNReal)
    (hMono : Monotone allocation)
    (hRange : ∀ u, 0 ≤ allocation u ∧ allocation u ≤ (weight : ℝ))
    (hLip : LipschitzWith sensitivity allocation)
    {reserve value capacity action : ℝ}
    (hValue : reserve ≤ value) (hCapacity : 0 < capacity)
    (hBest : NonnegativeBestResponse
      (advantageUtility allocation (quadraticAdvantageCost capacity)
        reserve value) action) :
    quadraticAdvantageCost capacity action ≤
      capacity * (value - reserve) ^ 2 * (sensitivity : ℝ) ^ 2 / 2 := by
  let bound : ℝ := capacity * (value - reserve) * (sensitivity : ℝ)
  have hBoundNonneg : 0 ≤ bound := by
    exact mul_nonneg
      (mul_nonneg hCapacity.le (sub_nonneg.mpr hValue)) sensitivity.coe_nonneg
  have hActionBound : action ≤ bound := by
    exact quadratic_bestResponse_action_le allocation weight sensitivity
      hMono hRange hLip hValue hCapacity hBest
  have hSquare : action ^ 2 ≤ bound ^ 2 :=
    (sq_le_sq₀ hBest.1 hBoundNonneg).2 hActionBound
  unfold quadraticAdvantageCost
  calc
    action ^ 2 / (2 * capacity) ≤ bound ^ 2 / (2 * capacity) := by
      exact (div_le_div_iff_of_pos_right
        (mul_pos (by norm_num) hCapacity)).2 hSquare
    _ = capacity * (value - reserve) ^ 2 *
        (sensitivity : ℝ) ^ 2 / 2 := by
      dsimp [bound]
      field_simp [ne_of_gt hCapacity]

/-- Summing the preceding pointwise bound yields the paper's finite-agent
quadratic dissipation certificate. -/
theorem sum_quadratic_bestResponse_cost_le
    {ι : Type*} [Fintype ι]
    (allocation : ι → ℝ → ℝ) (weight sensitivity : NNReal)
    (value capacity action : ι → ℝ) (reserve : ℝ)
    (hMono : ∀ i, Monotone (allocation i))
    (hRange : ∀ i u,
      0 ≤ allocation i u ∧ allocation i u ≤ (weight : ℝ))
    (hLip : ∀ i, LipschitzWith sensitivity (allocation i))
    (hValue : ∀ i, reserve ≤ value i)
    (hCapacity : ∀ i, 0 < capacity i)
    (hBest : ∀ i, NonnegativeBestResponse
      (advantageUtility (allocation i)
        (quadraticAdvantageCost (capacity i)) reserve (value i)) (action i)) :
    ∑ i, quadraticAdvantageCost (capacity i) (action i) ≤
      ∑ i, capacity i * (value i - reserve) ^ 2 *
        (sensitivity : ℝ) ^ 2 / 2 := by
  apply Finset.sum_le_sum
  intro i _
  exact quadratic_bestResponse_cost_le (allocation i) weight sensitivity
    (hMono i) (hRange i) (hLip i) (hValue i) (hCapacity i) (hBest i)

end

end SmoothingCliff.Racing
