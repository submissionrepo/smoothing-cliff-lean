import SmoothingCliff.Racing.RentDissipationCounterexample
import SmoothingCliff.Mechanism.OneSlotStability
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Vanishing spread and pointwise-bounded best responses

Proposition `prop:rentdissipation` (i) bounds every best response by the
supremum of a marginal-cost sublevel set.  Under the paper's stated cost
hypotheses that supremum can be infinite; see
`Racing/RentDissipationCounterexample.lean`.

This file supplies the part of the repair that needs no coercivity hypothesis.
A monotone interim allocation bounded by the top prize converges, so the
endpoint spread over a fixed value band vanishes as the advantage grows.
Strict convexity of the cost then bounds every best response against a *fixed*
opponent profile, with no assumption on the growth of marginal cost.

The escape level produced here depends on the response function, hence on the
opponents' effective inputs.  It is not uniform over opponent profiles, so it
does not by itself support a bound at every rationalizable profile.
-/

namespace SmoothingCliff.Racing

open Filter Topology

noncomputable section

/-- A monotone allocation bounded above converges, so the endpoint spread over
a fixed band vanishes as the advantage grows. -/
theorem allocationSpread_tendsto_zero
    (allocation : ℝ → ℝ) (hMono : Monotone allocation)
    (hBdd : BddAbove (Set.range allocation)) (reserve value : ℝ) :
    Tendsto (fun a => allocation (value + a) - allocation (reserve + a))
      atTop (𝓝 0) := by
  have hlimit : Tendsto allocation atTop (𝓝 (⨆ u : ℝ, allocation u)) :=
    tendsto_atTop_ciSup hMono hBdd
  have hshift (q : ℝ) : Tendsto (fun a : ℝ => q + a) atTop atTop :=
    tendsto_atTop_add_const_left _ q tendsto_id
  have hvalue := hlimit.comp (hshift value)
  have hreserve := hlimit.comp (hshift reserve)
  simpa using hvalue.sub hreserve

/-- The range hypothesis of the paper's allocation class bounds the range. -/
theorem bddAbove_range_of_le
    {allocation : ℝ → ℝ} {weight : ℝ}
    (hRange : ∀ u, allocation u ≤ weight) :
    BddAbove (Set.range allocation) := by
  refine ⟨weight, ?_⟩
  rintro y ⟨u, rfl⟩
  exact hRange u

/-- A vanishing spread and a marginal cost eventually bounded below by a
positive constant are strictly separated beyond a finite action level. -/
theorem exists_spread_lt_marginalCost_bound
    (allocation cost : ℝ → ℝ) (hMono : Monotone allocation)
    (hBdd : BddAbove (Set.range allocation))
    {reserve value floorAction floorSlope : ℝ}
    (hFloorAction : 0 ≤ floorAction) (hFloorSlope : 0 < floorSlope)
    (hSlope : ∀ a, floorAction < a → floorSlope ≤ deriv cost a) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ∀ a, bound < a →
      allocation (value + a) - allocation (reserve + a) < deriv cost a := by
  have hzero := allocationSpread_tendsto_zero allocation hMono hBdd reserve value
  have hEventually : ∀ᶠ a in atTop,
      allocation (value + a) - allocation (reserve + a) < floorSlope :=
    hzero.eventually_lt_const hFloorSlope
  obtain ⟨A, hA⟩ := eventually_atTop.mp hEventually
  refine ⟨max A floorAction, le_trans hFloorAction (le_max_right _ _), ?_⟩
  intro a ha
  have h1 : A ≤ a := le_of_lt (lt_of_le_of_lt (le_max_left _ _) ha)
  have h2 : floorAction < a := lt_of_le_of_lt (le_max_right _ _) ha
  exact lt_of_lt_of_le (hA a h1) (hSlope a h2)

/-- Best-response bound driven by the *actual* endpoint spread rather than by
the uniform Lipschitz cap.  No hypothesis on the growth of marginal cost. -/
theorem bestResponse_le_of_spread_lt_marginalCost
    (allocation cost : ℝ → ℝ) (hAllocationCont : Continuous allocation)
    {reserve value action bound : ℝ}
    (hBound : 0 ≤ bound)
    (hCostDiff : DifferentiableAt ℝ cost action)
    (hAbove : ∀ a : ℝ, bound < a →
      allocation (value + a) - allocation (reserve + a) < deriv cost a)
    (hBest : NonnegativeBestResponse
      (advantageUtility allocation cost reserve value) action) :
    action ≤ bound := by
  by_contra hNot
  have hPast : bound < action := lt_of_not_ge hNot
  have hPositive : 0 < action := lt_of_le_of_lt hBound hPast
  have hUtilityDeriv := advantageUtility_hasDerivAt allocation cost
    hAllocationCont (reserve := reserve) (value := value)
    (advantage := action) hCostDiff.hasDerivAt
  have hZero := positive_bestResponse_has_zero_deriv hPositive hBest hUtilityDeriv
  have hStrict := hAbove action hPast
  linarith

/-! ### The escape level cannot be made uniform over opponent profiles

The bound above is built from a fixed response function, so it depends on the
opponents' effective inputs.  This section shows the dependence is essential.
The one-slot Luce allocation is invariant under a common translation of the own
score and the opponents' log-intensity, so the endpoint spread available to a
bidder is the same at every advantage level.  Against the asymptotically linear
cost of `RentDissipationCounterexample.lean`, whose marginal cost never reaches
one, marginal utility is therefore strictly positive at arbitrarily large
advantages.  No single escape level works for all opponent profiles. -/

theorem luceIntensity_shift (reserve temperature u h : ℝ) :
    Mechanism.luceIntensity reserve temperature (u + h) =
      Mechanism.luceIntensity reserve temperature u *
        Real.exp (h / temperature) := by
  have hsplit : (u + h - reserve) / temperature =
      (u - reserve) / temperature + h / temperature := by ring
  rw [Mechanism.luceIntensity, Mechanism.luceIntensity, hsplit, Real.exp_add]

/-- Translation invariance of the one-slot Luce allocation: raising the own
score by `h` and the opponents' intensity by the matching factor leaves the
interim allocation unchanged. -/
theorem oneSlotLuceAllocation_shift
    (weight reserve temperature opponentIntensity u h : ℝ)
    (hOpponent : 0 ≤ opponentIntensity) :
    Mechanism.oneSlotLuceAllocation weight reserve temperature
        (opponentIntensity * Real.exp (h / temperature)) (u + h) =
      Mechanism.oneSlotLuceAllocation weight reserve temperature
        opponentIntensity u := by
  rw [Mechanism.oneSlotLuceAllocation, Mechanism.oneSlotLuceAllocation,
    Mechanism.oneSlotLuceProbability, Mechanism.oneSlotLuceProbability,
    luceIntensity_shift]
  set I := Mechanism.luceIntensity reserve temperature u with hI
  set E := Real.exp (h / temperature) with hE
  have hIpos : 0 < I := Mechanism.luceIntensity_pos _ _ _
  have hEpos : 0 < E := Real.exp_pos _
  have hden : I + opponentIntensity ≠ 0 := by positivity
  have hdenE : I * E + opponentIntensity * E ≠ 0 := by
    have : I * E + opponentIntensity * E = (I + opponentIntensity) * E := by ring
    rw [this]
    exact mul_ne_zero hden (ne_of_gt hEpos)
  field_simp

/-- The spread available in the calibrated centered window exceeds one. -/
theorem centeredWindow_spread_gt_one :
    1 < Mechanism.oneSlotLuceAllocation 4 0 1 (Real.exp 2) 4 -
      Mechanism.oneSlotLuceAllocation 4 0 1 (Real.exp 2) 0 := by
  have h4 : Mechanism.luceIntensity 0 1 4 = Real.exp 2 * Real.exp 2 := by
    rw [Mechanism.luceIntensity, ← Real.exp_add]; norm_num
  have h0 : Mechanism.luceIntensity 0 1 0 = 1 := by
    rw [Mechanism.luceIntensity]; norm_num
  simp only [Mechanism.oneSlotLuceAllocation, Mechanism.oneSlotLuceProbability,
    h4, h0]
  have hx : (3 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  set x := Real.exp 2 with hxdef
  have hd1 : x * x + x ≠ 0 := by nlinarith
  have hd2 : (1 : ℝ) + x ≠ 0 := by linarith
  have hid : 4 * (x * x / (x * x + x)) - 4 * (1 / (1 + x)) - 1
      = (3 * x - 5) / (x + 1) := by
    field_simp
    ring
  have hpos : 0 < (3 * x - 5) / (x + 1) :=
    div_pos (by linarith) (by linarith)
  linarith

/-- **No escape level is uniform over opponent profiles.**  For the calibrated
one-slot Luce rule and the asymptotically linear cost of
`RentDissipationCounterexample.lean`, every candidate bound `B` is exceeded:
there is an opponent intensity and an advantage above `B` at which marginal
utility is strictly positive.  Hence the pointwise bound of
`bestResponse_le_of_spread_lt_marginalCost` cannot be promoted to a bound at
every rationalizable profile without a hypothesis on the growth of marginal
cost. -/
theorem no_uniform_escape_level (B : ℝ) :
    ∃ opponentIntensity a : ℝ,
      0 ≤ opponentIntensity ∧ B < a ∧
      deriv asymptoticallyLinearCost a <
        Mechanism.oneSlotLuceAllocation 4 0 1 opponentIntensity (4 + a) -
          Mechanism.oneSlotLuceAllocation 4 0 1 opponentIntensity (0 + a) := by
  have hB : B < max B 0 + 1 := by
    have : B ≤ max B 0 := le_max_left _ _
    linarith
  refine ⟨Real.exp 2 * Real.exp ((max B 0 + 1) / 1), max B 0 + 1,
    by positivity, hB, ?_⟩
  rw [oneSlotLuceAllocation_shift 4 0 1 (Real.exp 2) 4 (max B 0 + 1)
        (le_of_lt (Real.exp_pos 2)),
      oneSlotLuceAllocation_shift 4 0 1 (Real.exp 2) 0 (max B 0 + 1)
        (le_of_lt (Real.exp_pos 2))]
  have hderiv : deriv asymptoticallyLinearCost (max B 0 + 1)
      = 1 - Real.exp (-(max B 0 + 1)) := by
    have h := (asymptoticallyLinearCost_hasDerivAt (max B 0 + 1)).deriv
    simpa [asymptoticallyLinearMarginalCost] using h
  have hexp : 0 < Real.exp (-(max B 0 + 1)) := Real.exp_pos _
  have hspread := centeredWindow_spread_gt_one
  rw [hderiv]
  linarith

end

end SmoothingCliff.Racing
