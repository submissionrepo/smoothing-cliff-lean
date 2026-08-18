import SmoothingCliff.Racing.BottomCondition

/-!
# The lattice ceiling on cumulative mass

The upper half of the support recursion (S) in `prop:sp_allequilibria` (iii).
A player earning zero cannot profit by moving to the rung `k` bands up, and
every opponent action at least one full band below that rung hands over the
whole band.  So the opponent's cumulative mass on any set of actions a full
band below the rung is capped by `k` times the cost ratio.

Applied to the lattice `0, G, ..., (k-1)G` this is the ceiling `A_{k-1} <= k q`
the recursion uses.  It needs no lattice hypothesis on the support: the
inequality holds at every equilibrium, and it is part (i) that supplies a player
with zero payoff at each of them.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- Every opponent action a full band below the own action hands over the whole
contested band. -/
theorem strictPriorityCapturedGap_ge_finset_indicator
    {gap : ℝ} (hgap : 0 ≤ gap) {action : NNReal} (points : Finset NNReal)
    (hpoints : ∀ point ∈ points, (point : ℝ) + gap ≤ (action : ℝ))
    (rival : NNReal) :
    gap * (points : Set NNReal).indicator (fun _ => (1 : ℝ)) rival ≤
      strictPriorityCapturedGap gap (action : ℝ) (rival : ℝ) := by
  by_cases hrival : rival ∈ (points : Set NNReal)
  · have hle := hpoints rival (Finset.mem_coe.mp hrival)
    rw [Set.indicator_of_mem hrival, mul_one, strictPriorityCapturedGap,
      max_eq_left (by linarith : (0 : ℝ) ≤ (action : ℝ) - (rival : ℝ)),
      min_eq_right (by linarith : gap ≤ (action : ℝ) - (rival : ℝ))]
  · rw [Set.indicator_of_notMem hrival, mul_zero, strictPriorityCapturedGap]
    exact le_min (le_max_right _ _) hgap

/-- The expected captured band dominates the whole band times the opponent's
mass on those actions. -/
theorem borelPureExpectedCapturedGap_ge_finset_mass
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy)
    {action : NNReal} (points : Finset NNReal)
    (hpoints : ∀ point ∈ points, (point : ℝ) + gap ≤ (action : ℝ)) :
    gap * ((opponent.law : Measure NNReal) (points : Set NNReal)).toReal ≤
      borelPureExpectedCapturedGap gap opponent action := by
  have hmeas : MeasurableSet (points : Set NNReal) := points.measurableSet
  have hindicator :
      ∫ rival : NNReal,
          gap * (points : Set NNReal).indicator (fun _ => (1 : ℝ)) rival
          ∂(opponent.law : Measure NNReal) =
        gap * ((opponent.law : Measure NNReal) (points : Set NNReal)).toReal := by
    rw [integral_const_mul]
    simp only [← Pi.one_def]
    rw [integral_indicator_one hmeas, measureReal_def]
  rw [borelPureExpectedCapturedGap, ← hindicator]
  refine integral_mono ?_
    (borelPureCapturedGap_integrable_rival hgap opponent action) ?_
  · exact ((integrable_const (1 : ℝ)).indicator hmeas).const_mul _
  · exact fun rival =>
      strictPriorityCapturedGap_ge_finset_indicator hgap points hpoints rival

/-- **The cumulative ceiling.**  A player earning zero caps the opponent's mass
on any set of actions a full band below a deviation: that mass, valued at the
slot weight times the band, is at most the cost of the deviation. -/
theorem zeroPayoff_finset_mass_bound
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (hweight : 0 < slotWeight)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    (hzero : borelExpectedPayoff slotWeight gap marginalCost own opponent = 0)
    {action : NNReal} (points : Finset NNReal)
    (hpoints : ∀ point ∈ points, (point : ℝ) + gap ≤ (action : ℝ)) :
    slotWeight * gap *
        ((opponent.law : Measure NNReal) (points : Set NNReal)).toReal ≤
      marginalCost * (action : ℝ) := by
  have hdeviation := hbest action
  rw [hzero, borelPureExpectedPayoff] at hdeviation
  have hmass :=
    borelPureExpectedCapturedGap_ge_finset_mass hgap opponent points hpoints
  nlinarith [mul_le_mul_of_nonneg_left hmass hweight.le]

/-- The lattice of rungs `0, G, ..., (k-1)G`. -/
def borelLatticeRungs (gap : NNReal) (depth : ℕ) : Finset NNReal :=
  (Finset.range depth).image fun index : ℕ => (index : NNReal) * gap

theorem borelLatticeRungs_spec {gap : NNReal} {depth : ℕ} {point : NNReal}
    (hpoint : point ∈ borelLatticeRungs gap depth) :
    (point : ℝ) + (gap : ℝ) ≤ (depth : ℝ) * (gap : ℝ) := by
  rw [borelLatticeRungs, Finset.mem_image] at hpoint
  obtain ⟨index, hindex, rfl⟩ := hpoint
  have hlt : index < depth := Finset.mem_range.mp hindex
  have hle : (index : ℝ) + 1 ≤ (depth : ℝ) := by exact_mod_cast hlt
  have hgapNonneg : (0 : ℝ) ≤ (gap : ℝ) := gap.coe_nonneg
  push_cast
  nlinarith

/-- **The lattice ceiling (S), upper half.**  At every equilibrium the player
earning zero caps the opponent's cumulative mass on the first `k` rungs at `k`
times the cost ratio. -/
theorem zeroPayoff_latticeRungs_mass_bound
    {slotWeight marginalCost : ℝ} (hweight : 0 < slotWeight)
    (gap : NNReal) (depth : ℕ)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse
      slotWeight (gap : ℝ) marginalCost own opponent)
    (hzero : borelExpectedPayoff
      slotWeight (gap : ℝ) marginalCost own opponent = 0) :
    slotWeight *
        ((opponent.law : Measure NNReal)
          (borelLatticeRungs gap depth : Set NNReal)).toReal ≤
      marginalCost * (depth : ℝ) ∨ (gap : ℝ) = 0 := by
  rcases eq_or_lt_of_le gap.coe_nonneg with hgapZero | hgapPos
  · exact Or.inr hgapZero.symm
  refine Or.inl ?_
  have hbound :=
    zeroPayoff_finset_mass_bound (gap := (gap : ℝ)) gap.coe_nonneg hweight
      hbest hzero (action := (depth : NNReal) * gap)
      (borelLatticeRungs gap depth)
      (fun point hpoint => by
        have := borelLatticeRungs_spec hpoint
        push_cast
        linarith)
  have hcoe : (((depth : NNReal) * gap : NNReal) : ℝ) = (depth : ℝ) * (gap : ℝ) := by
    push_cast
    ring
  rw [hcoe] at hbound
  have hcancel :
      slotWeight * (gap : ℝ) *
          ((opponent.law : Measure NNReal)
            (borelLatticeRungs gap depth : Set NNReal)).toReal ≤
        marginalCost * (depth : ℝ) * (gap : ℝ) := by
    nlinarith [hbound]
  exact le_of_mul_le_mul_right (by nlinarith [hcancel]) hgapPos

/-- **The positive payoff is capped by the whole contested prize net of one
band's cost.**  The bottom condition prices the payoff by the opponent's atom
at zero, and an atom is at most one. -/
theorem payoff_le_of_pos
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    borelExpectedPayoff slotWeight gap marginalCost first second ≤
      (slotWeight - marginalCost) * gap := by
  obtain ⟨-, hvalue⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  have hatom := second.cdfReal_le_one 0
  have hstep : slotWeight * second.cdfReal 0 - marginalCost ≤
      slotWeight - marginalCost := by
    nlinarith [mul_le_mul_of_nonneg_left hatom hweight.le]
  rw [hvalue]
  exact mul_le_mul_of_nonneg_right hstep hgap.le

/-- The opponent's atom at zero strictly exceeds the cost ratio. -/
theorem atom_gt_cost_ratio_of_payoff_pos
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    marginalCost < slotWeight * second.cdfReal 0 := by
  obtain ⟨-, hvalue⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  rw [hvalue] at hpos
  nlinarith [hgap, hpos]

end

end SmoothingCliff.Racing
