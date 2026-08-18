import SmoothingCliff.Racing.AllMixedEquilibria

/-!
# The zero-payoff class dissipates at least the lattice amount

Part (ii) of Proposition `prop:sp_allequilibria`.  The Borel core already gives
each player a lower bound on the *opponent's* mean action whenever that player
is best-responding at payoff zero: deviating to each rung of the lattice must
not pay, and summing those deviation inequalities bounds how far back the
opponent's mass can sit.

When both payoffs vanish the bound applies in both directions, and adding the
two gives a lower bound on total dissipation that depends only on the cost
ratio.  At the lattice depth of the paper this is the displayed
`w1 G ς (2 - ς - κ̂)`.
-/

namespace SmoothingCliff.Racing

noncomputable section

/-- The lattice bound on one player's mean action, as it appears in both
directions. -/
def latticeMeanActionBound (slotWeight marginalCost : ℝ) (gap : NNReal)
    (depth : ℕ) : ℝ :=
  (depth : ℝ) * (gap : ℝ) -
    (marginalCost / slotWeight) * (gap : ℝ) *
      ((depth : ℝ) * ((depth : ℝ) + 1) / 2)

/-- **Part (ii), mean-action form.**  When both payoffs vanish, the two mean
actions together are at least twice the lattice bound. -/
theorem zeroPayoff_meanAction_sum_lower_bound
    {slotWeight marginalCost : ℝ} (hweight : 0 < slotWeight)
    (gap : NNReal) (depth : ℕ)
    {first second : BorelMixedStrategy}
    (hfirst : IsBorelMixedBestResponse
      slotWeight (gap : ℝ) marginalCost first second)
    (hsecond : IsBorelMixedBestResponse
      slotWeight (gap : ℝ) marginalCost second first)
    (hzeroFirst : borelExpectedPayoff
      slotWeight (gap : ℝ) marginalCost first second = 0)
    (hzeroSecond : borelExpectedPayoff
      slotWeight (gap : ℝ) marginalCost second first = 0) :
    2 * latticeMeanActionBound slotWeight marginalCost gap depth ≤
      first.meanAction + second.meanAction := by
  have hone := zeroPayoff_opponent_meanAction_lower_bound hweight gap depth
    hfirst hzeroFirst
  have htwo := zeroPayoff_opponent_meanAction_lower_bound hweight gap depth
    hsecond hzeroSecond
  rw [latticeMeanActionBound]
  linarith

/-- **Part (ii), dissipation form.**  Total dissipation in the zero-payoff
class is at least twice the cost of the lattice bound. -/
theorem zeroPayoff_dissipation_lower_bound
    {slotWeight marginalCost : ℝ} (hweight : 0 < slotWeight)
    (hcost : 0 ≤ marginalCost)
    (gap : NNReal) (depth : ℕ)
    {first second : BorelMixedStrategy}
    (hfirst : IsBorelMixedBestResponse
      slotWeight (gap : ℝ) marginalCost first second)
    (hsecond : IsBorelMixedBestResponse
      slotWeight (gap : ℝ) marginalCost second first)
    (hzeroFirst : borelExpectedPayoff
      slotWeight (gap : ℝ) marginalCost first second = 0)
    (hzeroSecond : borelExpectedPayoff
      slotWeight (gap : ℝ) marginalCost second first = 0) :
    marginalCost *
        (2 * latticeMeanActionBound slotWeight marginalCost gap depth) ≤
      marginalCost * (first.meanAction + second.meanAction) :=
  mul_le_mul_of_nonneg_left
    (zeroPayoff_meanAction_sum_lower_bound hweight gap depth hfirst hsecond
      hzeroFirst hzeroSecond) hcost

/-- The lattice bound in the paper's normalized form: with `ratio` the cost
ratio and `depth` the lattice length, twice the bound is
`gap * depth * (2 - ratio * (depth + 1))`. -/
theorem two_mul_latticeMeanActionBound_eq
    {slotWeight marginalCost : ℝ} (hweight : slotWeight ≠ 0)
    (gap : NNReal) (depth : ℕ) :
    2 * latticeMeanActionBound slotWeight marginalCost gap depth =
      (gap : ℝ) * (depth : ℝ) *
        (2 - (marginalCost / slotWeight) * ((depth : ℝ) + 1)) := by
  rw [latticeMeanActionBound]
  field_simp

end

end SmoothingCliff.Racing

namespace SmoothingCliff.Racing

noncomputable section

/-! ### A selection-free floor that does not wait on the window classification

Part (i) of `prop:sp_allequilibria` already gives that at least one payoff
vanishes in every equilibrium, and the lattice deviation bound turns a zero
payoff into a lower bound on the *opponent's* mean action.  Applying whichever
direction is available, and discarding the other mean action as nonnegative,
gives a floor that holds at every equilibrium, pure or mixed, with no appeal to
the positive-payoff window classification.

The constant is half of the paper's, which combines both directions.  Recovering
the full constant at a positive-payoff equilibrium needs the advantaged player's
payoff to be pinned down, and that is exactly what part (iii) supplies. -/

/-- **A universal one-sided floor.**  Every Nash equilibrium of the
strict-priority race has total mean action at least the lattice bound. -/
theorem nash_meanAction_sum_lower_bound
    {slotWeight marginalCost : ℝ} (hweight : 0 < slotWeight)
    (hcost : 0 ≤ marginalCost) (gap : NNReal) (depth : ℕ)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash
      slotWeight (gap : ℝ) marginalCost first second) :
    latticeMeanActionBound slotWeight marginalCost gap depth ≤
      first.meanAction + second.meanAction := by
  obtain ⟨-, -, hzero⟩ :=
    borelMixedNash_payoff_classification (gap := (gap : ℝ)) gap.coe_nonneg
      hcost hnash
  have hfirstNonneg := BorelMixedStrategy.meanAction_nonneg first
  have hsecondNonneg := BorelMixedStrategy.meanAction_nonneg second
  rcases hzero with hzero | hzero
  · have hbound := zeroPayoff_opponent_meanAction_lower_bound hweight gap depth
      hnash.1 hzero
    rw [latticeMeanActionBound]
    linarith
  · have hbound := zeroPayoff_opponent_meanAction_lower_bound hweight gap depth
      hnash.2 hzero
    rw [latticeMeanActionBound]
    linarith

/-- The same floor stated on dissipation. -/
theorem nash_dissipation_lower_bound
    {slotWeight marginalCost : ℝ} (hweight : 0 < slotWeight)
    (hcost : 0 ≤ marginalCost) (gap : NNReal) (depth : ℕ)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash
      slotWeight (gap : ℝ) marginalCost first second) :
    marginalCost * latticeMeanActionBound slotWeight marginalCost gap depth ≤
      borelExpectedDissipation marginalCost first second :=
  mul_le_mul_of_nonneg_left
    (nash_meanAction_sum_lower_bound hweight hcost gap depth hnash) hcost

end

end SmoothingCliff.Racing
