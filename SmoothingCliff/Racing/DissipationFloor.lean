import SmoothingCliff.Racing.LatticeSupport

/-!
# The floor at the paper's constant

Part (iv) of `prop:sp_allequilibria` chains two bounds: the lattice floor
`w1 G s (2 - s - q)` for the zero-payoff class, and the simpler
`(w1 - kappa) G` that the welfare comparison uses.  The chain closes on one
arithmetic identity.

Writing `s` for the lattice depth times the cost ratio, the definition of the
depth as the integer part of the reciprocal cost ratio says exactly
`s <= 1 < s + q`.  Then

    s (2 - s - q) - (1 - q) = (1 - s) (q - (1 - s)),

and both factors are nonnegative there.  So the lattice floor dominates, and in
the positive-payoff class the same bound comes from the payoff cap instead.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- **The arithmetic of the chain.**  At the integer part of the reciprocal
cost ratio the lattice floor dominates the prize net of one band's cost. -/
theorem lattice_floor_ge_prize_net_cost
    {ratio depthShare : ℝ} (_hratio : 0 < ratio)
    (hshare : depthShare ≤ 1) (hnext : 1 < depthShare + ratio) :
    1 - ratio ≤ depthShare * (2 - depthShare - ratio) := by
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - depthShare)
    (by linarith : (0 : ℝ) ≤ ratio - (1 - depthShare))]

/-- **The zero-payoff floor at the paper's constant.**  With the lattice depth
at the integer part of the reciprocal cost ratio, every equilibrium in which
both payoffs vanish dissipates at least the whole contested prize net of one
band's cost. -/
theorem zeroPayoff_dissipation_ge_prize_net_cost
    {slotWeight marginalCost : ℝ} (hweight : 0 < slotWeight)
    (hcost : 0 < marginalCost) (gap : NNReal) (depth : ℕ)
    {first second : BorelMixedStrategy}
    (hfirst : IsBorelMixedBestResponse
      slotWeight (gap : ℝ) marginalCost first second)
    (hsecond : IsBorelMixedBestResponse
      slotWeight (gap : ℝ) marginalCost second first)
    (hzeroFirst : borelExpectedPayoff
      slotWeight (gap : ℝ) marginalCost first second = 0)
    (hzeroSecond : borelExpectedPayoff
      slotWeight (gap : ℝ) marginalCost second first = 0)
    (hshare : (depth : ℝ) * (marginalCost / slotWeight) ≤ 1)
    (hnext : 1 < (depth : ℝ) * (marginalCost / slotWeight) +
      marginalCost / slotWeight) :
    (slotWeight - marginalCost) * (gap : ℝ) ≤
      borelExpectedDissipation marginalCost first second := by
  have hratio : 0 < marginalCost / slotWeight := div_pos hcost hweight
  have hfloor := lattice_floor_ge_prize_net_cost hratio hshare hnext
  have hbound := zeroPayoff_dissipation_lower_bound hweight hcost.le gap depth
    hfirst hsecond hzeroFirst hzeroSecond
  have hshape := two_mul_latticeMeanActionBound_eq
    (slotWeight := slotWeight) (marginalCost := marginalCost)
    (ne_of_gt hweight) gap depth
  rw [hshape] at hbound
  have hgapNonneg : (0 : ℝ) ≤ (gap : ℝ) := gap.coe_nonneg
  have hkey : (slotWeight - marginalCost) * (gap : ℝ) ≤
      marginalCost * ((gap : ℝ) * (depth : ℝ) *
        (2 - marginalCost / slotWeight * ((depth : ℝ) + 1))) := by
    have hexpand : marginalCost * ((gap : ℝ) * (depth : ℝ) *
        (2 - marginalCost / slotWeight * ((depth : ℝ) + 1))) =
      slotWeight * (gap : ℝ) *
        (((depth : ℝ) * (marginalCost / slotWeight)) *
          (2 - (depth : ℝ) * (marginalCost / slotWeight) -
            marginalCost / slotWeight)) := by
      field_simp
      ring
    rw [hexpand]
    have hstep : slotWeight * (gap : ℝ) * (1 - marginalCost / slotWeight) ≤
        slotWeight * (gap : ℝ) *
          (((depth : ℝ) * (marginalCost / slotWeight)) *
            (2 - (depth : ℝ) * (marginalCost / slotWeight) -
              marginalCost / slotWeight)) := by
      refine mul_le_mul_of_nonneg_left hfloor (by positivity)
    have hleft : slotWeight * (gap : ℝ) * (1 - marginalCost / slotWeight) =
        (slotWeight - marginalCost) * (gap : ℝ) := by
      field_simp
    linarith [hstep, hleft]
  rw [borelExpectedDissipation]
  linarith [hbound, hkey]

/-- **The floor in the positive-payoff class.**  The payoff cap and the payoff
identity give the same bound there. -/
theorem positive_dissipation_ge_prize_net_cost
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ)
    (hSecondRung : ∀ j ≤ depth, ∃ action ∈ second.support,
      (action : ℝ) = 2 * (j : ℝ) * gap)
    (hFirstRung : ∀ j ≤ depth, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap)
    (hFirstTerminal : ∀ action ∈ first.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap)
    (hSecondTerminal : ∀ action ∈ second.support,
      (action : ℝ) ≤ 2 * (depth : ℝ) * gap) :
    (slotWeight - marginalCost) * gap ≤
      borelExpectedDissipation marginalCost first second := by
  have hvalue := positive_dissipation_value hgap hweight hcost hnash hpos depth
    hSecondRung hFirstRung hFirstTerminal hSecondTerminal
  have hedge := window_lower_edge hgap hweight hcost hnash hpos depth
    hFirstTerminal
  rw [hvalue]
  nlinarith [hedge, hgap]

end

end SmoothingCliff.Racing
