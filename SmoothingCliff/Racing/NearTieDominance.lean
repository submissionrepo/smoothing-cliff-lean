import SmoothingCliff.Racing.BoundaryFloor
import SmoothingCliff.Racing.NetSurplus

/-!
# Dominance at a value tie

Corollary `cor:neartie_dominance`.  At a value tie the allocation is worth the
same whoever wins, so smoothing costs no allocative welfare and its net surplus
is the whole prize.  The strict-priority race gives the same allocation value
less what the two players burn, and the selection-free floor bounds that from
below at every equilibrium.  The gap is therefore at least the prize net of one
band's cost, whatever equilibrium the race lands in.
-/

namespace SmoothingCliff.Racing

noncomputable section

/-- Net surplus of the strict-priority race at a value tie. -/
def tiedStrictPriorityNetSurplus (slotWeight lowValue marginalCost : ℝ)
    (first second : BorelMixedStrategy) : ℝ :=
  slotWeight * lowValue - borelExpectedDissipation marginalCost first second

/-- At a value tie the smoothed rule loses no allocative welfare. -/
theorem zeroInvestmentPLNetSurplus_at_tie
    (slotWeight lowValue temperature : ℝ) :
    zeroInvestmentPLNetSurplus slotWeight lowValue 0 temperature =
      slotWeight * lowValue := by
  rw [zeroInvestmentPLNetSurplus_eq]
  ring

/-- **Dominance at a value tie.**  Against every equilibrium of the race, pure
or mixed, the smoothed rule's net surplus exceeds the race's by at least the
whole contested prize net of one band's cost. -/
theorem neartie_dominance
    {slotWeight lowValue marginalCost temperature : ℝ}
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {gap : NNReal} (hgap : 0 < (gap : ℝ))
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight (gap : ℝ) marginalCost first second) :
    (slotWeight - marginalCost) * (gap : ℝ) ≤
      zeroInvestmentPLNetSurplus slotWeight lowValue 0 temperature -
        tiedStrictPriorityNetSurplus slotWeight lowValue marginalCost first
          second := by
  rw [zeroInvestmentPLNetSurplus_at_tie, tiedStrictPriorityNetSurplus]
  have hfloor := nash_dissipation_ge_prize_net_cost hweight hcost hgap hnash
  linarith

/-- The gap is strictly positive whenever the racing technology is cheaper than
the slot itself. -/
theorem neartie_dominance_pos
    {slotWeight lowValue marginalCost temperature : ℝ}
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    (hcheap : marginalCost < slotWeight)
    {gap : NNReal} (hgap : 0 < (gap : ℝ))
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight (gap : ℝ) marginalCost first second) :
    0 < zeroInvestmentPLNetSurplus slotWeight lowValue 0 temperature -
      tiedStrictPriorityNetSurplus slotWeight lowValue marginalCost first
        second := by
  have hbound := neartie_dominance (lowValue := lowValue)
    (temperature := temperature) hweight hcost hgap hnash
  nlinarith [hbound, hgap, hcheap]

end

end SmoothingCliff.Racing
