import SmoothingCliff.Racing.RungStep

/-!
# The size of a rung

Equation (S) of `prop:sp_allequilibria` (iii).  Across two contested bands the
payoff change is read off exactly: the window that arrives carries the new level
of the opponent's distribution function for one band and the old level for the
other, while the window that departs carries the old level for both.  So the
payoff climbs by the slot weight times one band times the jump, and falls by
two bands' worth of cost.

Anchoring at an action where the payoff attains its maximum, the deviation
inequality caps the jump at twice the cost ratio, and if the payoff attains its
maximum again two bands up the jump is exactly twice the cost ratio.  That is
the recursion's mass equation; `rung_step_clear` is what puts the next support
point two bands up in the first place.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- **The two-band payoff change.**  It is the slot weight times one band times
the jump in the opponent's distribution function, net of two bands of cost. -/
theorem realPureExpectedPayoff_sub_two_bands
    {slotWeight gap marginalCost low high : ℝ} (hgap : 0 ≤ gap)
    {opponent : BorelMixedStrategy} {anchor : ℝ}
    (hflatLow : ∀ point ∈ Set.Ico (anchor - gap) (anchor + gap),
      opponent.cdfReal point = low)
    (hflatHigh : ∀ point ∈ Set.Ico (anchor + gap) (anchor + 2 * gap),
      opponent.cdfReal point = high) :
    realPureExpectedPayoff slotWeight gap marginalCost opponent
          (anchor + 2 * gap) -
        realPureExpectedPayoff slotWeight gap marginalCost opponent anchor =
      slotWeight * gap * (high - low) - marginalCost * (2 * gap) := by
  have hdepart :
      (∫ point in (anchor - gap)..(anchor + gap), opponent.cdfReal point) =
        2 * gap * low := by
    have hstep := opponent.integral_cdfReal_of_flat
      (by linarith : anchor - gap ≤ anchor + gap) hflatLow
    rw [hstep]
    ring
  have hfirstBand :
      (∫ point in anchor..(anchor + gap), opponent.cdfReal point) =
        gap * low := by
    have hstep := opponent.integral_cdfReal_of_flat (base := low)
      (by linarith : anchor ≤ anchor + gap)
      (fun point hpoint => hflatLow point ⟨by linarith [hpoint.1], hpoint.2⟩)
    rw [hstep]
    ring
  have hsecondBand :
      (∫ point in (anchor + gap)..(anchor + 2 * gap), opponent.cdfReal point) =
        gap * high := by
    have hstep := opponent.integral_cdfReal_of_flat (base := high)
      (by linarith : anchor + gap ≤ anchor + 2 * gap) hflatHigh
    rw [hstep]
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (opponent.intervalIntegrable_cdfReal anchor (anchor + gap))
    (opponent.intervalIntegrable_cdfReal (anchor + gap) (anchor + 2 * gap))
  have harrive :
      (∫ point in anchor..(anchor + 2 * gap), opponent.cdfReal point) =
        gap * low + gap * high := by
    rw [← hsplit, hfirstBand, hsecondBand]
  have hdiff := realPureExpectedPayoff_sub (slotWeight := slotWeight)
    (gap := gap) (marginalCost := marginalCost) opponent anchor
    (anchor + 2 * gap)
  rw [show anchor + 2 * gap - gap = anchor + gap by ring] at hdiff
  rw [hdiff, harrive, hdepart]
  ring

/-- **The rung is capped.**  Anchored where the payoff attains its maximum, the
jump across the rung is at most twice the cost ratio. -/
theorem rung_increment_le
    {slotWeight gap marginalCost low high : ℝ} (hgap : 0 < gap)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {anchor : ℝ} (hanchorNonneg : 0 ≤ anchor)
    (hflatLow : ∀ point ∈ Set.Ico (anchor - gap) (anchor + gap),
      opponent.cdfReal point = low)
    (hflatHigh : ∀ point ∈ Set.Ico (anchor + gap) (anchor + 2 * gap),
      opponent.cdfReal point = high)
    (hanchor :
      realPureExpectedPayoff slotWeight gap marginalCost opponent anchor =
        borelExpectedPayoff slotWeight gap marginalCost own opponent) :
    slotWeight * (high - low) ≤ 2 * marginalCost := by
  have hchange := realPureExpectedPayoff_sub_two_bands (slotWeight := slotWeight)
    (marginalCost := marginalCost) hgap.le hflatLow hflatHigh
  have hceiling := realPureExpectedPayoff_le_max (slotWeight := slotWeight)
    (marginalCost := marginalCost) hgap.le hbest
    (x := anchor + 2 * gap) (by linarith)
  rw [hanchor] at hchange
  have hscaled :
      slotWeight * (high - low) * gap ≤ 2 * marginalCost * gap := by
    nlinarith [hchange, hceiling]
  exact le_of_mul_le_mul_right hscaled hgap

/-- **The rung is exactly twice the cost ratio.**  If the payoff attains its
maximum both at the anchor and two bands up, the jump across the rung is
exactly twice the cost ratio.  This is equation (S). -/
theorem rung_increment_eq
    {slotWeight gap marginalCost low high : ℝ} (hgap : 0 < gap)
    {own opponent : BorelMixedStrategy}
    {anchor : ℝ}
    (hflatLow : ∀ point ∈ Set.Ico (anchor - gap) (anchor + gap),
      opponent.cdfReal point = low)
    (hflatHigh : ∀ point ∈ Set.Ico (anchor + gap) (anchor + 2 * gap),
      opponent.cdfReal point = high)
    (hanchor :
      realPureExpectedPayoff slotWeight gap marginalCost opponent anchor =
        borelExpectedPayoff slotWeight gap marginalCost own opponent)
    (hnext :
      realPureExpectedPayoff slotWeight gap marginalCost opponent
          (anchor + 2 * gap) =
        borelExpectedPayoff slotWeight gap marginalCost own opponent) :
    slotWeight * (high - low) = 2 * marginalCost := by
  have hchange := realPureExpectedPayoff_sub_two_bands (slotWeight := slotWeight)
    (marginalCost := marginalCost) hgap.le hflatLow hflatHigh
  rw [hanchor, hnext, sub_self] at hchange
  have hscaled : slotWeight * (high - low) * gap = 2 * marginalCost * gap := by
    nlinarith [hchange]
  exact mul_right_cancel₀ (ne_of_gt hgap) hscaled

/-- The payoff attains its maximum at every support action, in the form the
rung equations consume. -/
theorem realPureExpectedPayoff_eq_max_at_support
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {action : NNReal} (hmem : action ∈ own.support) {x : ℝ}
    (hx : x = (action : ℝ)) :
    realPureExpectedPayoff slotWeight gap marginalCost opponent x =
      borelExpectedPayoff slotWeight gap marginalCost own opponent := by
  rw [hx, realPureExpectedPayoff_coe hgap,
    borelMixedBestResponse_payoff_eq_on_support hgap hbest action hmem]

end

end SmoothingCliff.Racing
