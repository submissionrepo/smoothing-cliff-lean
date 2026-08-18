import SmoothingCliff.Racing.AtomSum

/-!
# One step of the support recursion

The recursion of `prop:sp_allequilibria` (iii) advances two contested bands at a
time, and the same argument serves both players.  Anchor the step at an action
where the payoff attains its maximum, and suppose the opponent's distribution
function is flat across the band before the anchor and the band after it.

Over the first band the payoff falls at the cost rate, because nothing arrives
in the window that is not also leaving it.  Over the second band the payoff may
climb, but it cannot climb back to the maximum: reaching it would already have
cleared the cost ratio, and the climb would then carry the payoff past the
maximum before the band ends.

So the player keeps nothing strictly between the anchor and two bands above it,
which is what places the next atom exactly two bands up.  The flat stretch is
half-open on the right, so the opponent's own next atom does not block the
hypothesis.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- The payoff at an anchor of a flat stretch falls at the cost rate across the
first band. -/
theorem realPureExpectedPayoff_of_anchor
    {slotWeight gap marginalCost base : ℝ} (hgap : 0 ≤ gap)
    {opponent : BorelMixedStrategy} {anchor level : ℝ}
    (hflat : ∀ point ∈ Set.Ico (anchor - gap) (anchor + gap),
      opponent.cdfReal point = base)
    (hanchor :
      realPureExpectedPayoff slotWeight gap marginalCost opponent anchor = level)
    {x : ℝ} (hlow : anchor ≤ x) (hhigh : x ≤ anchor + gap) :
    realPureExpectedPayoff slotWeight gap marginalCost opponent x =
      level - marginalCost * (x - anchor) := by
  have hstep := realPureExpectedPayoff_sub_of_flat (slotWeight := slotWeight)
    (marginalCost := marginalCost) (base := base) hgap (opponent := opponent)
    (start := anchor) (finish := x) hlow
    (fun point hpoint => hflat point ⟨hpoint.1, by linarith [hpoint.2]⟩)
  rw [hanchor] at hstep
  linarith

/-- **One step of the recursion.**  A player whose payoff attains its maximum at
the anchor of a flat stretch keeps nothing strictly between the anchor and two
contested bands above it. -/
theorem rung_step_clear
    {slotWeight gap marginalCost base : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {anchor : ℝ}
    (hflat : ∀ point ∈ Set.Ico (anchor - gap) (anchor + gap),
      opponent.cdfReal point = base)
    (hanchor :
      realPureExpectedPayoff slotWeight gap marginalCost opponent anchor =
        borelExpectedPayoff slotWeight gap marginalCost own opponent)
    {action : NNReal} (hmem : action ∈ own.support)
    (hlow : anchor < (action : ℝ)) (hhigh : (action : ℝ) < anchor + 2 * gap) :
    False := by
  have hvalue :
      realPureExpectedPayoff slotWeight gap marginalCost opponent (action : ℝ) =
        borelExpectedPayoff slotWeight gap marginalCost own opponent := by
    rw [realPureExpectedPayoff_coe hgap.le,
      borelMixedBestResponse_payoff_eq_on_support hgap.le hbest action hmem]
  have hunder :
      realPureExpectedPayoff slotWeight gap marginalCost opponent
          (anchor + gap) <
        borelExpectedPayoff slotWeight gap marginalCost own opponent := by
    have hfall := realPureExpectedPayoff_of_anchor (slotWeight := slotWeight)
      (marginalCost := marginalCost) (base := base) hgap.le hflat hanchor
      (x := anchor + gap) (by linarith) (le_refl _)
    rw [hfall]
    nlinarith [hgap, hcost]
  rcases le_or_gt (action : ℝ) (anchor + gap) with hfirst | hsecond
  · have hfall := realPureExpectedPayoff_of_anchor (slotWeight := slotWeight)
      (marginalCost := marginalCost) (base := base) hgap.le hflat hanchor
      hlow.le hfirst
    rw [hvalue] at hfall
    nlinarith [hfall, hlow, hcost]
  · refine support_clear_in_window_of_best (base := base) hgap.le hweight hbest
      (start := anchor + gap) (finish := anchor + 2 * gap) ?_ hunder hmem
      hsecond.le hhigh
    intro point hpoint
    exact hflat point ⟨by linarith [hpoint.1], by linarith [hpoint.2]⟩

end

end SmoothingCliff.Racing
