import SmoothingCliff.Racing.RungIncrement

/-!
# The first rung is exactly twice the cost ratio

Running the two halves of the recursion once.  A stretch with no support in it
leaves the distribution function flat across that stretch, which is the
hypothesis both halves need, so the clearings already proved feed straight into
the next step.

The opponent keeps nothing strictly between zero and two contested bands, so
its distribution function is flat across the whole first window and the
advantaged player keeps nothing strictly between one band and three.  That in
turn flattens the advantaged player's distribution function across the second
window, and if the opponent continues at two bands the two-band payoff equation
pins its mass at one band to exactly twice the cost ratio.

This is `alpha_1 = 2 q` of equation (S), and every later rung repeats it with
the two players and the two windows exchanged.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- **Flatness from clearing.**  A stretch with no support in it leaves the
distribution function constant across that stretch. -/
theorem cdfReal_eq_of_support_clear (strategy : BorelMixedStrategy)
    {lower upper x y : ℝ}
    (hclear : ∀ action ∈ strategy.support,
      (action : ℝ) ≤ lower ∨ upper ≤ (action : ℝ))
    (hx : lower ≤ x) (hxy : x ≤ y) (hy : y < upper) :
    strategy.cdfReal x = strategy.cdfReal y := by
  refine le_antisymm (strategy.cdfReal_mono hxy) ?_
  have hcompl : (strategy.law : Measure NNReal)
      {action : NNReal | action ∉ strategy.support} = 0 :=
    ae_iff.mp strategy.ae_mem_support
  have hsub : {action : NNReal | (action : ℝ) ≤ y} ⊆
      {action : NNReal | (action : ℝ) ≤ x} ∪
        {action : NNReal | action ∉ strategy.support} := by
    intro action haction
    by_cases hsmall : (action : ℝ) ≤ x
    · exact Or.inl hsmall
    · refine Or.inr ?_
      intro hmem
      rcases hclear action hmem with hlow | hhigh
      · exact hsmall (le_trans hlow hx)
      · exact absurd (lt_of_le_of_lt (le_trans hhigh haction) hy) (lt_irrefl _)
  have hle : strategy.cdf y ≤ strategy.cdf x := by
    calc strategy.cdf y
        ≤ (strategy.law : Measure NNReal)
            ({action : NNReal | (action : ℝ) ≤ x} ∪
              {action : NNReal | action ∉ strategy.support}) :=
          measure_mono hsub
      _ ≤ strategy.cdf x +
            (strategy.law : Measure NNReal)
              {action : NNReal | action ∉ strategy.support} :=
          measure_union_le _ _
      _ = strategy.cdf x := by rw [hcompl, add_zero]
  exact ENNReal.toReal_mono (strategy.cdf_ne_top x) hle

/-- The opponent's distribution function is flat across the first window. -/
theorem second_cdfReal_flat_first_window
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    {point : ℝ} (hlow : 0 ≤ point) (hhigh : point < 2 * gap) :
    second.cdfReal point = second.cdfReal 0 := by
  have hclear : ∀ action ∈ second.support,
      (action : ℝ) ≤ 0 ∨ 2 * gap ≤ (action : ℝ) := by
    intro action hmem
    by_cases hzero : action = 0
    · exact Or.inl (by rw [hzero]; simp)
    · exact Or.inr
        (second_support_clear_below_two_gap hgap hweight hcost hnash hpos hmem
          hzero)
  exact (cdfReal_eq_of_support_clear second hclear (le_refl 0) hlow hhigh).symm

/-- **The advantaged player keeps nothing between one band and three.**  Its
return is flat across the first window, so the payoff falls at the cost rate
over the first band and cannot climb back over the second. -/
theorem first_support_clear_below_three_gap
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    {action : NNReal} (hmem : action ∈ first.support) :
    (action : ℝ) = gap ∨ 3 * gap ≤ (action : ℝ) := by
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  by_contra hcon
  rw [not_or, not_le] at hcon
  obtain ⟨hne, hhigh⟩ := hcon
  have hlow : gap ≤ (action : ℝ) := by
    rw [← hband]
    exact_mod_cast first.lowerSupport_le_of_mem_support hmem
  refine rung_step_clear (base := second.cdfReal 0) hgap hweight hcost hnash.1
    (anchor := gap) ?_ ?_ hmem (lt_of_le_of_ne hlow (Ne.symm hne))
    (by linarith)
  · intro spot hspot
    exact second_cdfReal_flat_first_window hgap hweight hcost hnash hpos
      (by linarith [hspot.1]) (by linarith [hspot.2])
  · exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.1
      first.lowerSupport_mem_support hband.symm

/-- The advantaged player's distribution function is flat across the second
window. -/
theorem first_cdfReal_flat_second_window
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    {point : ℝ} (hlow : gap ≤ point) (hhigh : point < 3 * gap) :
    first.cdfReal point = first.cdfReal gap := by
  have hclear : ∀ action ∈ first.support,
      (action : ℝ) ≤ gap ∨ 3 * gap ≤ (action : ℝ) := by
    intro action hmem
    rcases first_support_clear_below_three_gap hgap hweight hcost hnash hpos
      hmem with heq | hfar
    · exact Or.inl (le_of_eq heq)
    · exact Or.inr hfar
  exact (cdfReal_eq_of_support_clear first hclear (le_refl gap) hlow hhigh).symm

/-- **The first rung of equation (S).**  If the opponent continues at two
contested bands, the advantaged player's mass at one band is exactly twice the
cost ratio. -/
theorem first_rung_increment_eq
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    {rung : NNReal} (hrungValue : (rung : ℝ) = 2 * gap)
    (hrung : rung ∈ second.support) :
    slotWeight * first.cdfReal gap = 2 * marginalCost := by
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  obtain ⟨hbottom, hzeroPayoff, -⟩ :=
    opponent_at_bottom_of_payoff_pos hgap.le hcost hnash hpos
  have hbottomReal : ((second.lowerSupport : NNReal) : ℝ) = 0 := by
    rw [hbottom]; simp
  have hkey :
      slotWeight * (first.cdfReal gap - 0) = 2 * marginalCost := by
    refine rung_increment_eq (own := second) (opponent := first) (anchor := 0)
      hgap ?_ ?_ ?_ ?_
    · intro spot hspot
      exact cdfReal_eq_zero_of_lt_lowerSupport first
        (by rw [hband]; linarith [hspot.2])
    · intro spot hspot
      exact first_cdfReal_flat_second_window hgap hweight hcost hnash hpos
        (by linarith [hspot.1]) (by linarith [hspot.2])
    · exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.2
        second.lowerSupport_mem_support hbottomReal.symm
    · exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.2 hrung
        (by rw [hrungValue]; ring)
  linarith [hkey]

/-! ### The mirror half

With the advantaged player's distribution function flat across the second
window, the same two moves run with the players exchanged: the opponent keeps
nothing between two contested bands and four, its own distribution function is
flat there, and the two-band payoff equation caps its mass at two bands by
twice the cost ratio, with equality exactly when the advantaged player
continues at three bands. -/

/-- **The opponent keeps nothing between two bands and four.** -/
theorem second_support_clear_below_four_gap
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    {rung : NNReal} (hrungValue : (rung : ℝ) = 2 * gap)
    (hrung : rung ∈ second.support)
    {action : NNReal} (hmem : action ∈ second.support)
    (hlow : 2 * gap < (action : ℝ)) (hhigh : (action : ℝ) < 4 * gap) :
    False := by
  obtain ⟨-, hzeroPayoff, -⟩ :=
    opponent_at_bottom_of_payoff_pos hgap.le hcost hnash hpos
  refine rung_step_clear (base := first.cdfReal gap) hgap hweight hcost hnash.2
    (anchor := 2 * gap) ?_ ?_ hmem hlow (by linarith)
  · intro spot hspot
    exact first_cdfReal_flat_second_window hgap hweight hcost hnash hpos
      (by linarith [hspot.1]) (by linarith [hspot.2])
  · exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.2 hrung
      hrungValue.symm

/-- The opponent's distribution function is flat across the third window. -/
theorem second_cdfReal_flat_third_window
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    {rung : NNReal} (hrungValue : (rung : ℝ) = 2 * gap)
    (hrung : rung ∈ second.support)
    {point : ℝ} (hlow : 2 * gap ≤ point) (hhigh : point < 4 * gap) :
    second.cdfReal point = second.cdfReal (2 * gap) := by
  have hclear : ∀ action ∈ second.support,
      (action : ℝ) ≤ 2 * gap ∨ 4 * gap ≤ (action : ℝ) := by
    intro action hmem
    by_contra hcon
    rw [not_or, not_le, not_le] at hcon
    exact second_support_clear_below_four_gap hgap hweight hcost hnash hpos
      hrungValue hrung hmem hcon.1 hcon.2
  exact (cdfReal_eq_of_support_clear second hclear (le_refl (2 * gap)) hlow
    hhigh).symm

/-- **The opponent's rung is capped.**  Its mass at two contested bands is at
most twice the cost ratio. -/
theorem second_rung_increment_le
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    {rung : NNReal} (hrungValue : (rung : ℝ) = 2 * gap)
    (hrung : rung ∈ second.support) :
    slotWeight * (second.cdfReal (2 * gap) - second.cdfReal 0) ≤
      2 * marginalCost := by
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  refine rung_increment_le (own := first) (opponent := second) (anchor := gap)
    hgap hnash.1 hgap.le ?_ ?_ ?_
  · intro spot hspot
    exact second_cdfReal_flat_first_window hgap hweight hcost hnash hpos
      (by linarith [hspot.1]) (by linarith [hspot.2])
  · intro spot hspot
    exact second_cdfReal_flat_third_window hgap hweight hcost hnash hpos
      hrungValue hrung (by linarith [hspot.1]) (by linarith [hspot.2])
  · exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.1
      first.lowerSupport_mem_support hband.symm

/-- **The opponent's rung is exact when the advantaged player continues.**  If
the advantaged player keeps mass at three contested bands, the opponent's mass
at two bands is exactly twice the cost ratio. -/
theorem second_rung_increment_eq
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    {rung : NNReal} (hrungValue : (rung : ℝ) = 2 * gap)
    (hrung : rung ∈ second.support)
    {next : NNReal} (hnextValue : (next : ℝ) = 3 * gap)
    (hnext : next ∈ first.support) :
    slotWeight * (second.cdfReal (2 * gap) - second.cdfReal 0) =
      2 * marginalCost := by
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  refine rung_increment_eq (own := first) (opponent := second) (anchor := gap)
    hgap ?_ ?_ ?_ ?_
  · intro spot hspot
    exact second_cdfReal_flat_first_window hgap hweight hcost hnash hpos
      (by linarith [hspot.1]) (by linarith [hspot.2])
  · intro spot hspot
    exact second_cdfReal_flat_third_window hgap hweight hcost hnash hpos
      hrungValue hrung (by linarith [hspot.1]) (by linarith [hspot.2])
  · exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.1
      first.lowerSupport_mem_support hband.symm
  · exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.1 hnext
      (by rw [hnextValue]; ring)

end

end SmoothingCliff.Racing
