import SmoothingCliff.Racing.LatticeCumulative

/-!
# Reading the slope off the window

The engine of the support recursion (S) in `prop:sp_allequilibria` (iii).
Moving the window forward adds the distribution function over the new stretch
and drops it over the stretch that leaves at the bottom.  When the departing
stretch is flat, the whole change is carried by the arriving one, and
monotonicity turns that into two-sided bounds on the payoff change.

The consequence used below is the one the paper states as "the positive return
slope would make the payoff exceed its maximum".  If the payoff climbs back to
its maximum across a stretch whose departing window is flat, the distribution
function at the far end already clears the cost ratio, and then it keeps
climbing past the maximum.  So the payoff cannot return to its maximum strictly
inside such a stretch.

Everything here is stated through integrals, so none of it needs the
distribution function to be differentiable or right-continuous.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

namespace BorelMixedStrategy

theorem integral_cdfReal_le_right
    (strategy : BorelMixedStrategy) {lower upper : ℝ} (hle : lower ≤ upper) :
    (∫ point in lower..upper, strategy.cdfReal point) ≤
      (upper - lower) * strategy.cdfReal upper := by
  have hbound := intervalIntegral.integral_mono_on hle
    (strategy.intervalIntegrable_cdfReal lower upper)
    (intervalIntegrable_const (c := strategy.cdfReal upper))
    (fun point hpoint => strategy.cdfReal_mono hpoint.2)
  simpa [smul_eq_mul] using hbound

theorem integral_cdfReal_ge_left
    (strategy : BorelMixedStrategy) {lower upper : ℝ} (hle : lower ≤ upper) :
    (upper - lower) * strategy.cdfReal lower ≤
      ∫ point in lower..upper, strategy.cdfReal point := by
  have hbound := intervalIntegral.integral_mono_on hle
    (intervalIntegrable_const (c := strategy.cdfReal lower))
    (strategy.intervalIntegrable_cdfReal lower upper)
    (fun point hpoint => strategy.cdfReal_mono hpoint.1)
  simpa [smul_eq_mul] using hbound

theorem integral_cdfReal_of_flat
    (strategy : BorelMixedStrategy) {lower upper base : ℝ} (hle : lower ≤ upper)
    (hflat : ∀ point ∈ Set.Ico lower upper, strategy.cdfReal point = base) :
    (∫ point in lower..upper, strategy.cdfReal point) = (upper - lower) * base := by
  have hae : ∀ᵐ point : ℝ, point ≠ upper := by
    rw [ae_iff]
    simp
  rw [intervalIntegral.integral_congr_ae (g := fun _ : ℝ => base) ?_]
  · simp [smul_eq_mul]
  · filter_upwards [hae] with point hpoint hmem
    rw [Set.uIoc_of_le hle] at hmem
    exact hflat point ⟨le_of_lt hmem.1, lt_of_le_of_ne hmem.2 hpoint⟩

end BorelMixedStrategy

/-- Moving the window forward adds the arriving stretch and drops the departing
one. -/
theorem realPureExpectedPayoff_sub
    {slotWeight gap marginalCost : ℝ} (opponent : BorelMixedStrategy)
    (lower upper : ℝ) :
    realPureExpectedPayoff slotWeight gap marginalCost opponent upper -
        realPureExpectedPayoff slotWeight gap marginalCost opponent lower =
      slotWeight *
          ((∫ point in lower..upper, opponent.cdfReal point) -
            ∫ point in (lower - gap)..(upper - gap), opponent.cdfReal point) -
        marginalCost * (upper - lower) := by
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (opponent.intervalIntegrable_cdfReal (lower - gap) lower)
    (opponent.intervalIntegrable_cdfReal lower upper)
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (opponent.intervalIntegrable_cdfReal (lower - gap) (upper - gap))
    (opponent.intervalIntegrable_cdfReal (upper - gap) upper)
  have hkey : (∫ point in (upper - gap)..upper, opponent.cdfReal point) =
      (∫ point in (lower - gap)..lower, opponent.cdfReal point) +
        (∫ point in lower..upper, opponent.cdfReal point) -
        ∫ point in (lower - gap)..(upper - gap), opponent.cdfReal point := by
    linarith
  rw [realPureExpectedPayoff, realPureExpectedPayoff, hkey]
  ring

/-- **The climb needs a cleared distribution function.**  If the payoff is
strictly higher at the far end of a stretch whose departing window is flat, the
distribution function there already exceeds the cost ratio above the flat
level. -/
theorem cdfReal_gt_of_payoff_increase
    {slotWeight gap marginalCost base : ℝ} (hweight : 0 < slotWeight)
    {opponent : BorelMixedStrategy} {lower upper : ℝ} (hle : lower ≤ upper)
    (hflat : ∀ point ∈ Set.Ico (lower - gap) (upper - gap),
      opponent.cdfReal point = base)
    (hincrease :
      realPureExpectedPayoff slotWeight gap marginalCost opponent lower <
        realPureExpectedPayoff slotWeight gap marginalCost opponent upper) :
    marginalCost < slotWeight * (opponent.cdfReal upper - base) := by
  have hlt : lower < upper := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact absurd (heq ▸ rfl : realPureExpectedPayoff slotWeight gap
        marginalCost opponent lower = realPureExpectedPayoff slotWeight gap
        marginalCost opponent upper) (ne_of_lt hincrease)
    · exact hlt
  have hdiff := realPureExpectedPayoff_sub (slotWeight := slotWeight)
    (gap := gap) (marginalCost := marginalCost) opponent lower upper
  have hdrop :
      (∫ point in (lower - gap)..(upper - gap), opponent.cdfReal point) =
        (upper - lower) * base := by
    have := opponent.integral_cdfReal_of_flat (base := base)
      (by linarith : lower - gap ≤ upper - gap) hflat
    rw [this]
    ring_nf
  have harrive := opponent.integral_cdfReal_le_right hle
  have hpos : 0 < upper - lower := by linarith
  nlinarith [hdiff, hdrop, harrive, hincrease, hpos]

/-- **The climb continues.**  If the distribution function already exceeds the
cost ratio above the flat level of the departing window, the payoff is strictly
higher at the far end. -/
theorem payoff_increase_of_cdfReal_gt
    {slotWeight gap marginalCost base : ℝ} (hweight : 0 < slotWeight)
    {opponent : BorelMixedStrategy} {lower upper : ℝ} (hlt : lower < upper)
    (hflat : ∀ point ∈ Set.Ico (lower - gap) (upper - gap),
      opponent.cdfReal point = base)
    (hcleared : marginalCost < slotWeight * (opponent.cdfReal lower - base)) :
    realPureExpectedPayoff slotWeight gap marginalCost opponent lower <
      realPureExpectedPayoff slotWeight gap marginalCost opponent upper := by
  have hdiff := realPureExpectedPayoff_sub (slotWeight := slotWeight)
    (gap := gap) (marginalCost := marginalCost) opponent lower upper
  have hdrop :
      (∫ point in (lower - gap)..(upper - gap), opponent.cdfReal point) =
        (upper - lower) * base := by
    have := opponent.integral_cdfReal_of_flat (base := base)
      (by linarith : lower - gap ≤ upper - gap) hflat
    rw [this]
    ring_nf
  have harrive := opponent.integral_cdfReal_ge_left hlt.le
  have hpos : 0 < upper - lower := by linarith
  nlinarith [hdiff, hdrop, harrive, hcleared, hpos]

/-- A player earning zero never beats zero with any admissible deviation. -/
theorem realPureExpectedPayoff_nonpos_of_zero_payoff
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    (hzero : borelExpectedPayoff slotWeight gap marginalCost own opponent = 0)
    {x : ℝ} (hx : 0 ≤ x) :
    realPureExpectedPayoff slotWeight gap marginalCost opponent x ≤ 0 := by
  have hdev := hbest x.toNNReal
  rw [hzero] at hdev
  rwa [← realPureExpectedPayoff_coe hgap opponent x.toNNReal,
    Real.coe_toNNReal x hx] at hdev

/-- A player earning zero is exactly indifferent on its own support. -/
theorem realPureExpectedPayoff_eq_zero_on_support
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    (hzero : borelExpectedPayoff slotWeight gap marginalCost own opponent = 0)
    {action : NNReal} (hmem : action ∈ own.support) :
    realPureExpectedPayoff slotWeight gap marginalCost opponent
      (action : ℝ) = 0 := by
  rw [realPureExpectedPayoff_coe hgap,
    borelMixedBestResponse_payoff_eq_on_support hgap hbest action hmem, hzero]

/-- **The second rung is clear.**  In a positive-payoff equilibrium the
opponent keeps no mass strictly between zero and two contested bands.  The
argument is the recursion's: the payoff at one band is strictly negative, so
climbing back to zero inside the stretch would already have cleared the cost
ratio, and the climb would then carry the payoff above its maximum. -/
theorem second_support_clear_below_two_gap
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    {rival : NNReal} (hrival : rival ∈ second.support) (hne : rival ≠ 0) :
    2 * gap ≤ (rival : ℝ) := by
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  obtain ⟨-, hzeroPayoff, -⟩ :=
    opponent_at_bottom_of_payoff_pos hgap.le hcost hnash hpos
  have hflatBelow : ∀ x : ℝ, x < gap → first.cdfReal x = 0 := by
    intro x hx
    exact cdfReal_eq_zero_of_lt_lowerSupport first (by rw [hband]; exact hx)
  have hbandLe :=
    second_support_clear_of_payoff_pos hgap.le hcost hnash hpos rival hrival hne
  rw [hband] at hbandLe
  have hsupportValue :=
    realPureExpectedPayoff_eq_zero_on_support hgap.le hnash.2 hzeroPayoff hrival
  have hatBand :
      realPureExpectedPayoff slotWeight gap marginalCost first gap =
        -(marginalCost * gap) := by
    have hcoe : ((gap.toNNReal : NNReal) : ℝ) = gap := Real.coe_toNNReal gap hgap.le
    have hzeroGap :
        borelPureExpectedCapturedGap gap first gap.toNNReal = 0 := by
      refine borelPureExpectedCapturedGap_eq_zero_of_le_lowerSupport hgap.le
        first ?_
      have : (gap.toNNReal : ℝ) ≤ (first.lowerSupport : ℝ) := by
        rw [hcoe, hband]
      exact_mod_cast this
    have hstep := realPureExpectedPayoff_coe (slotWeight := slotWeight)
      (gap := gap) (marginalCost := marginalCost) hgap.le first gap.toNNReal
    rw [borelPureExpectedPayoff, hzeroGap, hcoe] at hstep
    rw [hstep]
    ring
  by_contra hlt
  rw [not_le] at hlt
  have hstrict : gap < (rival : ℝ) := by
    rcases eq_or_lt_of_le hbandLe with heq | hgt
    · exfalso
      rw [← heq] at hsupportValue
      rw [hatBand] at hsupportValue
      nlinarith
    · exact hgt
  have hcleared : marginalCost < slotWeight * (first.cdfReal (rival : ℝ) - 0) := by
    refine cdfReal_gt_of_payoff_increase (gap := gap) (marginalCost := marginalCost)
      hweight hstrict.le ?_ ?_
    · intro point hpoint
      exact hflatBelow point (by linarith [hpoint.2])
    · rw [hatBand, hsupportValue]
      nlinarith
  set middle : ℝ := ((rival : ℝ) + 2 * gap) / 2 with hmiddle
  have hmidlt : (rival : ℝ) < middle := by rw [hmiddle]; linarith
  have hmidhigh : middle < 2 * gap := by rw [hmiddle]; linarith
  have hclimb :
      realPureExpectedPayoff slotWeight gap marginalCost first (rival : ℝ) <
        realPureExpectedPayoff slotWeight gap marginalCost first middle := by
    refine payoff_increase_of_cdfReal_gt (gap := gap)
      (marginalCost := marginalCost) hweight hmidlt ?_ hcleared
    intro point hpoint
    exact hflatBelow point (by linarith [hpoint.2])
  have hceiling :=
    realPureExpectedPayoff_nonpos_of_zero_payoff (slotWeight := slotWeight)
      (marginalCost := marginalCost) hgap.le hnash.2 hzeroPayoff
      (x := middle) (by rw [hmiddle]; nlinarith [rival.coe_nonneg])
  rw [hsupportValue] at hclimb
  linarith

/-- **The recursion's engine, in general form.**  Suppose a player earning zero
is strictly under water at the start of a stretch, and the opponent's
distribution function is flat across the window that departs over that stretch.
Then the player keeps no mass anywhere strictly inside the stretch: reaching
its maximum there would already have cleared the cost ratio, and the climb
would carry it above the maximum before the stretch ends.

The concrete clearings below the lattice rungs are instances of this, with the
flat departing window supplied by the previous rung. -/
theorem support_clear_in_window
    {slotWeight gap marginalCost base : ℝ} (hgap : 0 ≤ gap)
    (hweight : 0 < slotWeight)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    (hzero : borelExpectedPayoff slotWeight gap marginalCost own opponent = 0)
    {start finish : ℝ}
    (hflat : ∀ point ∈ Set.Ico (start - gap) (finish - gap),
      opponent.cdfReal point = base)
    (hunder :
      realPureExpectedPayoff slotWeight gap marginalCost opponent start < 0)
    {action : NNReal} (hmem : action ∈ own.support)
    (hlow : start ≤ (action : ℝ)) (hhigh : (action : ℝ) < finish) :
    False := by
  have hvalue :=
    realPureExpectedPayoff_eq_zero_on_support (slotWeight := slotWeight)
      (marginalCost := marginalCost) hgap hbest hzero hmem
  have hcleared :
      marginalCost < slotWeight * (opponent.cdfReal (action : ℝ) - base) := by
    refine cdfReal_gt_of_payoff_increase (gap := gap)
      (marginalCost := marginalCost) hweight hlow ?_ ?_
    · intro point hpoint
      exact hflat point ⟨hpoint.1, lt_of_lt_of_le hpoint.2 (by linarith)⟩
    · rw [hvalue]
      exact hunder
  set middle : ℝ := ((action : ℝ) + finish) / 2 with hmiddle
  have hmidlow : (action : ℝ) < middle := by rw [hmiddle]; linarith
  have hmidhigh : middle < finish := by rw [hmiddle]; linarith
  have hclimb :
      realPureExpectedPayoff slotWeight gap marginalCost opponent
          (action : ℝ) <
        realPureExpectedPayoff slotWeight gap marginalCost opponent middle := by
    refine payoff_increase_of_cdfReal_gt (gap := gap)
      (marginalCost := marginalCost) hweight hmidlow ?_ hcleared
    intro point hpoint
    refine hflat point ⟨le_trans (by linarith) hpoint.1, ?_⟩
    exact lt_of_lt_of_le hpoint.2 (by linarith)
  have hceiling :=
    realPureExpectedPayoff_nonpos_of_zero_payoff (slotWeight := slotWeight)
      (marginalCost := marginalCost) hgap hbest hzero
      (x := middle) (by rw [hmiddle]; linarith [action.coe_nonneg])
  rw [hvalue] at hclimb
  linarith

/-- No admissible deviation beats the equilibrium payoff. -/
theorem realPureExpectedPayoff_le_max
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {x : ℝ} (hx : 0 ≤ x) :
    realPureExpectedPayoff slotWeight gap marginalCost opponent x ≤
      borelExpectedPayoff slotWeight gap marginalCost own opponent := by
  have hdev := hbest x.toNNReal
  rwa [← realPureExpectedPayoff_coe hgap opponent x.toNNReal,
    Real.coe_toNNReal x hx] at hdev

/-- **The recursion's engine at an arbitrary payoff level.**  If the payoff is
strictly below its maximum at the start of a stretch and the opponent's
distribution function is flat across the departing window, the player keeps no
mass anywhere in the stretch: reaching the maximum inside it would already have
cleared the cost ratio, and the climb would carry the payoff past the maximum
before the stretch ends. -/
theorem support_clear_in_window_of_best
    {slotWeight gap marginalCost base : ℝ} (hgap : 0 ≤ gap)
    (hweight : 0 < slotWeight)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {start finish : ℝ}
    (hflat : ∀ point ∈ Set.Ico (start - gap) (finish - gap),
      opponent.cdfReal point = base)
    (hunder :
      realPureExpectedPayoff slotWeight gap marginalCost opponent start <
        borelExpectedPayoff slotWeight gap marginalCost own opponent)
    {action : NNReal} (hmem : action ∈ own.support)
    (hlow : start ≤ (action : ℝ)) (hhigh : (action : ℝ) < finish) :
    False := by
  have hvalue :
      realPureExpectedPayoff slotWeight gap marginalCost opponent (action : ℝ) =
        borelExpectedPayoff slotWeight gap marginalCost own opponent := by
    rw [realPureExpectedPayoff_coe hgap,
      borelMixedBestResponse_payoff_eq_on_support hgap hbest action hmem]
  have hcleared :
      marginalCost < slotWeight * (opponent.cdfReal (action : ℝ) - base) := by
    refine cdfReal_gt_of_payoff_increase (gap := gap)
      (marginalCost := marginalCost) hweight hlow ?_ ?_
    · intro point hpoint
      exact hflat point ⟨hpoint.1, lt_of_lt_of_le hpoint.2 (by linarith)⟩
    · rw [hvalue]
      exact hunder
  set middle : ℝ := ((action : ℝ) + finish) / 2 with hmiddle
  have hmidlow : (action : ℝ) < middle := by rw [hmiddle]; linarith
  have hmidhigh : middle < finish := by rw [hmiddle]; linarith
  have hclimb :
      realPureExpectedPayoff slotWeight gap marginalCost opponent
          (action : ℝ) <
        realPureExpectedPayoff slotWeight gap marginalCost opponent middle := by
    refine payoff_increase_of_cdfReal_gt (gap := gap)
      (marginalCost := marginalCost) hweight hmidlow ?_ hcleared
    intro point hpoint
    refine hflat point ⟨le_trans (by linarith) hpoint.1, ?_⟩
    exact lt_of_lt_of_le hpoint.2 (by linarith)
  have hceiling :=
    realPureExpectedPayoff_le_max (slotWeight := slotWeight)
      (marginalCost := marginalCost) hgap hbest
      (x := middle) (by rw [hmiddle]; linarith [action.coe_nonneg])
  rw [hvalue] at hclimb
  linarith

/-- **The flat stretch falls at the cost rate.**  Where the distribution
function is flat across both the arriving and the departing window, the payoff
declines exactly at the marginal cost. -/
theorem realPureExpectedPayoff_sub_of_flat
    {slotWeight gap marginalCost base : ℝ} (hgap : 0 ≤ gap)
    {opponent : BorelMixedStrategy} {start finish : ℝ} (hle : start ≤ finish)
    (hflat : ∀ point ∈ Set.Ico (start - gap) finish,
      opponent.cdfReal point = base) :
    realPureExpectedPayoff slotWeight gap marginalCost opponent finish -
        realPureExpectedPayoff slotWeight gap marginalCost opponent start =
      -(marginalCost * (finish - start)) := by
  have harrive : (∫ point in start..finish, opponent.cdfReal point) =
      (finish - start) * base :=
    opponent.integral_cdfReal_of_flat hle
      (fun point hpoint => hflat point ⟨by linarith [hpoint.1], hpoint.2⟩)
  have hdepart :
      (∫ point in (start - gap)..(finish - gap), opponent.cdfReal point) =
        (finish - start) * base := by
    have hstep := opponent.integral_cdfReal_of_flat
      (base := base) (by linarith : start - gap ≤ finish - gap)
      (fun point hpoint => hflat point ⟨hpoint.1, by linarith [hpoint.2]⟩)
    rw [hstep]
    ring_nf
  rw [realPureExpectedPayoff_sub (slotWeight := slotWeight) (gap := gap)
    (marginalCost := marginalCost) opponent start finish, harrive, hdepart]
  ring

end

end SmoothingCliff.Racing
