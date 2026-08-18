import SmoothingCliff.Racing.RungAdvance

/-!
# How many rungs the ladder can have

The recursion terminates because each rung takes twice the cost ratio out of a
distribution function bounded by one.  Counting that bounds the cost ratio from
above by the ladder length, which is what forces termination: cheap racing
technology is what buys a long ladder.

The sharp statement is on the opponent's side.  Its distribution function at its
own rungs is its atom at zero plus the rung count times twice the cost ratio,
and that atom strictly exceeds the cost ratio in a positive-payoff equilibrium,
so a ladder reaching rung `N` forces `(2N+1)` times the cost ratio strictly
below one.  With `nu = N+1` that is exactly the upper edge
`q < 1/(2 nu - 1)` of the window in `prop:sp_allequilibria` (iii).  The lower
edge runs the other way and needs the terminal rung, where the ladder stops.

The flatness induction is repeated here with the rung hypotheses bounded, since
the count needs the ladder only as far as it actually goes.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- The flatness recursion, run only as far as the ladder reaches. -/
theorem rung_flatness_le
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ)
    (hSecondRung : ∀ j ≤ depth, ∃ action ∈ second.support,
      (action : ℝ) = 2 * (j : ℝ) * gap)
    (hFirstRung : ∀ j ≤ depth, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap) :
    ∀ j ≤ depth,
      (∀ point ∈ Set.Ico (2 * (j : ℝ) * gap) ((2 * (j : ℝ) + 2) * gap),
        second.cdfReal point = second.cdfReal (2 * (j : ℝ) * gap)) ∧
      (∀ point ∈ Set.Ico ((2 * (j : ℝ) + 1) * gap) ((2 * (j : ℝ) + 3) * gap),
        first.cdfReal point = first.cdfReal ((2 * (j : ℝ) + 1) * gap)) := by
  have hsecondMax : ∀ j ≤ depth,
      realPureExpectedPayoff slotWeight gap marginalCost first
          (2 * (j : ℝ) * gap) =
        borelExpectedPayoff slotWeight gap marginalCost second first := by
    intro j hj
    obtain ⟨action, hmem, hvalue⟩ := hSecondRung j hj
    exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.2 hmem
      hvalue.symm
  have hfirstMax : ∀ j ≤ depth,
      realPureExpectedPayoff slotWeight gap marginalCost second
          ((2 * (j : ℝ) + 1) * gap) =
        borelExpectedPayoff slotWeight gap marginalCost first second := by
    intro j hj
    obtain ⟨action, hmem, hvalue⟩ := hFirstRung j hj
    exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.1 hmem
      hvalue.symm
  intro j
  induction j with
  | zero =>
    intro _
    constructor
    · intro point hpoint
      obtain ⟨hlo, hhi⟩ := hpoint
      norm_num at hlo hhi
      have hzero : 2 * ((0 : ℕ) : ℝ) * gap = 0 := by norm_num
      rw [hzero]
      exact second_cdfReal_flat_first_window hgap hweight hcost hnash hpos
        (by linarith) (by linarith)
    · intro point hpoint
      obtain ⟨hlo, hhi⟩ := hpoint
      norm_num at hlo hhi
      have hone : (2 * ((0 : ℕ) : ℝ) + 1) * gap = gap := by norm_num
      rw [hone]
      exact first_cdfReal_flat_second_window hgap hweight hcost hnash hpos
        (by linarith) (by linarith)
  | succ m ih =>
    intro hsucc
    obtain ⟨ihSecond, ihFirst⟩ := ih (Nat.le_of_succ_le hsucc)
    have hsecondNext :
        ∀ point ∈ Set.Ico (2 * ((m : ℝ) + 1) * gap)
            ((2 * ((m : ℝ) + 1) + 2) * gap),
          second.cdfReal point = second.cdfReal (2 * ((m : ℝ) + 1) * gap) := by
      have hstep := own_cdfReal_flat_two_bands (base := first.cdfReal
        ((2 * (m : ℝ) + 1) * gap)) hgap hweight hcost hnash.2
        (anchor := 2 * ((m : ℝ) + 1) * gap)
        (fun point hpoint => ihFirst point
          ⟨by have := hpoint.1; linarith, by have := hpoint.2; linarith⟩)
        (by simpa using hsecondMax (m + 1) hsucc)
      intro point hpoint
      exact hstep point ⟨hpoint.1, by have := hpoint.2; linarith⟩
    refine ⟨?_, ?_⟩
    · intro point hpoint
      have hcast : (((m : ℕ) + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hpoint ⊢
      exact hsecondNext point hpoint
    · have hstep := own_cdfReal_flat_two_bands (base := second.cdfReal
        (2 * ((m : ℝ) + 1) * gap)) hgap hweight hcost hnash.1
        (anchor := (2 * ((m : ℝ) + 1) + 1) * gap)
        (fun point hpoint => hsecondNext point
          ⟨by have := hpoint.1; linarith, by have := hpoint.2; linarith⟩)
        (by simpa using hfirstMax (m + 1) hsucc)
      intro point hpoint
      have hcast : (((m : ℕ) + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hpoint ⊢
      exact hstep point ⟨hpoint.1, by have := hpoint.2; linarith⟩

/-- Equation (S) at every rung the ladder reaches. -/
theorem first_rung_increments_le
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ)
    (hSecondRung : ∀ j ≤ depth + 1, ∃ action ∈ second.support,
      (action : ℝ) = 2 * (j : ℝ) * gap)
    (hFirstRung : ∀ j ≤ depth, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap) :
    ∀ j ≤ depth,
      slotWeight *
          (first.cdfReal ((2 * (j : ℝ) + 1) * gap) -
            first.cdfReal ((2 * (j : ℝ) - 1) * gap)) =
        2 * marginalCost := by
  have hflat := rung_flatness_le hgap hweight hcost hnash hpos depth
    (fun j hj => hSecondRung j (Nat.le_succ_of_le hj)) hFirstRung
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  have hsecondMax : ∀ j ≤ depth + 1,
      realPureExpectedPayoff slotWeight gap marginalCost first
          (2 * (j : ℝ) * gap) =
        borelExpectedPayoff slotWeight gap marginalCost second first := by
    intro j hj
    obtain ⟨action, hmem, hvalue⟩ := hSecondRung j hj
    exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.2 hmem
      hvalue.symm
  intro j hj
  refine rung_increment_eq (own := second) (opponent := first)
    (anchor := 2 * (j : ℝ) * gap) hgap ?_ ?_ ?_ ?_
  · rcases j with _ | m
    · intro point hpoint
      have hlow : point < gap := by
        have := hpoint.2
        push_cast at this ⊢
        linarith
      have hbelow : ((2 * ((0 : ℕ) : ℝ) - 1) * gap) < gap := by
        push_cast
        linarith
      rw [cdfReal_eq_zero_of_lt_lowerSupport first (by rw [hband]; exact hlow),
        cdfReal_eq_zero_of_lt_lowerSupport first (by rw [hband]; exact hbelow)]
    · intro point hpoint
      have hstep := (hflat m (Nat.le_of_succ_le hj)).2 point
        ⟨by have := hpoint.1; push_cast at this ⊢; linarith,
          by have := hpoint.2; push_cast at this ⊢; linarith⟩
      have hindex : (2 * ((m : ℝ) + 1) - 1) * gap = (2 * (m : ℝ) + 1) * gap := by
        ring
      rw [hstep]
      push_cast
      rw [hindex]
  · intro point hpoint
    have hstep := (hflat j hj).2 point
      ⟨by have := hpoint.1; linarith, by have := hpoint.2; linarith⟩
    rw [hstep]
  · exact hsecondMax j (Nat.le_succ_of_le hj)
  · have hnext := hsecondMax (j + 1) (by omega)
    have hindex : 2 * (((j : ℝ) + 1)) * gap = 2 * (j : ℝ) * gap + 2 * gap := by
      ring
    push_cast at hnext
    rw [hindex] at hnext
    exact hnext

/-- The rung count as far as the ladder reaches. -/
theorem first_cdfReal_rung_value_le
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ)
    (hSecondRung : ∀ j ≤ depth + 1, ∃ action ∈ second.support,
      (action : ℝ) = 2 * (j : ℝ) * gap)
    (hFirstRung : ∀ j ≤ depth, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap) :
    ∀ j ≤ depth,
      slotWeight * first.cdfReal ((2 * (j : ℝ) + 1) * gap) =
        ((j : ℝ) + 1) * (2 * marginalCost) := by
  have hincrement := first_rung_increments_le hgap hweight hcost hnash hpos
    depth hSecondRung hFirstRung
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  intro j
  induction j with
  | zero =>
    intro hj
    have hstep := hincrement 0 hj
    have hbelow : first.cdfReal ((2 * ((0 : ℕ) : ℝ) - 1) * gap) = 0 := by
      refine cdfReal_eq_zero_of_lt_lowerSupport first ?_
      rw [hband]
      push_cast
      linarith
    rw [hbelow] at hstep
    push_cast at hstep ⊢
    linarith
  | succ m ih =>
    intro hsucc
    have hprev := ih (Nat.le_of_succ_le hsucc)
    have hstep := hincrement (m + 1) hsucc
    have hindex : (2 * (((m : ℕ) + 1 : ℕ) : ℝ) - 1) * gap =
        (2 * (m : ℝ) + 1) * gap := by
      push_cast
      ring
    rw [hindex] at hstep
    push_cast at hstep hprev ⊢
    linarith

/-- **The ladder length bounds the cost ratio.**  A ladder reaching rung `depth`
forces `2(depth+1)` times the cost ratio to be at most one.  This is what makes
the recursion terminate; it is weaker than the window's edges, which the
opponent's ladder supplies. -/
theorem rung_count_bound
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ)
    (hSecondRung : ∀ j ≤ depth + 1, ∃ action ∈ second.support,
      (action : ℝ) = 2 * (j : ℝ) * gap)
    (hFirstRung : ∀ j ≤ depth, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap) :
    ((depth : ℝ) + 1) * (2 * marginalCost) ≤ slotWeight := by
  have hvalue := first_cdfReal_rung_value_le hgap hweight hcost hnash hpos depth
    hSecondRung hFirstRung depth (le_refl depth)
  have hbound := first.cdfReal_le_one ((2 * (depth : ℝ) + 1) * gap)
  nlinarith [mul_le_mul_of_nonneg_left hbound hweight.le, hvalue]

/-! ### The opponent's ladder and the window's upper edge

The same two-band equation anchored at the odd rungs reads the opponent's
increments, so the opponent's distribution function at its own rungs is its
atom at zero plus the rung count times twice the cost ratio.  Since that atom
strictly exceeds the cost ratio in a positive-payoff equilibrium, and a
distribution function is bounded by one, the ladder length bounds the cost ratio
from above: this is `q < 1/(2 nu - 1)`. -/

/-- Equation (S) on the opponent's ladder. -/
theorem second_rung_increments_le
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ)
    (hSecondRung : ∀ j ≤ depth, ∃ action ∈ second.support,
      (action : ℝ) = 2 * (j : ℝ) * gap)
    (hFirstRung : ∀ j ≤ depth, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap) :
    ∀ m : ℕ, m + 1 ≤ depth →
      slotWeight *
          (second.cdfReal ((2 * (m : ℝ) + 2) * gap) -
            second.cdfReal (2 * (m : ℝ) * gap)) =
        2 * marginalCost := by
  have hflat := rung_flatness_le hgap hweight hcost hnash hpos depth
    hSecondRung hFirstRung
  have hfirstMax : ∀ j ≤ depth,
      realPureExpectedPayoff slotWeight gap marginalCost second
          ((2 * (j : ℝ) + 1) * gap) =
        borelExpectedPayoff slotWeight gap marginalCost first second := by
    intro j hj
    obtain ⟨action, hmem, hvalue⟩ := hFirstRung j hj
    exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.1 hmem
      hvalue.symm
  intro m hm
  have hmle : m ≤ depth := Nat.le_of_succ_le hm
  refine rung_increment_eq (own := first) (opponent := second)
    (anchor := (2 * (m : ℝ) + 1) * gap) hgap ?_ ?_ ?_ ?_
  · intro point hpoint
    exact (hflat m hmle).1 point
      ⟨by have := hpoint.1; linarith, by have := hpoint.2; linarith⟩
  · intro point hpoint
    have hstep := (hflat (m + 1) hm).1 point
      ⟨by have := hpoint.1; push_cast at this ⊢; linarith,
        by have := hpoint.2; push_cast at this ⊢; linarith⟩
    have hindex : 2 * (((m : ℕ) + 1 : ℕ) : ℝ) * gap =
        (2 * (m : ℝ) + 2) * gap := by
      push_cast
      ring
    rw [hstep, hindex]
  · exact hfirstMax m hmle
  · have hnext := hfirstMax (m + 1) hm
    have hindex : (2 * (((m : ℕ) + 1 : ℕ) : ℝ) + 1) * gap =
        (2 * (m : ℝ) + 1) * gap + 2 * gap := by
      push_cast
      ring
    rw [hindex] at hnext
    exact hnext

/-- The opponent's distribution function at its own rungs. -/
theorem second_cdfReal_rung_value_le
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ)
    (hSecondRung : ∀ j ≤ depth, ∃ action ∈ second.support,
      (action : ℝ) = 2 * (j : ℝ) * gap)
    (hFirstRung : ∀ j ≤ depth, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap) :
    ∀ j ≤ depth,
      slotWeight * second.cdfReal (2 * (j : ℝ) * gap) =
        slotWeight * second.cdfReal 0 + (j : ℝ) * (2 * marginalCost) := by
  have hincrement := second_rung_increments_le hgap hweight hcost hnash hpos
    depth hSecondRung hFirstRung
  intro j
  induction j with
  | zero =>
    intro _
    norm_num
  | succ m ih =>
    intro hsucc
    have hprev := ih (Nat.le_of_succ_le hsucc)
    have hstep := hincrement m hsucc
    have hindex : 2 * (((m : ℕ) + 1 : ℕ) : ℝ) * gap =
        (2 * (m : ℝ) + 2) * gap := by
      push_cast
      ring
    rw [hindex]
    push_cast at hstep hprev ⊢
    linarith

/-- **The window's upper edge.**  A ladder reaching rung `depth` forces
`2 depth + 1` times the cost ratio to be strictly below one.  With
`nu = depth + 1` this is the paper's `q < 1/(2 nu - 1)`, and it is sharp: at
`nu = 2` it reads `3 q < 1`. -/
theorem window_upper_edge
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ)
    (hSecondRung : ∀ j ≤ depth, ∃ action ∈ second.support,
      (action : ℝ) = 2 * (j : ℝ) * gap)
    (hFirstRung : ∀ j ≤ depth, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap) :
    (2 * (depth : ℝ) + 1) * marginalCost < slotWeight := by
  have hvalue := second_cdfReal_rung_value_le hgap hweight hcost hnash hpos
    depth hSecondRung hFirstRung depth (le_refl depth)
  have hbound := second.cdfReal_le_one (2 * (depth : ℝ) * gap)
  have hatom := atom_gt_cost_ratio_of_payoff_pos hgap hweight hcost hnash hpos
  nlinarith [mul_le_mul_of_nonneg_left hbound hweight.le, hvalue, hatom]

/-! ### The terminal rung and the window's lower edge

The edges proved so far use only that a distribution function is bounded by
one.  The lower edge uses that it reaches one: once the advantaged player's
ladder stops, its distribution function is flat at one above the last rung, so
the opponent's unused deviation one band further reads the cost ratio from
below. -/

/-- A distribution function reaches one above the whole support. -/
theorem cdfReal_eq_one_of_support_le (strategy : BorelMixedStrategy) {x : ℝ}
    (hsupport : ∀ action ∈ strategy.support, (action : ℝ) ≤ x) :
    strategy.cdfReal x = 1 := by
  have hcompl : (strategy.law : Measure NNReal)
      {action : NNReal | action ∉ strategy.support} = 0 :=
    ae_iff.mp strategy.ae_mem_support
  have hmeas : MeasurableSet {action : NNReal | (action : ℝ) ≤ x} :=
    measurable_coe_nnreal_real measurableSet_Iic
  have hsub : ({action : NNReal | (action : ℝ) ≤ x})ᶜ ⊆
      {action : NNReal | action ∉ strategy.support} := by
    intro action haction hmem
    exact haction (hsupport action hmem)
  have hzero : (strategy.law : Measure NNReal)
      ({action : NNReal | (action : ℝ) ≤ x})ᶜ = 0 :=
    measure_mono_null hsub hcompl
  have hsplit := measure_add_measure_compl
    (μ := (strategy.law : Measure NNReal)) hmeas
  rw [hzero, add_zero] at hsplit
  have hone : strategy.cdf x = 1 := by simpa using hsplit
  rw [BorelMixedStrategy.cdfReal, hone, ENNReal.toReal_one]

/-- **The window's lower edge.**  If the advantaged player's ladder stops at
rung `depth`, the opponent's unused deviation one band past the top of that
ladder forces `2 depth + 2` times the cost ratio to be at least one.  With
`nu = depth + 1` this is the paper's `q >= 1/(2 nu)`. -/
theorem window_lower_edge
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (_hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ)
    (hterminal : ∀ action ∈ first.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap) :
    slotWeight ≤ (2 * (depth : ℝ) + 2) * marginalCost := by
  obtain ⟨-, hzeroPayoff, -⟩ :=
    opponent_at_bottom_of_payoff_pos hgap.le hcost hnash hpos
  have hfull : ∀ point : ℝ, (2 * (depth : ℝ) + 1) * gap ≤ point →
      first.cdfReal point = 1 := by
    intro point hpoint
    exact cdfReal_eq_one_of_support_le first
      (fun action hmem => le_trans (hterminal action hmem) hpoint)
  have hdepthNonneg : (0 : ℝ) ≤ (depth : ℝ) := Nat.cast_nonneg depth
  have hintegral :
      (∫ point in ((2 * (depth : ℝ) + 2) * gap - gap)..
          ((2 * (depth : ℝ) + 2) * gap), first.cdfReal point) = gap := by
    have hlow : (2 * (depth : ℝ) + 2) * gap - gap =
        (2 * (depth : ℝ) + 1) * gap := by ring
    rw [hlow]
    have hstep := first.integral_cdfReal_of_flat (base := 1)
      (by nlinarith : (2 * (depth : ℝ) + 1) * gap ≤ (2 * (depth : ℝ) + 2) * gap)
      (fun point hpoint => hfull point hpoint.1)
    rw [hstep]
    ring
  have hdeviation :=
    realPureExpectedPayoff_nonpos_of_zero_payoff (slotWeight := slotWeight)
      (marginalCost := marginalCost) hgap.le hnash.2 hzeroPayoff
      (x := (2 * (depth : ℝ) + 2) * gap) (by nlinarith)
  rw [realPureExpectedPayoff, hintegral] at hdeviation
  nlinarith [hdeviation, hgap]

/-- **The window.**  A ladder that reaches rung `depth` and stops there places
the cost ratio in the paper's window: with `nu = depth + 1`,
`1/(2 nu) <= q < 1/(2 nu - 1)`. -/
theorem positive_payoff_window
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
    (hterminal : ∀ action ∈ first.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap) :
    slotWeight ≤ (2 * (depth : ℝ) + 2) * marginalCost ∧
      (2 * (depth : ℝ) + 1) * marginalCost < slotWeight :=
  ⟨window_lower_edge hgap hweight hcost hnash hpos depth hterminal,
    window_upper_edge hgap hweight hcost hnash hpos depth hSecondRung
      hFirstRung⟩

/-! ### The payoff on the window

The bottom condition prices the advantaged player's payoff by the opponent's
atom at zero.  The opponent's ladder turns that atom into the ladder length
once the ladder is complete, and the payoff comes out in closed form. -/

/-- **The payoff on the window.**  If the opponent's ladder reaches rung `depth`
and stops there, the advantaged player's payoff is the contested band times the
slot weight net of `2 depth + 1` times the marginal cost.  With
`nu = depth + 1` this is the paper's `U = w1 G (1 - (2 nu - 1) q)`. -/
theorem positive_payoff_value
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
    (hSecondTerminal : ∀ action ∈ second.support,
      (action : ℝ) ≤ 2 * (depth : ℝ) * gap) :
    borelExpectedPayoff slotWeight gap marginalCost first second =
      (slotWeight - (2 * (depth : ℝ) + 1) * marginalCost) * gap := by
  obtain ⟨-, hvalue⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  have hladder := second_cdfReal_rung_value_le hgap hweight hcost hnash hpos
    depth hSecondRung hFirstRung depth (le_refl depth)
  have hcomplete : second.cdfReal (2 * (depth : ℝ) * gap) = 1 :=
    cdfReal_eq_one_of_support_le second hSecondTerminal
  rw [hcomplete, mul_one] at hladder
  rw [hvalue]
  have hatom : slotWeight * second.cdfReal 0 =
      slotWeight - (depth : ℝ) * (2 * marginalCost) := by
    linarith
  rw [show slotWeight * second.cdfReal 0 - marginalCost =
      slotWeight - (2 * (depth : ℝ) + 1) * marginalCost by
    rw [hatom]; ring]

/-- **The payoff is at most one band's cost.**  The window's lower edge caps the
advantaged player's payoff, which is the form part (iv) of
`prop:sp_allequilibria` consumes. -/
theorem positive_payoff_le_cost_band
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
    (hSecondTerminal : ∀ action ∈ second.support,
      (action : ℝ) ≤ 2 * (depth : ℝ) * gap)
    (hFirstTerminal : ∀ action ∈ first.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap) :
    borelExpectedPayoff slotWeight gap marginalCost first second ≤
      marginalCost * gap := by
  have hvalue := positive_payoff_value hgap hweight hcost hnash hpos depth
    hSecondRung hFirstRung hSecondTerminal
  have hedge := window_lower_edge hgap hweight hcost hnash hpos depth
    hFirstTerminal
  rw [hvalue]
  nlinarith [hedge, hgap]

end

end SmoothingCliff.Racing
