import SmoothingCliff.Racing.RungCount

/-!
# The support is the lattice

The clearings proved so far say that between consecutive rungs there is no
support.  Assembling them upward turns that into the containment the paper
states: the advantaged player keeps mass only on the odd rungs, and the
opponent only on the even ones.

The assembly is an induction on the ladder length.  An action at or below the
top rung is either at or below the rung before it, in which case the shorter
ladder already places it, or above the previous clearing, in which case it is
squeezed onto the top rung itself.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- The clearing at each odd rung, from the flatness the recursion supplies. -/
theorem first_support_cleared_at
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
    ∀ j ≤ depth, ∀ action ∈ first.support,
      (action : ℝ) ≤ (2 * (j : ℝ) + 1) * gap ∨
        (2 * (j : ℝ) + 3) * gap ≤ (action : ℝ) := by
  have hflat := rung_flatness_le hgap hweight hcost hnash hpos depth
    hSecondRung hFirstRung
  intro j hj action hmem
  obtain ⟨rung, hrungMem, hrungValue⟩ := hFirstRung j hj
  have hstep := support_cleared_two_bands (base := second.cdfReal
    (2 * (j : ℝ) * gap)) hgap hweight hcost hnash.1
    (anchor := (2 * (j : ℝ) + 1) * gap)
    (fun point hpoint => (hflat j hj).1 point
      ⟨by have := hpoint.1; linarith, by have := hpoint.2; linarith⟩)
    (realPureExpectedPayoff_eq_max_at_support hgap.le hnash.1 hrungMem
      hrungValue.symm)
    hmem
  rcases hstep with hlow | hhigh
  · exact Or.inl hlow
  · exact Or.inr (by linarith)

/-- **The advantaged player's support is the odd lattice.**  Every action it
keeps at or below the top rung sits exactly on one of the rungs. -/
theorem first_support_lattice
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    ∀ depth : ℕ,
      (∀ j ≤ depth, ∃ action ∈ second.support,
        (action : ℝ) = 2 * (j : ℝ) * gap) →
      (∀ j ≤ depth, ∃ action ∈ first.support,
        (action : ℝ) = (2 * (j : ℝ) + 1) * gap) →
      ∀ action ∈ first.support,
        (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap →
          ∃ j ≤ depth, (action : ℝ) = (2 * (j : ℝ) + 1) * gap := by
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  intro depth
  induction depth with
  | zero =>
    intro _ _ action hmem hle
    refine ⟨0, le_refl 0, ?_⟩
    have hlow : gap ≤ (action : ℝ) := by
      rw [← hband]
      exact_mod_cast first.lowerSupport_le_of_mem_support hmem
    push_cast at hle ⊢
    linarith
  | succ m ih =>
    intro hSecondRung hFirstRung action hmem hle
    have hclear := first_support_cleared_at hgap hweight hcost hnash hpos (m + 1)
      hSecondRung hFirstRung m (Nat.le_succ m) action hmem
    rcases hclear with hbelow | habove
    · obtain ⟨j, hj, hvalue⟩ := ih
        (fun i hi => hSecondRung i (Nat.le_succ_of_le hi))
        (fun i hi => hFirstRung i (Nat.le_succ_of_le hi)) action hmem hbelow
      exact ⟨j, Nat.le_succ_of_le hj, hvalue⟩
    · refine ⟨m + 1, le_refl _, ?_⟩
      push_cast at hle habove ⊢
      linarith

/-- The clearing at each even rung.  Below the first rung the advantaged
player's distribution function vanishes, which is the flat window the anchor at
zero needs. -/
theorem second_support_cleared_at
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
    ∀ j ≤ depth, ∀ action ∈ second.support,
      (action : ℝ) ≤ 2 * (j : ℝ) * gap ∨
        (2 * (j : ℝ) + 2) * gap ≤ (action : ℝ) := by
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  have hflat := rung_flatness_le hgap hweight hcost hnash hpos depth
    hSecondRung hFirstRung
  intro j hj action hmem
  obtain ⟨rung, hrungMem, hrungValue⟩ := hSecondRung j hj
  have hanchor := realPureExpectedPayoff_eq_max_at_support hgap.le hnash.2
    hrungMem hrungValue.symm
  have hstep : (action : ℝ) ≤ 2 * (j : ℝ) * gap ∨
      2 * (j : ℝ) * gap + 2 * gap ≤ (action : ℝ) := by
    rcases j with _ | m
    · refine support_cleared_two_bands (base := (0 : ℝ)) hgap hweight hcost
        hnash.2 (anchor := 2 * ((0 : ℕ) : ℝ) * gap) ?_ hanchor hmem
      intro point hpoint
      refine cdfReal_eq_zero_of_lt_lowerSupport first ?_
      rw [hband]
      have := hpoint.2
      push_cast at this ⊢
      linarith
    · refine support_cleared_two_bands (base := first.cdfReal
        ((2 * (m : ℝ) + 1) * gap)) hgap hweight hcost hnash.2
        (anchor := 2 * (((m : ℕ) + 1 : ℕ) : ℝ) * gap) ?_ hanchor hmem
      intro point hpoint
      refine (hflat m (Nat.le_of_succ_le hj)).2 point ?_
      constructor
      · have := hpoint.1; push_cast at this ⊢; linarith
      · have := hpoint.2; push_cast at this ⊢; linarith
  rcases hstep with hlow | hhigh
  · exact Or.inl hlow
  · exact Or.inr (by linarith)

/-- **The opponent's support is the even lattice.** -/
theorem second_support_lattice
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    ∀ depth : ℕ,
      (∀ j ≤ depth, ∃ action ∈ second.support,
        (action : ℝ) = 2 * (j : ℝ) * gap) →
      (∀ j ≤ depth, ∃ action ∈ first.support,
        (action : ℝ) = (2 * (j : ℝ) + 1) * gap) →
      ∀ action ∈ second.support,
        (action : ℝ) ≤ 2 * (depth : ℝ) * gap →
          ∃ j ≤ depth, (action : ℝ) = 2 * (j : ℝ) * gap := by
  intro depth
  induction depth with
  | zero =>
    intro _ _ action _ hle
    refine ⟨0, le_refl 0, ?_⟩
    have hlow : (0 : ℝ) ≤ (action : ℝ) := action.coe_nonneg
    push_cast at hle ⊢
    linarith
  | succ m ih =>
    intro hSecondRung hFirstRung action hmem hle
    have hclear := second_support_cleared_at hgap hweight hcost hnash hpos
      (m + 1) hSecondRung hFirstRung m (Nat.le_succ m) action hmem
    rcases hclear with hbelow | habove
    · obtain ⟨j, hj, hvalue⟩ := ih
        (fun i hi => hSecondRung i (Nat.le_succ_of_le hi))
        (fun i hi => hFirstRung i (Nat.le_succ_of_le hi)) action hmem hbelow
      exact ⟨j, Nat.le_succ_of_le hj, hvalue⟩
    · refine ⟨m + 1, le_refl _, ?_⟩
      push_cast at hle habove ⊢
      linarith

/-! ### Odd gaps and the dissipation

Every distance between an odd rung and an even rung is an odd multiple of the
contested band, so it is at least one band and the capped absolute difference
saturates.  The payoff identity then reads dissipation off the payoff. -/

/-- An odd number and an even number are at least one apart. -/
theorem one_le_abs_odd_sub_even (j k : ℕ) :
    (1 : ℝ) ≤ |(2 * (j : ℝ) + 1) - 2 * (k : ℝ)| := by
  rcases le_or_gt (k : ℝ) (j : ℝ) with hle | hlt
  · rw [abs_of_nonneg (by linarith)]
    linarith
  · have hkj : j < k := by exact_mod_cast hlt
    have hstep : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hkj
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- **The gaps saturate the band.**  Almost surely the two actions are at least
one contested band apart, so the capped absolute difference is the band. -/
theorem min_abs_diff_eq_gap_ae
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
    ∀ᵐ profile ∂((first.law : Measure NNReal).prod
        (second.law : Measure NNReal)),
      min |(profile.1 : ℝ) - (profile.2 : ℝ)| gap = gap := by
  have haeFirst : ∀ᵐ profile : NNReal × NNReal
      ∂((first.law : Measure NNReal).prod (second.law : Measure NNReal)),
      profile.1 ∈ first.support :=
    Measure.quasiMeasurePreserving_fst.ae first.ae_mem_support
  have haeSecond : ∀ᵐ profile : NNReal × NNReal
      ∂((first.law : Measure NNReal).prod (second.law : Measure NNReal)),
      profile.2 ∈ second.support :=
    Measure.quasiMeasurePreserving_snd.ae second.ae_mem_support
  filter_upwards [haeFirst, haeSecond] with profile hone htwo
  obtain ⟨j, -, hjvalue⟩ := first_support_lattice hgap hweight hcost hnash hpos
    depth hSecondRung hFirstRung profile.1 hone (hFirstTerminal profile.1 hone)
  obtain ⟨k, -, hkvalue⟩ := second_support_lattice hgap hweight hcost hnash hpos
    depth hSecondRung hFirstRung profile.2 htwo
    (hSecondTerminal profile.2 htwo)
  have hdiff : (profile.1 : ℝ) - (profile.2 : ℝ) =
      ((2 * (j : ℝ) + 1) - 2 * (k : ℝ)) * gap := by
    rw [hjvalue, hkvalue]
    ring
  have hband : gap ≤ |(profile.1 : ℝ) - (profile.2 : ℝ)| := by
    rw [hdiff, abs_mul, abs_of_pos hgap]
    nlinarith [one_le_abs_odd_sub_even j k, hgap]
  exact min_eq_right hband

/-- **The dissipation on the window.**  Total dissipation is the contested band
times `2 depth + 1` marginal costs; with `nu = depth + 1` this is the paper's
`D = (2 nu - 1) q w1 G`. -/
theorem positive_dissipation_value
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
    borelExpectedDissipation marginalCost first second =
      (2 * (depth : ℝ) + 1) * marginalCost * gap := by
  obtain ⟨-, hzeroPayoff, -⟩ :=
    opponent_at_bottom_of_payoff_pos hgap.le hcost hnash hpos
  have hpayoff := positive_payoff_value hgap hweight hcost hnash hpos depth
    hSecondRung hFirstRung hSecondTerminal
  have hidentity := borelExpectedPayoff_add_symm (slotWeight := slotWeight)
    (marginalCost := marginalCost) hgap.le first second
    (by
      refine (integrable_const gap).mono' ?_ ?_
      · refine Measurable.aestronglyMeasurable ?_
        unfold strictPriorityCapturedGap
        fun_prop
      · filter_upwards with profile
        rw [Real.norm_eq_abs,
          abs_of_nonneg (strictPriorityCapturedGap_nonneg hgap.le)]
        exact strictPriorityCapturedGap_le_gap)
    (by
      refine (integrable_const gap).mono' ?_ ?_
      · refine Measurable.aestronglyMeasurable ?_
        unfold strictPriorityCapturedGap
        fun_prop
      · filter_upwards with profile
        rw [Real.norm_eq_abs,
          abs_of_nonneg (strictPriorityCapturedGap_nonneg hgap.le)]
        exact strictPriorityCapturedGap_le_gap)
  have hconstant :
      (∫ profile : NNReal × NNReal,
          min |(profile.1 : ℝ) - (profile.2 : ℝ)| gap
          ∂((first.law : Measure NNReal).prod
            (second.law : Measure NNReal))) = gap := by
    rw [integral_congr_ae (min_abs_diff_eq_gap_ae hgap hweight hcost hnash hpos
      depth hSecondRung hFirstRung hFirstTerminal hSecondTerminal)]
    simp
  rw [hconstant, hzeroPayoff, hpayoff] at hidentity
  linarith

/-! ### The lower boundary

The window's lower edge came from the opponent's deviation one band past the
top of the advantaged player's ladder being unprofitable.  If the opponent
actually keeps mass there, that deviation is used and the inequality becomes an
equality: the cost ratio sits exactly on the lower boundary.  This is the
paper's second terminal case, where the opponent has a final atom at
`2 nu` bands, and it is what separates the one-parameter family from the unique
profile on the open window. -/

/-- **The lower boundary is forced.**  If the advantaged player's ladder stops
at rung `depth` and the opponent keeps mass one band past the top of it, the
cost ratio sits exactly on the boundary `q = 1/(2 nu)` with `nu = depth + 1`. -/
theorem boundary_forced
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (_hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ)
    (hFirstTerminal : ∀ action ∈ first.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap)
    {rung : NNReal} (hrungValue : (rung : ℝ) = (2 * (depth : ℝ) + 2) * gap)
    (hrung : rung ∈ second.support) :
    slotWeight = (2 * (depth : ℝ) + 2) * marginalCost := by
  obtain ⟨-, hzeroPayoff, -⟩ :=
    opponent_at_bottom_of_payoff_pos hgap.le hcost hnash hpos
  have hdepthNonneg : (0 : ℝ) ≤ (depth : ℝ) := Nat.cast_nonneg depth
  have hfull : ∀ point : ℝ, (2 * (depth : ℝ) + 1) * gap ≤ point →
      first.cdfReal point = 1 := by
    intro point hpoint
    exact cdfReal_eq_one_of_support_le first
      (fun action hmem => le_trans (hFirstTerminal action hmem) hpoint)
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
  have hused := realPureExpectedPayoff_eq_max_at_support hgap.le hnash.2 hrung
    hrungValue.symm
  rw [hzeroPayoff, realPureExpectedPayoff, hintegral] at hused
  have hgapNe : gap ≠ 0 := ne_of_gt hgap
  field_simp at hused
  nlinarith [hused, hgap]

/-- **The open window admits no extra rung.**  Strictly inside the window the
opponent keeps no mass one band past the top of the advantaged player's ladder,
so the one-parameter family lives only on the boundary. -/
theorem no_extra_rung_off_boundary
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ)
    (hFirstTerminal : ∀ action ∈ first.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap)
    (hopen : slotWeight ≠ (2 * (depth : ℝ) + 2) * marginalCost)
    {rung : NNReal} (hrungValue : (rung : ℝ) = (2 * (depth : ℝ) + 2) * gap) :
    rung ∉ second.support := fun hrung =>
  hopen (boundary_forced hgap hweight hcost hnash hpos depth hFirstTerminal
    hrungValue hrung)

/-- **The payoff cap on the boundary.**  Even when the opponent carries a final
atom past the ladder, its atom at zero is at most twice the cost ratio, so the
advantaged player's payoff is still at most one band's cost. -/
theorem positive_payoff_le_cost_band_boundary
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
    (hboundary : slotWeight = (2 * (depth : ℝ) + 2) * marginalCost) :
    borelExpectedPayoff slotWeight gap marginalCost first second ≤
      marginalCost * gap := by
  obtain ⟨-, hvalue⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  have hladder := second_cdfReal_rung_value_le hgap hweight hcost hnash hpos
    depth hSecondRung hFirstRung depth (le_refl depth)
  have hbound := second.cdfReal_le_one (2 * (depth : ℝ) * gap)
  have hatom : slotWeight * second.cdfReal 0 ≤ 2 * marginalCost := by
    nlinarith [mul_le_mul_of_nonneg_left hbound hweight.le, hladder, hboundary]
  rw [hvalue]
  nlinarith [hatom, hgap]

end

end SmoothingCliff.Racing
