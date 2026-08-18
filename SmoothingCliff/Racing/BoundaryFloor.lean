import SmoothingCliff.Racing.PositiveProfile
import SmoothingCliff.Racing.NextSupport

/-!
# The boundary family, and the selection-free floor

The classification leaves the boundary case with an extra atom one band above
the advantaged player's top rung.  That atom still sits on the even lattice, so
the support gaps are still odd and the capped absolute difference still
saturates.  The payoff identity then gives the dissipation there too, and with
the unconditional payoff cap the floor of `prop:sp_floor` holds in every
equilibrium of the race, whichever class it falls in.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- In the boundary case the opponent's support still sits on the even lattice,
one rung further out. -/
theorem second_support_lattice_boundary
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ) (hreach : LadderReaches first second gap depth)
    (hcap : ∀ action ∈ second.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 2) * gap) :
    ∀ action ∈ second.support,
      ∃ j ≤ depth + 1, (action : ℝ) = 2 * (j : ℝ) * gap := by
  intro action hmem
  rcases second_support_cleared_at hgap hweight hcost hnash hpos depth
    hreach.1 hreach.2 depth (le_refl depth) action hmem with hlow | hhigh
  · obtain ⟨j, hj, hvalue⟩ := second_support_lattice hgap hweight hcost hnash
      hpos depth hreach.1 hreach.2 action hmem hlow
    exact ⟨j, Nat.le_succ_of_le hj, hvalue⟩
  · refine ⟨depth + 1, le_refl _, ?_⟩
    have := le_antisymm (hcap action hmem) hhigh
    rw [this]
    push_cast
    ring

/-- The gaps still saturate in the boundary case. -/
theorem min_abs_diff_eq_gap_ae_boundary
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ) (hreach : LadderReaches first second gap depth)
    (hFirstTerminal : ∀ action ∈ first.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap)
    (hcap : ∀ action ∈ second.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 2) * gap) :
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
    depth hreach.1 hreach.2 profile.1 hone (hFirstTerminal profile.1 hone)
  obtain ⟨k, -, hkvalue⟩ := second_support_lattice_boundary hgap hweight hcost
    hnash hpos depth hreach hcap profile.2 htwo
  have hdiff : (profile.1 : ℝ) - (profile.2 : ℝ) =
      ((2 * (j : ℝ) + 1) - 2 * (k : ℝ)) * gap := by
    rw [hjvalue, hkvalue]
    ring
  have hband : gap ≤ |(profile.1 : ℝ) - (profile.2 : ℝ)| := by
    rw [hdiff, abs_mul, abs_of_pos hgap]
    nlinarith [one_le_abs_odd_sub_even j k, hgap]
  exact min_eq_right hband

/-- **The floor in the boundary case.**  The capped difference saturates there
too, so the payoff identity and the unconditional payoff cap give the same
bound. -/
theorem boundary_dissipation_ge_prize_net_cost
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ) (hreach : LadderReaches first second gap depth)
    (hFirstTerminal : ∀ action ∈ first.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap)
    (hcap : ∀ action ∈ second.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 2) * gap) :
    (slotWeight - marginalCost) * gap ≤
      borelExpectedDissipation marginalCost first second := by
  obtain ⟨-, hzeroSecond, -⟩ :=
    opponent_at_bottom_of_payoff_pos hgap.le hcost hnash hpos
  have hcapPayoff := positive_payoff_le_cost_band_of_support hgap hweight hcost
    hnash hzeroSecond
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
    rw [integral_congr_ae (min_abs_diff_eq_gap_ae_boundary hgap hweight hcost
      hnash hpos depth hreach hFirstTerminal hcap)]
    simp
  rw [hconstant, hzeroSecond] at hidentity
  linarith [hidentity, hcapPayoff]

/-! ### The selection-free floor

Part (i) says at least one payoff vanishes in every equilibrium.  If both do,
the lattice deviation bound applies in both directions and the arithmetic of
part (iv) lifts it to the paper's constant.  If one is positive, the
classification places the equilibrium in one of the two terminal cases, and both
give the same bound.  So the floor holds at every equilibrium with no selection.
-/

theorem borelExpectedDissipation_comm
    (marginalCost : ℝ) (first second : BorelMixedStrategy) :
    borelExpectedDissipation marginalCost first second =
      borelExpectedDissipation marginalCost second first := by
  unfold borelExpectedDissipation
  ring

/-- The floor whenever one player earns a positive payoff. -/
theorem positive_nash_dissipation_ge_prize_net_cost
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    (slotWeight - marginalCost) * gap ≤
      borelExpectedDissipation marginalCost first second := by
  obtain ⟨depth, hreach, hmaximal⟩ :=
    exists_last_rung hgap hweight hcost hnash hpos
  have hcap := second_support_le_two_bands_past hgap hweight hcost hnash hpos
    depth hreach hmaximal
  rcases positive_payoff_terminal_dichotomy hgap hweight hcost hnash hpos depth
    hreach hmaximal hcap with hstop | ⟨-, hFirstTerminal⟩
  · exact positive_dissipation_ge_prize_net_cost hgap hweight hcost hnash hpos
      depth hreach.1 hreach.2
      (first_terminal_of_second_terminal hgap hweight hcost hnash hpos depth
        hreach hstop)
      hstop
  · exact boundary_dissipation_ge_prize_net_cost hgap hweight hcost hnash hpos
      depth hreach hFirstTerminal hcap

/-- The floor-depth conditions at the integer part of the reciprocal cost
ratio. -/
theorem floorDepth_bounds {slotWeight marginalCost : ℝ} (hweight : 0 < slotWeight)
    (hcost : 0 < marginalCost) :
    ((⌊slotWeight / marginalCost⌋₊ : ℝ) * (marginalCost / slotWeight) ≤ 1) ∧
      1 < (⌊slotWeight / marginalCost⌋₊ : ℝ) * (marginalCost / slotWeight) +
        marginalCost / slotWeight := by
  have hquotNonneg : (0 : ℝ) ≤ slotWeight / marginalCost :=
    le_of_lt (div_pos hweight hcost)
  have hfloorLe := Nat.floor_le hquotNonneg
  have hfloorLt := Nat.lt_floor_add_one (slotWeight / marginalCost)
  rw [le_div_iff₀ hcost] at hfloorLe
  rw [div_lt_iff₀ hcost] at hfloorLt
  constructor
  · rw [← mul_div_assoc, div_le_one hweight]
    exact hfloorLe
  · rw [show ((⌊slotWeight / marginalCost⌋₊ : ℝ)) * (marginalCost / slotWeight) +
        marginalCost / slotWeight =
      (((⌊slotWeight / marginalCost⌋₊ : ℝ)) + 1) * marginalCost / slotWeight by
      ring]
    rw [lt_div_iff₀ hweight, one_mul]
    exact hfloorLt

/-- **The selection-free floor.**  Every Nash equilibrium of the
strict-priority race, pure or mixed, dissipates at least the whole contested
prize net of one band's cost.  This is `prop:sp_floor`. -/
theorem nash_dissipation_ge_prize_net_cost
    {slotWeight marginalCost : ℝ} (hweight : 0 < slotWeight)
    (hcost : 0 < marginalCost) {gap : NNReal} (hgap : 0 < (gap : ℝ))
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight (gap : ℝ) marginalCost first second) :
    (slotWeight - marginalCost) * (gap : ℝ) ≤
      borelExpectedDissipation marginalCost first second := by
  obtain ⟨hshare, hnext⟩ := floorDepth_bounds hweight hcost
  obtain ⟨hfirstNonneg, hsecondNonneg, hzero⟩ :=
    borelMixedNash_payoff_classification (gap := (gap : ℝ)) hgap.le hcost.le
      hnash
  rcases hzero with hzeroFirst | hzeroSecond
  · rcases lt_or_eq_of_le hsecondNonneg with hposSecond | hzeroSecond
    · have hswap : IsBorelMixedNash slotWeight (gap : ℝ) marginalCost second
          first := ⟨hnash.2, hnash.1⟩
      rw [borelExpectedDissipation_comm]
      exact positive_nash_dissipation_ge_prize_net_cost hgap hweight hcost
        hswap hposSecond
    · exact zeroPayoff_dissipation_ge_prize_net_cost hweight hcost gap
        ⌊slotWeight / marginalCost⌋₊ hnash.1 hnash.2 hzeroFirst
        hzeroSecond.symm hshare hnext
  · rcases lt_or_eq_of_le hfirstNonneg with hposFirst | hzeroFirst
    · exact positive_nash_dissipation_ge_prize_net_cost hgap hweight hcost
        hnash hposFirst
    · exact zeroPayoff_dissipation_ge_prize_net_cost hweight hcost gap
        ⌊slotWeight / marginalCost⌋₊ hnash.1 hnash.2 hzeroFirst.symm
        hzeroSecond hshare hnext

end

end SmoothingCliff.Racing
