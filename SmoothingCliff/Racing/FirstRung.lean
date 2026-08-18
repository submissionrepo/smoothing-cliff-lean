import SmoothingCliff.Racing.WindowSlope

/-!
# The first rung and the terminal case at one window

With the opponent's support cleared below two contested bands, the advantaged
player's return is flat across the whole first window: every action between one
band and two bands captures the opponent's atom at zero and nothing else, so
the payoff falls at the cost rate there.  The advantaged player therefore keeps
nothing strictly above one band and weakly below two, which is the first rung
of the odd lattice.

When the opponent puts everything at zero the recursion terminates at once.
The advantaged player is then pure at one band, the cost ratio is at least one
half, and the pair is the pure equilibrium of `prop:sp_race`: this is the case
`nu = 1` of the classification, with payoff the whole contested prize net of one
band's cost and dissipation exactly the cost of one band.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- **The first window is flat.**  With the opponent cleared below two bands,
every action between one band and two captures exactly the opponent's atom at
zero times the whole band. -/
theorem borelPureExpectedCapturedGap_first_window
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    {action : NNReal} (hlow : gap ≤ (action : ℝ))
    (hhigh : (action : ℝ) ≤ 2 * gap) :
    borelPureExpectedCapturedGap gap second action =
      second.cdfReal 0 * gap := by
  have hclear : ∀ rival ∈ second.support, rival ≠ 0 →
      (action : ℝ) ≤ (rival : ℝ) := by
    intro rival hrival hne
    exact le_trans hhigh
      (second_support_clear_below_two_gap hgap hweight hcost hnash hpos hrival
        hne)
  rw [borelPureExpectedCapturedGap_eq_atom_mul hgap.le second action hclear,
    min_eq_right hlow]

/-- **The first rung.**  The advantaged player keeps nothing strictly above one
contested band and weakly below two: on that stretch the payoff falls at the
cost rate from its maximum. -/
theorem first_support_clear_below_two_gap
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    {action : NNReal} (hmem : action ∈ first.support) :
    (action : ℝ) = gap ∨ 2 * gap < (action : ℝ) := by
  obtain ⟨hband, hvalue⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  by_contra hcon
  rw [not_or, not_lt] at hcon
  obtain ⟨hne, hhigh⟩ := hcon
  have hlow : gap ≤ (action : ℝ) := by
    rw [← hband]
    exact_mod_cast first.lowerSupport_le_of_mem_support hmem
  have hstrict : gap < (action : ℝ) := lt_of_le_of_ne hlow (Ne.symm hne)
  have hind :=
    borelMixedBestResponse_payoff_eq_on_support hgap.le hnash.1 action hmem
  rw [borelPureExpectedPayoff,
    borelPureExpectedCapturedGap_first_window hgap hweight hcost hnash hpos
      hlow hhigh, hvalue] at hind
  nlinarith [hind, hstrict, hcost]

/-- A law whose support sits at one point puts all its mass there. -/
theorem law_singleton_eq_one_of_support_subset
    (strategy : BorelMixedStrategy) {point : NNReal}
    (hsub : ∀ action ∈ strategy.support, action = point) :
    (strategy.law : Measure NNReal) {point} = 1 := by
  have hcompl : (strategy.law : Measure NNReal)
      {action : NNReal | action ∉ strategy.support} = 0 :=
    ae_iff.mp strategy.ae_mem_support
  have hsubset : (({point} : Set NNReal))ᶜ ⊆
      {action : NNReal | action ∉ strategy.support} := fun action haction hmem =>
    haction (hsub action hmem)
  have hzero : (strategy.law : Measure NNReal) (({point} : Set NNReal))ᶜ = 0 :=
    measure_mono_null hsubset hcompl
  have hsplit := measure_add_measure_compl (μ := (strategy.law : Measure NNReal))
    (measurableSet_singleton point)
  rw [hzero, add_zero] at hsplit
  simpa using hsplit

/-- All the mass at one point means almost every draw is that point. -/
theorem ae_eq_of_singleton_mass_one
    {strategy : BorelMixedStrategy} {point : NNReal}
    (hmass : (strategy.law : Measure NNReal) {point} = 1) :
    ∀ᵐ action ∂(strategy.law : Measure NNReal), action = point := by
  rw [ae_iff]
  have hcompl : (strategy.law : Measure NNReal) (({point} : Set NNReal))ᶜ = 0 := by
    rw [measure_compl (measurableSet_singleton point) (measure_ne_top _ _),
      hmass]
    simp
  simpa [Set.compl_def] using hcompl

/-- A pure opponent captures exactly the pointwise band. -/
theorem borelPureExpectedCapturedGap_of_singleton
    {gap : ℝ} {opponent : BorelMixedStrategy} {point : NNReal}
    (hmass : (opponent.law : Measure NNReal) {point} = 1) (action : NNReal) :
    borelPureExpectedCapturedGap gap opponent action =
      strictPriorityCapturedGap gap (action : ℝ) (point : ℝ) := by
  rw [borelPureExpectedCapturedGap]
  have hconst : ∫ rival : NNReal,
      strictPriorityCapturedGap gap (action : ℝ) (rival : ℝ)
      ∂(opponent.law : Measure NNReal) =
        ∫ _rival : NNReal,
          strictPriorityCapturedGap gap (action : ℝ) (point : ℝ)
          ∂(opponent.law : Measure NNReal) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_eq_of_singleton_mass_one hmass] with rival hrival
    rw [hrival]
  rw [hconst, MeasureTheory.integral_const]
  simp

/-- If the opponent keeps everything at zero, the captured band is the own
action capped at one contested band. -/
theorem borelPureExpectedCapturedGap_of_full_atom
    {gap : ℝ} {second : BorelMixedStrategy}
    (hfull : second.cdfReal 0 = 1) (action : NNReal) :
    borelPureExpectedCapturedGap gap second action =
      min (action : ℝ) gap := by
  have hmass : (second.law : Measure NNReal) {0} = 1 := by
    have hreal := hfull
    rw [cdfReal_zero_eq_massReal] at hreal
    rwa [ENNReal.toReal_eq_one_iff] at hreal
  rw [borelPureExpectedCapturedGap_of_singleton hmass action,
    strictPriorityCapturedGap, NNReal.coe_zero, sub_zero,
    max_eq_left action.coe_nonneg]

/-- **The terminal case at one window.**  If the opponent keeps everything at
zero, the advantaged player is pure at one contested band, the cost ratio is at
least one half, and the payoff is the contested prize net of one band's cost.
This is the case `nu = 1` of the classification. -/
theorem terminal_case_of_full_atom
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (hfull : second.cdfReal 0 = 1) :
    (first.law : Measure NNReal) {gap.toNNReal} = 1 ∧
      slotWeight ≤ 2 * marginalCost ∧
      borelExpectedPayoff slotWeight gap marginalCost first second =
        (slotWeight - marginalCost) * gap := by
  obtain ⟨hband, hvalue⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  have hgapCoe : ((gap.toNNReal : NNReal) : ℝ) = gap :=
    Real.coe_toNNReal gap hgap.le
  have hpayoff :
      borelExpectedPayoff slotWeight gap marginalCost first second =
        (slotWeight - marginalCost) * gap := by
    rw [hvalue, hfull]
    ring
  have hpure : ∀ action ∈ first.support, action = gap.toNNReal := by
    intro action hmem
    have hlow : gap ≤ (action : ℝ) := by
      rw [← hband]
      exact_mod_cast first.lowerSupport_le_of_mem_support hmem
    have hind :=
      borelMixedBestResponse_payoff_eq_on_support hgap.le hnash.1 action hmem
    rw [borelPureExpectedPayoff,
      borelPureExpectedCapturedGap_of_full_atom hfull action, hpayoff,
      min_eq_right hlow] at hind
    have hcoe : (action : ℝ) = gap := by nlinarith [hind, hcost]
    have : (action : ℝ) = ((gap.toNNReal : NNReal) : ℝ) := by rw [hcoe, hgapCoe]
    exact_mod_cast this
  have hmassFirst := law_singleton_eq_one_of_support_subset first hpure
  refine ⟨hmassFirst, ?_, hpayoff⟩
  have hdouble : ((2 * gap).toNNReal : NNReal) = (2 : NNReal) * gap.toNNReal := by
    ext
    push_cast [Real.coe_toNNReal _ hgap.le,
      Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ 2 * gap)]
    ring
  have hdev := hnash.2 (2 * gap).toNNReal
  obtain ⟨-, hzeroPayoff, -⟩ :=
    opponent_at_bottom_of_payoff_pos hgap.le hcost hnash hpos
  rw [hzeroPayoff, borelPureExpectedPayoff,
    borelPureExpectedCapturedGap_of_singleton hmassFirst,
    Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ 2 * gap), hgapCoe,
    strictPriorityCapturedGap,
    max_eq_left (by linarith : (0 : ℝ) ≤ 2 * gap - gap),
    min_eq_right (by linarith : gap ≤ 2 * gap - gap)] at hdev
  nlinarith [hdev]

end

end SmoothingCliff.Racing
