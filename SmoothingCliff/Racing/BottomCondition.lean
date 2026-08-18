import SmoothingCliff.Racing.SupportFOC

/-!
# The bottom of a positive-payoff equilibrium

The first half of the classification in `prop:sp_allequilibria` (iii).  A
player earning a positive payoff has to be the one whose support starts
higher, because the lower of the two supports earns nothing against an opponent
who never falls below it and pays for its own action.

That pins the opponent at the bottom: its payoff is zero and its support starts
at zero.  It also empties the opponent's support of everything strictly between
zero and the advantaged player's lowest action, since any such point would be
bought at positive cost with no return.  So the opponent's distribution
function is flat across the whole stretch, which is the input the bottom
condition needs.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- Below the bottom of the support the distribution function vanishes. -/
theorem cdfReal_eq_zero_of_lt_lowerSupport
    (strategy : BorelMixedStrategy) {x : ℝ}
    (hx : x < (strategy.lowerSupport : ℝ)) :
    strategy.cdfReal x = 0 := by
  have hcompl : (strategy.law : Measure NNReal)
      {action : NNReal | action ∉ strategy.support} = 0 :=
    ae_iff.mp strategy.ae_mem_support
  have hsub : {action : NNReal | (action : ℝ) ≤ x} ⊆
      {action : NNReal | action ∉ strategy.support} := by
    intro action haction hmem
    have hlow := strategy.lowerSupport_le_of_mem_support hmem
    have hlowReal : (strategy.lowerSupport : ℝ) ≤ (action : ℝ) := by
      exact_mod_cast hlow
    exact absurd (lt_of_le_of_lt hlowReal (lt_of_le_of_lt haction hx))
      (lt_irrefl _)
  have hzero : strategy.cdf x = 0 :=
    measure_mono_null hsub hcompl
  rw [BorelMixedStrategy.cdfReal, hzero, ENNReal.toReal_zero]

/-- No return below the opponent's bottom: an action weakly under the
opponent's lowest one captures nothing. -/
theorem borelPureExpectedCapturedGap_eq_zero_of_le_lowerSupport
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy)
    {action : NNReal} (hle : action ≤ opponent.lowerSupport) :
    borelPureExpectedCapturedGap gap opponent action = 0 := by
  unfold borelPureExpectedCapturedGap
  apply integral_eq_zero_of_ae
  filter_upwards [opponent.ae_mem_support] with rival hrival
  have horder : action ≤ rival :=
    hle.trans (opponent.lowerSupport_le_of_mem_support hrival)
  have horderReal : (action : ℝ) ≤ (rival : ℝ) := by exact_mod_cast horder
  simp [strictPriorityCapturedGap, sub_nonpos.mpr horderReal, hgap]

/-- **The lower support earns nothing.**  A player whose support starts no
higher than the opponent's has payoff exactly minus the cost of its own lowest
action. -/
theorem borelMixedBestResponse_payoff_eq_neg_cost
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    (hlower : own.lowerSupport ≤ opponent.lowerSupport) :
    borelExpectedPayoff slotWeight gap marginalCost own opponent =
      -(marginalCost * (own.lowerSupport : ℝ)) := by
  have hsupport :=
    borelMixedBestResponse_payoff_eq_on_support hgap hbest own.lowerSupport
      own.lowerSupport_mem_support
  rw [← hsupport, borelPureExpectedPayoff,
    borelPureExpectedCapturedGap_eq_zero_of_le_lowerSupport hgap opponent
      hlower]
  ring

/-- The lower player's support starts at zero and its payoff is zero. -/
theorem lowerSupport_eq_zero_of_le
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (hcost : 0 < marginalCost)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    (hlower : own.lowerSupport ≤ opponent.lowerSupport) :
    own.lowerSupport = 0 ∧
      borelExpectedPayoff slotWeight gap marginalCost own opponent = 0 := by
  have hnonneg := borelMixedBestResponse_payoff_nonneg hgap hbest
  have heq := borelMixedBestResponse_payoff_eq_neg_cost hgap hbest hlower
  have hzeroReal : (own.lowerSupport : ℝ) = 0 := by
    by_contra hne
    have hpos : 0 < (own.lowerSupport : ℝ) :=
      lt_of_le_of_ne own.lowerSupport.coe_nonneg (Ne.symm hne)
    nlinarith
  refine ⟨by exact_mod_cast hzeroReal, ?_⟩
  rw [heq, hzeroReal]
  ring

/-- **The advantaged player starts higher.**  A positive payoff forces the
opponent to the bottom: zero payoff and a support starting at zero. -/
theorem opponent_at_bottom_of_payoff_pos
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    second.lowerSupport = 0 ∧
      borelExpectedPayoff slotWeight gap marginalCost second first = 0 ∧
      0 < (first.lowerSupport : ℝ) := by
  have hnotle : ¬ first.lowerSupport ≤ second.lowerSupport := by
    intro hle
    have := (lowerSupport_eq_zero_of_le hgap hcost hnash.1 hle).2
    exact absurd this (ne_of_gt hpos)
  have hlt : second.lowerSupport < first.lowerSupport := lt_of_not_ge hnotle
  obtain ⟨hzero, hpayoff⟩ :=
    lowerSupport_eq_zero_of_le hgap hcost hnash.2 hlt.le
  refine ⟨hzero, hpayoff, ?_⟩
  have : (second.lowerSupport : ℝ) < (first.lowerSupport : ℝ) := by
    exact_mod_cast hlt
  rw [hzero] at this
  simpa using this

/-- The mass the opponent keeps at zero, as a real number. -/
theorem cdfReal_zero_eq_massReal (strategy : BorelMixedStrategy) :
    strategy.cdfReal 0 =
      ((strategy.law : Measure NNReal) {0}).toReal := by
  have hset : {action : NNReal | (action : ℝ) ≤ 0} = ({0} : Set NNReal) := by
    ext action
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      have hle : action ≤ 0 := by exact_mod_cast h
      exact le_zero_iff.mp hle
    · rintro rfl
      simp
  rw [BorelMixedStrategy.cdfReal, BorelMixedStrategy.cdf, hset]

/-- The captured band dominates the return against an opponent sitting at
zero. -/
theorem strictPriorityCapturedGap_ge_atom
    {gap : ℝ} (hgap : 0 ≤ gap) {action : NNReal} (rival : NNReal) :
    min (action : ℝ) gap *
        ({0} : Set NNReal).indicator (fun _ => (1 : ℝ)) rival ≤
      strictPriorityCapturedGap gap (action : ℝ) (rival : ℝ) := by
  by_cases hrival : rival = 0
  · subst hrival
    rw [Set.indicator_of_mem (Set.mem_singleton (0 : NNReal)), mul_one,
      strictPriorityCapturedGap,
      NNReal.coe_zero, sub_zero, max_eq_left action.coe_nonneg]
  · have hnot : rival ∉ ({0} : Set NNReal) := by simpa using hrival
    rw [Set.indicator_of_notMem hnot, mul_zero, strictPriorityCapturedGap]
    exact le_min (le_max_right _ _) hgap

/-- The captured band is integrable against the opponent's law: it is bounded
by the contested band. -/
theorem borelPureCapturedGap_integrable_rival
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy)
    (action : NNReal) :
    Integrable (fun rival : NNReal =>
      strictPriorityCapturedGap gap (action : ℝ) (rival : ℝ))
      (opponent.law : Measure NNReal) := by
  refine (integrable_const gap).mono' ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    unfold strictPriorityCapturedGap
    fun_prop
  · filter_upwards with rival
    rw [Real.norm_eq_abs,
      abs_of_nonneg (strictPriorityCapturedGap_nonneg hgap)]
    exact strictPriorityCapturedGap_le_gap

/-- The mass at zero, integrated. -/
theorem integral_atom_indicator
    {gap : ℝ} (opponent : BorelMixedStrategy) (action : NNReal) :
    ∫ rival : NNReal,
        min (action : ℝ) gap *
          ({0} : Set NNReal).indicator (fun _ => (1 : ℝ)) rival
        ∂(opponent.law : Measure NNReal) =
      opponent.cdfReal 0 * min (action : ℝ) gap := by
  rw [integral_const_mul]
  simp only [← Pi.one_def]
  rw [integral_indicator_one (measurableSet_singleton (0 : NNReal)),
    cdfReal_zero_eq_massReal, measureReal_def, mul_comm]

theorem integrable_atom_indicator
    {gap : ℝ} (opponent : BorelMixedStrategy) (action : NNReal) :
    Integrable (fun rival : NNReal =>
      min (action : ℝ) gap *
        ({0} : Set NNReal).indicator (fun _ => (1 : ℝ)) rival)
      (opponent.law : Measure NNReal) :=
  ((integrable_const (1 : ℝ)).indicator
    (measurableSet_singleton (0 : NNReal))).const_mul _

/-- **The atom floor.**  The expected captured band is at least the mass the
opponent leaves at zero, times the band the own action clears. -/
theorem borelPureExpectedCapturedGap_ge_atom_mul
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy)
    (action : NNReal) :
    opponent.cdfReal 0 * min (action : ℝ) gap ≤
      borelPureExpectedCapturedGap gap opponent action := by
  rw [borelPureExpectedCapturedGap, ← integral_atom_indicator opponent action]
  exact integral_mono (integrable_atom_indicator opponent action)
    (borelPureCapturedGap_integrable_rival hgap opponent action)
    (fun rival => strictPriorityCapturedGap_ge_atom hgap rival)

/-- **The atom is everything below a clear stretch.**  If the opponent keeps no
mass strictly between zero and the own action, the expected captured band is
exactly the atom at zero times the band the action clears. -/
theorem borelPureExpectedCapturedGap_eq_atom_mul
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy)
    (action : NNReal)
    (hclear : ∀ rival ∈ opponent.support, rival ≠ 0 →
      (action : ℝ) ≤ (rival : ℝ)) :
    borelPureExpectedCapturedGap gap opponent action =
      opponent.cdfReal 0 * min (action : ℝ) gap := by
  rw [borelPureExpectedCapturedGap, ← integral_atom_indicator opponent action]
  refine integral_congr_ae ?_
  filter_upwards [opponent.ae_mem_support] with rival hrival
  by_cases hzero : rival = 0
  · subst hzero
    rw [Set.indicator_of_mem (Set.mem_singleton (0 : NNReal)), mul_one,
      strictPriorityCapturedGap, NNReal.coe_zero, sub_zero,
      max_eq_left action.coe_nonneg]
  · have hnot : rival ∉ ({0} : Set NNReal) := by simpa using hzero
    have hle := hclear rival hrival hzero
    rw [Set.indicator_of_notMem hnot, mul_zero, strictPriorityCapturedGap,
      max_eq_right (by linarith : (action : ℝ) - (rival : ℝ) ≤ 0),
      min_eq_left hgap]

/-- The opponent of a player earning a positive payoff keeps no mass strictly
between zero and that player's lowest action. -/
theorem second_support_clear_of_payoff_pos
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (rival : NNReal) (hrival : rival ∈ second.support) (hne : rival ≠ 0) :
    (first.lowerSupport : ℝ) ≤ (rival : ℝ) := by
  obtain ⟨-, hzeroPayoff, -⟩ :=
    opponent_at_bottom_of_payoff_pos hgap hcost hnash hpos
  by_contra hlt
  rw [not_le] at hlt
  have hleNN : rival ≤ first.lowerSupport := by exact_mod_cast hlt.le
  have hind :=
    borelMixedBestResponse_payoff_eq_on_support hgap hnash.2 rival hrival
  rw [hzeroPayoff, borelPureExpectedPayoff,
    borelPureExpectedCapturedGap_eq_zero_of_le_lowerSupport hgap first
      hleNN] at hind
  have hrivalPos : 0 < (rival : ℝ) := by
    refine lt_of_le_of_ne rival.coe_nonneg (fun h => hne ?_)
    exact_mod_cast h.symm
  nlinarith

/-- **The bottom condition (B).**  In an equilibrium where one player earns a
positive payoff, that player's lowest action is exactly one contested band, and
the opponent's mass at zero pays for it: the payoff is the band times the
opponent's atom valued at the slot weight, net of the cost of the band. -/
theorem bottomCondition_of_payoff_pos
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    (first.lowerSupport : ℝ) = gap ∧
      borelExpectedPayoff slotWeight gap marginalCost first second =
        (slotWeight * second.cdfReal 0 - marginalCost) * gap := by
  obtain ⟨-, -, hlowPos⟩ :=
    opponent_at_bottom_of_payoff_pos hgap.le hcost hnash hpos
  have hclear := second_support_clear_of_payoff_pos hgap.le hcost hnash hpos
  have hind :=
    borelMixedBestResponse_payoff_eq_on_support hgap.le hnash.1
      first.lowerSupport first.lowerSupport_mem_support
  have hphi :
      borelPureExpectedCapturedGap gap second first.lowerSupport =
        second.cdfReal 0 * min (first.lowerSupport : ℝ) gap :=
    borelPureExpectedCapturedGap_eq_atom_mul hgap.le second first.lowerSupport
      hclear
  have hU : borelExpectedPayoff slotWeight gap marginalCost first second =
      slotWeight * (second.cdfReal 0 * min (first.lowerSupport : ℝ) gap) -
        marginalCost * (first.lowerSupport : ℝ) := by
    rw [← hind, borelPureExpectedPayoff, hphi]
  have hgapCoe : ((gap.toNNReal : NNReal) : ℝ) = gap :=
    Real.coe_toNNReal gap hgap.le
  have hdev := hnash.1 gap.toNNReal
  rw [borelPureExpectedPayoff, hgapCoe] at hdev
  have hband : (first.lowerSupport : ℝ) = gap := by
    rcases lt_trichotomy (first.lowerSupport : ℝ) gap with hlt | heq | hgt
    · exfalso
      have hfloor :=
        borelPureExpectedCapturedGap_ge_atom_mul hgap.le second gap.toNNReal
      rw [hgapCoe, min_self] at hfloor
      rw [min_eq_left hlt.le] at hU
      have hmul : slotWeight * (second.cdfReal 0 * gap) ≤
          slotWeight * borelPureExpectedCapturedGap gap second gap.toNNReal :=
        mul_le_mul_of_nonneg_left hfloor hweight.le
      have hXg : (slotWeight * second.cdfReal 0 - marginalCost) * gap ≤
          borelExpectedPayoff slotWeight gap marginalCost first second := by
        nlinarith [hmul, hdev]
      have hXl : borelExpectedPayoff slotWeight gap marginalCost first second =
          (slotWeight * second.cdfReal 0 - marginalCost) *
            (first.lowerSupport : ℝ) := by
        rw [hU]; ring
      have hXpos : 0 < slotWeight * second.cdfReal 0 - marginalCost := by
        nlinarith [hpos, hlowPos, hXl]
      nlinarith [hXpos, hXg, hXl, hlt]
    · exact heq
    · exfalso
      have hclearGap : ∀ rival ∈ second.support, rival ≠ 0 →
          ((gap.toNNReal : NNReal) : ℝ) ≤ (rival : ℝ) := by
        intro rival hrival hne
        rw [hgapCoe]
        exact le_trans hgt.le (hclear rival hrival hne)
      have hexact :=
        borelPureExpectedCapturedGap_eq_atom_mul hgap.le second gap.toNNReal
          hclearGap
      rw [hgapCoe, min_self] at hexact
      rw [min_eq_right hgt.le] at hU
      rw [hexact] at hdev
      nlinarith [hdev, hU, hgt, hcost]
  refine ⟨hband, ?_⟩
  rw [hU, hband, min_self]
  ring

end

end SmoothingCliff.Racing
