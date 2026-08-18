import SmoothingCliff.Racing.DissipationFloor

/-!
# Every equilibrium support is bounded

The captured band never exceeds the contested band, so the return from any
action is capped while its cost is not.  A best response therefore keeps
nothing whose cost exceeds the whole prize, and in particular the ladder can
carry only finitely many rungs.

This is the paper's remark that actions above `w1 (v - r) / kappa` yield a
negative payoff and can be discarded, stated where the classification needs it:
it is what turns "the recursion terminates" into a concrete last rung.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- The expected captured band never exceeds the contested band. -/
theorem borelPureExpectedCapturedGap_le_gap
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy)
    (action : NNReal) :
    borelPureExpectedCapturedGap gap opponent action ≤ gap := by
  have hle : borelPureExpectedCapturedGap gap opponent action ≤
      ∫ _rival : NNReal, gap ∂(opponent.law : Measure NNReal) := by
    rw [borelPureExpectedCapturedGap]
    refine integral_mono (borelPureCapturedGap_integrable_rival hgap opponent
      action) (integrable_const gap) ?_
    intro rival
    exact strictPriorityCapturedGap_le_gap
  simpa using hle

/-- **The support is bounded by the prize over the marginal cost.**  No best
response keeps an action whose cost exceeds the whole contested prize. -/
theorem support_action_cost_le_prize
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (hweight : 0 ≤ slotWeight)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {action : NNReal} (hmem : action ∈ own.support) :
    marginalCost * (action : ℝ) ≤ slotWeight * gap := by
  have hpayoff :=
    borelMixedBestResponse_payoff_eq_on_support hgap hbest action hmem
  have hnonneg := borelMixedBestResponse_payoff_nonneg hgap hbest
  rw [← hpayoff, borelPureExpectedPayoff] at hnonneg
  have hcap := borelPureExpectedCapturedGap_le_gap hgap opponent action
  nlinarith [hcap, hnonneg, hweight]

/-- **The ladder is finite.**  A rung of the advantaged player's ladder at
`2 j + 1` bands forces `2 j + 1` marginal costs to be at most the slot weight,
so only finitely many rungs can exist. -/
theorem first_rung_index_le
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 ≤ slotWeight)
    {first second : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost first second)
    {j : ℕ} {action : NNReal} (hmem : action ∈ first.support)
    (hvalue : (action : ℝ) = (2 * (j : ℝ) + 1) * gap) :
    (2 * (j : ℝ) + 1) * marginalCost ≤ slotWeight := by
  have hstep := support_action_cost_le_prize hgap.le hweight hbest hmem
  rw [hvalue] at hstep
  have hcancel : (2 * (j : ℝ) + 1) * marginalCost * gap ≤ slotWeight * gap := by
    nlinarith [hstep]
  exact le_of_mul_le_mul_right hcancel hgap

/-- The same bound on the opponent's ladder. -/
theorem second_rung_index_le
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 ≤ slotWeight)
    {first second : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost second first)
    {j : ℕ} {action : NNReal} (hmem : action ∈ second.support)
    (hvalue : (action : ℝ) = 2 * (j : ℝ) * gap) :
    2 * (j : ℝ) * marginalCost ≤ slotWeight := by
  have hstep := support_action_cost_le_prize hgap.le hweight hbest hmem
  rw [hvalue] at hstep
  have hcancel : 2 * (j : ℝ) * marginalCost * gap ≤ slotWeight * gap := by
    nlinarith [hstep]
  exact le_of_mul_le_mul_right hcancel hgap

/-- **No ladder is infinite.**  Rungs at every index would need the cost ratio
to vanish. -/
theorem first_rungs_not_unbounded
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 ≤ slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost first second) :
    ¬(∀ j : ℕ, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap) := by
  intro hrungs
  obtain ⟨j, hj⟩ := exists_nat_gt (slotWeight / marginalCost)
  obtain ⟨action, hmem, hvalue⟩ := hrungs j
  have hbound := first_rung_index_le hgap hweight hbest hmem hvalue
  rw [div_lt_iff₀ hcost] at hj
  nlinarith [hbound, hj, hcost]

/-! ### The last rung is well defined

Both ladders reach index zero, the property of reaching an index is downward
closed by construction, and the cost bound caps how far it can reach.  So there
is a largest index both ladders reach, and that index is the paper's `nu - 1`. -/

/-- Both ladders reach every index up to `n`. -/
def LadderReaches (first second : BorelMixedStrategy) (gap : ℝ) (n : ℕ) : Prop :=
  (∀ j ≤ n, ∃ action ∈ second.support, (action : ℝ) = 2 * (j : ℝ) * gap) ∧
    (∀ j ≤ n, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap)

/-- Both ladders always reach index zero: the opponent sits at the bottom and
the advantaged player at one contested band. -/
theorem ladderReaches_zero
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    LadderReaches first second gap 0 := by
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  obtain ⟨hbottom, -, -⟩ :=
    opponent_at_bottom_of_payoff_pos hgap.le hcost hnash hpos
  constructor
  · intro j hj
    refine ⟨second.lowerSupport, second.lowerSupport_mem_support, ?_⟩
    rw [hbottom]
    interval_cases j
    push_cast
    simp
  · intro j hj
    refine ⟨first.lowerSupport, first.lowerSupport_mem_support, ?_⟩
    rw [hband]
    interval_cases j
    push_cast
    ring

/-- The cost bound caps how far the ladders reach. -/
theorem ladderReaches_index_le
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 ≤ slotWeight)
    {first second : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost first second)
    {n : ℕ} (hreach : LadderReaches first second gap n) :
    (2 * (n : ℝ) + 1) * marginalCost ≤ slotWeight := by
  obtain ⟨action, hmem, hvalue⟩ := hreach.2 n (le_refl n)
  exact first_rung_index_le hgap hweight hbest hmem hvalue

/-- **The last rung.**  There is a largest index both ladders reach; the paper
calls the number of rungs `nu`, so that index is `nu - 1`. -/
theorem exists_last_rung
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    ∃ depth : ℕ, LadderReaches first second gap depth ∧
      ¬ LadderReaches first second gap (depth + 1) := by
  classical
  obtain ⟨bound, hbound⟩ := exists_nat_gt (slotWeight / marginalCost)
  have hboundReal : slotWeight < (bound : ℝ) * marginalCost := by
    rw [div_lt_iff₀ hcost] at hbound
    exact hbound
  have hstrict : ∀ n : ℕ, LadderReaches first second gap n → n < bound := by
    intro n hreach
    have hcap := ladderReaches_index_le hgap hweight.le hnash.1 hreach
    have hlt : (n : ℝ) < (bound : ℝ) := by nlinarith [hcap, hboundReal, hcost]
    exact_mod_cast hlt
  have hzero := ladderReaches_zero hgap hweight hcost hnash hpos
  refine ⟨Nat.findGreatest (LadderReaches first second gap) bound, ?_, ?_⟩
  · exact Nat.findGreatest_spec (Nat.zero_le bound) hzero
  · refine Nat.findGreatest_is_greatest (Nat.lt_succ_self _) ?_
    have hreach := Nat.findGreatest_spec
      (P := LadderReaches first second gap) (Nat.zero_le bound) hzero
    exact hstrict _ hreach

/-! ### The payoff cap without any terminal hypothesis

The lattice route to `U <= kappa G` needed both ladders located and both
terminal hypotheses.  There is a shorter one that needs neither.

The support is closed and, by the cost bound, bounded, so it has a largest
action.  Above that action the advantaged player's distribution function is
already one, so the opponent's deviation one band further captures the whole
contested band, and being unprofitable it prices the largest action from below.
The advantaged player's own indifference at that action then prices its payoff
from above, and the two bounds meet at one band's cost. -/

/-- The support is bounded above by the prize over the marginal cost. -/
theorem support_bddAbove
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (hweight : 0 ≤ slotWeight) (hcost : 0 < marginalCost)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent) :
    BddAbove own.support := by
  refine ⟨(slotWeight * gap / marginalCost).toNNReal, fun action hmem => ?_⟩
  have hstep := support_action_cost_le_prize hgap hweight hbest hmem
  have hle : (action : ℝ) ≤ slotWeight * gap / marginalCost := by
    rw [le_div_iff₀ hcost]
    linarith
  have hcoe : (action : ℝ) ≤
      (((slotWeight * gap / marginalCost).toNNReal : NNReal) : ℝ) := by
    rw [Real.coe_toNNReal _ (le_trans action.coe_nonneg hle)]
    exact hle
  exact_mod_cast hcoe

/-- The largest action the player keeps. -/
def BorelMixedStrategy.upperSupport (strategy : BorelMixedStrategy) : NNReal :=
  sSup strategy.support

theorem upperSupport_mem_support
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (hweight : 0 ≤ slotWeight) (hcost : 0 < marginalCost)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent) :
    own.upperSupport ∈ own.support :=
  IsClosed.csSup_mem own.support_closed own.support_nonempty
    (support_bddAbove hgap hweight hcost hbest)

theorem le_upperSupport
    {slotWeight gap marginalCost : ℝ} (hgap : 0 ≤ gap)
    (hweight : 0 ≤ slotWeight) (hcost : 0 < marginalCost)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {action : NNReal} (hmem : action ∈ own.support) :
    action ≤ own.upperSupport :=
  le_csSup (support_bddAbove hgap hweight hcost hbest) hmem

/-- **The payoff cap, unconditionally.**  In every positive-payoff equilibrium
the advantaged player's payoff is at most one contested band's cost.  No ladder
and no terminal hypothesis is needed. -/
theorem positive_payoff_le_cost_band_of_support
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hzeroSecond : borelExpectedPayoff
      slotWeight gap marginalCost second first = 0) :
    borelExpectedPayoff slotWeight gap marginalCost first second ≤
      marginalCost * gap := by
  set top := first.upperSupport with htop
  have htopMem : top ∈ first.support :=
    upperSupport_mem_support hgap.le hweight.le hcost hnash.1
  have htopNonneg : (0 : ℝ) ≤ (top : ℝ) := top.coe_nonneg
  have hfull : ∀ point : ℝ, (top : ℝ) ≤ point → first.cdfReal point = 1 := by
    intro point hpoint
    refine cdfReal_eq_one_of_support_le first fun action hmem => ?_
    have hle := le_upperSupport hgap.le hweight.le hcost hnash.1 hmem
    have : ((action : NNReal) : ℝ) ≤ (top : ℝ) := by exact_mod_cast hle
    linarith
  have hintegral :
      (∫ point in ((top : ℝ) + gap - gap)..((top : ℝ) + gap),
        first.cdfReal point) = gap := by
    have hlow : (top : ℝ) + gap - gap = (top : ℝ) := by ring
    rw [hlow]
    have hstep := first.integral_cdfReal_of_flat (base := 1)
      (by linarith : (top : ℝ) ≤ (top : ℝ) + gap)
      (fun point hpoint => hfull point hpoint.1)
    rw [hstep]
    ring
  have hdeviation :=
    realPureExpectedPayoff_nonpos_of_zero_payoff (slotWeight := slotWeight)
      (marginalCost := marginalCost) hgap.le hnash.2 hzeroSecond
      (x := (top : ℝ) + gap) (by linarith)
  rw [realPureExpectedPayoff, hintegral] at hdeviation
  have hindifferent :=
    borelMixedBestResponse_payoff_eq_on_support hgap.le hnash.1 top htopMem
  have hcap := borelPureExpectedCapturedGap_le_gap hgap.le second top
  rw [borelPureExpectedPayoff] at hindifferent
  nlinarith [hdeviation, hindifferent, hcap, hweight]

/-! ### One terminal hypothesis implies the other

If the opponent stops at its last rung, the advantaged player's largest action
is pinned exactly at its own last rung, so the second terminal hypothesis is a
consequence of the first rather than an extra assumption.

The opponent's ladder value plus completeness fixes its atom at zero, hence the
payoff; and the largest action captures the whole band, since every opponent
action is at least one band below it, so the payoff is also the band's worth
net of that action's cost.  Equating the two locates the action. -/

/-- An action a full band above the whole opponent support captures the whole
contested band. -/
theorem borelPureExpectedCapturedGap_eq_gap_of_clear
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy)
    (action : NNReal)
    (hclear : ∀ rival ∈ opponent.support,
      (rival : ℝ) + gap ≤ (action : ℝ)) :
    borelPureExpectedCapturedGap gap opponent action = gap := by
  rw [borelPureExpectedCapturedGap]
  have hconst : ∫ rival : NNReal,
      strictPriorityCapturedGap gap (action : ℝ) (rival : ℝ)
      ∂(opponent.law : Measure NNReal) =
        ∫ _rival : NNReal, gap ∂(opponent.law : Measure NNReal) := by
    refine integral_congr_ae ?_
    filter_upwards [opponent.ae_mem_support] with rival hrival
    have hle := hclear rival hrival
    rw [strictPriorityCapturedGap,
      max_eq_left (by linarith : (0 : ℝ) ≤ (action : ℝ) - (rival : ℝ)),
      min_eq_right (by linarith : gap ≤ (action : ℝ) - (rival : ℝ))]
  rw [hconst]
  simp

/-- **The advantaged player's last action is its last rung.**  Given that the
opponent stops at its own last rung, the advantaged player keeps nothing above
`2 depth + 1` bands. -/
theorem first_terminal_of_second_terminal
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ) (hreach : LadderReaches first second gap depth)
    (hSecondTerminal : ∀ action ∈ second.support,
      (action : ℝ) ≤ 2 * (depth : ℝ) * gap) :
    ∀ action ∈ first.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap := by
  obtain ⟨hSecondRung, hFirstRung⟩ := hreach
  obtain ⟨-, hbottomValue⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  set top := first.upperSupport with htop
  have htopMem : top ∈ first.support :=
    upperSupport_mem_support hgap.le hweight.le hcost hnash.1
  obtain ⟨rung, hrungMem, hrungValue⟩ := hFirstRung depth (le_refl depth)
  have htopLow : (2 * (depth : ℝ) + 1) * gap ≤ (top : ℝ) := by
    have hle := le_upperSupport hgap.le hweight.le hcost hnash.1 hrungMem
    have : ((rung : NNReal) : ℝ) ≤ (top : ℝ) := by exact_mod_cast hle
    linarith [hrungValue]
  have hcaptured : borelPureExpectedCapturedGap gap second top = gap := by
    refine borelPureExpectedCapturedGap_eq_gap_of_clear hgap.le second top
      fun rival hrival => ?_
    have := hSecondTerminal rival hrival
    linarith
  have hladder := second_cdfReal_rung_value_le hgap hweight hcost hnash hpos
    depth hSecondRung hFirstRung depth (le_refl depth)
  have hcomplete : second.cdfReal (2 * (depth : ℝ) * gap) = 1 :=
    cdfReal_eq_one_of_support_le second hSecondTerminal
  rw [hcomplete, mul_one] at hladder
  have hindifferent :=
    borelMixedBestResponse_payoff_eq_on_support hgap.le hnash.1 top htopMem
  rw [borelPureExpectedPayoff, hcaptured, hbottomValue] at hindifferent
  have htopValue : (top : ℝ) = (2 * (depth : ℝ) + 1) * gap := by
    have hcancel : marginalCost * (top : ℝ) =
        marginalCost * ((2 * (depth : ℝ) + 1) * gap) := by
      nlinarith [hindifferent, hladder]
    exact mul_left_cancel₀ (ne_of_gt hcost) hcancel
  intro action hmem
  have hle := le_upperSupport hgap.le hweight.le hcost hnash.1 hmem
  have hcoe : ((action : NNReal) : ℝ) ≤ (top : ℝ) := by exact_mod_cast hle
  linarith [htopValue]

/-! ### The classification, packaged

Everything the forward direction of `prop:sp_allequilibria` (iii) asserts about
a positive-payoff equilibrium, at the last rung both ladders reach and under
the terminal hypotheses that neither support goes above its own last rung.

The terminal hypotheses are the one thing the maximality of the last rung does
not by itself supply: maximality says only that one of the two ladders misses
the next rung, which does not on its own exclude support further up.  Closing
that would need the alternation continued at the actual next support points
rather than at the lattice positions. -/

/-- **The classification of a positive-payoff equilibrium.**  At the last rung
both ladders reach, the cost ratio lies in the paper's window, the supports are
the odd and the even lattice, the payoff is the contested band times the slot
weight net of `2 nu - 1` marginal costs, the dissipation is the complementary
amount, and the dissipation is at least the whole prize net of one band's
cost. -/
theorem positive_payoff_classification
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ) (hreach : LadderReaches first second gap depth)
    (hSecondTerminal : ∀ action ∈ second.support,
      (action : ℝ) ≤ 2 * (depth : ℝ) * gap) :
    ((2 * (depth : ℝ) + 1) * marginalCost < slotWeight ∧
        slotWeight ≤ (2 * (depth : ℝ) + 2) * marginalCost) ∧
      (∀ action ∈ first.support,
        ∃ j ≤ depth, (action : ℝ) = (2 * (j : ℝ) + 1) * gap) ∧
      (∀ action ∈ second.support,
        ∃ j ≤ depth, (action : ℝ) = 2 * (j : ℝ) * gap) ∧
      borelExpectedPayoff slotWeight gap marginalCost first second =
        (slotWeight - (2 * (depth : ℝ) + 1) * marginalCost) * gap ∧
      borelExpectedDissipation marginalCost first second =
        (2 * (depth : ℝ) + 1) * marginalCost * gap ∧
      (slotWeight - marginalCost) * gap ≤
        borelExpectedDissipation marginalCost first second := by
  have hFirstTerminal := first_terminal_of_second_terminal hgap hweight hcost
    hnash hpos depth hreach hSecondTerminal
  obtain ⟨hSecondRung, hFirstRung⟩ := hreach
  refine ⟨⟨window_upper_edge hgap hweight hcost hnash hpos depth hSecondRung
      hFirstRung,
    window_lower_edge hgap hweight hcost hnash hpos depth hFirstTerminal⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact fun action hmem => first_support_lattice hgap hweight hcost hnash hpos
      depth hSecondRung hFirstRung action hmem (hFirstTerminal action hmem)
  · exact fun action hmem => second_support_lattice hgap hweight hcost hnash
      hpos depth hSecondRung hFirstRung action hmem (hSecondTerminal action hmem)
  · exact positive_payoff_value hgap hweight hcost hnash hpos depth hSecondRung
      hFirstRung hSecondTerminal
  · exact positive_dissipation_value hgap hweight hcost hnash hpos depth
      hSecondRung hFirstRung hFirstTerminal hSecondTerminal
  · exact positive_dissipation_ge_prize_net_cost hgap hweight hcost hnash hpos
      depth hSecondRung hFirstRung hFirstTerminal hSecondTerminal

/-! ### How the two tops sit

The advantaged player's largest action is never more than one contested band
above the opponent's largest: its own deviation to one band above the
opponent's top already captures the whole band, so if it were higher its
indifference would be violated.

This is what separates the two terminal cases.  In the first the opponent's top
is one band below the advantaged player's, and the opponent stops at its own
last rung; in the second the opponent carries a final atom one band above, and
the cost ratio is forced onto the window's lower boundary. -/

/-- **The tops are within one band.**  The advantaged player keeps nothing more
than one contested band above the opponent's largest action. -/
theorem upperSupport_le_opponent_upperSupport_add_gap
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second) :
    (first.upperSupport : ℝ) ≤ (second.upperSupport : ℝ) + gap := by
  set top := first.upperSupport with htop
  set rivalTop := second.upperSupport with hrivalTop
  have htopMem : top ∈ first.support :=
    upperSupport_mem_support hgap.le hweight.le hcost hnash.1
  have hrivalNonneg : (0 : ℝ) ≤ (rivalTop : ℝ) := rivalTop.coe_nonneg
  have hfull : ∀ point : ℝ, (rivalTop : ℝ) ≤ point →
      second.cdfReal point = 1 := by
    intro point hpoint
    refine cdfReal_eq_one_of_support_le second fun action hmem => ?_
    have hle := le_upperSupport hgap.le hweight.le hcost hnash.2 hmem
    have hcoe : ((action : NNReal) : ℝ) ≤ (rivalTop : ℝ) := by exact_mod_cast hle
    linarith
  have hintegral :
      (∫ point in ((rivalTop : ℝ) + gap - gap)..((rivalTop : ℝ) + gap),
        second.cdfReal point) = gap := by
    have hlow : (rivalTop : ℝ) + gap - gap = (rivalTop : ℝ) := by ring
    rw [hlow]
    have hstep := second.integral_cdfReal_of_flat (base := 1)
      (by linarith : (rivalTop : ℝ) ≤ (rivalTop : ℝ) + gap)
      (fun point hpoint => hfull point hpoint.1)
    rw [hstep]
    ring
  have hdeviation := realPureExpectedPayoff_le_max (slotWeight := slotWeight)
    (marginalCost := marginalCost) hgap.le hnash.1
    (x := (rivalTop : ℝ) + gap) (by linarith)
  rw [realPureExpectedPayoff, hintegral] at hdeviation
  have hindifferent :=
    borelMixedBestResponse_payoff_eq_on_support hgap.le hnash.1 top htopMem
  have hcap := borelPureExpectedCapturedGap_le_gap hgap.le second top
  rw [borelPureExpectedPayoff] at hindifferent
  nlinarith [hdeviation, hindifferent, hcap, hweight, hcost]

/-! ### Excluding a stray action above the boundary atom

Suppose the opponent's ladder ends with a final atom one band above the
advantaged player's last rung, and the advantaged player has no rung two bands
above that.  Then the advantaged player keeps nothing above its last rung
either.

Two readings of the payoff meet.  An action above the opponent's final atom
captures the whole band, so the payoff is the band's worth net of that action's
cost, which the action's height bounds from above.  The opponent's final atom
also caps the rung it sits on by twice the cost ratio, which through the
opponent's ladder value and the bottom condition bounds the payoff from below.
The two bounds force the stray action onto the rung the hypothesis excludes. -/

/-- **No stray action above the boundary atom.**  With the opponent's support
capped at its final atom and the advantaged player lacking the next rung, the
advantaged player keeps nothing above its own last rung. -/
theorem first_terminal_of_boundary_atom
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ) (hreach : LadderReaches first second gap depth)
    (hSecondCap : ∀ action ∈ second.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 2) * gap)
    (hNoNextRung : ∀ action ∈ first.support,
      (action : ℝ) ≠ (2 * (depth : ℝ) + 3) * gap) :
    ∀ action ∈ first.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap := by
  obtain ⟨hSecondRung, hFirstRung⟩ := hreach
  obtain ⟨-, hbottomValue⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  set top := first.upperSupport with htop
  have htopMem : top ∈ first.support :=
    upperSupport_mem_support hgap.le hweight.le hcost hnash.1
  have hcapAll : ∀ action ∈ first.support, (action : ℝ) ≤ (top : ℝ) := by
    intro action hmem
    have hle := le_upperSupport hgap.le hweight.le hcost hnash.1 hmem
    exact_mod_cast hle
  have hcomplete : ∀ point : ℝ, (2 * (depth : ℝ) + 2) * gap ≤ point →
      second.cdfReal point = 1 := by
    intro point hpoint
    refine cdfReal_eq_one_of_support_le second fun action hmem => ?_
    exact le_trans (hSecondCap action hmem) hpoint
  have htopLe : (top : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap := by
    by_contra hcon
    rw [not_le] at hcon
    have hcleared := first_support_cleared_at hgap hweight hcost hnash hpos
      depth hSecondRung hFirstRung depth (le_refl depth) top htopMem
    have htopFar : (2 * (depth : ℝ) + 3) * gap ≤ (top : ℝ) := by
      rcases hcleared with hlow | hhigh
      · exact absurd hlow (not_le.mpr hcon)
      · linarith
    have hcaptured : borelPureExpectedCapturedGap gap second top = gap := by
      refine borelPureExpectedCapturedGap_eq_gap_of_clear hgap.le second top
        fun rival hrival => ?_
      have := hSecondCap rival hrival
      linarith
    have hindifferent :=
      borelMixedBestResponse_payoff_eq_on_support hgap.le hnash.1 top htopMem
    rw [borelPureExpectedPayoff, hcaptured] at hindifferent
    have hflat := rung_flatness_le hgap hweight hcost hnash hpos depth
      hSecondRung hFirstRung
    obtain ⟨rung, hrungMem, hrungValue⟩ := hFirstRung depth (le_refl depth)
    have hincrement := rung_increment_le (own := first) (opponent := second)
      (low := second.cdfReal (2 * (depth : ℝ) * gap)) (high := 1)
      (anchor := (2 * (depth : ℝ) + 1) * gap) hgap hnash.1 (by positivity)
      (fun point hpoint => (hflat depth (le_refl depth)).1 point
        ⟨by have := hpoint.1; linarith, by have := hpoint.2; linarith⟩)
      (fun point hpoint => hcomplete point (by have := hpoint.1; linarith))
      (realPureExpectedPayoff_eq_max_at_support hgap.le hnash.1 hrungMem
        hrungValue.symm)
    have hladder := second_cdfReal_rung_value_le hgap hweight hcost hnash hpos
      depth hSecondRung hFirstRung depth (le_refl depth)
    have htopValue : (top : ℝ) = (2 * (depth : ℝ) + 3) * gap := by
      have hcancel : marginalCost * (top : ℝ) =
          marginalCost * ((2 * (depth : ℝ) + 3) * gap) := by
        nlinarith [hindifferent, hincrement, hladder, hbottomValue, htopFar]
      exact mul_left_cancel₀ (ne_of_gt hcost) hcancel
    exact hNoNextRung top htopMem htopValue
  intro action hmem
  exact le_trans (hcapAll action hmem) htopLe

/-! ### The dichotomy at the last rung

The clearing at the last rung leaves the opponent's largest action either at or
below that rung, or at least two bands above it.  If it is not more than two
bands above, those are the paper's two terminal cases and both are now settled:
the first gives the whole classification, the second forces the cost ratio onto
the window's lower boundary. -/

/-- **The two terminal cases.**  With the opponent's largest action no more
than two bands above its last rung, a positive-payoff equilibrium either has the
opponent stopping at its last rung, in which case the classification applies, or
has it carrying a final atom two bands up, in which case the cost ratio sits
exactly on the window's lower boundary and the advantaged player still stops at
its own last rung. -/
theorem positive_payoff_terminal_dichotomy
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ) (hreach : LadderReaches first second gap depth)
    (hmaximal : ¬ LadderReaches first second gap (depth + 1))
    (hSecondCap : ∀ action ∈ second.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 2) * gap) :
    (∀ action ∈ second.support, (action : ℝ) ≤ 2 * (depth : ℝ) * gap) ∨
      (slotWeight = (2 * (depth : ℝ) + 2) * marginalCost ∧
        ∀ action ∈ first.support,
          (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap) := by
  classical
  by_cases hlow : ∀ action ∈ second.support,
      (action : ℝ) ≤ 2 * (depth : ℝ) * gap
  · exact Or.inl hlow
  refine Or.inr ?_
  simp only [not_forall, not_le] at hlow
  obtain ⟨stray, hstrayMem, hstray⟩ := hlow
  have hstrayValue : (stray : ℝ) = (2 * (depth : ℝ) + 2) * gap := by
    have hcleared := second_support_cleared_at hgap hweight hcost hnash hpos
      depth hreach.1 hreach.2 depth (le_refl depth) stray hstrayMem
    rcases hcleared with hbelow | habove
    · exact absurd hbelow (not_le.mpr hstray)
    · exact le_antisymm (hSecondCap stray hstrayMem) habove
  have hNoNextRung : ∀ action ∈ first.support,
      (action : ℝ) ≠ (2 * (depth : ℝ) + 3) * gap := by
    intro action hmem hvalue
    refine hmaximal ⟨fun j hj => ?_, fun j hj => ?_⟩
    · rcases Nat.lt_or_ge j (depth + 1) with hlt | hge
      · exact hreach.1 j (Nat.lt_succ_iff.mp hlt)
      · have hjeq : j = depth + 1 := le_antisymm hj hge
        subst hjeq
        refine ⟨stray, hstrayMem, ?_⟩
        rw [hstrayValue]
        push_cast
        ring
    · rcases Nat.lt_or_ge j (depth + 1) with hlt | hge
      · exact hreach.2 j (Nat.lt_succ_iff.mp hlt)
      · have hjeq : j = depth + 1 := le_antisymm hj hge
        subst hjeq
        refine ⟨action, hmem, ?_⟩
        rw [hvalue]
        push_cast
        ring
  have hFirstTerminal := first_terminal_of_boundary_atom hgap hweight hcost
    hnash hpos depth hreach hSecondCap hNoNextRung
  refine ⟨?_, hFirstTerminal⟩
  exact boundary_forced hgap hweight hcost hnash hpos depth hFirstTerminal
    hstrayValue hstrayMem

end

end SmoothingCliff.Racing
