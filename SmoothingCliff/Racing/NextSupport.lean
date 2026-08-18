import SmoothingCliff.Racing.SupportBound

/-!
# The next support point, and blocking

The last branch of the classification is the one where the opponent keeps mass
more than two contested bands above its last rung.  Ruling it out needs the
alternation run at the actual next support points rather than at the lattice
positions, so this file supplies them.

The blocking lemma is the reason the alternation closes.  On a stretch where
the opponent's distribution function is flat across both windows the payoff
falls at the cost rate, so a player anchored at its maximum keeps nothing
strictly inside that stretch.  Each player's next point is therefore beyond the
other's, and two such inequalities cannot both hold.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- The smallest action the player keeps at or above a given level. -/
def BorelMixedStrategy.nextAtLeast (strategy : BorelMixedStrategy)
    (level : NNReal) : NNReal :=
  sInf (strategy.support ∩ Set.Ici level)

theorem nextAtLeast_mem (strategy : BorelMixedStrategy) {level : NNReal}
    (hne : (strategy.support ∩ Set.Ici level).Nonempty) :
    strategy.nextAtLeast level ∈ strategy.support ∩ Set.Ici level :=
  IsClosed.csInf_mem (strategy.support_closed.inter isClosed_Ici) hne
    ⟨0, fun _ _ => bot_le⟩

theorem nextAtLeast_le (strategy : BorelMixedStrategy) {level action : NNReal}
    (hmem : action ∈ strategy.support) (hlevel : level ≤ action) :
    strategy.nextAtLeast level ≤ action :=
  csInf_le ⟨0, fun _ _ => bot_le⟩ ⟨hmem, hlevel⟩

/-- **Blocking.**  A player anchored at its maximum keeps nothing strictly
inside a stretch on which the opponent's distribution function is flat across
both windows: the payoff falls there at the cost rate. -/
theorem no_support_in_flat_stretch
    {slotWeight gap marginalCost base : ℝ} (hgap : 0 < gap)
    (hcost : 0 < marginalCost)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {anchor finish : ℝ}
    (hflat : ∀ point ∈ Set.Ico (anchor - gap) finish,
      opponent.cdfReal point = base)
    (hanchor :
      realPureExpectedPayoff slotWeight gap marginalCost opponent anchor ≤
        borelExpectedPayoff slotWeight gap marginalCost own opponent)
    {action : NNReal} (hmem : action ∈ own.support)
    (hlow : anchor < (action : ℝ)) (hhigh : (action : ℝ) ≤ finish) :
    False := by
  have hvalue :=
    realPureExpectedPayoff_eq_max_at_support hgap.le hbest hmem (x := (action : ℝ))
      rfl
  have hfall := realPureExpectedPayoff_sub_of_flat (slotWeight := slotWeight)
    (marginalCost := marginalCost) (base := base) hgap.le (opponent := opponent)
    (start := anchor) (finish := (action : ℝ)) hlow.le
    (fun point hpoint => hflat point ⟨hpoint.1, by linarith [hpoint.2]⟩)
  rw [hvalue] at hfall
  nlinarith [hfall, hanchor, hlow, hcost]

/-! ### Closing the last branch

Suppose the opponent keeps mass more than two contested bands above its last
rung.  Two clearings then block each other.

The advantaged player's own next point past its last rung leaves its
distribution function flat up to there, so the opponent keeps nothing between
two bands up and that point.  The opponent's own next point past that leaves
its distribution function flat up to there, so the advantaged player keeps
nothing between three bands up and that point.  Each next point is therefore
strictly beyond the other, which is impossible. -/

/-- **The opponent stays within two bands of its last rung.**  This is the
hypothesis the terminal dichotomy was still carrying. -/
theorem second_support_le_two_bands_past
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (depth : ℕ) (hreach : LadderReaches first second gap depth)
    (hmaximal : ¬ LadderReaches first second gap (depth + 1)) :
    ∀ action ∈ second.support,
      (action : ℝ) ≤ (2 * (depth : ℝ) + 2) * gap := by
  classical
  obtain ⟨hSecondRung, hFirstRung⟩ := hreach
  obtain ⟨-, hzeroSecond, -⟩ :=
    opponent_at_bottom_of_payoff_pos hgap.le hcost hnash hpos
  have hdepthNonneg : (0 : ℝ) ≤ (depth : ℝ) := Nat.cast_nonneg depth
  have hfirstClear := first_support_cleared_at hgap hweight hcost hnash hpos
    depth hSecondRung hFirstRung depth (le_refl depth)
  have hsecondClear := second_support_cleared_at hgap hweight hcost hnash hpos
    depth hSecondRung hFirstRung depth (le_refl depth)
  intro stray hstrayMem
  by_contra hstray
  rw [not_le] at hstray
  by_cases hfirstHigh : ∃ action ∈ first.support,
      (2 * (depth : ℝ) + 3) * gap ≤ (action : ℝ)
  · obtain ⟨witness, hwitnessMem, hwitness⟩ := hfirstHigh
    set level : NNReal := ((2 * (depth : ℝ) + 3) * gap).toNNReal with hlevel
    have hlevelCoe : ((level : NNReal) : ℝ) = (2 * (depth : ℝ) + 3) * gap := by
      rw [hlevel]
      exact Real.coe_toNNReal _ (by positivity)
    have hne : (first.support ∩ Set.Ici level).Nonempty := by
      refine ⟨witness, hwitnessMem, ?_⟩
      have hcoe : ((level : NNReal) : ℝ) ≤ (witness : ℝ) := by
        rw [hlevelCoe]; exact hwitness
      exact_mod_cast hcoe
    obtain ⟨hTmem, hTlevel⟩ := nextAtLeast_mem first hne
    set nextFirst : NNReal := first.nextAtLeast level with hnextFirst
    have hTlow : (2 * (depth : ℝ) + 3) * gap ≤ (nextFirst : ℝ) := by
      have hcoe : ((level : NNReal) : ℝ) ≤ (nextFirst : ℝ) := by
        exact_mod_cast hTlevel
      rw [hlevelCoe] at hcoe
      exact hcoe
    have hgapClear : ∀ action ∈ first.support,
        (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap ∨
          (nextFirst : ℝ) ≤ (action : ℝ) := by
      intro action hmem
      rcases hfirstClear action hmem with hlow | hhigh
      · exact Or.inl hlow
      · refine Or.inr ?_
        have hge : level ≤ action := by
          have hcoe : ((level : NNReal) : ℝ) ≤ (action : ℝ) := by
            rw [hlevelCoe]; exact hhigh
          exact_mod_cast hcoe
        have hstep := nextAtLeast_le first hmem hge
        exact_mod_cast hstep
    have hfirstFlat : ∀ point ∈ Set.Ico ((2 * (depth : ℝ) + 1) * gap)
        ((nextFirst : ℝ)), first.cdfReal point =
          first.cdfReal ((2 * (depth : ℝ) + 1) * gap) :=
      fun point hpoint => (cdfReal_eq_of_support_clear first hgapClear
        (le_refl _) hpoint.1 hpoint.2).symm
    have hsecondBlocked : ∀ action ∈ second.support,
        (2 * (depth : ℝ) + 2) * gap < (action : ℝ) →
          (nextFirst : ℝ) < (action : ℝ) := by
      intro action hmem hhigh
      by_contra hle
      rw [not_lt] at hle
      refine no_support_in_flat_stretch (base := first.cdfReal
        ((2 * (depth : ℝ) + 1) * gap)) hgap hcost hnash.2
        (anchor := (2 * (depth : ℝ) + 2) * gap) (finish := (nextFirst : ℝ))
        (fun point hpoint => hfirstFlat point
          ⟨by have := hpoint.1; linarith, hpoint.2⟩)
        ?_ hmem hhigh hle
      rw [hzeroSecond]
      exact realPureExpectedPayoff_nonpos_of_zero_payoff hgap.le hnash.2
        hzeroSecond (by positivity)
    have hstrayFar : (nextFirst : ℝ) < (stray : ℝ) :=
      hsecondBlocked stray hstrayMem hstray
    have hne2 : (second.support ∩ Set.Ici nextFirst).Nonempty := by
      refine ⟨stray, hstrayMem, ?_⟩
      have hcoe : (nextFirst : ℝ) ≤ (stray : ℝ) := le_of_lt hstrayFar
      exact_mod_cast hcoe
    obtain ⟨hSmem, hSlevel⟩ := nextAtLeast_mem second hne2
    set nextSecond : NNReal := second.nextAtLeast nextFirst with hnextSecond
    have hSlow : (nextFirst : ℝ) ≤ (nextSecond : ℝ) := by exact_mod_cast hSlevel
    have hsecondGapClear : ∀ action ∈ second.support,
        (action : ℝ) ≤ (2 * (depth : ℝ) + 2) * gap ∨
          (nextSecond : ℝ) ≤ (action : ℝ) := by
      intro action hmem
      by_cases hhigh : (2 * (depth : ℝ) + 2) * gap < (action : ℝ)
      · refine Or.inr ?_
        have hbeyond := hsecondBlocked action hmem hhigh
        have hge : nextFirst ≤ action := by
          have hcoe : (nextFirst : ℝ) ≤ (action : ℝ) := le_of_lt hbeyond
          exact_mod_cast hcoe
        have hstep := nextAtLeast_le second hmem hge
        exact_mod_cast hstep
      · exact Or.inl (not_lt.mp hhigh)
    have hsecondFlat : ∀ point ∈ Set.Ico ((2 * (depth : ℝ) + 2) * gap)
        ((nextSecond : ℝ)), second.cdfReal point =
          second.cdfReal ((2 * (depth : ℝ) + 2) * gap) :=
      fun point hpoint => (cdfReal_eq_of_support_clear second hsecondGapClear
        (le_refl _) hpoint.1 hpoint.2).symm
    have hfirstBlocked : ∀ action ∈ first.support,
        (2 * (depth : ℝ) + 3) * gap < (action : ℝ) →
          (nextSecond : ℝ) < (action : ℝ) := by
      intro action hmem hhigh
      by_contra hle
      rw [not_lt] at hle
      refine no_support_in_flat_stretch (base := second.cdfReal
        ((2 * (depth : ℝ) + 2) * gap)) hgap hcost hnash.1
        (anchor := (2 * (depth : ℝ) + 3) * gap) (finish := (nextSecond : ℝ))
        (fun point hpoint => hsecondFlat point
          ⟨by have := hpoint.1; linarith, hpoint.2⟩)
        (realPureExpectedPayoff_le_max hgap.le hnash.1 (by positivity))
        hmem hhigh hle
    rcases eq_or_lt_of_le hTlow with heq | hgt
    · refine hmaximal ⟨fun j hj => ?_, fun j hj => ?_⟩
      · rcases Nat.lt_or_ge j (depth + 1) with hlt | hge
        · exact hSecondRung j (Nat.lt_succ_iff.mp hlt)
        · exfalso
          have hnoAtom : ∀ action ∈ second.support,
              (action : ℝ) ≤ 2 * (depth : ℝ) * gap ∨
                (nextFirst : ℝ) < (action : ℝ) := by
            intro action hmem
            rcases hsecondClear action hmem with hlow | hhigh
            · exact Or.inl hlow
            · rcases eq_or_lt_of_le hhigh with hatom | habove
              · exfalso
                refine hmaximal ⟨fun i hi => ?_, fun i hi => ?_⟩
                · rcases Nat.lt_or_ge i (depth + 1) with hlt2 | hge2
                  · exact hSecondRung i (Nat.lt_succ_iff.mp hlt2)
                  · have hieq : i = depth + 1 := le_antisymm hi hge2
                    subst hieq
                    exact ⟨action, hmem, by rw [← hatom]; push_cast; ring⟩
                · rcases Nat.lt_or_ge i (depth + 1) with hlt2 | hge2
                  · exact hFirstRung i (Nat.lt_succ_iff.mp hlt2)
                  · have hieq : i = depth + 1 := le_antisymm hi hge2
                    subst hieq
                    exact ⟨nextFirst, hTmem, by rw [← heq]; push_cast; ring⟩
              · exact Or.inr (hsecondBlocked action hmem (by linarith))
          have hwideFlat : ∀ point ∈ Set.Ico (2 * (depth : ℝ) * gap)
              ((nextFirst : ℝ)), second.cdfReal point =
                second.cdfReal (2 * (depth : ℝ) * gap) := by
            intro point hpoint
            refine (cdfReal_eq_of_support_clear second
              (fun action hmem => ?_) (le_refl _) hpoint.1 hpoint.2).symm
            rcases hnoAtom action hmem with hlow | hhigh
            · exact Or.inl hlow
            · exact Or.inr (le_of_lt hhigh)
          obtain ⟨rung, hrungMem, hrungValue⟩ := hFirstRung depth (le_refl depth)
          refine no_support_in_flat_stretch (base := second.cdfReal
            (2 * (depth : ℝ) * gap)) hgap hcost hnash.1
            (anchor := (2 * (depth : ℝ) + 1) * gap)
            (finish := (nextFirst : ℝ))
            (fun point hpoint => hwideFlat point
              ⟨by have := hpoint.1; linarith, hpoint.2⟩)
            (le_of_eq (realPureExpectedPayoff_eq_max_at_support hgap.le hnash.1
              hrungMem hrungValue.symm))
            hTmem (by linarith) (le_refl _)
      · rcases Nat.lt_or_ge j (depth + 1) with hlt | hge
        · exact hFirstRung j (Nat.lt_succ_iff.mp hlt)
        · have hjeq : j = depth + 1 := le_antisymm hj hge
          subst hjeq
          exact ⟨nextFirst, hTmem, by rw [← heq]; push_cast; ring⟩
    · have hblock := hfirstBlocked nextFirst hTmem hgt
      linarith [hSlow]
  · simp only [not_exists, not_and, not_le] at hfirstHigh
    have hcap : ∀ action ∈ first.support,
        (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap := by
      intro action hmem
      rcases hfirstClear action hmem with hlow | hhigh
      · exact hlow
      · exact absurd hhigh (not_le.mpr (hfirstHigh action hmem))
    have hfull : ∀ point : ℝ, (2 * (depth : ℝ) + 1) * gap ≤ point →
        first.cdfReal point = 1 := fun point hpoint =>
      cdfReal_eq_one_of_support_le first
        (fun action hmem => le_trans (hcap action hmem) hpoint)
    refine no_support_in_flat_stretch (base := 1) hgap hcost hnash.2
      (anchor := (2 * (depth : ℝ) + 2) * gap) (finish := (stray : ℝ))
      (fun point hpoint => hfull point (by have := hpoint.1; linarith))
      ?_ hstrayMem hstray (le_refl _)
    rw [hzeroSecond]
    exact realPureExpectedPayoff_nonpos_of_zero_payoff hgap.le hnash.2
      hzeroSecond (by positivity)

/-! ### The classification, unconditional

Every hypothesis the classification was carrying is now discharged.  The last
rung is constructed, the opponent stays within two bands of it, and the two
terminal cases are settled, so an arbitrary positive-payoff equilibrium falls
into one of them with nothing assumed. -/

/-- **The terminal dichotomy, unconditional.**  Every positive-payoff
equilibrium has a last rung, and at it either the opponent stops, or the cost
ratio sits exactly on the window's lower boundary and the advantaged player
stops at its own last rung. -/
theorem positive_payoff_dichotomy
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    ∃ depth : ℕ, LadderReaches first second gap depth ∧
      ((∀ action ∈ second.support, (action : ℝ) ≤ 2 * (depth : ℝ) * gap) ∨
        (slotWeight = (2 * (depth : ℝ) + 2) * marginalCost ∧
          ∀ action ∈ first.support,
            (action : ℝ) ≤ (2 * (depth : ℝ) + 1) * gap)) := by
  obtain ⟨depth, hreach, hmaximal⟩ :=
    exists_last_rung hgap hweight hcost hnash hpos
  refine ⟨depth, hreach, ?_⟩
  exact positive_payoff_terminal_dichotomy hgap hweight hcost hnash hpos depth
    hreach hmaximal
    (second_support_le_two_bands_past hgap hweight hcost hnash hpos depth
      hreach hmaximal)

/-- **The classification, unconditional.**  Every positive-payoff equilibrium
has a last rung, and either it is the first terminal case, where the whole
classification holds, or it is the boundary case, where the cost ratio is
exactly the window's lower edge. -/
theorem positive_payoff_classification_unconditional
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    ∃ depth : ℕ,
      (((2 * (depth : ℝ) + 1) * marginalCost < slotWeight ∧
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
          borelExpectedDissipation marginalCost first second) ∨
      slotWeight = (2 * (depth : ℝ) + 2) * marginalCost := by
  obtain ⟨depth, hreach, hcase⟩ :=
    positive_payoff_dichotomy hgap hweight hcost hnash hpos
  refine ⟨depth, ?_⟩
  rcases hcase with hstop | ⟨hboundary, -⟩
  · exact Or.inl (positive_payoff_classification hgap hweight hcost hnash hpos
      depth hreach hstop)
  · exact Or.inr hboundary

end

end SmoothingCliff.Racing
