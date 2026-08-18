import SmoothingCliff.Racing.SecondRung

/-!
# The recursion advances by itself

The first rung pair used two moves: clear a player two contested bands above an
anchor where its payoff attains its maximum, then read off that the player's
distribution function is flat across the cleared stretch.  Stated generically,
those two moves feed each other.

Clearing the opponent above an even rung flattens the opponent across the next
two bands, which is exactly the hypothesis for clearing the advantaged player
above the following odd rung, which flattens the advantaged player across the
two bands after that, which is the hypothesis for the next even rung.  So the
alternation is self-feeding and the induction carries no data beyond the
flatness it produces.

What the induction does need from outside is that both players actually keep
mass at the rungs; that is the paper's "unless that distribution is exhausted",
and the terminal cases are where it fails.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- **The clearing move, as a disjunction.**  With a flat departing window and
an anchor at the maximum, every support action is at or below the anchor, or at
least two contested bands above it. -/
theorem support_cleared_two_bands
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
    {action : NNReal} (hmem : action ∈ own.support) :
    (action : ℝ) ≤ anchor ∨ anchor + 2 * gap ≤ (action : ℝ) := by
  by_contra hcon
  rw [not_or, not_le, not_le] at hcon
  exact rung_step_clear (base := base) hgap hweight hcost hbest hflat hanchor
    hmem hcon.1 hcon.2

/-- **The flattening move.**  The cleared stretch leaves the player's own
distribution function constant across it. -/
theorem own_cdfReal_flat_two_bands
    {slotWeight gap marginalCost base : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {own opponent : BorelMixedStrategy}
    (hbest : IsBorelMixedBestResponse slotWeight gap marginalCost own opponent)
    {anchor : ℝ}
    (hflat : ∀ point ∈ Set.Ico (anchor - gap) (anchor + gap),
      opponent.cdfReal point = base)
    (hanchor :
      realPureExpectedPayoff slotWeight gap marginalCost opponent anchor =
        borelExpectedPayoff slotWeight gap marginalCost own opponent) :
    ∀ point ∈ Set.Ico anchor (anchor + 2 * gap),
      own.cdfReal point = own.cdfReal anchor := by
  intro point hpoint
  exact (cdfReal_eq_of_support_clear own
    (fun action hmem => support_cleared_two_bands hgap hweight hcost hbest hflat
      hanchor hmem)
    (le_refl anchor) hpoint.1 hpoint.2).symm

/-- **The recursion, indexed by the rung.**  While both players keep mass at
every rung of their lattices, each player's distribution function is flat
across the two contested bands above each of its own rungs. -/
theorem rung_flatness_induction
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (hSecondRung : ∀ j : ℕ, ∃ action ∈ second.support,
      (action : ℝ) = 2 * (j : ℝ) * gap)
    (hFirstRung : ∀ j : ℕ, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap) :
    ∀ j : ℕ,
      (∀ point ∈ Set.Ico (2 * (j : ℝ) * gap) ((2 * (j : ℝ) + 2) * gap),
        second.cdfReal point = second.cdfReal (2 * (j : ℝ) * gap)) ∧
      (∀ point ∈ Set.Ico ((2 * (j : ℝ) + 1) * gap) ((2 * (j : ℝ) + 3) * gap),
        first.cdfReal point = first.cdfReal ((2 * (j : ℝ) + 1) * gap)) := by
  have hsecondMax : ∀ j : ℕ,
      realPureExpectedPayoff slotWeight gap marginalCost first
          (2 * (j : ℝ) * gap) =
        borelExpectedPayoff slotWeight gap marginalCost second first := by
    intro j
    obtain ⟨action, hmem, hvalue⟩ := hSecondRung j
    exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.2 hmem
      hvalue.symm
  have hfirstMax : ∀ j : ℕ,
      realPureExpectedPayoff slotWeight gap marginalCost second
          ((2 * (j : ℝ) + 1) * gap) =
        borelExpectedPayoff slotWeight gap marginalCost first second := by
    intro j
    obtain ⟨action, hmem, hvalue⟩ := hFirstRung j
    exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.1 hmem
      hvalue.symm
  intro j
  induction j with
  | zero =>
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
    obtain ⟨ihSecond, ihFirst⟩ := ih
    have hsecondNext :
        ∀ point ∈ Set.Ico (2 * ((m : ℝ) + 1) * gap)
            ((2 * ((m : ℝ) + 1) + 2) * gap),
          second.cdfReal point = second.cdfReal (2 * ((m : ℝ) + 1) * gap) := by
      have hstep := own_cdfReal_flat_two_bands (base := first.cdfReal
        ((2 * (m : ℝ) + 1) * gap)) hgap hweight hcost hnash.2
        (anchor := 2 * ((m : ℝ) + 1) * gap)
        (fun point hpoint => ihFirst point
          ⟨by have := hpoint.1; linarith, by have := hpoint.2; linarith⟩)
        (by simpa using hsecondMax (m + 1))
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
        (by simpa using hfirstMax (m + 1))
      intro point hpoint
      have hcast : (((m : ℕ) + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hpoint ⊢
      exact hstep point ⟨hpoint.1, by have := hpoint.2; linarith⟩

/-- **Equation (S) at every rung.**  While both players keep mass at every rung,
the advantaged player's mass at each odd rung is exactly twice the cost ratio.
Below the lowest rung the distribution function vanishes, so the statement holds
verbatim at the first rung too. -/
theorem first_rung_increments
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (hSecondRung : ∀ j : ℕ, ∃ action ∈ second.support,
      (action : ℝ) = 2 * (j : ℝ) * gap)
    (hFirstRung : ∀ j : ℕ, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap) :
    ∀ j : ℕ,
      slotWeight *
          (first.cdfReal ((2 * (j : ℝ) + 1) * gap) -
            first.cdfReal ((2 * (j : ℝ) - 1) * gap)) =
        2 * marginalCost := by
  have hflat := rung_flatness_induction hgap hweight hcost hnash hpos
    hSecondRung hFirstRung
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  have hsecondMax : ∀ j : ℕ,
      realPureExpectedPayoff slotWeight gap marginalCost first
          (2 * (j : ℝ) * gap) =
        borelExpectedPayoff slotWeight gap marginalCost second first := by
    intro j
    obtain ⟨action, hmem, hvalue⟩ := hSecondRung j
    exact realPureExpectedPayoff_eq_max_at_support hgap.le hnash.2 hmem
      hvalue.symm
  intro j
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
      have hstep := (hflat m).2 point
        ⟨by have := hpoint.1; push_cast at this ⊢; linarith,
          by have := hpoint.2; push_cast at this ⊢; linarith⟩
      have hindex : (2 * ((m : ℝ) + 1) - 1) * gap = (2 * (m : ℝ) + 1) * gap := by
        ring
      rw [hstep]
      push_cast
      rw [hindex]
  · intro point hpoint
    have hstep := (hflat j).2 point
      ⟨by have := hpoint.1; linarith, by have := hpoint.2; linarith⟩
    rw [hstep]
  · exact hsecondMax j
  · have hnext := hsecondMax (j + 1)
    have hindex : 2 * (((j : ℝ) + 1)) * gap = 2 * (j : ℝ) * gap + 2 * gap := by
      ring
    push_cast at hnext
    rw [hindex] at hnext
    exact hnext

/-- **The rung count.**  While both players keep going, the advantaged player's
distribution function at the `j`-th odd rung is `j+1` times twice the cost
ratio: each rung takes exactly that much mass and the ladder starts from
nothing. -/
theorem first_cdfReal_rung_value
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second)
    (hSecondRung : ∀ j : ℕ, ∃ action ∈ second.support,
      (action : ℝ) = 2 * (j : ℝ) * gap)
    (hFirstRung : ∀ j : ℕ, ∃ action ∈ first.support,
      (action : ℝ) = (2 * (j : ℝ) + 1) * gap) :
    ∀ j : ℕ,
      slotWeight * first.cdfReal ((2 * (j : ℝ) + 1) * gap) =
        ((j : ℝ) + 1) * (2 * marginalCost) := by
  have hincrement := first_rung_increments hgap hweight hcost hnash hpos
    hSecondRung hFirstRung
  obtain ⟨hband, -⟩ :=
    bottomCondition_of_payoff_pos hgap hweight hcost hnash hpos
  intro j
  induction j with
  | zero =>
    have hstep := hincrement 0
    have hbelow : first.cdfReal ((2 * ((0 : ℕ) : ℝ) - 1) * gap) = 0 := by
      refine cdfReal_eq_zero_of_lt_lowerSupport first ?_
      rw [hband]
      push_cast
      linarith
    rw [hbelow] at hstep
    push_cast at hstep ⊢
    linarith
  | succ m ih =>
    have hstep := hincrement (m + 1)
    have hindex : (2 * (((m : ℕ) + 1 : ℕ) : ℝ) - 1) * gap =
        (2 * (m : ℝ) + 1) * gap := by
      push_cast
      ring
    rw [hindex] at hstep
    push_cast at hstep ih ⊢
    linarith

/-- **The recursion terminates.**  Both players cannot keep mass at every rung:
each rung takes twice the cost ratio out of a distribution function bounded by
one.  So some rung is missing, and that is where the terminal cases of
`prop:sp_allequilibria` (iii) begin. -/
theorem rungs_cannot_continue_forever
    {slotWeight gap marginalCost : ℝ} (hgap : 0 < gap)
    (hweight : 0 < slotWeight) (hcost : 0 < marginalCost)
    {first second : BorelMixedStrategy}
    (hnash : IsBorelMixedNash slotWeight gap marginalCost first second)
    (hpos : 0 < borelExpectedPayoff slotWeight gap marginalCost first second) :
    ¬((∀ j : ℕ, ∃ action ∈ second.support,
        (action : ℝ) = 2 * (j : ℝ) * gap) ∧
      (∀ j : ℕ, ∃ action ∈ first.support,
        (action : ℝ) = (2 * (j : ℝ) + 1) * gap)) := by
  rintro ⟨hSecondRung, hFirstRung⟩
  have hvalue := first_cdfReal_rung_value hgap hweight hcost hnash hpos
    hSecondRung hFirstRung
  obtain ⟨j, hj⟩ := exists_nat_gt (slotWeight / (2 * marginalCost))
  have hbound := first.cdfReal_le_one ((2 * (j : ℝ) + 1) * gap)
  have hkey := hvalue j
  have hle : ((j : ℝ) + 1) * (2 * marginalCost) ≤ slotWeight := by
    nlinarith [mul_le_mul_of_nonneg_left hbound hweight.le, hkey]
  have hgt : slotWeight < (j : ℝ) * (2 * marginalCost) := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * marginalCost)] at hj
    linarith
  nlinarith [hle, hgt, hcost]

end

end SmoothingCliff.Racing
