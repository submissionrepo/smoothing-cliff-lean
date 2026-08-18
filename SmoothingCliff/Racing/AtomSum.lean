import SmoothingCliff.Racing.FirstRung

/-!
# Computing the return against a finitely supported opponent

The bookkeeping lemma behind every rung value in `prop:sp_allequilibria` (iii).
Below the own action the opponent's support is a finite set of rungs, and
everything the opponent keeps above the own action returns nothing.  So the
expected captured band is the finite sum of the opponent's atoms weighted by
the band each of them concedes.

Both earlier computations are instances: a single atom at zero, and a pure
opponent.  What the recursion adds is that the sum runs over a lattice, so the
rung values are linear in the accumulated masses.
-/

namespace SmoothingCliff.Racing

open MeasureTheory

noncomputable section

/-- **The finite-atom formula.**  If everything the opponent keeps outside a
finite set is weakly above the own action, the expected captured band is the
sum over that set of the atom times the band it concedes. -/
theorem borelPureExpectedCapturedGap_eq_finset_sum
    {gap : ℝ} (hgap : 0 ≤ gap) (opponent : BorelMixedStrategy)
    (action : NNReal) (atoms : Finset NNReal)
    (hclear : ∀ rival ∈ opponent.support, rival ∉ atoms →
      (action : ℝ) ≤ (rival : ℝ)) :
    borelPureExpectedCapturedGap gap opponent action =
      ∑ point ∈ atoms, ((opponent.law : Measure NNReal) {point}).toReal *
        strictPriorityCapturedGap gap (action : ℝ) (point : ℝ) := by
  classical
  have hterm : ∀ point : NNReal,
      ∫ rival : NNReal,
          strictPriorityCapturedGap gap (action : ℝ) (point : ℝ) *
            ({point} : Set NNReal).indicator (fun _ => (1 : ℝ)) rival
          ∂(opponent.law : Measure NNReal) =
        ((opponent.law : Measure NNReal) {point}).toReal *
          strictPriorityCapturedGap gap (action : ℝ) (point : ℝ) := by
    intro point
    rw [integral_const_mul]
    simp only [← Pi.one_def]
    rw [integral_indicator_one (measurableSet_singleton point), measureReal_def,
      mul_comm]
  have hint : ∀ point : NNReal, Integrable (fun rival : NNReal =>
      strictPriorityCapturedGap gap (action : ℝ) (point : ℝ) *
        ({point} : Set NNReal).indicator (fun _ => (1 : ℝ)) rival)
      (opponent.law : Measure NNReal) := fun point =>
    ((integrable_const (1 : ℝ)).indicator
      (measurableSet_singleton point)).const_mul _
  rw [borelPureExpectedCapturedGap]
  have hsum : ∫ rival : NNReal,
        strictPriorityCapturedGap gap (action : ℝ) (rival : ℝ)
        ∂(opponent.law : Measure NNReal) =
      ∫ rival : NNReal, ∑ point ∈ atoms,
          strictPriorityCapturedGap gap (action : ℝ) (point : ℝ) *
            ({point} : Set NNReal).indicator (fun _ => (1 : ℝ)) rival
        ∂(opponent.law : Measure NNReal) := by
    refine integral_congr_ae ?_
    filter_upwards [opponent.ae_mem_support] with rival hrival
    by_cases hmem : rival ∈ atoms
    · rw [Finset.sum_eq_single rival]
      · rw [Set.indicator_of_mem (Set.mem_singleton rival), mul_one]
      · intro other _ hne
        have hnot : rival ∉ ({other} : Set NNReal) := fun hcon =>
          hne (Set.mem_singleton_iff.mp hcon).symm
        rw [Set.indicator_of_notMem hnot, mul_zero]
      · intro hcon
        exact absurd hmem hcon
    · have hle := hclear rival hrival hmem
      rw [strictPriorityCapturedGap,
        max_eq_right (by linarith : (action : ℝ) - (rival : ℝ) ≤ 0),
        min_eq_left hgap]
      symm
      refine Finset.sum_eq_zero fun other hother => ?_
      have hnot : rival ∉ ({other} : Set NNReal) := by
        intro hcon
        rw [Set.mem_singleton_iff] at hcon
        exact hmem (by rw [hcon]; exact hother)
      rw [Set.indicator_of_notMem hnot, mul_zero]
  rw [hsum, integral_finsetSum atoms fun point _ => hint point]
  exact Finset.sum_congr rfl fun point _ => hterm point

end

end SmoothingCliff.Racing
