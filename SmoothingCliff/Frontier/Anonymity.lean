import SmoothingCliff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Anonymity cannot be dropped

Formal target: the counterexample of Remark `rem:classscope` in
`Smoothing_the_Cliff_ITCS.tex`, whose full form sits in the frontier appendix.

The certified class is defined with anonymity, and the remark's point is that
this is forced rather than convenient: without it, pointwise welfare optimality
already fails at two bidders.  The constant favoritism rules give each leader
the whole prize at an arbitrarily small lead, so a pointwise-optimal rule would
have to do the same on both sides; walking each leader's own bid back to the
tie then violates feasibility.

Only the own-bid Lipschitz property and one-slot feasibility are used.
-/

namespace SmoothingCliff.Frontier

noncomputable section

/-- **Remark `rem:classscope`.**  No feasible rule with an own-bid Lipschitz
certificate can give each of two bidders the whole prize at an `epsilon` lead,
once `epsilon` is below half the certified band. -/
theorem no_pointwise_optimum_without_anonymity
    {weight sensitivity tie epsilon : ℝ}
    (hSmall : 2 * sensitivity * epsilon < weight)
    (first second : ℝ → ℝ → ℝ)
    (hFeasible : first tie tie + second tie tie ≤ weight)
    (hLipFirst :
      |first (tie + epsilon) tie - first tie tie| ≤ sensitivity * epsilon)
    (hLipSecond :
      |second tie (tie + epsilon) - second tie tie| ≤ sensitivity * epsilon)
    (hLeaderFirst : first (tie + epsilon) tie = weight)
    (hLeaderSecond : second tie (tie + epsilon) = weight) :
    False := by
  have hFirst : weight - sensitivity * epsilon ≤ first tie tie := by
    have := abs_le.mp hLipFirst
    rw [hLeaderFirst] at this
    linarith [this.1]
  have hSecond : weight - sensitivity * epsilon ≤ second tie tie := by
    have := abs_le.mp hLipSecond
    rw [hLeaderSecond] at this
    linarith [this.1]
  linarith

/-- The remark's displayed threshold: below `weight / (2 * sensitivity)` the
contradiction bites. -/
theorem no_pointwise_optimum_without_anonymity_at_threshold
    {weight sensitivity tie epsilon : ℝ}
    (hWeight : 0 < weight) (hSensitivity : 0 < sensitivity)
    (hEpsilon : 0 < epsilon) (hSmall : epsilon < weight / (2 * sensitivity))
    (first second : ℝ → ℝ → ℝ)
    (hFeasible : first tie tie + second tie tie ≤ weight)
    (hLipFirst :
      |first (tie + epsilon) tie - first tie tie| ≤ sensitivity * epsilon)
    (hLipSecond :
      |second tie (tie + epsilon) - second tie tie| ≤ sensitivity * epsilon)
    (hLeaderFirst : first (tie + epsilon) tie = weight)
    (hLeaderSecond : second tie (tie + epsilon) = weight) :
    False := by
  refine no_pointwise_optimum_without_anonymity ?_ first
    second hFeasible hLipFirst hLipSecond hLeaderFirst hLeaderSecond
  have hpos : 0 < 2 * sensitivity := by linarith
  calc
    2 * sensitivity * epsilon < 2 * sensitivity * (weight / (2 * sensitivity)) :=
      by exact mul_lt_mul_of_pos_left hSmall hpos
    _ = weight := by field_simp

end

end SmoothingCliff.Frontier
