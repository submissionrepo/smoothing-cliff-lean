import SmoothingCliff.Frontier.Squeeze

/-!
# The adjacent-profile shortfall certificate

This file formalizes the algebraic obstruction at the heart of Theorem
`thm:impossibility`.  The remaining part of that theorem is constructive: it
must build the paper's two global rank rules and implement their feasible
weight vectors as measurable lotteries over assignments.  Those constructions
are deliberately not replaced here by existential assumptions.
-/

namespace SmoothingCliff.Frontier

/-- The exact shortfall inequality in the proof of `thm:impossibility`.

`loneLeader` and `loneTrailer` are allocations at `R₁`; `tiedLeader` is either
leader's allocation at `R₂`; `a` and `b` are the welfare shortfalls.  The four
premises are precisely the two cap-shortfall identities, no waste plus trailer
symmetry at `R₁`, and the own-bid Lipschitz comparison between the profiles.
-/
theorem adjacent_profile_shortfall
    {n sensitivity delta u a b loneLeader loneTrailer tiedLeader : ℝ}
    (hn : 1 < n) (hDelta : 0 < delta)
    (hR1 : u + sensitivity * delta - a / delta ≤ loneLeader)
    (hR1Mass : loneLeader + (n - 1) * loneTrailer = n * u)
    (hR2 : 2 * (u + sensitivity * delta) - b / delta ≤
      2 * tiedLeader)
    (hLip : tiedLeader - loneTrailer ≤ sensitivity * delta) :
    2 * a + (n - 1) * b ≥ 2 * sensitivity * delta ^ 2 := by
  have hnpos : 0 < n - 1 := by linarith
  have hdelta_ne : delta ≠ 0 := ne_of_gt hDelta
  field_simp [hdelta_ne] at hR1 hR2
  nlinarith [mul_pos hnpos hDelta]

/-- Consequence used in the final contradiction: a rule that attains the
`R₁` cap assigns each tied leader at `R₂` strictly less than rule B does. -/
theorem tied_leader_strict_gap
    {n sensitivity delta u b tiedLeader : ℝ}
    (hn : 3 < n) (hSensitivity : 0 < sensitivity)
    (hDelta : 0 < delta)
    (hShort : 2 * sensitivity * delta ^ 2 ≤ (n - 1) * b)
    (hDef : 2 * tiedLeader =
      2 * (u + sensitivity * delta) - b / delta) :
    tiedLeader < u + (n - 1) / n * sensitivity * delta := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have h2d : 0 < 2 * delta := mul_pos (by norm_num) hDelta
  have hdne : delta ≠ 0 := ne_of_gt hDelta
  have hbdiv :
      sensitivity * delta / (n - 1) ≤ b / (2 * delta) := by
    apply (div_le_div_iff₀ hn1 h2d).2
    nlinarith
  have hTied :
      tiedLeader = u + sensitivity * delta - b / (2 * delta) := by
    field_simp [hdne] at hDef ⊢
    nlinarith
  have hid :
      sensitivity * delta - sensitivity * delta / (n - 1) =
        (n - 2) / (n - 1) * sensitivity * delta := by
    field_simp
    ring
  have hbound :
      tiedLeader ≤ u + (n - 2) / (n - 1) * sensitivity * delta := by
    rw [hTied, ← hid]
    linarith
  have hcoef : (n - 2) / (n - 1) < (n - 1) / n := by
    apply (div_lt_div_iff₀ hn1 hn0).2
    nlinarith
  have haux : 0 < sensitivity * delta := mul_pos hSensitivity hDelta
  have hmul := mul_lt_mul_of_pos_right hcoef haux
  linarith

end SmoothingCliff.Frontier
