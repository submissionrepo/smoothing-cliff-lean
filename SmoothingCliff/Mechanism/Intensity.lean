import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Shared Luce intensity vocabulary

The exponential intensity of an eligible bid is used by both the exponential-race
monotonicity development and the exact one-slot stability development.  It lives
in its own module so that neither of those files has to depend on the other.
-/

namespace SmoothingCliff.Mechanism

/-- Exponential intensity of an eligible bid, normalized to one at the reserve. -/
noncomputable def luceIntensity
    (reserve temperature bid : ℝ) : ℝ :=
  Real.exp ((bid - reserve) / temperature)

theorem luceIntensity_pos (reserve temperature bid : ℝ) :
    0 < luceIntensity reserve temperature bid :=
  Real.exp_pos _

theorem luceIntensity_mono
    (reserve temperature a b : ℝ)
    (hTemperature : 0 < temperature) (hab : a ≤ b) :
    luceIntensity reserve temperature a ≤
      luceIntensity reserve temperature b := by
  apply Real.exp_le_exp.mpr
  exact (div_le_div_iff_of_pos_right hTemperature).2
    (sub_le_sub_right hab reserve)

end SmoothingCliff.Mechanism
