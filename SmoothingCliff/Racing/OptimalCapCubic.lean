import SmoothingCliff.Racing.OptimalCap

/-!
# The dissipation-only cap and its closed form

Formal target: Remark `rem:optcert_cubic` in `Smoothing_the_Cliff_ITCS.tex`.

A principal who prices burned resources alone, so that investment is positive
at every cap, solves `min_S w1^2/(4 S) + (Gamma2 / 2) S^2`.  The optimum is the
cube root of the squared prize over aggregate racing capacity, and the total
certified concession is three halves of the quadratic term there.

The optimum is characterized through the cubic `4 * Gamma2 * S^3 = w1^2` rather
than through a real cube root, which keeps the value identity exact: at the
optimum the smoothing concession equals the quadratic racing term, so the total
is three halves of either.
-/

namespace SmoothingCliff.Racing

noncomputable section

/-- The dissipation-only objective `w1^2/(4 S) + (Gamma2 / 2) S^2`. -/
def dissipationOnlyCost (slotWeight capacityAggregate cap : ℝ) : ℝ :=
  slotWeight ^ 2 / 4 * cap⁻¹ + capacityAggregate / 2 * cap ^ 2

/-- Marginal certified concession. -/
def dissipationOnlyMarginal (slotWeight capacityAggregate cap : ℝ) : ℝ :=
  -(slotWeight ^ 2 / 4) * (cap ^ 2)⁻¹ + capacityAggregate * cap

theorem dissipationOnlyCost_hasDerivAt
    (slotWeight capacityAggregate : ℝ) {cap : ℝ} (hCap : cap ≠ 0) :
    HasDerivAt (dissipationOnlyCost slotWeight capacityAggregate)
      (dissipationOnlyMarginal slotWeight capacityAggregate cap) cap := by
  have hinv : HasDerivAt (fun c : ℝ => c⁻¹) (-((cap ^ 2)⁻¹)) cap :=
    hasDerivAt_inv hCap
  have hfirst := hinv.const_mul (slotWeight ^ 2 / 4)
  have hsq : HasDerivAt (fun c : ℝ => c ^ 2) (2 * cap) cap := by
    simpa using hasDerivAt_pow 2 cap
  have hsecond := hsq.const_mul (capacityAggregate / 2)
  have hsum := hfirst.add hsecond
  convert hsum using 1
  rw [dissipationOnlyMarginal]
  ring

/-- The marginal concession is strictly increasing on the positive caps. -/
theorem dissipationOnlyMarginal_strictMonoOn
    {slotWeight capacityAggregate : ℝ} (hCapacity : 0 < capacityAggregate) :
    StrictMonoOn (dissipationOnlyMarginal slotWeight capacityAggregate)
      (Set.Ioi 0) := by
  intro a ha b hb hab
  have hapos : (0 : ℝ) < a := ha
  have hbpos : (0 : ℝ) < b := hb
  have hsq : a ^ 2 < b ^ 2 := by nlinarith
  have hinv : (b ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := by
    have ha2 : (0 : ℝ) < a ^ 2 := by positivity
    have hb2 : (0 : ℝ) < b ^ 2 := by positivity
    have key : (a ^ 2)⁻¹ - (b ^ 2)⁻¹ = (b ^ 2 - a ^ 2) / (a ^ 2 * b ^ 2) := by
      field_simp
    have hnonneg : 0 ≤ (b ^ 2 - a ^ 2) / (a ^ 2 * b ^ 2) :=
      div_nonneg (by linarith) (by positivity)
    linarith
  have hweight : (0 : ℝ) ≤ slotWeight ^ 2 / 4 := by positivity
  have hlinear : capacityAggregate * a < capacityAggregate * b :=
    mul_lt_mul_of_pos_left hab hCapacity
  have hfirst : -(slotWeight ^ 2 / 4) * (a ^ 2)⁻¹ ≤
      -(slotWeight ^ 2 / 4) * (b ^ 2)⁻¹ := by
    nlinarith [hinv, hweight]
  simp only [dissipationOnlyMarginal]
  linarith

/-- A positive minimizer solves the cubic. -/
theorem cubic_of_isMinOn
    {slotWeight capacityAggregate cap : ℝ} (hCap : 0 < cap)
    (hMin : IsMinOn (dissipationOnlyCost slotWeight capacityAggregate)
      (Set.Ioi 0) cap) :
    4 * capacityAggregate * cap ^ 3 = slotWeight ^ 2 := by
  have hderiv := dissipationOnlyCost_hasDerivAt slotWeight capacityAggregate
    (ne_of_gt hCap)
  have hlocal : IsLocalMin (dissipationOnlyCost slotWeight capacityAggregate)
      cap := hMin.isLocalMin (Ioi_mem_nhds hCap)
  have hzero : dissipationOnlyMarginal slotWeight capacityAggregate cap = 0 :=
    hlocal.hasDerivAt_eq_zero hderiv
  simp only [dissipationOnlyMarginal] at hzero
  have hcancel : (cap ^ 2)⁻¹ * cap ^ 2 = 1 :=
    inv_mul_cancel₀ (by positivity)
  have hexpand :
      -(slotWeight ^ 2 / 4) + capacityAggregate * cap ^ 3 = 0 := by
    calc -(slotWeight ^ 2 / 4) + capacityAggregate * cap ^ 3
        = (-(slotWeight ^ 2 / 4) * (cap ^ 2)⁻¹ +
            capacityAggregate * cap) * cap ^ 2 := by
          rw [add_mul, mul_assoc, hcancel]
          ring
      _ = 0 := by rw [hzero, zero_mul]
  linarith

/-- **Remark `rem:optcert_cubic`, uniqueness.**  At most one positive cap
minimizes the dissipation-only objective. -/
theorem dissipationOnlyCost_unique_minimizer
    {slotWeight capacityAggregate first second : ℝ}
    (hCapacity : 0 < capacityAggregate)
    (hFirst : 0 < first) (hSecond : 0 < second)
    (hFirstMin : IsMinOn (dissipationOnlyCost slotWeight capacityAggregate)
      (Set.Ioi 0) first)
    (hSecondMin : IsMinOn (dissipationOnlyCost slotWeight capacityAggregate)
      (Set.Ioi 0) second) :
    first = second := by
  have hFirstZero : dissipationOnlyMarginal slotWeight capacityAggregate
      first = 0 :=
    (hFirstMin.isLocalMin (Ioi_mem_nhds hFirst)).hasDerivAt_eq_zero
      (dissipationOnlyCost_hasDerivAt slotWeight capacityAggregate
        (ne_of_gt hFirst))
  have hSecondZero : dissipationOnlyMarginal slotWeight capacityAggregate
      second = 0 :=
    (hSecondMin.isLocalMin (Ioi_mem_nhds hSecond)).hasDerivAt_eq_zero
      (dissipationOnlyCost_hasDerivAt slotWeight capacityAggregate
        (ne_of_gt hSecond))
  exact (dissipationOnlyMarginal_strictMonoOn hCapacity).injOn hFirst hSecond
    (hFirstZero.trans hSecondZero.symm)

/-- At a cap solving the cubic, the smoothing concession equals the quadratic
racing term. -/
theorem concession_eq_quadratic_of_cubic
    {slotWeight capacityAggregate cap : ℝ} (hCap : 0 < cap)
    (hCubic : 4 * capacityAggregate * cap ^ 3 = slotWeight ^ 2) :
    slotWeight ^ 2 / 4 * cap⁻¹ = capacityAggregate * cap ^ 2 := by
  rw [← hCubic]
  field_simp

/-- **Remark `rem:optcert_cubic`, value identity.**  At the optimum the total
certified concession is three halves of the quadratic racing term. -/
theorem dissipationOnlyCost_eq_of_cubic
    {slotWeight capacityAggregate cap : ℝ} (hCap : 0 < cap)
    (hCubic : 4 * capacityAggregate * cap ^ 3 = slotWeight ^ 2) :
    dissipationOnlyCost slotWeight capacityAggregate cap =
      3 / 2 * (capacityAggregate * cap ^ 2) := by
  rw [dissipationOnlyCost, concession_eq_quadratic_of_cubic hCap hCubic]
  ring

end

end SmoothingCliff.Racing
