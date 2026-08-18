/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

/-!
# Set integral and interval integral bridges

Set integrals (`∫ x in Icc a b, f x`) and interval integrals (`∫ x in a..b, f x`) coincide for
`a ≤ b`. This lemma converts between the two forms.

## Main statements

* `MeasureTheory.setIntegral_Icc_eq_intervalIntegral` — `∫ x in Icc a b, f x = ∫ x in a..b, f x`
  for `a ≤ b`.

## Tags

integral, interval integral, set integral
-/

namespace MeasureTheory

/-- `∫ x in Icc a b, f x = ∫ x in a..b, f x` when `a ≤ b`. -/
public theorem setIntegral_Icc_eq_intervalIntegral {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Icc a b, f x = ∫ x in a..b, f x := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]

end MeasureTheory
