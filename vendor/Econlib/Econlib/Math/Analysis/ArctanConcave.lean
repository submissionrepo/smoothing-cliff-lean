/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Concavity of `arctan` on the nonnegative reals

`Real.arctan` is concave on `[0, ∞)`, since its derivative `1/(1+x²)` is antitone there. The
statement is given on the maximal natural domain `Set.Ici 0`; consumers restrict to a subinterval
with `ConcaveOn.subset`.

## Main statements

* `Real.arctan_concaveOn_nonneg` — `arctan` is concave on `Set.Ici 0`.
* `Real.abs_arctan_le_pi_div_two` — `|arctan x| ≤ π/2` everywhere.

## Tags

arctan, concave, monotone derivative
-/

@[expose] public section

open Set

namespace Real

/-- `arctan` is concave on the nonnegative reals `[0, ∞)`: Its derivative `1/(1+x²)` is antitone
there. Restrict with `ConcaveOn.subset` to any subinterval of `[0, ∞)`. -/
lemma arctan_concaveOn_nonneg : ConcaveOn ℝ (Set.Ici (0:ℝ)) Real.arctan := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
      Real.continuous_arctan.continuousOn
      Real.differentiable_arctan.differentiableOn
  -- `deriv arctan x = 1/(1+x²)` is antitone on `(0, ∞)`: `x ↦ 1+x²` is increasing and positive.
  rw [interior_Ici]
  intro a ha b hb hab
  rw [Real.deriv_arctan]
  have ha0' : (0:ℝ) ≤ a := le_of_lt (mem_Ioi.mp ha)
  change 1 / (1 + b ^ 2) ≤ 1 / (1 + a ^ 2)
  have _hda : (0:ℝ) < 1 + a ^ 2 := by positivity
  gcongr

/-- The arctangent is bounded in magnitude by `π/2`: `|arctan x| ≤ π/2` for every `x`. Combines the
two-sided bounds `-(π/2) < arctan x < π/2`. -/
lemma abs_arctan_le_pi_div_two (x : ℝ) : |Real.arctan x| ≤ π / 2 :=
  abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan x).le, (Real.arctan_lt_pi_div_two x).le⟩

end Real
