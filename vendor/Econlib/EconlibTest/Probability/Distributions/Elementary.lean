/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# Elementary Distribution Non-Vacuity Checks

These are compile-time semantic witnesses for the elementary distribution constructors. They use
concrete legal parameters to check that masses, moments, modes, support, and CDF endpoints line up
with the economic/probabilistic reading of each API theorem.
-/

noncomputable section

namespace EconlibTest.Probability.Distributions.Elementary

open Econlib.Probability

section bernoulli

theorem bernoulli_three_four_mass_success :
    (FinDist.bernoulli (3 / 4 : ℝ) (by norm_num) (by norm_num)).pmf 1 = 3 / 4 := by
  simpa using
    FinDist.bernoulli_apply_one (3 / 4 : ℝ) (by norm_num) (by norm_num)

theorem bernoulli_three_four_mass_failure :
    (FinDist.bernoulli (3 / 4 : ℝ) (by norm_num) (by norm_num)).pmf 0 = 1 / 4 := by
  calc
    (FinDist.bernoulli (3 / 4 : ℝ) (by norm_num) (by norm_num)).pmf 0
        = 1 - (3 / 4 : ℝ) := by
          simpa using
            FinDist.bernoulli_apply_zero (3 / 4 : ℝ) (by norm_num) (by norm_num)
    _ = 1 / 4 := by norm_num

theorem bernoulli_three_four_mean :
    ((FinDist.bernoulli (3 / 4 : ℝ) (by norm_num) (by norm_num)).expect
      fun i : Fin 2 => (i : ℝ)) = 3 / 4 := by
  simpa using
    FinDist.bernoulli_expect (3 / 4 : ℝ) (by norm_num) (by norm_num)

theorem bernoulli_three_four_variance :
    ((FinDist.bernoulli (3 / 4 : ℝ) (by norm_num) (by norm_num)).variance
      fun i : Fin 2 => (i : ℝ)) = 3 / 16 := by
  calc
    ((FinDist.bernoulli (3 / 4 : ℝ) (by norm_num) (by norm_num)).variance
        fun i : Fin 2 => (i : ℝ))
        = (3 / 4 : ℝ) * (1 - 3 / 4) := by
          simpa using
            FinDist.bernoulli_variance (3 / 4 : ℝ) (by norm_num) (by norm_num)
    _ = 3 / 16 := by norm_num

theorem bernoulli_half_has_both_modes :
    (FinDist.bernoulli (1 / 2 : ℝ) (by norm_num) (by norm_num)).IsMode 0 ∧
      (FinDist.bernoulli (1 / 2 : ℝ) (by norm_num) (by norm_num)).IsMode 1 := by
  constructor
  · simpa using
      FinDist.bernoulli_isMode_zero (1 / 2 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  · simpa using
      FinDist.bernoulli_isMode_one (1 / 2 : ℝ) (by norm_num) (by norm_num) (by norm_num)

/-- For `p = 1/4 < 1/2`, outcome `0` is a mode of `Bernoulli(1/4)` (failure is more probable).
Hand-computation: pmf(0) = 1 - 1/4 = 3/4 > 1/4 = pmf(1), so 0 is the unique mode. -/
theorem bernoulli_quarter_zero_is_mode :
    (FinDist.bernoulli (1 / 4 : ℝ) (by norm_num) (by norm_num)).IsMode 0 := by
  simpa using
    FinDist.bernoulli_isMode_zero (1 / 4 : ℝ) (by norm_num) (by norm_num) (by norm_num)

/-- For `p = 3/4 ≥ 1/2`, outcome `1` is a mode of `Bernoulli(3/4)` (success is more probable).
Hand-computation: pmf(1) = 3/4 > 1/4 = pmf(0), so 1 is the unique mode. -/
theorem bernoulli_three_quarter_one_is_mode :
    (FinDist.bernoulli (3 / 4 : ℝ) (by norm_num) (by norm_num)).IsMode 1 := by
  simpa using
    FinDist.bernoulli_isMode_one (3 / 4 : ℝ) (by norm_num) (by norm_num) (by norm_num)

theorem bernoulli_three_four_support_univ :
    (FinDist.bernoulli (3 / 4 : ℝ) (by norm_num) (by norm_num)).support = Finset.univ := by
  simpa using
    FinDist.bernoulli_support_univ (3 / 4 : ℝ) (by norm_num) (by norm_num)

end bernoulli

section binomial

theorem binomial_two_quarter_mass_zero :
    (FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 2).pmf 0 = 9 / 16 := by
  calc
    (FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 2).pmf 0
        = (1 - (1 / 4 : ℝ)) ^ 2 := by
          rw [FinDist.binomial_apply_zero]
    _ = 9 / 16 := by norm_num

theorem binomial_two_quarter_mass_all_successes :
    (FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 2).pmf (Fin.last 2) =
      1 / 16 := by
  calc
    (FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 2).pmf (Fin.last 2)
        = (1 / 4 : ℝ) ^ 2 := by
          simpa using
            FinDist.binomial_apply_last (1 / 4 : ℝ) (by norm_num) (by norm_num) 2
    _ = 1 / 16 := by norm_num

theorem binomial_two_quarter_cdf_one :
    (FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 2).cdf (1 : Fin 3) =
      15 / 16 := by
  rw [FinDist.binomial_cdf]
  norm_num [Finset.sum_range_succ]

theorem binomial_two_quarter_mean :
    ((FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 2).expect
      fun i : Fin (2 + 1) => (i : ℝ)) = 1 / 2 := by
  calc
    ((FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 2).expect
        fun i : Fin (2 + 1) => (i : ℝ))
        = (2 : ℝ) * (1 / 4) := by
          simpa using
            FinDist.binomial_expect (1 / 4 : ℝ) (by norm_num) (by norm_num) 2
    _ = 1 / 2 := by norm_num

theorem binomial_two_quarter_variance :
    ((FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 2).variance
      fun i : Fin (2 + 1) => (i : ℝ)) = 3 / 8 := by
  calc
    ((FinDist.binomial (1 / 4 : ℝ) (by norm_num) (by norm_num) 2).variance
        fun i : Fin (2 + 1) => (i : ℝ))
        = (2 : ℝ) * (1 / 4) * (1 - 1 / 4) := by
          simpa using
            FinDist.binomial_variance (1 / 4 : ℝ) (by norm_num) (by norm_num) 2
    _ = 3 / 8 := by norm_num

theorem binomial_one_matches_bernoulli_mean :
    ((FinDist.binomial (3 / 4 : ℝ) (by norm_num) (by norm_num) 1).expect
      fun i : Fin (1 + 1) => (i : ℝ)) =
        (FinDist.bernoulli (3 / 4 : ℝ) (by norm_num) (by norm_num)).expect
          fun i : Fin 2 => (i : ℝ) := by
  simpa using
    FinDist.binomial_expect_one_eq_bernoulli (3 / 4 : ℝ) (by norm_num) (by norm_num)

/-- `Binomial(1, 3/4)` has mean `3/4`.
Hand-computation: mean = n · p = 1 · (3/4) = 3/4. This discriminates a `(b - a) / 2` width bug
that would produce 3/8 instead of 3/4. -/
theorem binomial_one_three_quarter_mean :
    ((FinDist.binomial (3 / 4 : ℝ) (by norm_num) (by norm_num) 1).expect
      fun i : Fin (1 + 1) => (i : ℝ)) = 3 / 4 := by
  calc ((FinDist.binomial (3 / 4 : ℝ) (by norm_num) (by norm_num) 1).expect
          fun i : Fin (1 + 1) => (i : ℝ))
      = (1 : ℝ) * (3 / 4) := by
        simpa using FinDist.binomial_expect (3 / 4 : ℝ) (by norm_num) (by norm_num) 1
    _ = 3 / 4 := by norm_num

end binomial

section geometric

theorem geometric_half_mass_two :
    (CountDist.geometric (1 / 2 : ℝ) (by norm_num) (by norm_num)).pmf 2 = 1 / 8 := by
  calc
    (CountDist.geometric (1 / 2 : ℝ) (by norm_num) (by norm_num)).pmf 2
        = (1 - (1 / 2 : ℝ)) ^ 2 * (1 / 2) := by
          rw [CountDist.geometric_apply]
    _ = 1 / 8 := by norm_num

theorem geometric_half_cdf_two :
    (CountDist.geometric (1 / 2 : ℝ) (by norm_num) (by norm_num)).cdf 2 = 7 / 8 := by
  calc
    (CountDist.geometric (1 / 2 : ℝ) (by norm_num) (by norm_num)).cdf 2
        = 1 - (1 - (1 / 2 : ℝ)) ^ (2 + 1) := by
          simpa using
            CountDist.geometric_cdf (1 / 2 : ℝ) (by norm_num) (by norm_num) 2
    _ = 7 / 8 := by norm_num

theorem geometric_half_mean :
    ((CountDist.geometric (1 / 2 : ℝ) (by norm_num) (by norm_num)).expect
      fun n : ℕ => (n : ℝ)) = 1 := by
  calc
    ((CountDist.geometric (1 / 2 : ℝ) (by norm_num) (by norm_num)).expect
        fun n : ℕ => (n : ℝ))
        = (1 - (1 / 2 : ℝ)) / (1 / 2) := by
          simpa using
            CountDist.geometric_expect (1 / 2 : ℝ) (by norm_num) (by norm_num)
    _ = 1 := by norm_num

theorem geometric_half_variance :
    ((CountDist.geometric (1 / 2 : ℝ) (by norm_num) (by norm_num)).variance
      fun n : ℕ => (n : ℝ)) = 2 := by
  calc
    ((CountDist.geometric (1 / 2 : ℝ) (by norm_num) (by norm_num)).variance
        fun n : ℕ => (n : ℝ))
        = (1 - (1 / 2 : ℝ)) / (1 / 2) ^ 2 := by
          simpa using
            CountDist.geometric_variance (1 / 2 : ℝ) (by norm_num) (by norm_num)
    _ = 2 := by norm_num

-- Asymmetric anchors at p = 1/3 (success probability), convention: pmf(n) = (1-p)^n * p.
-- This breaks the p = 1/2 symmetry p ↔ 1 - p and catches sign/parameter-swap bugs.

/-- `Geometric(1/3)` assigns mass `4/27` to `n = 2`.
Hand-computation: pmf(2) = (1 - 1/3)^2 · (1/3) = (2/3)^2 · (1/3) = (4/9) · (1/3) = 4/27. -/
theorem geometric_third_mass_two :
    (CountDist.geometric (1 / 3 : ℝ) (by norm_num) (by norm_num)).pmf 2 = 4 / 27 := by
  calc (CountDist.geometric (1 / 3 : ℝ) (by norm_num) (by norm_num)).pmf 2
      = (1 - (1 / 3 : ℝ)) ^ 2 * (1 / 3) := by rw [CountDist.geometric_apply]
    _ = 4 / 27 := by norm_num

/-- `Geometric(1/3)` has CDF `19/27` at `n = 2`.
Hand-computation: CDF(2) = 1 - (1 - 1/3)^(2+1) = 1 - (2/3)^3 = 1 - 8/27 = 19/27. -/
theorem geometric_third_cdf_two :
    (CountDist.geometric (1 / 3 : ℝ) (by norm_num) (by norm_num)).cdf 2 = 19 / 27 := by
  calc (CountDist.geometric (1 / 3 : ℝ) (by norm_num) (by norm_num)).cdf 2
      = 1 - (1 - (1 / 3 : ℝ)) ^ (2 + 1) := by
        simpa using CountDist.geometric_cdf (1 / 3 : ℝ) (by norm_num) (by norm_num) 2
    _ = 19 / 27 := by norm_num

/-- `Geometric(1/3)` has mean `2`.
Hand-computation: mean = (1 - p) / p = (2/3) / (1/3) = 2. -/
theorem geometric_third_mean :
    ((CountDist.geometric (1 / 3 : ℝ) (by norm_num) (by norm_num)).expect
      fun n : ℕ => (n : ℝ)) = 2 := by
  calc ((CountDist.geometric (1 / 3 : ℝ) (by norm_num) (by norm_num)).expect
          fun n : ℕ => (n : ℝ))
      = (1 - (1 / 3 : ℝ)) / (1 / 3) := by
        simpa using CountDist.geometric_expect (1 / 3 : ℝ) (by norm_num) (by norm_num)
    _ = 2 := by norm_num

/-- `Geometric(1/3)` has variance `6`.
Hand-computation: variance = (1 - p) / p^2 = (2/3) / (1/9) = (2/3) · 9 = 6. -/
theorem geometric_third_variance :
    ((CountDist.geometric (1 / 3 : ℝ) (by norm_num) (by norm_num)).variance
      fun n : ℕ => (n : ℝ)) = 6 := by
  calc ((CountDist.geometric (1 / 3 : ℝ) (by norm_num) (by norm_num)).variance
          fun n : ℕ => (n : ℝ))
      = (1 - (1 / 3 : ℝ)) / (1 / 3) ^ 2 := by
        simpa using CountDist.geometric_variance (1 / 3 : ℝ) (by norm_num) (by norm_num)
    _ = 6 := by norm_num

end geometric

section poisson

theorem poisson_zero_mass_zero :
    (CountDist.poisson 0 (by norm_num)).pmf 0 = 1 := by
  rw [CountDist.poisson_apply]
  norm_num [Real.exp_zero]

theorem poisson_two_mean :
    ((CountDist.poisson 2 (by norm_num)).expect fun n : ℕ => (n : ℝ)) = 2 := by
  simpa using CountDist.poisson_expect 2 (by norm_num)

theorem poisson_two_variance :
    ((CountDist.poisson 2 (by norm_num)).variance fun n : ℕ => (n : ℝ)) = 2 := by
  simpa using CountDist.poisson_variance 2 (by norm_num)

theorem poisson_two_floor_mode :
    (CountDist.poisson 2 (by norm_num)).IsMode 2 := by
  simpa using CountDist.poisson_isMode_floor 2 (by norm_num)

/-- `Poisson(5/2)` has mode `2` (floor of 5/2).
Hand-computation: ⌊5/2⌋₊ = ⌊2.5⌋₊ = 2.  This exercises `poisson_isMode_floor` at a
non-integer rate, discriminating an off-by-one bug that would return 3. -/
theorem poisson_five_halves_floor_mode :
    (CountDist.poisson (5 / 2 : ℝ) (by norm_num)).IsMode 2 := by
  have : ⌊(5 / 2 : ℝ)⌋₊ = 2 := by norm_num
  simpa [this] using CountDist.poisson_isMode_floor (5 / 2 : ℝ) (by norm_num)

theorem poisson_two_mass_one :
    (CountDist.poisson 2 (by norm_num)).pmf 1 = 2 * Real.exp (-2) := by
  rw [CountDist.poisson_apply]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one]
  ring

theorem poisson_zero_cdf_three :
    (CountDist.poisson 0 (by norm_num)).cdf 3 = 1 := by
  rw [CountDist.poisson_cdf]
  norm_num [Finset.sum_range_succ]

/-- `Poisson(2)` has pmf `exp(-2)` at `0` and `2·exp(-2)` at `1`.
Hand-computation: pmf(0) = e^{-2} · 2^0 / 0! = e^{-2}; pmf(1) = e^{-2} · 2^1 / 1! = 2e^{-2}.
This tests a nonzero-rate mass at a non-symmetric point, discriminating a zero-rate collapse bug. -/
theorem poisson_two_mass_zero :
    (CountDist.poisson 2 (by norm_num)).pmf 0 = Real.exp (-2) := by
  rw [CountDist.poisson_apply]
  simp

/-- `Poisson(2)` has CDF `3·exp(-2)` at `n = 1`.
Hand-computation: CDF(1) = e^{-2} · (2^0/0! + 2^1/1!) = e^{-2} · (1 + 2) = 3·e^{-2}. -/
theorem poisson_two_cdf_one :
    (CountDist.poisson 2 (by norm_num)).cdf 1 = 3 * Real.exp (-2) := by
  rw [CountDist.poisson_cdf]
  norm_num [Finset.sum_range_succ, mul_comm]

end poisson

section uniform

theorem uniform_zero_two_density_midpoint :
    (ContDist.uniform 0 2 (by norm_num)).density 1 = 1 / 2 := by
  rw [ContDist.uniform_density]
  norm_num

theorem uniform_zero_two_density_left_outside :
    (ContDist.uniform 0 2 (by norm_num)).density (-1) = 0 := by
  rw [ContDist.uniform_density_eq_zero_of_not_mem]
  norm_num

theorem uniform_zero_two_cdf_left :
    (ContDist.uniform 0 2 (by norm_num)).cdf (-1) = 0 := by
  rw [ContDist.uniform_cdf]
  norm_num

theorem uniform_zero_two_cdf_midpoint :
    (ContDist.uniform 0 2 (by norm_num)).cdf 1 = 1 / 2 := by
  rw [ContDist.uniform_cdf]
  norm_num

/-- `Uniform[0,2]` has CDF `1/4` at `x = 1/2` (off-center, non-midpoint).
Hand-computation: CDF(1/2) = (1/2 - 0) / (2 - 0) = (1/2) / 2 = 1/4.
This discriminates a (a + b)/2-indexed formula that would evaluate to 1/2 instead. -/
theorem uniform_zero_two_cdf_quarter :
    (ContDist.uniform 0 2 (by norm_num)).cdf (1 / 2) = 1 / 4 := by
  rw [ContDist.uniform_cdf]
  norm_num

theorem uniform_zero_two_cdf_right :
    (ContDist.uniform 0 2 (by norm_num)).cdf 3 = 1 := by
  rw [ContDist.uniform_cdf]
  norm_num

theorem uniform_zero_two_mean :
    (ContDist.uniform 0 2 (by norm_num)).expect id = 1 := by
  calc
    (ContDist.uniform 0 2 (by norm_num)).expect id = ((0 : ℝ) + 2) / 2 := by
      simpa using ContDist.uniform_expect 0 2 (by norm_num)
    _ = 1 := by norm_num

/-- `Uniform[1, 3]` has mean `2` (shifted interval, non-zero left endpoint).
Hand-computation: mean = (a + b) / 2 = (1 + 3) / 2 = 2.
This catches a `(b - a) / 2`-width-only formula that would give 1 instead of 2. -/
theorem uniform_one_three_mean :
    (ContDist.uniform 1 3 (by norm_num)).expect id = 2 := by
  calc
    (ContDist.uniform 1 3 (by norm_num)).expect id = ((1 : ℝ) + 3) / 2 := by
      simpa using ContDist.uniform_expect 1 3 (by norm_num)
    _ = 2 := by norm_num

theorem uniform_zero_two_variance :
    (ContDist.uniform 0 2 (by norm_num)).variance id = 1 / 3 := by
  calc
    (ContDist.uniform 0 2 (by norm_num)).variance id = ((2 : ℝ) - 0) ^ 2 / 12 := by
      simpa using ContDist.uniform_variance 0 2 (by norm_num)
    _ = 1 / 3 := by norm_num

theorem uniform_zero_two_stopLoss_midpoint :
    (ContDist.uniform 0 2 (by norm_num)).toMeasure.stopLoss 1 = 1 / 4 := by
  calc
    (ContDist.uniform 0 2 (by norm_num)).toMeasure.stopLoss 1 =
        ((2 : ℝ) - 1) ^ 2 / (2 * (2 - 0)) := by
          simpa using
            ContDist.uniform_stopLoss 0 2 (by norm_num) (z := 1) (by norm_num)
    _ = 1 / 4 := by norm_num

/-- `Uniform[0, 2]` has stop-loss `9/16` at threshold `s = 1/2` (off-center, non-midpoint).
Hand-computation: stopLoss(s) = (b - s)^2 / (2(b - a)) at s ∈ [a, b];
at s = 1/2, a = 0, b = 2: (2 - 1/2)^2 / (2 · 2) = (3/2)^2 / 4 = (9/4) / 4 = 9/16.
This catches a formula that mis-uses the midpoint instead of the threshold. -/
theorem uniform_zero_two_stopLoss_quarter :
    (ContDist.uniform 0 2 (by norm_num)).toMeasure.stopLoss (1 / 2) = 9 / 16 := by
  calc
    (ContDist.uniform 0 2 (by norm_num)).toMeasure.stopLoss (1 / 2) =
        ((2 : ℝ) - 1 / 2) ^ 2 / (2 * (2 - 0)) := by
          simpa using
            ContDist.uniform_stopLoss 0 2 (by norm_num) (z := 1 / 2) (by norm_num)
    _ = 9 / 16 := by norm_num

theorem uniform_zero_two_midpoint_mode :
    (ContDist.uniform 0 2 (by norm_num)).IsMode 1 := by
  simpa using
    ContDist.uniform_isMode 0 2 (by norm_num) (c := 1) (by norm_num)

end uniform

end EconlibTest.Probability.Distributions.Elementary

end
