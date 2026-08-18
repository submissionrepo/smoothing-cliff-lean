/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
import Econlib.Probability
import Mathlib

/-!
# Continuous Distribution Non-Vacuity Checks

These are compile-time semantic witnesses for continuous distribution constructors. They
instantiate the APIs at concrete legal parameters so that support, endpoint, mode, and moment
statements cannot silently drift away from their probabilistic reading.

Selected non-degenerate anchors are included to discriminate parameter-swap and off-center bugs
(e.g. Laplace off-mean CDF, logistic off-mean CDF, logNormal non-neutral input,
truncated-exponential interior CDF, truncated-exponential expectation at rate 2).
-/

noncomputable section

namespace EconlibTest.Probability.Distributions.Continuous

open Econlib.Probability

section beta

theorem beta_two_three_mean :
    (ContDist.beta 2 3 (by norm_num) (by norm_num)).expect id = 2 / 5 := by
  calc
    (ContDist.beta 2 3 (by norm_num) (by norm_num)).expect id = (2 : ℝ) / (2 + 3) := by
      simpa using ContDist.beta_expect 2 3 (by norm_num) (by norm_num)
    _ = 2 / 5 := by norm_num

theorem beta_two_three_variance :
    (ContDist.beta 2 3 (by norm_num) (by norm_num)).variance id = 1 / 25 := by
  calc
    (ContDist.beta 2 3 (by norm_num) (by norm_num)).variance id =
        (2 : ℝ) * 3 / ((2 + 3) ^ 2 * (2 + 3 + 1)) := by
          simpa using ContDist.beta_variance 2 3 (by norm_num) (by norm_num)
    _ = 1 / 25 := by norm_num

theorem beta_two_three_density_right_outside :
    (ContDist.beta 2 3 (by norm_num) (by norm_num)).density 2 = 0 := by
  simpa using
    ContDist.beta_density_eq_zero_of_not_mem 2 3 (by norm_num) (by norm_num) (x := 2)
      (by norm_num [Set.mem_Icc])

theorem betaWithMean_quarter_three_mean :
    (betaWithMean (1 / 4 : ℝ) 3 (by norm_num) (by norm_num) (by norm_num)).expect id =
      1 / 4 := by
  simpa using
    betaWithMean_expect (pi := (1 / 4 : ℝ)) (kappa := 3) (by norm_num) (by norm_num)
      (by norm_num)

theorem betaWithMean_quarter_three_variance :
    (betaWithMean (1 / 4 : ℝ) 3 (by norm_num) (by norm_num) (by norm_num)).variance id =
      3 / 64 := by
  calc
    (betaWithMean (1 / 4 : ℝ) 3 (by norm_num) (by norm_num) (by norm_num)).variance id =
        (1 / 4 : ℝ) * (1 - 1 / 4) / (3 + 1) := by
          simpa using
            betaWithMean_variance (pi := (1 / 4 : ℝ)) (kappa := 3) (by norm_num)
              (by norm_num) (by norm_num)
    _ = 3 / 64 := by norm_num

theorem betaWithMean_quarter_three_cdf_left_endpoint :
    (betaWithMean (1 / 4 : ℝ) 3 (by norm_num) (by norm_num) (by norm_num)).cdf 0 = 0 := by
  simpa using
    betaWithMean_cdf_zero (pi := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (κ := 3)
      (by norm_num) 0 (by norm_num)

theorem betaWithMean_quarter_three_cdf_right_endpoint :
    (betaWithMean (1 / 4 : ℝ) 3 (by norm_num) (by norm_num) (by norm_num)).cdf 1 = 1 := by
  simpa using
    betaWithMean_cdf_one (pi := (1 / 4 : ℝ)) (by norm_num) (by norm_num) (κ := 3)
      (by norm_num) 1 (by norm_num)

end beta

section exponential

theorem exponential_two_density_zero :
    (ContDist.exponential 2 (by norm_num)).density 0 = 2 := by
  rw [ContDist.exponential_density]
  have h := congrFun (density_eq_exponentialPDFReal 2) (0 : ℝ)
  rw [← h]
  norm_num [Real.exp_zero]

theorem exponential_two_density_left_outside :
    (ContDist.exponential 2 (by norm_num)).density (-1) = 0 := by
  simpa using
    ContDist.exponential_density_eq_zero_of_neg 2 (by norm_num) (x := -1) (by norm_num)

theorem exponential_two_cdf_zero :
    (ContDist.exponential 2 (by norm_num)).cdf 0 = 0 := by
  rw [ContDist.exponential_cdf]
  norm_num [Real.exp_zero]

theorem exponential_two_survival_one :
    1 - (ContDist.exponential 2 (by norm_num)).cdf 1 = Real.exp (-2) := by
  simpa using
    ContDist.exponential_survival 2 (by norm_num) 1 (by norm_num)

theorem exponential_two_mean :
    (ContDist.exponential 2 (by norm_num)).expect id = 1 / 2 := by
  simpa using ContDist.exponential_expect 2 (by norm_num)

theorem exponential_two_variance :
    (ContDist.exponential 2 (by norm_num)).variance id = 1 / 4 := by
  calc
    (ContDist.exponential 2 (by norm_num)).variance id = 1 / (2 : ℝ) ^ 2 := by
      simpa using ContDist.exponential_variance 2 (by norm_num)
    _ = 1 / 4 := by norm_num

theorem exponential_two_memoryless_one_three :
    let d := ContDist.exponential 2 (by norm_num)
    (1 - d.cdf (1 + 3)) / (1 - d.cdf 1) = 1 - d.cdf 3 := by
  simpa using
    ContDist.exponential_memoryless 2 (by norm_num) 1 3 (by norm_num) (by norm_num)

end exponential

section gamma

theorem gamma_two_four_density_left_outside :
    (ContDist.gamma 2 4 (by norm_num) (by norm_num)).density (-1) = 0 := by
  simpa using
    ContDist.gamma_density_eq_zero_of_neg 2 4 (by norm_num) (by norm_num) (x := -1)
      (by norm_num)

theorem gamma_two_four_mean :
    (ContDist.gamma 2 4 (by norm_num) (by norm_num)).expect id = 1 / 2 := by
  calc
    (ContDist.gamma 2 4 (by norm_num) (by norm_num)).expect id = (2 : ℝ) / 4 := by
      simpa using ContDist.gamma_expect 2 4 (by norm_num) (by norm_num)
    _ = 1 / 2 := by norm_num

theorem gamma_two_four_variance :
    (ContDist.gamma 2 4 (by norm_num) (by norm_num)).variance id = 1 / 8 := by
  calc
    (ContDist.gamma 2 4 (by norm_num) (by norm_num)).variance id = (2 : ℝ) / 4 ^ 2 := by
      simpa using ContDist.gamma_variance 2 4 (by norm_num) (by norm_num)
    _ = 1 / 8 := by norm_num

end gamma

section gaussian

theorem gaussian_three_four_mean :
    (ContDist.gaussian 3 4 (by norm_num)).expect id = 3 := by
  simpa using ContDist.gaussian_expect 3 4 (by norm_num)

theorem gaussian_three_four_variance :
    (ContDist.gaussian 3 4 (by norm_num)).variance id = 4 := by
  simpa using ContDist.gaussian_variance 3 4 (by norm_num)

theorem gaussian_three_four_mode :
    (ContDist.gaussian 3 4 (by norm_num)).IsMode 3 := by
  simpa using ContDist.gaussian_isMode_mean 3 4 (by norm_num)

theorem normal_alias_matches_gaussian_density :
    (ContDist.normal 3 4 (by norm_num)).density 5 =
      (ContDist.gaussian 3 4 (by norm_num)).density 5 := by
  rfl

theorem gaussian_variance_nnreal_coe_four :
    (gaussianVarianceNNReal 4 (by norm_num) : ℝ) = 4 := by
  rfl

end gaussian

section laplace

theorem laplace_one_two_cdf_at_mean :
    (ContDist.laplace 1 2 (by norm_num)).cdf 1 = 1 / 2 := by
  rw [ContDist.laplace_cdf]
  norm_num [Real.exp_zero]

/-- `Laplace(mean=1, scale=2)` has CDF `exp(-1)/2` at `x = -1` (left branch, off-mean).
Hand-computation: x = -1 ≤ mean = 1, so CDF(x) = exp((x - mean)/scale) / 2
= exp((-1 - 1)/2) / 2 = exp(-1) / 2.
This tests the left-branch formula at a non-zero non-mean point. -/
theorem laplace_one_two_cdf_left_off_mean :
    (ContDist.laplace 1 2 (by norm_num)).cdf (-1) = Real.exp (-1) / 2 := by
  rw [ContDist.laplace_cdf]
  norm_num

/-- `Laplace(mean=1, scale=2)` has CDF `1 - exp(-1)/2` at `x = 3` (right branch, off-mean).
Hand-computation: x = 3 > mean = 1, so CDF(x) = 1 - exp(-(x - mean)/scale) / 2
= 1 - exp(-(3 - 1)/2) / 2 = 1 - exp(-1) / 2.
This tests the right-branch formula at a non-zero non-mean point. -/
theorem laplace_one_two_cdf_right_off_mean :
    (ContDist.laplace 1 2 (by norm_num)).cdf 3 = 1 - Real.exp (-1) / 2 := by
  rw [ContDist.laplace_cdf]
  norm_num

theorem laplace_one_two_mean :
    (ContDist.laplace 1 2 (by norm_num)).expect id = 1 := by
  simpa using ContDist.laplace_expect 1 2 (by norm_num)

theorem laplace_one_two_variance :
    (ContDist.laplace 1 2 (by norm_num)).variance id = 8 := by
  calc
    (ContDist.laplace 1 2 (by norm_num)).variance id = 2 * (2 : ℝ) ^ 2 := by
      simpa using ContDist.laplace_variance 1 2 (by norm_num)
    _ = 8 := by norm_num

theorem laplace_one_two_mode :
    (ContDist.laplace 1 2 (by norm_num)).IsMode 1 := by
  simpa using ContDist.laplace_isMode_mean 1 2 (by norm_num)

end laplace

section logistic

theorem logistic_one_two_cdf_at_mean :
    (ContDist.logistic 1 2 (by norm_num)).cdf 1 = 1 / 2 := by
  rw [ContDist.logistic_cdf, logisticCDFReal]
  norm_num [Real.sigmoid_zero]

/-- `Logistic(mean=1, scale=2)` has CDF `sigmoid(1)` at `x = 3` (off-mean).
Hand-computation: CDF(3) = logisticCDFReal 1 2 3 = sigmoid((3 - 1)/2) = sigmoid(1).
This tests the formula away from the neutral point sigmoid(0) = 1/2. -/
theorem logistic_one_two_cdf_off_mean :
    (ContDist.logistic 1 2 (by norm_num)).cdf 3 = Real.sigmoid 1 := by
  rw [ContDist.logistic_cdf, logisticCDFReal]
  norm_num

theorem logistic_one_two_density_at_mean :
    (ContDist.logistic 1 2 (by norm_num)).density 1 = 1 / 8 := by
  rw [ContDist.logistic_density, logisticPDFReal]
  norm_num [Real.sigmoid_zero]

theorem logistic_one_two_mean :
    (ContDist.logistic 1 2 (by norm_num)).expect id = 1 := by
  simpa using ContDist.logistic_expect 1 2 (by norm_num)

theorem logistic_one_two_variance :
    (ContDist.logistic 1 2 (by norm_num)).variance id = 4 * Real.pi ^ 2 / 3 := by
  calc
    (ContDist.logistic 1 2 (by norm_num)).variance id =
        Real.pi ^ 2 / 3 * (2 : ℝ) ^ 2 := by
          simpa using ContDist.logistic_variance 1 2 (by norm_num)
    _ = 4 * Real.pi ^ 2 / 3 := by ring

theorem logistic_one_two_mode :
    (ContDist.logistic 1 2 (by norm_num)).IsMode 1 := by
  simpa using ContDist.logistic_isMode_mean 1 2 (by norm_num)

end logistic

section logNormal

theorem logNormal_zero_two_density_zero :
    (ContDist.logNormal 0 2 (by norm_num)).density 0 = 0 := by
  simpa using
    ContDist.logNormal_density_eq_zero_of_nonpos 0 2 (by norm_num) (x := 0) (by norm_num)

theorem logNormal_zero_two_cdf_zero :
    (ContDist.logNormal 0 2 (by norm_num)).cdf 0 = 0 := by
  simpa using
    ContDist.logNormal_cdf_of_nonpos 0 2 (by norm_num) (x := 0) (by norm_num)

theorem logNormal_zero_two_cdf_one_matches_gaussian_zero :
    (ContDist.logNormal 0 2 (by norm_num)).cdf 1 =
      (ContDist.gaussian 0 2 (by norm_num)).cdf 0 := by
  simpa [Real.log_one] using
    ContDist.logNormal_cdf_of_pos 0 2 (by norm_num) (x := 1) (by norm_num)

/-- `LogNormal(mean=0, variance=2)` at input `exp(1)` equals `Gaussian(0, 2)` at `1`.
Hand-computation: for x = e^1 > 0, logNormal CDF(e^1) = gaussianCDF(log(e^1)) = gaussianCDF(1).
This tests the bridge at a non-neutral point (log(e^1) = 1 ≠ 0), discriminating a
hardcoded-log-zero bug. -/
theorem logNormal_zero_two_cdf_exp_one_matches_gaussian_one :
    (ContDist.logNormal 0 2 (by norm_num)).cdf (Real.exp 1) =
      (ContDist.gaussian 0 2 (by norm_num)).cdf 1 := by
  simpa [Real.log_exp] using
    ContDist.logNormal_cdf_of_pos 0 2 (by norm_num) (x := Real.exp 1) (by positivity)

theorem logNormal_zero_two_mean :
    (ContDist.logNormal 0 2 (by norm_num)).expect id = Real.exp 1 := by
  calc
    (ContDist.logNormal 0 2 (by norm_num)).expect id = Real.exp (0 + (2 : ℝ) / 2) := by
      simpa using ContDist.logNormal_expect 0 2 (by norm_num)
    _ = Real.exp 1 := by norm_num

theorem logNormal_zero_two_variance :
    (ContDist.logNormal 0 2 (by norm_num)).variance id =
      (Real.exp 2 - 1) * Real.exp 2 := by
  calc
    (ContDist.logNormal 0 2 (by norm_num)).variance id =
        (Real.exp (2 : ℝ) - 1) * Real.exp (2 * 0 + 2) := by
          simpa using ContDist.logNormal_variance 0 2 (by norm_num)
    _ = (Real.exp 2 - 1) * Real.exp 2 := by ring_nf

end logNormal

section triangular

theorem triangular_zero_four_one_density_left_outside :
    (ContDist.triangular 0 4 1 (by norm_num) (by norm_num)).density (-1) = 0 := by
  simpa using
    ContDist.triangular_density_eq_zero_of_not_mem 0 4 1 (by norm_num) (by norm_num)
      (x := -1) (by norm_num [Set.mem_Icc])

theorem triangular_zero_four_one_mean :
    (ContDist.triangular 0 4 1 (by norm_num) (by norm_num)).expect id = 5 / 3 := by
  calc
    (ContDist.triangular 0 4 1 (by norm_num) (by norm_num)).expect id =
        ((0 : ℝ) + 4 + 1) / 3 := by
          simpa using ContDist.triangular_expect 0 4 1 (by norm_num) (by norm_num)
    _ = 5 / 3 := by norm_num

theorem triangular_zero_four_one_variance :
    (ContDist.triangular 0 4 1 (by norm_num) (by norm_num)).variance id = 13 / 18 := by
  calc
    (ContDist.triangular 0 4 1 (by norm_num) (by norm_num)).variance id =
        ((0 : ℝ) ^ 2 + 4 ^ 2 + 1 ^ 2 - 0 * 4 - 0 * 1 - 4 * 1) / 18 := by
          simpa using ContDist.triangular_variance 0 4 1 (by norm_num) (by norm_num)
    _ = 13 / 18 := by norm_num

theorem triangular_zero_four_one_mode :
    (ContDist.triangular 0 4 1 (by norm_num) (by norm_num)).IsMode 1 := by
  simpa using ContDist.triangular_isMode 0 4 1 (by norm_num) (by norm_num)

end triangular

section truncExponential

/-- `TruncExponential(0, 1, 2)` has expectation `1/2 - exp(-2) / (1 - exp(-2))`.
Hand-computation: mean = a + 1/rate - (b-a)·exp(-rate·(b-a)) / (1 - exp(-rate·(b-a)))
with a=0, b=1, rate=2: 0 + 1/2 - 1·exp(-2) / (1 - exp(-2)) = 1/2 - exp(-2)/(1 - exp(-2)).
This exercises the expectation formula at a non-degenerate interior case. -/
theorem truncExponential_zero_one_two_expect :
    (ContDist.truncExponential 0 1 2 (by norm_num) (by norm_num)).expect id =
      1 / 2 - Real.exp (-2) / (1 - Real.exp (-2)) := by
  calc (ContDist.truncExponential 0 1 2 (by norm_num) (by norm_num)).expect id
      = (0 : ℝ) + 1 / 2 -
          (1 - 0) * Real.exp (-2 * (1 - 0)) / (1 - Real.exp (-2 * (1 - 0))) := by
        simpa using ContDist.truncExponential_expect 0 1 2 (by norm_num) (by norm_num)
    _ = 1 / 2 - Real.exp (-2) / (1 - Real.exp (-2)) := by norm_num

theorem truncExponential_zero_one_two_density_right_outside :
    (ContDist.truncExponential 0 1 2 (by norm_num) (by norm_num)).density 2 = 0 := by
  simpa using
    ContDist.truncExponential_density_eq_zero_of_not_mem 0 1 2 (by norm_num) (by norm_num)
      (x := 2) (by norm_num [Set.mem_Icc])

theorem truncExponential_zero_one_two_cdf_left_endpoint :
    (ContDist.truncExponential 0 1 2 (by norm_num) (by norm_num)).cdf 0 = 0 := by
  rw [ContDist.truncExponential_cdf]
  norm_num [Real.exp_zero]

/-- `TruncExponential(0, 1, 2)` has CDF `(1 - exp(-1)) / (1 - exp(-2))` at `x = 1/2`.
Hand-computation: CDF formula for a ≤ x ≤ b:
  (1 - exp(-rate·(x - a))) / (1 - exp(-rate·(b - a)))
= (1 - exp(-2·(1/2 - 0))) / (1 - exp(-2·(1 - 0)))
= (1 - exp(-1)) / (1 - exp(-2)).
This tests the interior of the truncated support with a non-zero non-left numerator. -/
theorem truncExponential_zero_one_two_cdf_interior :
    (ContDist.truncExponential 0 1 2 (by norm_num) (by norm_num)).cdf (1 / 2) =
      (1 - Real.exp (-1)) / (1 - Real.exp (-2)) := by
  rw [ContDist.truncExponential_cdf]
  norm_num

theorem truncExponential_zero_one_two_cdf_right_outside :
    (ContDist.truncExponential 0 1 2 (by norm_num) (by norm_num)).cdf 2 = 1 := by
  rw [ContDist.truncExponential_cdf]
  norm_num

theorem truncExponential_zero_one_two_mode_left :
    (ContDist.truncExponential 0 1 2 (by norm_num) (by norm_num)).IsMode 0 := by
  simpa using ContDist.truncExponential_isMode_left 0 1 2 (by norm_num) (by norm_num)

end truncExponential

end EconlibTest.Probability.Distributions.Continuous

end
