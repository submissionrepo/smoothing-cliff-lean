/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.CountDist.Basic
public import Econlib.Probability.CountDist.CDF
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Probability.Distributions.Geometric

/-!
# Geometric distribution

This file defines geometric distributions as countable distributions on natural numbers and records
point-mass, expectation, and variance formulas.

## Main definitions

* `CountDist.geometric`: Geometric distribution with success probability `p`.

## Main statements

* `CountDist.geometric_apply`: Point-mass formula.
* `CountDist.geometric_cdf`: Closed-form CDF `1 - (1 - p) ^ (n + 1)`.
* `CountDist.geometric_isMode_zero`: The mode is `0`.
* `CountDist.geometric_expect`: Expectation formula `(1 - p) / p`.
* `CountDist.geometric_variance`: Variance formula `(1 - p) / p ^ 2`.
* `CountDist.geometric_expect_one`, `CountDist.geometric_variance_one`: The certain-success case
  `p = 1` has expectation and variance `0`.

## Tags

probability, discrete distributions, geometric
-/

@[expose] public section

namespace Econlib.Probability

open ProbabilityTheory

/-- Geometric distribution on `ℕ` with success probability `p ∈ (0, 1]`, counting the number of
failures before the first success. The point-mass at `n : ℕ` is `(1 - p) ^ n * p`. -/
noncomputable def CountDist.geometric (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) : CountDist ℕ :=
  CountDist.ofPMF (geometricPMF hp hp1)

/-- Point-mass formula: The probability of `n` failures before the first success is
`(1 - p) ^ n * p`. -/
@[simp] lemma CountDist.geometric_apply (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (n : ℕ) :
    (CountDist.geometric p hp hp1).pmf n = (1 - p) ^ n * p := by
  change (ENNReal.ofReal (geometricPMFReal p n)).toReal = (1 - p) ^ n * p
  rw [ENNReal.toReal_ofReal (geometricPMFReal_nonneg hp hp1), geometricPMFReal]

/-- Closed-form CDF: The probability of at most `n` failures before the first success is
`1 - (1 - p) ^ (n + 1)`. -/
lemma CountDist.geometric_cdf (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) (n : ℕ) :
    (CountDist.geometric p hp hp1).cdf n = 1 - (1 - p) ^ (n + 1) := by
  have h1p_ne : (1 : ℝ) - p ≠ 1 := fun h => hp.ne' (by linarith)
  rw [CountDist.cdf_eq_sum_range]
  simp only [CountDist.geometric_apply]
  rw [← Finset.sum_mul, geom_sum_eq h1p_ne]
  field_simp [hp.ne']
  ring

/-- `0` is a mode of the geometric distribution: The pmf `(1 - p)^n * p` is maximized at `0`. -/
lemma CountDist.geometric_isMode_zero (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (CountDist.geometric p hp hp1).IsMode 0 := by
  intro n
  rw [CountDist.geometric_apply, CountDist.geometric_apply]
  have hpow : (1 - p) ^ n ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  nlinarith

/-- The geometric ratio `1 - p` has norm below `1` whenever `0 < p ≤ 1`. -/
private lemma geometric_ratio_norm_lt_one (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ‖1 - p‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hp1)]
  linarith

/-- The series `n ↦ C(n,2) · r ^ n` is summable whenever `‖r‖ < 1`. -/
private lemma summable_choose_two_geometric {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => ((n.choose 2 : ℕ) : ℝ) * r ^ n) := by
  refine (summable_nat_add_iff 2).1 ?_
  convert (summable_choose_mul_geometric_of_norm_lt_one 2 hr).mul_left (r ^ 2) using 1 with n
  funext n
  rw [pow_add]
  ring

/-- The series `∑' n, C(n,2) · (1 - p) ^ n` sums to `(1 - p) ^ 2 / p ^ 3`. -/
private lemma tsum_geometric_choose_two (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∑' n : ℕ, ((n.choose 2 : ℕ) : ℝ) * (1 - p) ^ n = (1 - p) ^ 2 / p ^ 3 := by
  let r : ℝ := 1 - p
  have hr : ‖r‖ < 1 := by
    simpa [r] using geometric_ratio_norm_lt_one p hp hp1
  have hf : Summable (fun n : ℕ => ((n.choose 2 : ℕ) : ℝ) * r ^ n) :=
    summable_choose_two_geometric hr
  have hsplit := hf.sum_add_tsum_nat_add 2
  have hzero : ∑ i ∈ Finset.range 2, ((i.choose 2 : ℕ) : ℝ) * r ^ i = 0 := by
    simp [Finset.sum_range_succ]
  calc
    ∑' n : ℕ, ((n.choose 2 : ℕ) : ℝ) * (1 - p) ^ n
      = ∑' n : ℕ, ((((n + 2).choose 2 : ℕ) : ℝ) * r ^ (n + 2)) := by
          simpa [hzero, r] using hsplit.symm
    _ = ∑' n : ℕ, r ^ 2 * ((((n + 2).choose 2 : ℕ) : ℝ) * r ^ n) := by
          apply tsum_congr
          intro n
          simp [pow_add, mul_assoc, mul_comm]
    _ = r ^ 2 * ∑' n : ℕ, (((n + 2).choose 2 : ℕ) : ℝ) * r ^ n := by
          rw [tsum_mul_left]
    _ = r ^ 2 * (1 / (1 - r) ^ 3) := by
          rw [tsum_choose_mul_geometric_of_norm_lt_one 2 hr]
    _ = (1 - p) ^ 2 / p ^ 3 := by
          have hp_ne : p ≠ 0 := hp.ne'
          field_simp [r, hp_ne]
          ring

/-- The second moment of `CountDist.geometric p hp hp1` equals `(1 - p) * (2 - p) / p ^ 2`. -/
private lemma geometric_expect_sq (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (CountDist.geometric p hp hp1).expect (fun n => (n : ℝ) ^ 2) = (1 - p) * (2 - p) / p ^ 2 := by
  let r : ℝ := 1 - p
  have hr : ‖r‖ < 1 := by
    simpa [r] using geometric_ratio_norm_lt_one p hp hp1
  have hs_choose : Summable (fun n : ℕ => ((n.choose 2 : ℕ) : ℝ) * r ^ n) :=
    summable_choose_two_geometric hr
  have hs_linear : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  have hs_double_choose :
      Summable (fun n : ℕ => 2 * (((n.choose 2 : ℕ) : ℝ) * r ^ n)) :=
    hs_choose.mul_left 2
  have htsum_double_choose :
      ∑' n : ℕ, 2 * (((n.choose 2 : ℕ) : ℝ) * r ^ n) =
        2 * (∑' n : ℕ, ((n.choose 2 : ℕ) : ℝ) * r ^ n) := by
    simpa using
      (tsum_mul_left (a := (2 : ℝ))
        (f := fun n : ℕ => ((n.choose 2 : ℕ) : ℝ) * r ^ n))
  have hchoose_series :
      ∑' n : ℕ, ((n.choose 2 : ℕ) : ℝ) * r ^ n = r ^ 2 / p ^ 3 := by
    simpa [r] using tsum_geometric_choose_two p hp hp1
  rw [CountDist.expect_eq_tsum]
  calc
    ∑' a : ℕ, (CountDist.geometric p hp hp1).pmf a * (a : ℝ) ^ 2
      = ∑' n : ℕ, p * (((n : ℝ) ^ 2) * r ^ n) := by
          apply tsum_congr
          intro n
          rw [CountDist.geometric_apply]
          simp [r, mul_left_comm, mul_comm]
    _ = p * ∑' n : ℕ, ((n : ℝ) ^ 2) * r ^ n := by
          rw [tsum_mul_left]
    _ = p * (∑' n : ℕ, (2 * (((n.choose 2 : ℕ) : ℝ) * r ^ n) + (n : ℝ) * r ^ n)) := by
          congr 1
          apply tsum_congr
          intro n
          rw [Nat.cast_choose_two]
          ring
    _ = p * ((∑' n : ℕ, 2 * (((n.choose 2 : ℕ) : ℝ) * r ^ n)) + ∑' n : ℕ, (n : ℝ) * r ^ n) := by
          congr 1
          rw [Summable.tsum_add hs_double_choose hs_linear]
    _ = p * (2 * (r ^ 2 / p ^ 3) + r / p ^ 2) := by
          rw [htsum_double_choose, hchoose_series, tsum_coe_mul_geometric_of_norm_lt_one hr]
          ring
    _ = (1 - p) * (2 - p) / p ^ 2 := by
          have hp_ne : p ≠ 0 := hp.ne'
          field_simp [r, hp_ne]
          ring

/-- The expected value of `CountDist.geometric p hp hp1` is `(1 - p) / p`. -/
lemma CountDist.geometric_expect (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (CountDist.geometric p hp hp1).expect (fun n => (n : ℝ)) = (1 - p) / p := by
  let r : ℝ := 1 - p
  have hr : ‖r‖ < 1 := by
    simpa [r] using geometric_ratio_norm_lt_one p hp hp1
  rw [CountDist.expect_eq_tsum]
  calc
    ∑' a : ℕ, (CountDist.geometric p hp hp1).pmf a * (a : ℝ)
      = ∑' n : ℕ, p * ((n : ℝ) * r ^ n) := by
          apply tsum_congr
          intro n
          rw [CountDist.geometric_apply]
          simp [r, mul_left_comm, mul_comm]
    _ = p * ∑' n : ℕ, (n : ℝ) * r ^ n := by
          rw [tsum_mul_left]
    _ = p * (r / (1 - r) ^ 2) := by
          rw [tsum_coe_mul_geometric_of_norm_lt_one hr]
    _ = (1 - p) / p := by
          have hp_ne : p ≠ 0 := hp.ne'
          field_simp [r, hp_ne]
          ring

/-- The variance of `CountDist.geometric p hp hp1` is `(1 - p) / p ^ 2`. -/
lemma CountDist.geometric_variance (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    (CountDist.geometric p hp hp1).variance (fun n => (n : ℝ)) = (1 - p) / p ^ 2 := by
  rw [CountDist.variance, CountDist.geometric_expect p hp hp1, geometric_expect_sq p hp hp1]
  have hp_ne : p ≠ 0 := hp.ne'
  field_simp [hp_ne]
  ring

/-- The geometric distribution with `p = 1` (certain success) has expectation `0`. -/
lemma CountDist.geometric_expect_one :
    (CountDist.geometric 1 zero_lt_one le_rfl).expect (fun n => (n : ℝ)) = 0 := by
  simpa using CountDist.geometric_expect 1 zero_lt_one le_rfl

/-- The geometric distribution with `p = 1` (certain success) has variance `0`. -/
lemma CountDist.geometric_variance_one :
    (CountDist.geometric 1 zero_lt_one le_rfl).variance (fun n => (n : ℝ)) = 0 := by
  simpa using CountDist.geometric_variance 1 zero_lt_one le_rfl

end Econlib.Probability
