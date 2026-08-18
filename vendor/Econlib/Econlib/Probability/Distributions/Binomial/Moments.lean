/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Distributions.Bernoulli
public import Econlib.Probability.Distributions.Binomial.Basic

/-!
# Moments of the binomial distribution

This file proves expectation and variance formulas for the binomial distribution
`FinDist.binomial p hp hp1 n` on `Fin (n + 1)`.

## Main statements

* `FinDist.binomial_expect`: The expectation of the binomial distribution equals `n * p`.
* `FinDist.binomial_variance`: The variance of the binomial distribution equals `n * p * (1 - p)`.
* `FinDist.binomial_expect_one_eq_bernoulli`: The `n = 1` case agrees with the Bernoulli
  expectation.
* `FinDist.binomial_variance_one_eq_bernoulli`: The `n = 1` case agrees with the Bernoulli variance.

## Tags

probability, discrete distributions, binomial moments
-/

@[expose] public section

namespace Econlib.Probability

/-- The binomial weights `C(n,i) · p ^ i · (1 - p) ^ (n - i)` sum to `1`. -/
private lemma binomial_weight_sum (p : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i)) = 1 := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using (add_pow p (1 - p) n).symm

/-- For any weight function `g`,
`∑ C(n,i) p^i (1-p)^(n+1-i) g(i) = (1-p) * ∑ C(n,i) p^i (1-p)^(n-i) g(i)`. -/
private lemma binomial_one_minus_p_factor (p : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n + 1 - i) * g i) =
      (1 - p) * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * g i) := by
  rw [Finset.mul_sum]
  refine (Finset.sum_congr rfl fun i hi => ?_).symm
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hsub : n + 1 - i = n - i + 1 := by omega
  rw [hsub, pow_succ]
  ring

/-- The index-weighted binomial sum `∑ C(n,i) p^i (1-p)^(n-i) · i` equals `n · p`. -/
private lemma binomial_expect_sum (p : ℝ) :
    ∀ n : ℕ,
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ)) = (n : ℝ) * p
  | 0 => by simp
  | n + 1 => by
      have hsplit :=
        Finset.sum_choose_succ_mul (R := ℝ)
          (f := fun i j => p ^ i * (1 - p) ^ j * (i : ℝ)) n
      have hA := binomial_one_minus_p_factor p (fun i => (i : ℝ)) n
      have hB :
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) *
              (p ^ (i + 1) * (1 - p) ^ (n - i) * ((i + 1 : ℕ) : ℝ)) =
            p * ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * ((i : ℝ) + 1)) := by
            rw [Finset.mul_sum]
            symm
            apply Finset.sum_congr rfl
            intro i hi
            rw [pow_succ']
            norm_num
            ring
      have hPlusOne :
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * ((i : ℝ) + 1)) =
            ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ)) +
            ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i)) := by
            calc
              ∑ i ∈ Finset.range (n + 1),
                  (n.choose i : ℝ) *
                    (p ^ i * (1 - p) ^ (n - i) * ((i : ℝ) + 1))
                = ∑ i ∈ Finset.range (n + 1),
                    ((n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ)) +
                      (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i))) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
              _ = ∑ i ∈ Finset.range (n + 1),
                    (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ)) +
                    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i)) := by
                        rw [Finset.sum_add_distrib]
      have hPlusOneAffine :=
        congrArg (fun x : ℝ => (1 - p) * ((n : ℝ) * p) + p * x) hPlusOne
      calc
        ∑ i ∈ Finset.range (n + 2),
          ((n + 1).choose i : ℝ) * (p ^ i * (1 - p) ^ (n + 1 - i) * (i : ℝ))
          = ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n + 1 - i) * (i : ℝ)) +
              ∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) *
                  (p ^ (i + 1) * (1 - p) ^ (n - i) * ((i + 1 : ℕ) : ℝ)) := by
                simpa using hsplit
        _ = (1 - p) *
              ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ)) +
              p * ∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * ((i : ℝ) + 1)) := by
                rw [hA, hB]
        _ = (1 - p) * ((n : ℝ) * p) +
              p * (∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ)) +
                ∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i))) := by
                simpa [binomial_expect_sum p n] using hPlusOneAffine
        _ = (1 - p) * ((n : ℝ) * p) + p * ((n : ℝ) * p + 1) := by
                rw [binomial_expect_sum p n, binomial_weight_sum p n]
        _ = ((n + 1 : ℕ) : ℝ) * p := by
                norm_num [Nat.cast_add]
                ring

/-- The falling-factorial binomial sum `∑ C(n,i) p^i (1-p)^(n-i) · i · (i - 1)` equals
`n · (n - 1) · p ^ 2`. -/
private lemma binomial_factorial_second_sum (p : ℝ) :
    ∀ n : ℕ,
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) =
          (n : ℝ) * ((n - 1 : ℕ) : ℝ) * p ^ 2
  | 0 => by simp
  | n + 1 => by
      have hsplit :=
        Finset.sum_choose_succ_mul (R := ℝ)
          (f := fun i j => p ^ i * (1 - p) ^ j * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) n
      have hA :
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n + 1 - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) =
            (1 - p) *
              ∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) := by
            have h := binomial_one_minus_p_factor p (fun i => (i : ℝ) * ((i - 1 : ℕ) : ℝ)) n
            simpa only [mul_assoc] using h
      have hShift :
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) *
              (p ^ i * (1 - p) ^ (n - i) * ((i + 1 : ℕ) : ℝ) *
                ((i + 1 - 1 : ℕ) : ℝ)) =
            ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) +
            2 * ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ)) := by
            calc
              ∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) *
                  (p ^ i * (1 - p) ^ (n - i) * ((i + 1 : ℕ) : ℝ) *
                    ((i + 1 - 1 : ℕ) : ℝ))
                = ∑ i ∈ Finset.range (n + 1),
                    ((n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) +
                      2 * ((n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ)))) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        cases i <;> norm_num [pow_two]
                        ring
              _ = ∑ i ∈ Finset.range (n + 1),
                    (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) +
                  ∑ i ∈ Finset.range (n + 1),
                    2 * ((n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ))) := by
                        rw [Finset.sum_add_distrib]
              _ = ∑ i ∈ Finset.range (n + 1),
                    (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) +
                  2 * ∑ i ∈ Finset.range (n + 1),
                    (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ)) := by
                        rw [← Finset.mul_sum]
      have hB :
          ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) *
              (p ^ (i + 1) * (1 - p) ^ (n - i) * ((i + 1 : ℕ) : ℝ) *
                ((i + 1 - 1 : ℕ) : ℝ)) =
            p * (∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) +
                2 * ∑ i ∈ Finset.range (n + 1),
                  (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ))) := by
            calc
              ∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) *
                  (p ^ (i + 1) * (1 - p) ^ (n - i) * ((i + 1 : ℕ) : ℝ) *
                    ((i + 1 - 1 : ℕ) : ℝ))
                = p * ∑ i ∈ Finset.range (n + 1),
                    (n.choose i : ℝ) *
                      (p ^ i * (1 - p) ^ (n - i) * ((i + 1 : ℕ) : ℝ) *
                        ((i + 1 - 1 : ℕ) : ℝ)) := by
                        rw [Finset.mul_sum]
                        symm
                        apply Finset.sum_congr rfl
                        intro i hi
                        rw [pow_succ']
                        ring
              _ = p * (∑ i ∈ Finset.range (n + 1),
                    (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) +
                    2 * ∑ i ∈ Finset.range (n + 1),
                      (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ))) := by
                        rw [hShift]
      calc
        ∑ i ∈ Finset.range (n + 2),
          ((n + 1).choose i : ℝ) * (p ^ i * (1 - p) ^ (n + 1 - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ))
          = ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n + 1 - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) +
            ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) *
                (p ^ (i + 1) * (1 - p) ^ (n - i) * ((i + 1 : ℕ) : ℝ) * ((i + 1 - 1 : ℕ) : ℝ)) := by
                simpa using hsplit
        _ = (1 - p) *
              ∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) +
            p * (∑ i ∈ Finset.range (n + 1),
                (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) +
                2 * ∑ i ∈ Finset.range (n + 1),
                  (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ))) := by
                rw [hA, hB]
        _ = (1 - p) * ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * p ^ 2) +
            p * (((n : ℝ) * ((n - 1 : ℕ) : ℝ) * p ^ 2) + 2 * ((n : ℝ) * p)) := by
                rw [binomial_factorial_second_sum p n, binomial_expect_sum p n]
        _ = ((n + 1 : ℕ) : ℝ) * ((n + 1 - 1 : ℕ) : ℝ) * p ^ 2 := by
                cases n with
                | zero =>
                    norm_num
                | succ n =>
                    simp
                    ring

/-- The second-moment binomial sum `∑ C(n,i) p^i (1-p)^(n-i) · i ^ 2` equals
`n · (n - 1) · p ^ 2 + n · p`. -/
private lemma binomial_expect_sq_sum (p : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) ^ 2) =
        (n : ℝ) * ((n - 1 : ℕ) : ℝ) * p ^ 2 + (n : ℝ) * p := by
  rw [← binomial_factorial_second_sum p n, ← binomial_expect_sum p n]
  calc
    ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) ^ 2)
      = ∑ i ∈ Finset.range (n + 1),
          ((n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) +
            (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ))) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hi_sq : (i : ℝ) ^ 2 = (i : ℝ) * ((i - 1 : ℕ) : ℝ) + (i : ℝ) := by
                cases i <;> simp [pow_two]
                ring
              rw [hi_sq]
              ring
    _ = ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) * ((i - 1 : ℕ) : ℝ)) +
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ)) := by
              rw [Finset.sum_add_distrib]

/-- The expectation of the binomial distribution `Binomial(n, p)` equals `n * p`. -/
lemma FinDist.binomial_expect (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (FinDist.binomial p hp hp1 n).expect (fun i => (i : ℝ)) = (n : ℝ) * p := by
  rw [FinDist.expect_eq_sum]
  rw [Finset.sum_fin_eq_sum_range]
  calc
    ∑ i ∈ Finset.range (n + 1),
        (if h : i < n + 1 then
          (FinDist.binomial p hp hp1 n).pmf (Fin.mk i h) * (((Fin.mk i h : Fin (n + 1)) : ℝ))
         else 0)
      = ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hi' : i < n + 1 := Finset.mem_range.mp hi
            simp [hi', FinDist.binomial_apply, mul_left_comm, mul_comm]
    _ = (n : ℝ) * p := binomial_expect_sum p n

/-- The variance of the binomial distribution `Binomial(n, p)` equals `n * p * (1 - p)`. -/
lemma FinDist.binomial_variance (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (FinDist.binomial p hp hp1 n).variance (fun i => (i : ℝ)) = (n : ℝ) * p * (1 - p) := by
  rw [FinDist.variance, FinDist.binomial_expect p hp hp1 n]
  rw [FinDist.expect_eq_sum, Finset.sum_fin_eq_sum_range]
  calc
    ∑ i ∈ Finset.range (n + 1),
        (if h : i < n + 1 then
          (FinDist.binomial p hp hp1 n).pmf (Fin.mk i h) * ((((Fin.mk i h : Fin (n + 1)) : ℝ)) ^ 2)
         else 0) - ((n : ℝ) * p) ^ 2
      = ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * p ^ 2 + (n : ℝ) * p) - ((n : ℝ) * p) ^ 2 := by
          congr 1
          calc
            ∑ i ∈ Finset.range (n + 1),
                (if h : i < n + 1 then
                  (FinDist.binomial p hp hp1 n).pmf (Fin.mk i h) *
                    ((((Fin.mk i h : Fin (n + 1)) : ℝ)) ^ 2)
                 else 0)
              = ∑ i ∈ Finset.range (n + 1),
                  (n.choose i : ℝ) * (p ^ i * (1 - p) ^ (n - i) * (i : ℝ) ^ 2) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    have hi' : i < n + 1 := Finset.mem_range.mp hi
                    simp [hi', FinDist.binomial_apply, mul_left_comm, mul_comm]
            _ = (n : ℝ) * ((n - 1 : ℕ) : ℝ) * p ^ 2 + (n : ℝ) * p := binomial_expect_sq_sum p n
    _ = (n : ℝ) * p * (1 - p) := by
          cases n with
          | zero =>
              ring
          | succ n =>
              simp
              ring

/-- The expectation of `Binomial(1, p)` equals the expectation of `Bernoulli(p)`. -/
lemma FinDist.binomial_expect_one_eq_bernoulli (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (FinDist.binomial p hp hp1 1).expect (fun i => (i : ℝ)) =
      (FinDist.bernoulli p hp hp1).expect (fun i => (i : ℝ)) := by
  simpa [FinDist.bernoulli_expect] using FinDist.binomial_expect p hp hp1 1

/-- The variance of `Binomial(1, p)` equals the variance of `Bernoulli(p)`. -/
lemma FinDist.binomial_variance_one_eq_bernoulli (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (FinDist.binomial p hp hp1 1).variance (fun i => (i : ℝ)) =
      (FinDist.bernoulli p hp hp1).variance (fun i => (i : ℝ)) := by
  simpa [FinDist.bernoulli_variance] using FinDist.binomial_variance p hp hp1 1

end Econlib.Probability
