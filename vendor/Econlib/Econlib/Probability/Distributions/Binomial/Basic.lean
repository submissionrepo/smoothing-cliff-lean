/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.CDF
public import Econlib.Probability.FinDist.ProbDist
public import Mathlib.Probability.ProbabilityMassFunction.Binomial

/-!
# Binomial distribution

This file defines binomial distributions as finite distributions on `Fin (n + 1)` and records basic
point-mass formulas. The construction wraps `PMF.binomial` from Mathlib.

## Main definitions

* `FinDist.binomial`: Binomial distribution with `n` trials and success probability `p ∈ [0, 1]`.

## Main statements

* `FinDist.binomial_apply`: The point-mass at `i` equals `p ^ i * (1 - p) ^ (n - i) * C(n, i)`.
* `FinDist.binomial_apply_zero`: The probability of zero successes equals `(1 - p) ^ n`.
* `FinDist.binomial_apply_last`: The probability of `n` successes equals `p ^ n`.
* `FinDist.binomial_cdf`: The CDF at `k` equals `∑_{i=0}^{k} C(n,i) p^i (1-p)^(n-i)`.

## Tags

probability, discrete distributions, binomial
-/

@[expose] public section

namespace Econlib.Probability

/-- Binomial distribution with `n` trials and success probability `p ∈ [0, 1]`, as a
`FinDist (Fin (n + 1))`. The value at index `i` gives the probability of exactly `i` successes. -/
noncomputable def FinDist.binomial (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    FinDist (Fin (n + 1)) :=
  FinDist.ofPMF (PMF.binomial ⟨p, hp⟩ (by exact_mod_cast hp1) n)

/-- The point-mass of the binomial distribution at index `i` equals
`p ^ i * (1 - p) ^ (n - i) * n.choose i`. -/
lemma FinDist.binomial_apply (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (i : Fin (n + 1)) :
    (FinDist.binomial p hp hp1 n).pmf i =
      p ^ (i : ℕ) * (1 - p) ^ (i.rev : ℕ) * (n.choose i : ℕ) := by
  simp only [binomial, ofPMF, PMF.binomial, Fin.val_last, ENNReal.coe_mul, ENNReal.coe_pow,
    ENNReal.coe_sub, ENNReal.coe_one, ENNReal.coe_natCast, PMF.ofFintype_apply, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.coe_toReal, NNReal.coe_mk, ENNReal.toReal_natCast, Fin.val_rev,
    Nat.reduceSubDiff, mul_eq_mul_right_iff, mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq,
    Fin.val_eq_zero_iff, Nat.cast_eq_zero]
  left
  rw [ENNReal.toReal_sub_of_le (by exact_mod_cast hp1) ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, ENNReal.coe_toReal, NNReal.coe_mk]
  rfl

/-- The probability of zero successes in the binomial distribution equals `(1 - p) ^ n`. -/
@[simp] lemma FinDist.binomial_apply_zero (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (FinDist.binomial p hp hp1 n).pmf 0 = (1 - p) ^ n := by
  simp [FinDist.binomial_apply]

/-- The probability of `n` successes (all trials succeed) in the binomial distribution equals
`p ^ n`. -/
@[simp] lemma FinDist.binomial_apply_last (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (FinDist.binomial p hp hp1 n).pmf (Fin.last n) = p ^ n := by
  simp [FinDist.binomial_apply]

/-- Closed form for the binomial CDF: The probability of at most `k` successes equals
`∑_{i=0}^{k} C(n,i) p^i (1-p)^(n-i)`. -/
lemma FinDist.binomial_cdf (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) (k : Fin (n + 1)) :
    (FinDist.binomial p hp hp1 n).cdf k =
      ∑ i ∈ Finset.range ((k : ℕ) + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) := by
  refine FinDist.cdf_eq_sum_range _ (fun i => ?_) k
  rw [FinDist.binomial_apply p hp hp1 n i, Fin.val_rev]
  simp only [Nat.succ_sub_succ]
  ring

end Econlib.Probability
