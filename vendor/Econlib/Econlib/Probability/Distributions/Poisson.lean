/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.CountDist.Basic
public import Econlib.Probability.CountDist.CDF
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Poisson distribution

This file defines Poisson distributions as countable distributions on natural numbers and proves
point-mass, expectation, and variance formulas.

## Main definitions

* `CountDist.poisson`: Poisson distribution with rate `rate`.

## Main statements

* `CountDist.poisson_apply`: Point-mass formula.
* `CountDist.poisson_cdf`: The CDF at `n` equals `exp (-rate) * ∑_{k ≤ n} rate ^ k / k!`.
* `CountDist.poisson_isMode_floor`: `⌊rate⌋₊` is a mode.
* `CountDist.poisson_expect`: Expectation equals `rate`.
* `CountDist.poisson_variance`: Variance equals `rate`.
* `CountDist.poisson_expect_zero`, `CountDist.poisson_variance_zero`: The degenerate case
  `rate = 0` has expectation and variance `0`.

## Tags

probability, discrete distributions, poisson
-/

@[expose] public section

namespace Econlib.Probability

open ProbabilityTheory

/-- Poisson distribution on `ℕ`. -/
noncomputable def CountDist.poisson (rate : ℝ) (hrate : 0 ≤ rate) : CountDist ℕ :=
  CountDist.ofPMF (poissonPMF ⟨rate, hrate⟩)

/-- The point-mass of the Poisson distribution at `n` equals `exp(-rate) * rate ^ n / n!`. -/
@[simp] lemma CountDist.poisson_apply (rate : ℝ) (hrate : 0 ≤ rate) (n : ℕ) :
    (CountDist.poisson rate hrate).pmf n = Real.exp (-rate) * rate ^ n / Nat.factorial n := by
  change (ENNReal.ofReal (poissonPMFReal ⟨rate, hrate⟩ n)).toReal =
      Real.exp (-rate) * rate ^ n / Nat.factorial n
  rw [ENNReal.toReal_ofReal poissonPMFReal_nonneg, poissonPMFReal]
  norm_num
  rfl

/-- Partial-sum CDF: The probability of at most `n` events is
`exp (-rate) * ∑_{k ≤ n} rate ^ k / k!` (no elementary closed form). -/
lemma CountDist.poisson_cdf (rate : ℝ) (hrate : 0 ≤ rate) (n : ℕ) :
    (CountDist.poisson rate hrate).cdf n =
      Real.exp (-rate) * ∑ k ∈ Finset.range (n + 1), rate ^ k / Nat.factorial k := by
  rw [CountDist.cdf_eq_sum_range, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [CountDist.poisson_apply]; ring

/-- Ratio recursion for the Poisson pmf: `pmf (n + 1) = pmf n * (rate / (n + 1))`. -/
private lemma poisson_pmf_succ (rate : ℝ) (hrate : 0 ≤ rate) (n : ℕ) :
    (CountDist.poisson rate hrate).pmf (n + 1) =
      (CountDist.poisson rate hrate).pmf n * (rate / (n + 1)) := by
  rw [CountDist.poisson_apply, CountDist.poisson_apply, Nat.factorial_succ]
  have hfac : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `⌊rate⌋₊` is a mode of the Poisson distribution: The pmf rises (weakly) up to the floor of the
rate and falls (weakly) beyond it, since the successive-mass ratio is `rate / (n + 1)`. -/
lemma CountDist.poisson_isMode_floor (rate : ℝ) (hrate : 0 ≤ rate) :
    (CountDist.poisson rate hrate).IsMode ⌊rate⌋₊ := by
  -- Up-step below the floor: `j + 1 ≤ rate` makes the ratio at least one.
  have hup : ∀ j : ℕ, ((j : ℝ) + 1) ≤ rate →
      (CountDist.poisson rate hrate).pmf j ≤ (CountDist.poisson rate hrate).pmf (j + 1) := by
    intro j hj
    rw [poisson_pmf_succ rate hrate j]
    have hone : (1 : ℝ) ≤ rate / ((j : ℝ) + 1) := (one_le_div (by positivity)).mpr hj
    calc (CountDist.poisson rate hrate).pmf j
        = (CountDist.poisson rate hrate).pmf j * 1 := (mul_one _).symm
      _ ≤ (CountDist.poisson rate hrate).pmf j * (rate / ((j : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hone ((CountDist.poisson rate hrate).nonneg j)
  -- Down-step above the floor: `rate ≤ j + 1` makes the ratio at most one.
  have hdown : ∀ j : ℕ, rate ≤ ((j : ℝ) + 1) →
      (CountDist.poisson rate hrate).pmf (j + 1) ≤ (CountDist.poisson rate hrate).pmf j := by
    intro j hj
    rw [poisson_pmf_succ rate hrate j]
    have hle : rate / ((j : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ hj (by positivity)
    calc (CountDist.poisson rate hrate).pmf j * (rate / ((j : ℝ) + 1))
        ≤ (CountDist.poisson rate hrate).pmf j * 1 :=
          mul_le_mul_of_nonneg_left hle ((CountDist.poisson rate hrate).nonneg j)
      _ = (CountDist.poisson rate hrate).pmf j := mul_one _
  intro k
  rcases le_or_gt k ⌊rate⌋₊ with hk | hk
  · -- Climb the up-steps from `k` to the floor.
    have hclimb : ∀ i : ℕ, k + i ≤ ⌊rate⌋₊ →
        (CountDist.poisson rate hrate).pmf k ≤ (CountDist.poisson rate hrate).pmf (k + i) := by
      intro i
      induction i with
      | zero => intro _; exact le_refl _
      | succ i ih =>
          intro h
          refine (ih (by omega)).trans ?_
          have hcast : ((k + i : ℕ) : ℝ) + 1 ≤ rate := by
            have hle : ((k + i + 1 : ℕ) : ℝ) ≤ (⌊rate⌋₊ : ℝ) :=
              Nat.cast_le.mpr (by omega : k + i + 1 ≤ ⌊rate⌋₊)
            have hfloor := Nat.floor_le hrate
            push_cast at hle ⊢
            linarith
          exact hup (k + i) hcast
    have := hclimb (⌊rate⌋₊ - k) (by omega)
    rwa [Nat.add_sub_cancel' hk] at this
  · -- Descend the down-steps from the floor to `k`.
    have hdesc : ∀ i : ℕ,
        (CountDist.poisson rate hrate).pmf (⌊rate⌋₊ + i) ≤
          (CountDist.poisson rate hrate).pmf ⌊rate⌋₊ := by
      intro i
      induction i with
      | zero => exact le_refl _
      | succ i ih =>
          refine le_trans ?_ ih
          have hcast : rate ≤ ((⌊rate⌋₊ + i : ℕ) : ℝ) + 1 := by
            have hlt := Nat.lt_floor_add_one rate
            push_cast
            push_cast at hlt
            linarith
          exact hdown (⌊rate⌋₊ + i) hcast
    have := hdesc (k - ⌊rate⌋₊)
    rwa [Nat.add_sub_cancel' hk.le] at this

/-- `Real.exp (-rate) * Real.exp rate = 1`. -/
private lemma exp_neg_mul_exp_self (rate : ℝ) : Real.exp (-rate) * Real.exp rate = 1 := by
  rw [← Real.exp_add]; simp

/-- The series `∑' n, rate ^ n / n!` equals `Real.exp rate`. -/
private lemma tsum_pow_div_factorial (rate : ℝ) :
    ∑' n : ℕ, rate ^ n / Nat.factorial n = Real.exp rate := by
  simpa [Real.exp_eq_exp_ℝ] using
    (show ∑' n : ℕ, rate ^ n / Nat.factorial n = NormedSpace.exp rate from
      (NormedSpace.expSeries_div_hasSum_exp rate).tsum_eq)

/-- Index-shift identity: `(n + 1) * rate ^ (n+1) / (n+1)! = rate * (rate ^ n / n!)`. -/
private lemma shift_nat_mul_pow_div_factorial (rate : ℝ) :
    (fun n : ℕ => (↑(n + 1) : ℝ) * rate ^ (n + 1) / Nat.factorial (n + 1)) =
      fun n : ℕ => rate * (rate ^ n / Nat.factorial n) := by
  funext n
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnp1 : (↑n + 1 : ℝ) ≠ 0 := by positivity
  simp [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hfac, hnp1]

/-- Index-shift identity: `(n+2) * (n+1) * rate ^ (n+2) / (n+2)! = rate ^ 2 * (rate ^ n / n!)`. -/
private lemma shift_poisson_factorial_second (rate : ℝ) :
    (fun n : ℕ => (↑(n + 2) * ((↑(n + 2) - 1 : ℕ) : ℝ)) * rate ^ (n + 2) /
        Nat.factorial (n + 2)) =
      fun n : ℕ => rate ^ 2 * (rate ^ n / Nat.factorial n) := by
  funext n
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hnp1 : (↑n + 1 : ℝ) ≠ 0 := by positivity
  have hnp2 : (↑n + 2 : ℝ) ≠ 0 := by positivity
  simp [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp [hfac, hnp1, hnp2]
  ring

/-- The series `n ↦ n · rate ^ n / n!` is summable. -/
private lemma summable_nat_mul_pow_div_factorial (rate : ℝ) :
    Summable (fun n : ℕ => (n : ℝ) * rate ^ n / Nat.factorial n) := by
  refine (summable_nat_add_iff 1).1 ?_
  rw [shift_nat_mul_pow_div_factorial]
  exact (Real.summable_pow_div_factorial rate).mul_left rate

/-- The series `n ↦ n · (n - 1) · rate ^ n / n!` is summable. -/
private lemma summable_poisson_factorial_second (rate : ℝ) :
    Summable (fun n : ℕ => ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) * rate ^ n / Nat.factorial n) := by
  refine (summable_nat_add_iff 2).1 ?_
  rw [shift_poisson_factorial_second]
  exact (Real.summable_pow_div_factorial rate).mul_left (rate ^ 2)

/-- The series `∑' n, n · rate ^ n / n!` equals `rate · exp rate`. -/
private lemma tsum_nat_mul_pow_div_factorial (rate : ℝ) :
    ∑' n : ℕ, (n : ℝ) * rate ^ n / Nat.factorial n = rate * Real.exp rate := by
  have hf := summable_nat_mul_pow_div_factorial rate
  calc
    ∑' n : ℕ, (n : ℝ) * rate ^ n / Nat.factorial n
      = ∑' n : ℕ, (↑(n + 1) : ℝ) * rate ^ (n + 1) / Nat.factorial (n + 1) := by
        simpa using hf.tsum_eq_zero_add
    _ = ∑' n : ℕ, rate * (rate ^ n / Nat.factorial n) := by
        rw [shift_nat_mul_pow_div_factorial]
    _ = rate * ∑' n : ℕ, rate ^ n / Nat.factorial n := by rw [tsum_mul_left]
    _ = rate * Real.exp rate := by rw [tsum_pow_div_factorial]

/-- The series `∑' n, n · (n - 1) · rate ^ n / n!` equals `rate ^ 2 · exp rate`. -/
private lemma tsum_poisson_factorial_second (rate : ℝ) :
    ∑' n : ℕ, ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) * rate ^ n / Nat.factorial n =
      rate ^ 2 * Real.exp rate := by
  have hf := summable_poisson_factorial_second rate
  have hsplit := hf.sum_add_tsum_nat_add 2
  have hzero : ∑ i ∈ Finset.range 2, ((i : ℝ) * ((i - 1 : ℕ) : ℝ)) * rate ^ i / Nat.factorial i
      = 0 := by simp [Finset.sum_range_succ]
  calc
    ∑' n : ℕ, ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) * rate ^ n / Nat.factorial n
      = ∑' n : ℕ, (↑(n + 2) * ((↑(n + 2) - 1 : ℕ) : ℝ)) * rate ^ (n + 2) /
          Nat.factorial (n + 2) := by simpa [hzero] using hsplit.symm
    _ = ∑' n : ℕ, rate ^ 2 * (rate ^ n / Nat.factorial n) := by
        rw [shift_poisson_factorial_second]
    _ = rate ^ 2 * ∑' n : ℕ, rate ^ n / Nat.factorial n := by rw [tsum_mul_left]
    _ = rate ^ 2 * Real.exp rate := by rw [tsum_pow_div_factorial]

/-- The second moment `𝔼[N²]` of `Poisson(rate)` equals `rate ^ 2 + rate`. -/
private lemma poisson_expect_sq (rate : ℝ) (hrate : 0 ≤ rate) :
    (CountDist.poisson rate hrate).expect (fun n => (n : ℝ) ^ 2) = rate ^ 2 + rate := by
  rw [CountDist.expect_eq_tsum]
  calc
    ∑' a : ℕ, (CountDist.poisson rate hrate).pmf a * (a : ℝ) ^ 2
      = ∑' n : ℕ, (Real.exp (-rate) * rate ^ n / Nat.factorial n) * (n : ℝ) ^ 2 := by
          congr with n
          rw [CountDist.poisson_apply]
    _ = ∑' n : ℕ, Real.exp (-rate) *
        (((n : ℝ) * ((n - 1 : ℕ) : ℝ) * rate ^ n / Nat.factorial n) +
          ((n : ℝ) * rate ^ n / Nat.factorial n)) := by
          congr with n
          have hn' : (n : ℝ) * (((n - 1 : ℕ) : ℝ)) = (n : ℝ) ^ 2 - (n : ℝ) := by
            cases n with
            | zero => norm_num
            | succ n =>
                simp [pow_two]
                ring
          rw [hn']
          ring
    _ = Real.exp (-rate) *
        ∑' n : ℕ, ((n : ℝ) * ((n - 1 : ℕ) : ℝ) * rate ^ n / Nat.factorial n +
          ((n : ℝ) * rate ^ n / Nat.factorial n)) := by
          rw [tsum_mul_left]
    _ = Real.exp (-rate) *
        (∑' n : ℕ, (n : ℝ) * ((n - 1 : ℕ) : ℝ) * rate ^ n / Nat.factorial n +
          ∑' n : ℕ, (n : ℝ) * rate ^ n / Nat.factorial n) := by
          rw [Summable.tsum_add
            (summable_poisson_factorial_second rate)
            (summable_nat_mul_pow_div_factorial rate)]
    _ = Real.exp (-rate) * (rate ^ 2 * Real.exp rate + rate * Real.exp rate) := by
          rw [tsum_poisson_factorial_second, tsum_nat_mul_pow_div_factorial]
    _ = rate ^ 2 + rate := by
          rw [show Real.exp (-rate) * (rate ^ 2 * Real.exp rate + rate * Real.exp rate)
            = Real.exp (-rate) * Real.exp rate * (rate ^ 2 + rate) from by ring,
            exp_neg_mul_exp_self, one_mul]

/-- The expectation of the identity function under `Poisson(rate)` equals `rate`. -/
lemma CountDist.poisson_expect (rate : ℝ) (hrate : 0 ≤ rate) :
    (CountDist.poisson rate hrate).expect (fun n => (n : ℝ)) = rate := by
  rw [CountDist.expect_eq_tsum]
  calc
    ∑' a : ℕ, (CountDist.poisson rate hrate).pmf a * (a : ℝ)
      = ∑' n : ℕ, (Real.exp (-rate) * rate ^ n / Nat.factorial n) * (n : ℝ) := by
          congr with n
          rw [CountDist.poisson_apply]
    _ = Real.exp (-rate) * ∑' n : ℕ, (n : ℝ) * rate ^ n / Nat.factorial n := by
          rw [← tsum_mul_left]
          congr with n
          ring
    _ = Real.exp (-rate) * (rate * Real.exp rate) := by
          rw [tsum_nat_mul_pow_div_factorial]
    _ = rate := by
          rw [show Real.exp (-rate) * (rate * Real.exp rate)
            = rate * (Real.exp (-rate) * Real.exp rate) from by ring,
            exp_neg_mul_exp_self, mul_one]

/-- The variance of the identity function under `Poisson(rate)` equals `rate`. -/
lemma CountDist.poisson_variance (rate : ℝ) (hrate : 0 ≤ rate) :
    (CountDist.poisson rate hrate).variance (fun n => (n : ℝ)) = rate := by
  rw [CountDist.variance, CountDist.poisson_expect rate hrate, poisson_expect_sq rate hrate]
  ring

/-- The expectation of the identity function under `Poisson(0)` is zero. -/
lemma CountDist.poisson_expect_zero :
    (CountDist.poisson 0 le_rfl).expect (fun n => (n : ℝ)) = 0 := by
  simpa using CountDist.poisson_expect 0 le_rfl

/-- The variance of the identity function under `Poisson(0)` is zero. -/
lemma CountDist.poisson_variance_zero :
    (CountDist.poisson 0 le_rfl).variance (fun n => (n : ℝ)) = 0 := by
  simpa using CountDist.poisson_variance 0 le_rfl

end Econlib.Probability
