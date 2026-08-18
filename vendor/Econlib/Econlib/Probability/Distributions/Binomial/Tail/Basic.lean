/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Distributions.Binomial.Moments

/-!
# Binomial tail probabilities

This file defines upper binomial tail probabilities and proves boundary and monotonicity facts in
the count threshold and success probability.

## Main definitions

* `binomialTail`: Upper binomial tail probability.

## Main statements

* `binomialTail_zero`: The tail probability at threshold 0 equals 1.
* `binomialTail_large`: The tail probability is 0 when the threshold exceeds `n`.
* `binomialTail_last`: The tail probability at the top threshold equals `p ^ n`.
* `binomialTail_nonneg`: Nonnegativity of the tail probability.
* `binomialTail_le_one`: The tail probability is at most 1.
* `binomialTail_anti_k`: The tail probability is antitone in the threshold.
* `FinDist.binomial_cdf_eq_one_sub_binomialTail`: Complement identity
  `Pr(X ≤ k) = 1 - Pr(X ≥ k + 1)` linking the binomial CDF and the upper tail.
* `binomialTail_succ_succ`: Pascal recursion for the tail probability.
* `binomialTail_mono_p`: The tail probability is monotone in the success probability.
* `binomialTail_strict_mono_p`: Strict monotonicity of the tail probability in the success
  probability.
* `continuous_binomialTail`: Continuity of the tail probability as a function of `p`.

## Tags

probability, discrete distributions, binomial tails
-/

@[expose] public section

namespace Econlib.Probability

/-- The upper binomial tail probability `Pr(Bin(n, p) ≥ k) = ∑_{i=k}^{n} C(n,i) p^i (1-p)^{n-i}`.
Defined for all `k : ℕ`; equals 1 when `k = 0` and 0 when `k > n`. -/
def binomialTail (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.filter (fun i => k ≤ i) (Finset.range (n + 1)),
    (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

/-- The tail probability at threshold 0 equals 1, i.e., `Pr(Bin(n, p) ≥ 0) = 1`. -/
@[simp] lemma binomialTail_zero (n : ℕ) (p : ℝ) :
    binomialTail n p 0 = 1 := by
  simp only [binomialTail, Nat.zero_le, Finset.filter_true_of_mem (fun _ _ => trivial)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using (add_pow p (1 - p) n).symm

/-- The tail probability is 0 when the threshold `k` exceeds `n`. -/
lemma binomialTail_large (n : ℕ) (p : ℝ) (k : ℕ) (hk : n < k) :
    binomialTail n p k = 0 := by
  simp only [binomialTail]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  omega

/-- The tail probability at the top threshold equals `p ^ n`, i.e., `Pr(Bin(n, p) ≥ n) = p ^ n`. -/
lemma binomialTail_last (n : ℕ) (p : ℝ) :
    binomialTail n p n = p ^ n := by
  simp only [binomialTail]
  have : Finset.filter (fun i => n ≤ i) (Finset.range (n + 1)) = {n} := by
    ext i; simp [Finset.mem_filter, Finset.mem_range]; omega
  rw [this, Finset.sum_singleton]; simp

private lemma binomialTail_term_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n i : ℕ) :
    0 ≤ (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _)) (pow_nonneg (by linarith) _)

/-- The tail probability is nonneg when `0 ≤ p ≤ 1`. -/
lemma binomialTail_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n k : ℕ) :
    0 ≤ binomialTail n p k :=
  Finset.sum_nonneg fun i _ => binomialTail_term_nonneg hp hp1 n i

/-- The tail probability is at most 1 when `0 ≤ p ≤ 1`. -/
lemma binomialTail_le_one {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n k : ℕ) :
    binomialTail n p k ≤ 1 := by
  rw [← binomialTail_zero n p]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i; simp [Finset.mem_filter, Finset.mem_range]; omega
  · intro i _ _; exact binomialTail_term_nonneg hp hp1 n i

/-- Complement identity: The binomial CDF at `k` and the upper tail at `k + 1` partition the unit
mass, `Pr(X ≤ k) = 1 - Pr(X ≥ k + 1)`. -/
lemma FinDist.binomial_cdf_eq_one_sub_binomialTail (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (k : Fin (n + 1)) :
    (FinDist.binomial p hp hp1 n).cdf k = 1 - binomialTail n p ((k : ℕ) + 1) := by
  -- Split the full mass over `range (n + 1)` at the threshold `k`.
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (n + 1))
    (fun i => (k : ℕ) + 1 ≤ i) (fun i => (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i))
  have hnot : (Finset.range (n + 1)).filter (fun i => ¬ ((k : ℕ) + 1 ≤ i)) =
      Finset.range ((k : ℕ) + 1) := by
    have hk := k.isLt
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, not_le]
    omega
  have hfull : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) = 1 := by
    have h0 := binomialTail_zero n p
    unfold binomialTail at h0
    rwa [Finset.filter_true_of_mem fun i _ => Nat.zero_le i] at h0
  have htail : binomialTail n p ((k : ℕ) + 1) =
      ∑ i ∈ (Finset.range (n + 1)).filter (fun i => (k : ℕ) + 1 ≤ i),
        (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) := rfl
  rw [hnot] at hsplit
  rw [FinDist.binomial_cdf p hp hp1 n k, htail]
  linarith [hsplit, hfull]

/-- The tail probability is antitone in the threshold: `k₁ ≤ k₂` implies
`binomialTail n p k₂ ≤ binomialTail n p k₁`. -/
lemma binomialTail_anti_k {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) {k₁ k₂ : ℕ}
    (hk : k₁ ≤ k₂) :
    binomialTail n p k₂ ≤ binomialTail n p k₁ := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i; simp [Finset.mem_filter, Finset.mem_range]; omega
  · intro i _ _; exact binomialTail_term_nonneg hp hp1 n i

/-- Pascal recursion for the upper binomial tail:
`Pr(Bin(n+1, p) ≥ k+1) = (1-p) · Pr(Bin(n, p) ≥ k+1) + p · Pr(Bin(n, p) ≥ k)`. -/
lemma binomialTail_succ_succ (n : ℕ) (p : ℝ) (k : ℕ) :
    binomialTail (n + 1) p (k + 1) =
      (1 - p) * binomialTail n p (k + 1) + p * binomialTail n p k := by
  have to_ite : ∀ m q j, binomialTail m q j =
      ∑ i ∈ Finset.range (m + 1),
        (if j ≤ i then (m.choose i : ℝ) * q ^ i * (1 - q) ^ (m - i) else 0) := by
    intro m q j; simp only [binomialTail, Finset.sum_filter]
  rw [to_ite (n + 1) p (k + 1), to_ite n p (k + 1), to_ite n p k]
  -- Apply Pascal's identity via sum_choose_succ_mul, then factor out p and (1-p) from each half.
  have hsplit := Finset.sum_choose_succ_mul (R := ℝ)
    (f := fun i j => if k + 1 ≤ i then p ^ i * (1 - p) ^ j else 0) n
  have hLHS_eq : ∑ i ∈ Finset.range (n + 1 + 1),
      (if k + 1 ≤ i then ((n + 1).choose i : ℝ) * p ^ i * (1 - p) ^ (n + 1 - i) else 0) =
      ∑ i ∈ Finset.range (n + 2),
        ((n + 1).choose i : ℝ) * (if k + 1 ≤ i then p ^ i * (1 - p) ^ (n + 1 - i) else 0) := by
    apply Finset.sum_congr rfl; intro i _; split_ifs <;> ring
  rw [hLHS_eq]; clear hLHS_eq
  have hrewrite : ∑ i ∈ Finset.range (n + 2),
      ((n + 1).choose i : ℝ) * (if k + 1 ≤ i then p ^ i * (1 - p) ^ (n + 1 - i) else 0) =
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (if k + 1 ≤ i then p ^ i * (1 - p) ^ (n + 1 - i) else 0) +
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (if k + 1 ≤ i + 1 then p ^ (i + 1) * (1 - p) ^ (n - i) else 0) := by
    simpa using hsplit
  rw [hrewrite]; clear hrewrite
  have hA : ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (if k + 1 ≤ i then p ^ i * (1 - p) ^ (n + 1 - i) else 0) =
      (1 - p) * ∑ i ∈ Finset.range (n + 1),
        (if k + 1 ≤ i then (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) else 0) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
    have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    split_ifs with h
    · have : n + 1 - i = (n - i) + 1 := by omega
      rw [this, pow_succ]; ring
    · ring
  have hB : ∑ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * (if k + 1 ≤ i + 1 then p ^ (i + 1) * (1 - p) ^ (n - i) else 0) =
      p * ∑ i ∈ Finset.range (n + 1),
        (if k ≤ i then (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) else 0) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    by_cases h : k ≤ i
    · rw [if_pos (show k + 1 ≤ i + 1 from by omega), if_pos h, pow_succ']; ring
    · rw [if_neg (show ¬(k + 1 ≤ i + 1) from by omega), if_neg h]; ring
  rw [hA, hB]

/-- The tail probability is monotone in the success probability: If `p₁ ≤ p₂` then
`Pr(Bin(n, p₁) ≥ k) ≤ Pr(Bin(n, p₂) ≥ k)`. -/
theorem binomialTail_mono_p {p₁ p₂ : ℝ} (hp₁ : 0 ≤ p₁) (hp₁₂ : p₁ ≤ p₂) (hp₂ : p₂ ≤ 1)
    (n k : ℕ) :
    binomialTail n p₁ k ≤ binomialTail n p₂ k := by
  suffices h : ∀ k, binomialTail n p₁ k ≤ binomialTail n p₂ k from h k
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => simp
    | succ k => simp [binomialTail_large 0 _ (k + 1) (by omega)]
  | succ n ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [binomialTail_succ_succ, binomialTail_succ_succ]
      have hIH_k1 := ih (k + 1)
      have hIH_k := ih k
      have hmono_k := binomialTail_anti_k hp₁ (le_trans hp₁₂ hp₂) n (Nat.le_succ k)
      nlinarith

/-- The difference of consecutive tails equals the k-th binomial PMF term:
`Pr(Bin(n,p) ≥ k) - Pr(Bin(n,p) ≥ k+1) = C(n,k) p^k (1-p)^(n-k)`. -/
private lemma binomialTail_diff_succ (n k : ℕ) (p : ℝ) (hk : k ≤ n) :
    binomialTail n p k - binomialTail n p (k + 1) =
      (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) := by
  simp only [binomialTail]
  rw [show Finset.filter (fun i => k ≤ i) (Finset.range (n + 1)) =
    insert k (Finset.filter (fun i => k + 1 ≤ i) (Finset.range (n + 1))) from by
    ext i; simp [Finset.mem_filter, Finset.mem_range]; omega]
  rw [Finset.sum_insert (by simp [Finset.mem_filter, Finset.mem_range])]
  ring

/-- The tail probability is strictly increasing in the success probability: When `1 ≤ k ≤ n` and
`p₁ < p₂`, we have `Pr(Bin(n, p₁) ≥ k) < Pr(Bin(n, p₂) ≥ k)`. -/
theorem binomialTail_strict_mono_p {p₁ p₂ : ℝ} (hp₁ : 0 ≤ p₁) (hp₁₂ : p₁ < p₂) (hp₂ : p₂ ≤ 1)
    {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    binomialTail n p₁ k < binomialTail n p₂ k := by
  have hp₂_nn : 0 ≤ p₂ := le_trans hp₁ (le_of_lt hp₁₂)
  have hp₁_lt₁ : p₁ < 1 := lt_of_lt_of_le hp₁₂ hp₂
  revert k
  induction n with
  | zero => intro k hk1 hk0; omega
  | succ n ih =>
    intro k hk1 hkn
    by_cases hk_top : k = n + 1
    · -- Top case: binomialTail n+1 p (n+1) = p^{n+1}, which is strictly monotone.
      subst hk_top; rw [binomialTail_last, binomialTail_last]
      exact pow_lt_pow_left₀ hp₁₂ hp₁ (by omega)
    · have hkn' : k ≤ n := by omega
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      rw [binomialTail_succ_succ, binomialTail_succ_succ]
      have hΔ_k1 : binomialTail n p₁ (k' + 1) ≤ binomialTail n p₂ (k' + 1) :=
        binomialTail_mono_p hp₁ (le_of_lt hp₁₂) hp₂ n (k' + 1)
      have hΔ_k : binomialTail n p₁ k' ≤ binomialTail n p₂ k' :=
        binomialTail_mono_p hp₁ (le_of_lt hp₁₂) hp₂ n k'
      have h_mono_k : binomialTail n p₁ (k' + 1) ≤ binomialTail n p₁ k' :=
        binomialTail_anti_k hp₁ (le_trans (le_of_lt hp₁₂) hp₂) n (Nat.le_succ k')
      -- The difference decomposes as T1 + T2 + T3, all nonneg, with at least one strictly positive:
      -- T1 = (1-p₂)(BT(n,p₂,k'+1) - BT(n,p₁,k'+1)), T2 = p₂(BT(n,p₂,k') - BT(n,p₁,k')),
      -- T3 = (p₂-p₁)(BT(n,p₁,k') - BT(n,p₁,k'+1)).
      have h1p₂ : 0 ≤ 1 - p₂ := by linarith
      have hdp : 0 < p₂ - p₁ := by linarith
      have hT1 : 0 ≤ (1 - p₂) * (binomialTail n p₂ (k' + 1) - binomialTail n p₁ (k' + 1)) :=
        mul_nonneg h1p₂ (by linarith [hΔ_k1])
      have hT2 : 0 ≤ p₂ * (binomialTail n p₂ k' - binomialTail n p₁ k') :=
        mul_nonneg hp₂_nn (by linarith [hΔ_k])
      have hT3 : 0 ≤ (p₂ - p₁) * (binomialTail n p₁ k' - binomialTail n p₁ (k' + 1)) :=
        mul_nonneg (le_of_lt hdp) (by linarith [h_mono_k])
      have hstrict : 0 < (1 - p₂) * (binomialTail n p₂ (k' + 1) - binomialTail n p₁ (k' + 1)) +
          p₂ * (binomialTail n p₂ k' - binomialTail n p₁ k') +
          (p₂ - p₁) * (binomialTail n p₁ k' - binomialTail n p₁ (k' + 1)) := by
        by_cases hp₂_lt₁ : p₂ < 1
        · -- p₂ < 1: T1 is strict by induction hypothesis.
          have hih := @ih (k' + 1) (by omega) (by omega)
          have : 0 < (1 - p₂) * (binomialTail n p₂ (k' + 1) - binomialTail n p₁ (k' + 1)) :=
            mul_pos (by linarith) (by linarith)
          linarith
        · -- p₂ = 1
          have hp₂_eq : p₂ = 1 := le_antisymm hp₂ (by linarith)
          by_cases hk'_pos : 1 ≤ k'
          · -- k' ≥ 1: T2 is strict by induction hypothesis.
            have hih := @ih k' hk'_pos (by omega)
            have : 0 < p₂ * (binomialTail n p₂ k' - binomialTail n p₁ k') :=
              mul_pos (by linarith) (by linarith)
            linarith
          · -- k' = 0, p₂ = 1: T3 is strict since BT(n,p₁,0) - BT(n,p₁,1) = (1-p₁)^n > 0.
            have hk'_eq : k' = 0 := by omega
            subst hk'_eq
            have hdiff := binomialTail_diff_succ n 0 p₁ (by omega)
            simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul,
              Nat.sub_zero] at hdiff
            have h_diff_pos : 0 < binomialTail n p₁ 0 - binomialTail n p₁ (0 + 1) := by
              rw [hdiff]; exact pow_pos (by linarith) n
            linarith [mul_pos hdp h_diff_pos]
      nlinarith

/-- The tail probability `binomialTail n · k` is continuous as a function of the success
probability `p`, as it is a finite sum of continuous polynomial terms. -/
lemma continuous_binomialTail (n k : ℕ) : Continuous (fun p => binomialTail n p k) := by
  unfold binomialTail
  apply continuous_finset_sum
  intro i _
  apply Continuous.mul
  · apply Continuous.mul
    · exact continuous_const
    · exact continuous_pow i
  · exact (continuous_const.sub continuous_id).pow _

end Econlib.Probability
