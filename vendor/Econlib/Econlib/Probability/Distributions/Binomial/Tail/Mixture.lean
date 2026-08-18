/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Distributions.Binomial.Tail.Basic

/-!
# Mixtures of binomial tails

This file establishes two mixture identities for binomial tail probabilities: A convex-mixture
identity that replaces a weighted sum of `binomialTail` values with a single `binomialTail` at a
blended parameter, and a compound identity for two-stage Bernoulli trials.

## Main statements

* `binomialTail_mixture`: A weighted mixture of binomial tail probabilities equals a single
  binomial tail at the blended success probability `z + (1 - z) * q`.
* `binomialTail_compound`: A binomial mixture over the number of activated trials equals a single
  binomial tail at the compound success probability `σ * π`.

## Tags

probability, discrete distributions, binomial tails
-/

@[expose] public section

namespace Econlib.Probability

/-- **Binomial mixture identity:** A weighted sum of binomial tail probabilities, where the weights
are binomial coefficients for the "type" distribution `Bern(z)`, collapses to a single binomial
tail at the blended success probability `z + (1 - z) * q`.  Concretely,
`∑_{h=0}^n C(n,h) z^h (1-z)^{n-h} · BT(n-h, q, k-h) = BT(n, z+(1-z)q, k)`. -/
theorem binomialTail_mixture (n : ℕ) (z q : ℝ) (k : ℕ) :
    ∑ h ∈ Finset.range (n + 1),
      (n.choose h : ℝ) * z ^ h * (1 - z) ^ (n - h) *
        binomialTail (n - h) q (k - h) =
    binomialTail n (z + (1 - z) * q) k := by
  suffices hmain : ∀ k, ∑ h ∈ Finset.range (n + 1),
      (n.choose h : ℝ) * z ^ h * (1 - z) ^ (n - h) *
        binomialTail (n - h) q (k - h) =
      binomialTail n (z + (1 - z) * q) k from hmain k
  induction n with
  | zero =>
    intro k; cases k with
    | zero => simp [binomialTail_zero]
    | succ k =>
      have : binomialTail 0 (z + (1 - z) * q) (k + 1) = 0 := binomialTail_large 0 _ _ (by omega)
      have : binomialTail 0 q (k + 1) = 0 := binomialTail_large 0 _ _ (by omega)
      simp [*]
  | succ n ih =>
    intro k
    cases k with
    | zero =>
      simp
      simpa [mul_assoc, mul_left_comm, mul_comm] using (add_pow z (1 - z) (n + 1)).symm
    | succ k =>
      have hsplit := Finset.sum_choose_succ_mul (R := ℝ)
        (f := fun h j => z ^ h * (1 - z) ^ j * binomialTail j q (k + 1 - h)) n
      have hmatch : ∀ h ∈ Finset.range (n + 2),
          ((n + 1).choose h : ℝ) * z ^ h * (1 - z) ^ (n + 1 - h) *
            binomialTail (n + 1 - h) q (k + 1 - h) =
          ((n + 1).choose h : ℝ) *
            (fun a b => z ^ a * (1 - z) ^ b * binomialTail b q (k + 1 - a)) h (n + 1 - h) := by
        intro h _; simp; ring
      rw [Finset.sum_congr rfl hmatch, hsplit]; clear hmatch
      have hB : ∑ h ∈ Finset.range (n + 1),
          (n.choose h : ℝ) * (z ^ (h + 1) * (1 - z) ^ (n - h) *
            binomialTail (n - h) q (k + 1 - (h + 1))) =
          z * ∑ h ∈ Finset.range (n + 1),
            (n.choose h : ℝ) * z ^ h * (1 - z) ^ (n - h) *
              binomialTail (n - h) q (k - h) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro h _
        rw [show k + 1 - (h + 1) = k - h from by omega]
        rw [pow_succ']; ring
      rw [hB, ih k]; clear hB
      have hA_split : ∀ h ∈ Finset.range (n + 1),
          (n.choose h : ℝ) * (z ^ h * (1 - z) ^ (n + 1 - h) *
            binomialTail (n + 1 - h) q (k + 1 - h)) =
          (1 - z) * ((1 - q) * ((n.choose h : ℝ) * z ^ h * (1 - z) ^ (n - h) *
              binomialTail (n - h) q (k + 1 - h)) +
            q * ((n.choose h : ℝ) * z ^ h * (1 - z) ^ (n - h) *
              binomialTail (n - h) q (k - h))) := by
        intro h hh
        have hle : h ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
        have hsub1 : n + 1 - h = (n - h) + 1 := by omega
        rw [hsub1]
        by_cases hk : h ≤ k
        · rw [show k + 1 - h = (k - h) + 1 from by omega,
            binomialTail_succ_succ, pow_succ]; ring
        · rw [show k + 1 - h = 0 from by omega, show k - h = 0 from by omega,
            binomialTail_zero, binomialTail_zero]
          simp only [pow_succ]; ring
      rw [Finset.sum_congr rfl hA_split]
      simp_rw [show ∀ h, (1 - z) * ((1 - q) *
          ((n.choose h : ℝ) * z ^ h * (1 - z) ^ (n - h) *
            binomialTail (n - h) q (k + 1 - h)) +
        q * ((n.choose h : ℝ) * z ^ h * (1 - z) ^ (n - h) *
            binomialTail (n - h) q (k - h))) =
        (1 - z) * (1 - q) * ((n.choose h : ℝ) * z ^ h * (1 - z) ^ (n - h) *
            binomialTail (n - h) q (k + 1 - h)) +
        (1 - z) * q * ((n.choose h : ℝ) * z ^ h * (1 - z) ^ (n - h) *
            binomialTail (n - h) q (k - h)) from fun _ => by ring]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ih (k + 1), ih k]
      rw [binomialTail_succ_succ]
      ring

/-- **Compound Bernoulli identity:** If each of `n` trials independently succeeds via a two-stage
process — first "activate" with probability `σ`, then "succeed" with probability `π` — then the
tail probability of at least `k` total successes equals `binomialTail n (σ * π) k`.  Concretely,
`∑_{h=0}^n C(n,h) σ^h (1-σ)^{n-h} · BT(h, π, k) = BT(n, σπ, k)`. -/
theorem binomialTail_compound (n : ℕ) (σ π : ℝ) (k : ℕ) :
    ∑ h ∈ Finset.range (n + 1),
      (n.choose h : ℝ) * σ ^ h * (1 - σ) ^ (n - h) *
        binomialTail h π k =
    binomialTail n (σ * π) k := by
  suffices hmain : ∀ k, ∑ h ∈ Finset.range (n + 1),
      (n.choose h : ℝ) * σ ^ h * (1 - σ) ^ (n - h) *
        binomialTail h π k =
      binomialTail n (σ * π) k from hmain k
  induction n with
  | zero =>
    intro k; cases k with
    | zero => simp [binomialTail_zero]
    | succ k =>
      have : binomialTail 0 (σ * π) (k + 1) = 0 := binomialTail_large 0 _ _ (by omega)
      have : binomialTail 0 π (k + 1) = 0 := binomialTail_large 0 _ _ (by omega)
      simp [*]
  | succ n ih =>
    intro k; cases k with
    | zero =>
      simp only [binomialTail_zero, mul_one]
      simpa [mul_assoc, mul_left_comm, mul_comm] using (add_pow σ (1 - σ) (n + 1)).symm
    | succ k =>
      have hsplit := Finset.sum_choose_succ_mul (R := ℝ)
        (f := fun h j => σ ^ h * (1 - σ) ^ j * binomialTail h π (k + 1)) n
      have hmatch : ∀ h ∈ Finset.range (n + 2),
          ((n + 1).choose h : ℝ) * σ ^ h * (1 - σ) ^ (n + 1 - h) *
            binomialTail h π (k + 1) =
          ((n + 1).choose h : ℝ) *
            (fun a b => σ ^ a * (1 - σ) ^ b * binomialTail a π (k + 1)) h (n + 1 - h) := by
        intro h _; simp; ring
      rw [Finset.sum_congr rfl hmatch, hsplit]; clear hmatch
      have hB_split : ∀ h ∈ Finset.range (n + 1),
          (n.choose h : ℝ) * (σ ^ (h + 1) * (1 - σ) ^ (n - h) *
            binomialTail (h + 1) π (k + 1)) =
          σ * ((1 - π) * ((n.choose h : ℝ) * σ ^ h * (1 - σ) ^ (n - h) *
              binomialTail h π (k + 1)) +
            π * ((n.choose h : ℝ) * σ ^ h * (1 - σ) ^ (n - h) *
              binomialTail h π k)) := by
        intro h _
        rw [binomialTail_succ_succ, pow_succ']; ring
      have hA : ∑ h ∈ Finset.range (n + 1),
          (n.choose h : ℝ) * (σ ^ h * (1 - σ) ^ (n + 1 - h) *
            binomialTail h π (k + 1)) =
          (1 - σ) * ∑ h ∈ Finset.range (n + 1),
            (n.choose h : ℝ) * σ ^ h * (1 - σ) ^ (n - h) *
              binomialTail h π (k + 1) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro h hh
        have hle : h ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
        rw [show n + 1 - h = (n - h) + 1 from by omega, pow_succ]; ring
      rw [hA, ih (k + 1)]
      rw [Finset.sum_congr rfl hB_split]
      simp_rw [show ∀ h, σ * ((1 - π) *
          ((n.choose h : ℝ) * σ ^ h * (1 - σ) ^ (n - h) *
              binomialTail h π (k + 1)) +
            π * ((n.choose h : ℝ) * σ ^ h * (1 - σ) ^ (n - h) *
              binomialTail h π k)) =
        σ * (1 - π) * ((n.choose h : ℝ) * σ ^ h * (1 - σ) ^ (n - h) *
              binomialTail h π (k + 1)) +
        σ * π * ((n.choose h : ℝ) * σ ^ h * (1 - σ) ^ (n - h) *
              binomialTail h π k) from fun _ => by ring]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ih (k + 1), ih k]
      rw [binomialTail_succ_succ]
      ring

end Econlib.Probability
