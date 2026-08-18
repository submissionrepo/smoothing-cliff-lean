/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Gamma ↔ ascending Pochhammer identities

This file proves algebraic identities relating the Γ-function to the ascending Pochhammer
polynomial `ascPochhammer ℝ n`, together with the two-variable Chu-Vandermonde identity. The
contents are pure analysis and combinatorial algebra and do not depend on a distribution carrier.

## Main statements

* `Real.Gamma_ratio_eq_ascPochhammer` — `Γ(α+n)/Γ(α) = ascPochhammer ℝ n` evaluated at `α > 0`.
* `chu_vandermonde_two` — `∑_{(j,k) ∈ antidiagonal n} C(n,j)·(a)↑ʲ·(b)↑ᵏ = (a+b)↑ⁿ`.

## Tags

gamma function, pochhammer, ascending pochhammer, chu-vandermonde
-/

@[expose] public section

namespace Real

/-- `Γ(α + n) / Γ(α) = ascPochhammer ℝ n evaluated at α`, for `α > 0`. -/
lemma Gamma_ratio_eq_ascPochhammer (α : ℝ) (hα : 0 < α) (n : ℕ) :
    Real.Gamma (α + n) / Real.Gamma α =
      Polynomial.eval α (ascPochhammer ℝ n) := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, add_zero, ascPochhammer_zero, Polynomial.eval_one,
      div_self (ne_of_gt (Real.Gamma_pos_of_pos hα))]
  | succ n ih =>
    rw [Nat.cast_succ, ← add_assoc]
    have hαn_pos : 0 < α + ↑n := by positivity
    have hαn_ne : α + ↑n ≠ 0 := ne_of_gt hαn_pos
    rw [Real.Gamma_add_one hαn_ne, mul_div_assoc, ih, ascPochhammer_succ_eval, mul_comm]

end Real

/-- Two-variable Chu–Vandermonde identity for ascending Pochhammer symbols:
`∑_{(j,k) ∈ antidiagonal n} C(n,j) · (a)↑ʲ · (b)↑ᵏ = (a+b)↑ⁿ`. This is the ascending-Pochhammer
counterpart of Mathlib's `descPochhammer_smeval_add`, which states the same identity for the
descending Pochhammer polynomial. -/
lemma chu_vandermonde_two (a b : ℝ) (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
      (Nat.choose n p.1 : ℝ) *
        Polynomial.eval a (ascPochhammer ℝ p.1) *
        Polynomial.eval b (ascPochhammer ℝ p.2) =
      Polynomial.eval (a + b) (ascPochhammer ℝ n) := by
  induction n with
  | zero =>
    simp [Finset.antidiagonal_zero, ascPochhammer_zero, Polynomial.eval_one]
  | succ n ih =>
    set P := fun (j : ℕ) => Polynomial.eval a (ascPochhammer ℝ j) with hP_def
    set Q := fun (k : ℕ) => Polynomial.eval b (ascPochhammer ℝ k) with hQ_def
    rw [ascPochhammer_succ_eval, ← ih, Finset.sum_mul]
    have hRHS_eq : ∀ p ∈ Finset.antidiagonal n,
        (↑(n.choose p.1) * P p.1 * Q p.2) * (a + b + ↑n) =
        ↑(n.choose p.1) * P (p.1 + 1) * Q p.2 +
        ↑(n.choose p.1) * P p.1 * Q (p.2 + 1) := by
      intro p hp
      have hjk := Finset.mem_antidiagonal.mp hp
      simp only [hP_def, hQ_def, ascPochhammer_succ_eval]
      have : (a + b + (n : ℝ)) = (a + (p.1 : ℝ)) + (b + (p.2 : ℝ)) := by
        push_cast [← hjk]; ring
      rw [this]; ring
    rw [Finset.sum_congr rfl hRHS_eq, Finset.sum_add_distrib, Finset.Nat.sum_antidiagonal_succ]
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, ascPochhammer_zero,
      Polynomial.eval_one, hP_def, hQ_def]
    simp_rw [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
    set M := ∑ p ∈ Finset.antidiagonal (n + 1),
        ↑(n.choose p.1) * P p.1 * Q p.2
    have lhs_eq : M = Q (n + 1) +
        ∑ p ∈ Finset.antidiagonal n,
          ↑(n.choose (p.1 + 1)) * P (p.1 + 1) * Q p.2 := by
      simp [M, Finset.Nat.sum_antidiagonal_succ, Nat.choose_zero_right, hP_def,
        ascPochhammer_zero, Polynomial.eval_one]
    have rhs_eq : M = ∑ p ∈ Finset.antidiagonal n,
        ↑(n.choose p.1) * P p.1 * Q (p.2 + 1) := by
      simp [M, Finset.Nat.sum_antidiagonal_succ', Nat.choose_succ_self, hQ_def,
        ascPochhammer_zero, Polynomial.eval_one]
    linarith [lhs_eq, rhs_eq]
