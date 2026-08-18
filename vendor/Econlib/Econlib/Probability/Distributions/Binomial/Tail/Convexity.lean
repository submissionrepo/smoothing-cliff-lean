/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.RingTheory.Polynomial.Bernstein

/-!
# Convexity of the binomial expectation in the success probability

For a function `f : ℕ → ℝ` with nondecreasing differences, the map `p ↦ E_{Bin(n,p)}[f(X)]` is
convex on `[0, 1]`. The expectation is represented as a weighted sum of Bernstein basis
polynomials, so it is smooth in `p`, and its second derivative is nonnegative exactly when `f` has
nondecreasing differences.

## Main definitions

* `binomialExpect` — the map `p ↦ E_{Bin(n,p)}[f(X)]`, expressed as a polynomial in `p`.

## Main statements

* `ConvexOn.nondecreasing_differences` — a convex function on `ℝ` has nondecreasing differences on
  `ℕ`.
* `binomialExpect_convexOn` — `p ↦ E_{Bin(n,p)}[f(X)]` is convex on `[0, 1]` when `f` has
  nondecreasing differences.

## Notes

For a convex `φ`, `ConvexOn.nondecreasing_differences` supplies the hypothesis of
`binomialExpect_convexOn`. This is the step that derives the Dirichlet-multinomial marginal convex
order from the Beta convex order.

## Tags

binomial distribution, convexity, bernstein polynomial, nondecreasing differences
-/

@[expose] public noncomputable section

open Finset BigOperators Polynomial

namespace Econlib.Probability

/-- The binomial expectation `E_{Bin(n,p)}[f(X)]`, defined as a polynomial in `p` for all `p ∈ ℝ`.
This agrees with the true binomial expectation when `p ∈ [0, 1]`. -/
noncomputable def binomialExpect (n : ℕ) (f : ℕ → ℝ) (p : ℝ) : ℝ :=
  ∑ k : Fin (n + 1), (n.choose (k : ℕ) : ℝ) * p ^ (k : ℕ) * (1 - p) ^ (n - k) * f k

/-- A function that is convex on `ℝ` has nondecreasing differences on `ℕ`: For all `k : ℕ`,
`φ(k + 2) - φ(k + 1) ≥ φ(k + 1) - φ(k)`. -/
lemma _root_.ConvexOn.nondecreasing_differences (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    ∀ k : ℕ, φ (k + 2 : ℕ) - φ (k + 1 : ℕ) ≥ φ (k + 1 : ℕ) - φ (k : ℕ) := by
  intro k
  have hconv := hφ.2 (Set.mem_univ (k : ℝ)) (Set.mem_univ ((k + 2 : ℕ) : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  simp only [smul_eq_mul] at hconv
  have hmid : (1 : ℝ) / 2 * (k : ℝ) + 1 / 2 * ((k + 2 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by
    push_cast; ring
  rw [hmid] at hconv
  linarith

/-- The `Polynomial ℝ` whose evaluation at `p` equals `binomialExpect n f p`, expressed as a
weighted sum of Bernstein basis polynomials. -/
def binomialExpectPoly (n : ℕ) (f : ℕ → ℝ) : Polynomial ℝ :=
  ∑ k : Fin (n + 1), Polynomial.C (f k) * bernsteinPolynomial ℝ n k

/-- Evaluating `binomialExpectPoly n f` at `p` recovers `binomialExpect n f p`. -/
lemma binomialExpectPoly_eval (n : ℕ) (f : ℕ → ℝ) (p : ℝ) :
    Polynomial.eval p (binomialExpectPoly n f) = binomialExpect n f p := by
  simp only [binomialExpectPoly, binomialExpect, Polynomial.eval_finset_sum]
  congr 1; ext k
  simp only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_C]
  ring

/-- `binomialExpect n f` is smooth (`ContDiff ℝ ⊤`), since it is the evaluation of a polynomial. -/
lemma binomialExpect_contDiff (n : ℕ) (f : ℕ → ℝ) :
    ContDiff ℝ ⊤ (binomialExpect n f) := by
  rw [show binomialExpect n f = fun p => Polynomial.eval p (binomialExpectPoly n f) from
    funext (fun p => (binomialExpectPoly_eval n f p).symm)]
  exact Polynomial.contDiff_aeval (binomialExpectPoly n f) ⊤

/-- `binomialExpect n f` is differentiable. -/
lemma binomialExpect_differentiable (n : ℕ) (f : ℕ → ℝ) :
    Differentiable ℝ (binomialExpect n f) :=
  (binomialExpect_contDiff n f).differentiable (by simp)

/-- The formal derivative of `binomialExpectPoly (n + 1) f` equals
`(n + 1) * binomialExpectPoly n Δf`, where `Δf k = f (k + 1) - f k` is the forward difference. -/
lemma binomialExpectPoly_derivative (n : ℕ) (f : ℕ → ℝ) :
    Polynomial.derivative (binomialExpectPoly (n + 1) f) =
      (↑(n + 1) : Polynomial ℝ) * binomialExpectPoly n (fun k => f (k + 1) - f k) := by
  apply Polynomial.funext
  intro r
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, binomialExpectPoly,
    Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]
  rw [Polynomial.derivative_sum]
  simp only [Polynomial.derivative_C_mul, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ]
  rw [bernsteinPolynomial.derivative_zero]
  simp_rw [bernsteinPolynomial.derivative_succ]
  simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_natCast,
    Polynomial.eval_sub]
  simp only [show n + 1 - 1 = n from by omega]
  set B := fun j => Polynomial.eval r (bernsteinPolynomial ℝ n j) with hBdef
  -- B(n+1) = 0 because the index exceeds the degree n.
  have hBn1 : B (n + 1) = 0 := by
    simp [hBdef, bernsteinPolynomial.eq_zero_of_lt ℝ (by omega : n < n + 1)]
  change f 0 * (-(↑(n + 1)) * B 0) +
      ∑ x : Fin (n + 1), f (↑x + 1) * (↑(n + 1) * (B ↑x - B (↑x + 1))) =
    ↑(n + 1) * ∑ x : Fin (n + 1), (f (↑x + 1) - f ↑x) * B ↑x
  -- Telescope: ∑ f(j+1)*B(j+1) = ∑ f(j)*B(j) - f(0)*B(0), using B(n+1) = 0.
  have hshift : ∑ j : Fin (n + 1), f (↑j + 1) * B (↑j + 1) =
      (∑ j : Fin (n + 1), f ↑j * B ↑j) - f 0 * B 0 := by
    simp only [Fin.sum_univ_eq_sum_range (fun j => f (j + 1) * B (j + 1)),
      Fin.sum_univ_eq_sum_range (fun j => f j * B j)]
    set g := fun j => f j * B j
    have h1 : ∑ j ∈ Finset.range (n + 2), g j =
        ∑ j ∈ Finset.range (n + 1), g (j + 1) + g 0 :=
      Finset.sum_range_succ' g (n + 1)
    have h2 : ∑ j ∈ Finset.range (n + 2), g j =
        ∑ j ∈ Finset.range (n + 1), g j + g (n + 1) :=
      Finset.sum_range_succ g (n + 1)
    have h3 : g (n + 1) = 0 := by simp [g, hBn1]
    linarith
  have step1 : ∀ x : Fin (n + 1),
      f (↑x + 1) * (↑(n + 1) * (B ↑x - B (↑x + 1))) =
        ↑(n + 1) * (f (↑x + 1) * B ↑x) - ↑(n + 1) * (f (↑x + 1) * B (↑x + 1)) := by
    intro x; ring
  simp_rw [step1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have step2 : ∀ x : Fin (n + 1),
      (f (↑x + 1) - f ↑x) * B ↑x = f (↑x + 1) * B ↑x - f ↑x * B ↑x := by
    intro x; ring
  simp_rw [step2, Finset.sum_sub_distrib]
  rw [hshift]
  ring

/-- The first derivative of `binomialExpect (n + 1) f` at `p` equals
`(n + 1) * binomialExpect n Δf p`, where `Δf k = f (k + 1) - f k`. -/
lemma binomialExpect_deriv_eq (n : ℕ) (f : ℕ → ℝ) (p : ℝ) :
    deriv (binomialExpect (n + 1) f) p =
      (n + 1 : ℝ) * binomialExpect n (fun k => f (k + 1) - f k) p := by
  conv_lhs =>
    rw [show binomialExpect (n + 1) f = fun p => Polynomial.eval p (binomialExpectPoly (n + 1) f)
      from funext (fun p => (binomialExpectPoly_eval (n + 1) f p).symm)]
  simp only [← Polynomial.coe_aeval_eq_eval]
  rw [Polynomial.deriv_aeval]
  simp only [Polynomial.coe_aeval_eq_eval]
  rw [binomialExpectPoly_derivative]
  simp only [Polynomial.eval_mul, Polynomial.eval_natCast, binomialExpectPoly_eval]
  push_cast; ring

/-- `binomialExpect n f` is nonneg on `[0, 1]` when `f` is a nonneg function. -/
lemma binomialExpect_nonneg (n : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k, 0 ≤ f k) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ binomialExpect n f p := by
  apply Finset.sum_nonneg
  intro k _
  have hp0 : (0 : ℝ) ≤ p := hp.1
  have hp1 : (0 : ℝ) ≤ 1 - p := by linarith [hp.2]
  have := hf (k : ℕ)
  positivity

/-- The second derivative of `binomialExpect n f` is nonneg on `[0, 1]` whenever `f` has
nondecreasing differences. -/
lemma binomialExpect_deriv2_nonneg (n : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k : ℕ, f (k + 2) - f (k + 1) ≥ f (k + 1) - f k)
    (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ deriv (deriv (binomialExpect n f)) p := by
  match n with
  | 0 =>
    have heq : binomialExpect 0 f = fun _ => f 0 := by ext q; simp [binomialExpect]
    simp [heq]
  | 1 =>
    have hd : deriv (binomialExpect 1 f) =
        fun p => (1 : ℝ) * binomialExpect 0 (fun k => f (k + 1) - f k) p := by
      ext q; simpa using binomialExpect_deriv_eq 0 f q
    rw [hd]
    have hconst : (fun p => (1 : ℝ) * binomialExpect 0 (fun k => f (k + 1) - f k) p) =
        fun _ => f 1 - f 0 := by
      ext q; simp [binomialExpect]
    rw [hconst]; simp
  | n + 2 =>
    set Δf := fun k => f (k + 1) - f k with hΔf_def
    have hd1 : deriv (binomialExpect (n + 2) f) =
        fun q => ((n + 2 : ℕ) : ℝ) * binomialExpect (n + 1) Δf q := by
      ext q
      have h := binomialExpect_deriv_eq (n + 1) f q
      simp only [show n + 1 + 1 = n + 2 from by omega] at h
      rw [hΔf_def]
      convert h using 2
      push_cast; ring
    rw [hd1]
    rw [deriv_const_mul _ (binomialExpect_differentiable (n + 1) Δf).differentiableAt]
    set ΔΔf := fun k => Δf (k + 1) - Δf k with hΔΔf_def
    rw [binomialExpect_deriv_eq n Δf]
    apply mul_nonneg (Nat.cast_nonneg' (n + 2))
    apply mul_nonneg
    · have : (0 : ℝ) ≤ ↑n := Nat.cast_nonneg' n
      linarith
    apply binomialExpect_nonneg n _ _ p hp
    intro k
    simp only [hΔf_def]
    linarith [hf k]

/-- **Binomial Expectation Convexity:** If `f : ℕ → ℝ` has nondecreasing differences, i.e.,
`f (k + 2) - f (k + 1) ≥ f (k + 1) - f k` for all `k`, then the map
`p ↦ E_{Bin(n,p)}[f(X)] = binomialExpect n f p` is convex on `[0, 1]`. -/
theorem binomialExpect_convexOn (n : ℕ) (f : ℕ → ℝ)
    (hf : ∀ k : ℕ, f (k + 2) - f (k + 1) ≥ f (k + 1) - f k) :
    ConvexOn ℝ (Set.Icc 0 1) (binomialExpect n f) := by
  have hsmooth := binomialExpect_contDiff n f
  have hdiff : Differentiable ℝ (binomialExpect n f) :=
    hsmooth.differentiable (by simp)
  have hsmooth2 : ContDiff ℝ 2 (binomialExpect n f) := hsmooth.of_le le_top
  have hdiff' : Differentiable ℝ (deriv (binomialExpect n f)) :=
    hsmooth2.differentiable_deriv_two
  apply convexOn_of_deriv2_nonneg' (convex_Icc 0 1)
  · exact hdiff.differentiableOn
  · exact hdiff'.differentiableOn
  · intro p hp
    rw [Function.iterate_succ', Function.comp]
    exact binomialExpect_deriv2_nonneg n f hf p hp

end Econlib.Probability

end -- noncomputable section
