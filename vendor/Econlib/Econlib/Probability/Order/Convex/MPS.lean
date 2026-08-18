/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.FinDist.Expect
public import Econlib.Probability.FinDist.Simplex
public import Mathlib.Analysis.Convex.Mul

/-!
# Mean-preserving spread for finite distributions

A **mean-preserving spread** of a finite distribution keeps the mean of an outcome map `y` fixed
while increasing dispersion, so that every concave payoff loses expectation. This file defines the
relation — once over `FinDist (Fin n)` and once over a general finite carrier — and derives the
order structure and the basic dispersion consequences (convex payoffs gain, variance grows).

## Main definitions

* `IsMPS`, `FinDist.IsMPS` — `ds` is a mean-preserving spread of `d` with respect to values `y`:
  Equal means and weakly lower expectation under `ds` for every function concave on `ℝ`.

## Main statements

* `IsMPS.concave_expect_le'`, `FinDist.IsMPS.concave_expect_le` — concave payoffs lose expectation.
* `IsMPS.convex_expect_ge`, `FinDist.IsMPS.convex_expect_ge` — convex payoffs gain expectation.
* `IsMPS.variance_ge`, `FinDist.IsMPS.variance_ge` — variance increases.
* `FinDist.IsMPS.ofFinDist_iff` — the general and `Fin n` definitions agree.

## References

* Rothschild, Michael, and Joseph E. Stiglitz. 1970. “Increasing Risk: I. A Definition.” *Journal
  of Economic Theory* 2 (3): 225–43. [https://doi.org/10.1016/0022-0531(70)90038-4](https://doi.org/10.1016/0022-0531(70)90038-4).

## Tags

mean-preserving spread, convex order, second-order stochastic dominance, increasing risk, variance
-/

@[expose] public section

namespace Econlib.Probability

open Finset BigOperators

/-- `ds` is a **mean-preserving spread** of `d` with respect to values `y : Fin n → ℝ`: Same mean,
every concave function has weakly lower expectation under `ds`. -/
structure IsMPS {n : ℕ} (d ds : FinDist (Fin n))
    (y : Fin n → ℝ) : Prop where
  /-- The spread preserves the mean of `y`. -/
  same_mean : ds.expect y = d.expect y
  /-- Every concave payoff has weakly lower expectation under the spread. -/
  concave_le : ∀ f : ℝ → ℝ, ConcaveOn ℝ Set.univ f →
    ds.expect (f ∘ y) ≤ d.expect (f ∘ y)

namespace IsMPS

variable {n : ℕ} {d ds : FinDist (Fin n)} {y : Fin n → ℝ}

/-- Concave payoffs have weakly lower expectation under a mean-preserving spread. Accessor for the
`concave_le` field of `IsMPS`. -/
theorem concave_expect_le' (h : IsMPS d ds y)
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ Set.univ f) :
    ds.expect (f ∘ y) ≤ d.expect (f ∘ y) :=
  h.concave_le f hf

/-- Convex payoffs have weakly larger expectation under a mean-preserving spread. -/
theorem convex_expect_ge (h : IsMPS d ds y)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    d.expect (φ ∘ y) ≤ ds.expect (φ ∘ y) := by
  -- Apply the concave bound to `-φ` and negate both sides.
  have hle := h.concave_le (-φ) hφ.neg
  simpa only [FinDist.expect, Pi.neg_apply, Function.comp_def,
    mul_neg, sum_neg_distrib, neg_le_neg_iff] using hle

/-- MPS is reflexive. -/
theorem refl (d : FinDist (Fin n)) (y : Fin n → ℝ) :
    IsMPS d d y :=
  ⟨rfl, fun _ _ => le_refl _⟩

/-- MPS is transitive. -/
theorem trans (h₁₂ : IsMPS d₁ d₂ y) (h₂₃ : IsMPS d₂ d₃ y) :
    IsMPS d₁ d₃ y :=
  ⟨h₂₃.same_mean.trans h₁₂.same_mean,
    fun f hf => le_trans (h₂₃.concave_le f hf)
      (h₁₂.concave_le f hf)⟩

/-- Affine functions of `y` have equal expectation under `d` and a mean-preserving spread `ds`. -/
theorem affine_expect_eq (h : IsMPS d ds y) (a b : ℝ) :
    ds.expect (fun i => a * y i + b) =
      d.expect (fun i => a * y i + b) := by
  -- Rewrite as 𝔼[a • y + const b] = a 𝔼[y] + b
  have key : ∀ (μ : FinDist (Fin n)),
      μ.expect (fun i => a * y i + b) =
        a * μ.expect y + b := by
    intro μ
    have : (fun i => a * y i + b) = (a • y) + (fun _ => b) := by
      ext i; simp [smul_eq_mul]
    rw [this, μ.expect_add, μ.expect_smul, μ.expect_const]
  rw [key ds, key d, h.same_mean]

/-- Variance increases under a mean-preserving spread. Derived from the `concave_le` field by
applying the convex test function `x ↦ x ^ 2`. -/
theorem variance_ge (h : IsMPS d ds y) :
    ds.expect (fun i => (y i) ^ 2) -
      (ds.expect y) ^ 2 ≥
    d.expect (fun i => (y i) ^ 2) -
      (d.expect y) ^ 2 := by
  rw [h.same_mean]
  have hconv := h.convex_expect_ge (fun x => x ^ 2)
    (Even.convexOn_pow (even_two))
  -- hconv : d.expect ((· ^ 2) ∘ y) ≤ ds.expect ((· ^ 2) ∘ y)
  -- Goal: d.expect (y²) - (𝔼[y])² ≤ ds.expect (y²) - (𝔼[y])²
  simp only [Function.comp_def] at hconv
  linarith

end IsMPS

namespace FinDist

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `ds` is a mean-preserving spread of `d` with respect to values `y : α → ℝ`. -/
structure IsMPS (d ds : FinDist α) (y : α → ℝ) : Prop where
  /-- The spread preserves the mean of `y`. -/
  same_mean : ds.expect y = d.expect y
  /-- Every concave payoff has weakly lower expectation under the spread. -/
  concave_le : ∀ f : ℝ → ℝ, ConcaveOn ℝ Set.univ f →
    ds.expect (f ∘ y) ≤ d.expect (f ∘ y)

namespace IsMPS

variable {d ds d₁ d₂ d₃ : FinDist α} {y : α → ℝ}

/-- Concave payoffs decrease under MPS. Accessor for the `concave_le` field of `FinDist.IsMPS`. -/
theorem concave_expect_le (h : FinDist.IsMPS d ds y)
    (f : ℝ → ℝ) (hf : ConcaveOn ℝ Set.univ f) :
    ds.expect (f ∘ y) ≤ d.expect (f ∘ y) :=
  h.concave_le f hf

/-- Convex payoffs increase under MPS. -/
theorem convex_expect_ge (h : FinDist.IsMPS d ds y)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) :
    d.expect (φ ∘ y) ≤ ds.expect (φ ∘ y) := by
  -- Apply the concave bound to `-φ` and negate both sides.
  have hle := h.concave_le (-φ) hφ.neg
  simpa only [FinDist.expect, Pi.neg_apply, Function.comp_def,
    mul_neg, sum_neg_distrib, neg_le_neg_iff] using hle

/-- MPS is reflexive. -/
theorem refl (d : FinDist α) (y : α → ℝ) :
    FinDist.IsMPS d d y :=
  ⟨rfl, fun _ _ => le_refl _⟩

/-- MPS is transitive. -/
theorem trans (h₁₂ : FinDist.IsMPS d₁ d₂ y)
    (h₂₃ : FinDist.IsMPS d₂ d₃ y) :
    FinDist.IsMPS d₁ d₃ y :=
  ⟨h₂₃.same_mean.trans h₁₂.same_mean,
    fun f hf => le_trans (h₂₃.concave_le f hf)
      (h₁₂.concave_le f hf)⟩

/-- Affine functions are preserved by MPS. -/
theorem affine_expect_eq (h : FinDist.IsMPS d ds y) (a b : ℝ) :
    ds.expect (fun i => a * y i + b) =
      d.expect (fun i => a * y i + b) := by
  have key : ∀ (μ : FinDist α),
      μ.expect (fun i => a * y i + b) =
        a * μ.expect y + b := by
    intro μ
    have : (fun i => a * y i + b) = (a • y) + (fun _ => b) := by
      ext i; simp [smul_eq_mul]
    rw [this, μ.expect_add, μ.expect_smul, μ.expect_const]
  rw [key ds, key d, h.same_mean]

/-- Variance increases under MPS. Derived from the `concave_le` field by applying the convex test
function `x ↦ x ^ 2`. -/
theorem variance_ge (h : FinDist.IsMPS d ds y) :
    ds.variance y ≥ d.variance y := by
  rw [FinDist.variance, FinDist.variance, h.same_mean]
  have hconv := h.convex_expect_ge (fun x => x ^ 2)
    (Even.convexOn_pow (even_two))
  simp only [Function.comp_def] at hconv
  linarith

/-- Bridge between the generic `FinDist.IsMPS` and the `Fin n`-specialized
`Econlib.Probability.IsMPS`. -/
lemma ofFinDist_iff {n : ℕ} (d ds : FinDist (Fin n)) (y : Fin n → ℝ) :
    FinDist.IsMPS d ds y ↔ Econlib.Probability.IsMPS d ds y :=
  -- Both structures share `same_mean` and `concave_le` fields, so each direction repackages them.
  ⟨fun h => ⟨h.same_mean, h.concave_le⟩, fun h => ⟨h.same_mean, h.concave_le⟩⟩

end IsMPS

end FinDist

end Econlib.Probability
