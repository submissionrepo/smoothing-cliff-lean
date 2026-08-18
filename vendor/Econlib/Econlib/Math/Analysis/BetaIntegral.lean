/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Mathlib.Probability.Distributions.Beta

/-!
# The scaled real beta integral and the multivariate beta merge recurrence

This file develops two facts about the beta function. First, the value of the scaled real beta
integral `∫ x in 0..a, x ^ (s - 1) * (a - x) ^ (t - 1)` for positive parameters, obtained by
lifting the complex `Complex.betaIntegral_scaled` identity to `ℝ`. Second, a merge recurrence for
the multivariate beta function (the ratio of products of `Real.Gamma` values) that combines the
last two parameters into their sum, derived from `Γ(s)Γ(t) = Γ(s + t) · B(s, t)`.

## Main definitions

* `Real.mergeLastTwo` — the parameter-merge map on `Fin (k + 2) → ℝ` that combines the last two
  coordinates into their sum.

## Main statements

* `Real.betaIntegral_scaled_real` —
  `∫ x in 0..a, x ^ (s - 1) * (a - x) ^ (t - 1) = a ^ (s + t - 1) · B(s, t)`.
* `Real.mergeLastTwo_pos`, `Real.mergeLastTwo_sum` — positivity of the merged parameters and
  invariance of their sum.
* `Real.multivariateBeta_merge` — the multivariate beta merge recurrence.

## Tags

beta function, beta integral, gamma function, multivariate beta
-/

@[expose] public section

open MeasureTheory ProbabilityTheory BigOperators Real

namespace Real

/-! ### Real-valued beta integral on `[0, a]` -/

/-- The **scaled real beta integral**: `∫ x in 0..a, x^(s-1) * (a-x)^(t-1)` equals
`a^(s+t-1) * B(s,t)` for positive `s`, `t`, and `a`. -/
lemma betaIntegral_scaled_real {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    {a : ℝ} (ha : 0 < a) :
    ∫ x in (0 : ℝ)..a, (x : ℝ) ^ (s - 1) * (a - x) ^ (t - 1) =
      a ^ (s + t - 1) * ProbabilityTheory.beta s t := by
  -- Strategy: show ↑(LHS) = ↑(RHS) in ℂ, then use ofReal_injective
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, ← intervalIntegral.integral_ofReal]
  -- Match the integrand pointwise on [0, a]
  have hint : ∀ x ∈ Set.uIcc 0 a,
      (↑(x ^ (s - 1) * (a - x) ^ (t - 1)) : ℂ) =
      (↑x : ℂ) ^ ((↑s : ℂ) - 1) * ((↑a : ℂ) - (↑x : ℂ)) ^ ((↑t : ℂ) - 1) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    have hx0 : 0 ≤ x := by
      rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith [ha.le]
    have hax : 0 ≤ a - x := by
      rcases hx with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith [ha.le]
    push_cast
    rw [Complex.ofReal_cpow hx0, Complex.ofReal_cpow hax]
    congr 1 <;> [skip; rw [Complex.ofReal_sub]] <;>
    · push_cast; ring
  rw [intervalIntegral.integral_congr hint]
  -- Apply the complex identity
  rw [Complex.betaIntegral_scaled _ _ ha]
  -- Match LHS: ↑a^(↑s+↑t-1) * betaIntegral
  -- Match RHS: ↑(a^(s+t-1)) * ↑(beta s t)
  congr 1
  · rw [Complex.ofReal_cpow ha.le]; push_cast; ring
  · -- Need: (↑s).betaIntegral ↑t = ↑(beta s t)
    rw [beta_eq_betaIntegralReal s t hs ht]
    -- Goal: (↑s).betaIntegral ↑t = ↑(((↑s).betaIntegral ↑t).re)
    -- betaIntegral of real args is real: use Gamma representation
    rw [Complex.betaIntegral_eq_Gamma_mul_div _ _
        (by rwa [Complex.ofReal_re]) (by rwa [Complex.ofReal_re])]
    rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_add, Complex.Gamma_ofReal]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_re]

/-! ### Multivariate beta function merge recurrence -/

/-- Given `α : Fin (k+2) → ℝ`, merge the last two parameters: `mergeLastTwo α i = α i` for `i < k`,
and `mergeLastTwo α k = α k + α (k+1)`. -/
noncomputable def mergeLastTwo {k : ℕ} (α : Fin (k + 2) → ℝ) : Fin (k + 1) → ℝ :=
  fun i =>
    if h : i.val < k then α ⟨i.val, by omega⟩
    else α ⟨k, by omega⟩ + α ⟨k + 1, by omega⟩

/-- Positivity of merged parameters. -/
lemma mergeLastTwo_pos {k : ℕ} {α : Fin (k + 2) → ℝ} (hα : ∀ i, 0 < α i) :
    ∀ i, 0 < mergeLastTwo α i := by
  intro i; unfold mergeLastTwo
  split_ifs with h
  · exact hα ⟨i.val, by omega⟩
  · exact add_pos (hα ⟨k, by omega⟩) (hα ⟨k + 1, by omega⟩)

/-- Sum of merged parameters equals sum of original parameters. Both sides equal
`α 0 + α 1 + ⋯ + α (k+1)`. -/
lemma mergeLastTwo_sum {k : ℕ} (α : Fin (k + 2) → ℝ) :
    ∑ i, mergeLastTwo α i = ∑ i, α i := by
  -- Peel last element off LHS: ∑ Fin(k+1) = ∑ Fin(k) ∘ castSucc + f(last k)
  rw [Fin.sum_univ_castSucc (f := fun i => mergeLastTwo α i)]
  -- Peel last two elements off RHS
  rw [Fin.sum_univ_castSucc (f := α),
      Fin.sum_univ_castSucc (f := fun i => α (Fin.castSucc i))]
  -- mergeLastTwo at the last index = α k + α (k+1)
  have hlast : mergeLastTwo α (Fin.last k) = α ⟨k, by omega⟩ + α ⟨k + 1, by omega⟩ := by
    simp [mergeLastTwo, Fin.last]
  rw [hlast]
  -- For i : Fin k, castSucc i has val < k, so mergeLastTwo agrees with α
  suffices hsums : ∑ i : Fin k, mergeLastTwo α (Fin.castSucc i) =
      ∑ i : Fin k, α (Fin.castSucc (Fin.castSucc i)) by
    rw [hsums, show α (Fin.castSucc (Fin.last k)) = α ⟨k, by omega⟩ from by congr 1,
      show α (Fin.last (k + 1)) = α ⟨k + 1, by omega⟩ from by congr 1]
    ring
  apply Finset.sum_congr rfl
  intro i _
  have hi : (Fin.castSucc i).val < k := by simp [Fin.castSucc]
  simp only [mergeLastTwo, hi, dite_true]
  congr 1

/-- The multivariate beta merge recurrence: `B(α₁,...,αₖ₊₂) = B(αₖ₊₁, αₖ₊₂) · B(mergeLastTwo α)`,
where the multivariate beta function is written as a ratio of products of `Real.Gamma` values. -/
lemma multivariateBeta_merge {k : ℕ} (α : Fin (k + 2) → ℝ) (hα : ∀ i, 0 < α i) :
    (∏ i : Fin (k + 2), Real.Gamma (α i)) / Real.Gamma (∑ i : Fin (k + 2), α i) =
    ProbabilityTheory.beta (α ⟨k, by omega⟩) (α ⟨k + 1, by omega⟩) *
    ((∏ i : Fin (k + 1), Real.Gamma (mergeLastTwo α i)) /
      Real.Gamma (∑ i : Fin (k + 1), mergeLastTwo α i)) := by
  -- Unify denominators
  rw [mergeLastTwo_sum]
  -- Split LHS product: ∏ Fin(k+2) = (∏ Fin(k) via castSucc∘castSucc) · Γ(α_k) · Γ(α_{k+1})
  rw [Fin.prod_univ_castSucc (f := fun i => Real.Gamma (α i)),
      Fin.prod_univ_castSucc (f := fun i => Real.Gamma (α (Fin.castSucc i)))]
  -- Split RHS merged product: ∏ Fin(k+1) = (∏ Fin(k) via castSucc) · Γ(α_k + α_{k+1})
  rw [Fin.prod_univ_castSucc (f := fun i => Real.Gamma (mergeLastTwo α i))]
  -- mergeLastTwo at last k = α_k + α_{k+1}
  have hlast : mergeLastTwo α (Fin.last k) = α ⟨k, by omega⟩ + α ⟨k + 1, by omega⟩ := by
    simp [mergeLastTwo, Fin.last]
  rw [hlast]
  -- For i : Fin k, mergeLastTwo ∘ castSucc agrees with α ∘ castSucc ∘ castSucc
  have hprod : ∏ i : Fin k, Real.Gamma (mergeLastTwo α (Fin.castSucc i)) =
      ∏ i : Fin k, Real.Gamma (α (Fin.castSucc (Fin.castSucc i))) := by
    apply Finset.prod_congr rfl; intro i _
    congr 1
    have hi : (Fin.castSucc i).val < k := by simp [Fin.castSucc]
    simp only [mergeLastTwo, hi, dite_true]
    congr 1
  -- Match Fin terms: α (Fin.last k).castSucc = α ⟨k, _⟩, α (Fin.last (k+1)) = α ⟨k+1, _⟩
  rw [hprod, show α (Fin.castSucc (Fin.last k)) = α ⟨k, by omega⟩ from by congr 1,
    show α (Fin.last (k + 1)) = α ⟨k + 1, by omega⟩ from by congr 1]
  -- Now pure algebra: field_simp with positivity
  unfold ProbabilityTheory.beta
  have hΓk : Real.Gamma (α ⟨k, by omega⟩) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (hα ⟨k, by omega⟩))
  have hΓk1 : Real.Gamma (α ⟨k + 1, by omega⟩) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (hα ⟨k + 1, by omega⟩))
  have hΓsum : Real.Gamma (∑ i, α i) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (Finset.sum_pos (fun i _ => hα i)
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩))
  have hΓpair : Real.Gamma (α ⟨k, by omega⟩ + α ⟨k + 1, by omega⟩) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (add_pos (hα ⟨k, by omega⟩) (hα ⟨k + 1, by omega⟩)))
  field_simp

end Real
