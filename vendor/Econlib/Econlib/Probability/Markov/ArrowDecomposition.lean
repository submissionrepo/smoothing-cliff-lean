/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Markov.PresentValue

/-!
# Arrow-claim representation of an adapted process

Given an adapted process `V` over a finite Markov chain, an **Arrow decomposition** expresses
`V t h` as a deterministic drift plus a discounted state-contingent average of one-period claims:

```
V t h = drift t h + β · 𝔼_{s' | h.lastNode}[claim t h s'].
```

The canonical such decomposition for a present value `V = presentValue X` is given by `drift = X`
and `claim = presentValue X` at the extended history. The `innovation` of an adapted process is the
deviation of its next-period value from its conditional expectation.

## Main definitions

* `innovation` — the deviation of `V` at the next period from its conditional expectation.
* `ArrowDecomposition` — a one-period drift-plus-claim representation of an adapted process.
* `presentValue_arrowDecomposition` — the canonical Arrow decomposition of a present-value process.

## Main statements

* `innovation_zero_mean` — the innovation has zero conditional mean against the chain.
* `presentValue_telescope_finite` — the present value agrees with its first-`T` partial sum up to a
  discounted tail remainder bounded by `M · β^T / (1 - β)`.

## Tags

markov chain, arrow security, present value, adapted process, innovation
-/

@[expose] public section

open BigOperators Finset

namespace Econlib.Probability

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The innovation of `V` at history `(t, h)` along the next-period state `s'`: The deviation of
`V (t + 1, h.extend s')` from its conditional expectation under `P`. -/
noncomputable def innovation (P : FiniteMarkovChain α) (V : AdaptedProcess α)
    (t : ℕ) (h : History α t) (s' : α) : ℝ :=
  V.val (t + 1) (h.extend s') - V.condExpStep P t h

/-- The innovation has zero conditional mean against the chain: The transition-weighted average of
`innovation P V t h` over next-period states vanishes. This martingale-difference normalization
follows from `P_proper` (transition rows sum to one) and the definition of `innovation` alone. -/
theorem innovation_zero_mean (P : FiniteMarkovChain α) (V : AdaptedProcess α)
    (P_proper : ∀ s : α, ∑ s' : α, (P.transition s) s' = 1)
    (t : ℕ) (h : History α t) :
    ∑ s' : α, (P.transition h.lastNode) s' * innovation P V t h s' = 0 := by
  unfold innovation
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    P_proper h.lastNode, one_mul]
  -- The first summand is defeq to the conditional expectation; subtracting it from itself is zero.
  change V.condExpStep P t h - V.condExpStep P t h = 0
  ring

/-- A one-period Arrow representation of an adapted process `V` against payoffs discounted at
`β`. -/
structure ArrowDecomposition (P : FiniteMarkovChain α) (β : ℝ)
    (V : AdaptedProcess α) where
  /-- Deterministic part of the decomposition at history `(t, h)`. -/
  drift : (t : ℕ) → History α t → ℝ
  /-- One-period Arrow claim against next-period state `s'`. -/
  claim : (t : ℕ) → (h : History α t) → α → ℝ
  /-- The decomposition identity. -/
  decompose :
    ∀ t h, V.val t h = drift t h
                  + β * ∑ s' : α, (P.transition h.lastNode) s' * claim t h s'
  /-- Claims agree with `V` at the extended history. -/
  consistent :
    ∀ t h s', claim t h s' = V.val (t + 1) (h.extend s')

/-- The canonical Arrow decomposition of a present-value process: The drift is the per-period
payoff `X` and the claim is `PV X` at the extended history. -/
noncomputable def presentValue_arrowDecomposition
    (P : FiniteMarkovChain α) (β : ℝ)
    (hβ_nonneg : 0 ≤ β) (hβ_lt : β < 1) (X : AdaptedProcess α)
    {M : ℝ} (hX : X.Bounded M) :
    ArrowDecomposition P β (presentValue.adapted P β X) where
  drift     := fun t h => X.val t h
  claim     := fun t h s' => presentValue P β X (t + 1) (h.extend s')
  decompose := by
    intro t h
    change presentValue P β X t h
      = X.val t h + β *
          ∑ s' : α, (P.transition h.lastNode) s' *
            presentValue P β X (t + 1) (h.extend s')
    exact presentValue_bellman P β hβ_nonneg hβ_lt X hX t h
  consistent := by
    intro t h s'
    rfl

/-- Finite-horizon truncation of the Arrow decomposition: The present value agrees with its
first-`T` partial sum up to a discounted tail remainder bounded by `M · β^T / (1 - β)`. -/
theorem presentValue_telescope_finite
    (P : FiniteMarkovChain α) (β : ℝ) (hβ_nonneg : 0 ≤ β) (hβ_lt : β < 1)
    (X : AdaptedProcess α) {M : ℝ} (hX : X.Bounded M)
    (T : ℕ) (t : ℕ) (h : History α t) :
    ∃ remainder : ℝ, |remainder| ≤ M * β ^ T / (1 - β) ∧
      presentValue P β X t h
        = (∑ τ ∈ Finset.range T, β ^ τ * iterCondExp P X τ t h) + remainder := by
  -- The remainder is the discounted tail of the τ-tsum.
  refine ⟨∑' τ : ℕ, β ^ (τ + T) * iterCondExp P X (τ + T) t h, ?_, ?_⟩
  · -- Bound the tail summand by `M * β^(τ + T) = (M * β^T) * β^τ`, then sum a
    -- geometric series.
    have hbound : ∀ τ : ℕ,
        |β ^ (τ + T) * iterCondExp P X (τ + T) t h| ≤ (M * β ^ T) * β ^ τ := by
      intro τ
      rw [abs_mul, abs_of_nonneg (pow_nonneg hβ_nonneg _), pow_add]
      calc β ^ τ * β ^ T * |iterCondExp P X (τ + T) t h|
          ≤ β ^ τ * β ^ T * M :=
            mul_le_mul_of_nonneg_left
              (iterCondExp_bounded (M := M) P X hX (τ + T) t h)
              (mul_nonneg (pow_nonneg hβ_nonneg _) (pow_nonneg hβ_nonneg _))
        _ = (M * β ^ T) * β ^ τ := by ring
    have hsum_geom : Summable (fun τ : ℕ => (M * β ^ T) * β ^ τ) :=
      (summable_geometric_of_lt_one hβ_nonneg hβ_lt).mul_left (M * β ^ T)
    have hsum_abs : Summable
        (fun τ : ℕ => |β ^ (τ + T) * iterCondExp P X (τ + T) t h|) :=
      Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hbound hsum_geom
    calc |∑' τ : ℕ, β ^ (τ + T) * iterCondExp P X (τ + T) t h|
        ≤ ∑' τ : ℕ, |β ^ (τ + T) * iterCondExp P X (τ + T) t h| := by
          simpa [Real.norm_eq_abs] using
            norm_tsum_le_tsum_norm
              (E := ℝ) (f := fun τ => β ^ (τ + T) * iterCondExp P X (τ + T) t h)
              (by simpa [Real.norm_eq_abs] using hsum_abs)
      _ ≤ ∑' τ : ℕ, (M * β ^ T) * β ^ τ := by
          refine Summable.tsum_le_tsum hbound hsum_abs hsum_geom
      _ = (M * β ^ T) * ∑' τ : ℕ, β ^ τ := tsum_mul_left
      _ = (M * β ^ T) * (1 - β)⁻¹ := by rw [tsum_geometric_of_lt_one hβ_nonneg hβ_lt]
      _ = M * β ^ T / (1 - β) := by ring
  · -- Split the tsum at `T`.
    have hsum : Summable (fun τ : ℕ => β ^ τ * iterCondExp P X τ t h) :=
      presentValue_summable P β hβ_nonneg hβ_lt X hX t h
    have hsplit :
        ∑ τ ∈ Finset.range T, β ^ τ * iterCondExp P X τ t h
          + ∑' τ : ℕ, β ^ (τ + T) * iterCondExp P X (τ + T) t h
        = ∑' τ : ℕ, β ^ τ * iterCondExp P X τ t h :=
      Summable.sum_add_tsum_nat_add T hsum
    unfold presentValue
    rw [← hsplit]

end Econlib.Probability
