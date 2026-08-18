/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.Markov.AdaptedProcess
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Discounted conditional present values

For an `AdaptedProcess α` over a finite Markov chain, the conditional discounted present value at
history `(t, h)` is

```
PV X t h := ∑' τ : ℕ, β ^ τ · 𝔼[X (t+τ) | F_{t+τ}, F_t = h]
```

where the inner conditional expectation is the iterated one-step operator `iterCondExp`. Under
boundedness and `0 ≤ β < 1`, the tsum converges and `presentValue` is the unique bounded solution
of the Bellman equation

```
V t h = X t h + β · 𝔼[V (t + 1) | F_t = h].
```

## Main definitions

* `presentValue` — the conditional discounted present value of an adapted process.
* `presentValue.adapted` — the present value packaged as an adapted process.

## Main statements

* `presentValue_summable` — the present-value summand is summable for bounded `X` and `0 ≤ β < 1`.
* `presentValue_bellman` — the present value satisfies the Bellman recursion.
* `presentValue_bounded` — a uniformly bounded payoff yields present value bounded by `M / (1 - β)`.
* `presentValue_unique` — any bounded Bellman solution coincides with the present value.
* `presentValue_mono` — pointwise monotonicity of payoffs lifts to the present value.

## Tags

present value, discounted sum, bellman equation, markov chain, adapted process
-/

@[expose] public section

open BigOperators Finset

namespace Econlib.Probability

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Conditional discounted present value of an adapted process. -/
noncomputable def presentValue (P : FiniteMarkovChain α) (β : ℝ)
    (X : AdaptedProcess α) (t : ℕ) (h : History α t) : ℝ :=
  ∑' τ : ℕ, β ^ τ * iterCondExp P X τ t h

/-- Each PV summand is dominated by the geometric term `M · β^τ`. -/
private lemma presentValue_summand_abs_le (P : FiniteMarkovChain α) {β : ℝ}
    (hβ_nonneg : 0 ≤ β) (X : AdaptedProcess α) {M : ℝ} (hX : X.Bounded M)
    (t : ℕ) (h : History α t) (τ : ℕ) :
    |β ^ τ * iterCondExp P X τ t h| ≤ M * β ^ τ := by
  rw [abs_mul, abs_of_nonneg (pow_nonneg hβ_nonneg τ), mul_comm M (β ^ τ)]
  exact mul_le_mul_of_nonneg_left (iterCondExp_bounded (M := M) P X hX τ t h)
    (pow_nonneg hβ_nonneg τ)

/-- The PV summand `τ ↦ β^τ · 𝔼[X (t+τ) | F_t]` is summable for bounded `X` and `0 ≤ β < 1`. -/
theorem presentValue_summable (P : FiniteMarkovChain α) (β : ℝ)
    (hβ_nonneg : 0 ≤ β) (hβ_lt : β < 1) (X : AdaptedProcess α)
    {M : ℝ} (hX : X.Bounded M) (t : ℕ) (h : History α t) :
    Summable (fun τ : ℕ => β ^ τ * iterCondExp P X τ t h) :=
  Summable.of_norm_bounded (g := fun τ => M * β ^ τ)
    ((summable_geometric_of_lt_one hβ_nonneg hβ_lt).mul_left M)
    (fun τ => presentValue_summand_abs_le P hβ_nonneg X hX t h τ)

/-- The Bellman recursion satisfied by the conditional present value. -/
theorem presentValue_bellman (P : FiniteMarkovChain α) (β : ℝ)
    (hβ_nonneg : 0 ≤ β) (hβ_lt : β < 1) (X : AdaptedProcess α)
    {M : ℝ} (hX : X.Bounded M) (t : ℕ) (h : History α t) :
    presentValue P β X t h
      = X.val t h + β *
          ∑ s' : α, (P.transition h.lastNode) s' *
            presentValue P β X (t + 1) (h.extend s') := by
  -- Split the τ-tsum at τ=0, factor β out of the tail, swap the tsum with the
  -- finite sum over `s'`, and recognize the inner tsum as the next-period PV.
  have hsum : Summable (fun τ : ℕ => β ^ τ * iterCondExp P X τ t h) :=
    presentValue_summable P β hβ_nonneg hβ_lt X hX t h
  -- Split off τ = 0.
  have hsplit :
      presentValue P β X t h
        = X.val t h + ∑' τ : ℕ, β ^ (τ + 1) * iterCondExp P X (τ + 1) t h := by
    unfold presentValue
    rw [hsum.tsum_eq_zero_add]
    simp
  -- Rewrite each tail term as `β * (β^τ * iterCondExp ... (τ+1) ...)`.
  have hrewrite_summand :
      ∀ τ : ℕ, β ^ (τ + 1) * iterCondExp P X (τ + 1) t h
        = β * ∑ s' : α, (P.transition h.lastNode) s' *
            (β ^ τ * iterCondExp P X τ (t + 1) (h.extend s')) := by
    intro τ
    rw [iterCondExp_succ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    ring
  rw [hsplit]
  congr 1
  -- Pull β out of the tsum.
  calc ∑' τ : ℕ, β ^ (τ + 1) * iterCondExp P X (τ + 1) t h
      = ∑' τ : ℕ, β * ∑ s' : α, (P.transition h.lastNode) s' *
            (β ^ τ * iterCondExp P X τ (t + 1) (h.extend s')) := by
        exact tsum_congr hrewrite_summand
    _ = β * ∑' τ : ℕ, ∑ s' : α, (P.transition h.lastNode) s' *
            (β ^ τ * iterCondExp P X τ (t + 1) (h.extend s')) := tsum_mul_left
    _ = β * ∑ s' : α, ∑' τ : ℕ, (P.transition h.lastNode) s' *
            (β ^ τ * iterCondExp P X τ (t + 1) (h.extend s')) := by
        congr 1
        refine Summable.tsum_finsetSum (s := (Finset.univ : Finset α))
          (fun s' _ => ?_)
        exact (presentValue_summable P β hβ_nonneg hβ_lt X hX (t + 1)
          (h.extend s')).mul_left ((P.transition h.lastNode) s')
    _ = β * ∑ s' : α, (P.transition h.lastNode) s' *
            ∑' τ : ℕ, β ^ τ * iterCondExp P X τ (t + 1) (h.extend s') := by
        congr 1
        refine Finset.sum_congr rfl fun s' _ => ?_
        exact tsum_mul_left
    _ = β * ∑ s' : α, (P.transition h.lastNode) s' *
            presentValue P β X (t + 1) (h.extend s') := rfl

/-- A uniformly bounded payoff yields a present value bounded by `M / (1 - β)`. -/
theorem presentValue_bounded (P : FiniteMarkovChain α) (β : ℝ)
    (hβ_nonneg : 0 ≤ β) (hβ_lt : β < 1) (X : AdaptedProcess α)
    {M : ℝ} (hX : X.Bounded M) (t : ℕ) (h : History α t) :
    |presentValue P β X t h| ≤ M / (1 - β) := by
  unfold presentValue
  have hsum : Summable (fun τ : ℕ => β ^ τ * iterCondExp P X τ t h) :=
    presentValue_summable P β hβ_nonneg hβ_lt X hX t h
  have hbound : ∀ τ : ℕ, |β ^ τ * iterCondExp P X τ t h| ≤ M * β ^ τ :=
    presentValue_summand_abs_le P hβ_nonneg X hX t h
  have hsum_abs : Summable (fun τ : ℕ => |β ^ τ * iterCondExp P X τ t h|) := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hbound ?_
    exact (summable_geometric_of_lt_one hβ_nonneg hβ_lt).mul_left M
  calc |∑' τ : ℕ, β ^ τ * iterCondExp P X τ t h|
      ≤ ∑' τ : ℕ, |β ^ τ * iterCondExp P X τ t h| := by
        simpa [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (E := ℝ) (f := fun τ => β ^ τ * iterCondExp P X τ t h)
            (by simpa [Real.norm_eq_abs] using hsum_abs)
    _ ≤ ∑' τ : ℕ, M * β ^ τ := by
        refine Summable.tsum_le_tsum hbound hsum_abs ?_
        exact (summable_geometric_of_lt_one hβ_nonneg hβ_lt).mul_left M
    _ = M * ∑' τ : ℕ, β ^ τ := tsum_mul_left
    _ = M * (1 - β)⁻¹ := by rw [tsum_geometric_of_lt_one hβ_nonneg hβ_lt]
    _ = M / (1 - β) := by ring

/-- Any bounded `V` satisfying the Bellman equation against payoffs `X` agrees with the canonical
present value. -/
theorem presentValue_unique (P : FiniteMarkovChain α) (β : ℝ)
    (hβ_nonneg : 0 ≤ β) (hβ_lt : β < 1) (X : AdaptedProcess α)
    {M : ℝ} (hX : X.Bounded M)
    (V : (t : ℕ) → History α t → ℝ)
    (hV_bdd : ∃ K : ℝ, ∀ t h, |V t h| ≤ K)
    (hV_bell : ∀ t h, V t h = X.val t h
                + β * ∑ s' : α, (P.transition h.lastNode) s' * V (t + 1) (h.extend s')) :
    ∀ t h, V t h = presentValue P β X t h := by
  -- The difference `W = V - PV` is a bounded fixed point of the discounted
  -- averaging operator, hence vanishes.
  obtain ⟨K, hK⟩ := hV_bdd
  set W : (t : ℕ) → History α t → ℝ :=
    fun t h => V t h - presentValue P β X t h with hW_def
  -- Bellman residual identity for `W`.
  have hW_bell : ∀ t h, W t h
      = β * ∑ s' : α, (P.transition h.lastNode) s' * W (t + 1) (h.extend s') := by
    intro t h
    have hV := hV_bell t h
    have hPV := presentValue_bellman P β hβ_nonneg hβ_lt X hX t h
    have hsum_eq :
        ∑ s' : α, (P.transition h.lastNode) s' * W (t + 1) (h.extend s')
          = (∑ s' : α, (P.transition h.lastNode) s' * V (t + 1) (h.extend s'))
            - ∑ s' : α, (P.transition h.lastNode) s' *
                presentValue P β X (t + 1) (h.extend s') := by
      simp only [hW_def, mul_sub, Finset.sum_sub_distrib]
    change V t h - presentValue P β X t h
        = β * ∑ s' : α, (P.transition h.lastNode) s' * W (t + 1) (h.extend s')
    rw [hsum_eq, mul_sub, hV, hPV]
    ring
  -- Pointwise bound on `W`.
  set K' : ℝ := K + M / (1 - β) with hK'_def
  have hW_bdd : ∀ t h, |W t h| ≤ K' := by
    intro t h
    have hV_bd : |V t h| ≤ K := hK t h
    have hPV_bd : |presentValue P β X t h| ≤ M / (1 - β) :=
      presentValue_bounded P β hβ_nonneg hβ_lt X hX t h
    have : |W t h| ≤ |V t h| + |presentValue P β X t h| := by
      simp only [hW_def]; exact abs_sub _ _
    linarith
  -- Inductive sharpening: `|W t h| ≤ β^n * K'` for every `n`.
  have hW_pow : ∀ n t h, |W t h| ≤ β ^ n * K' := by
    intro n
    induction n with
    | zero => intro t h; simpa using hW_bdd t h
    | succ n ih =>
      intro t h
      rw [hW_bell t h, abs_mul, abs_of_nonneg hβ_nonneg]
      have hsum_bd :
          |∑ s' : α, (P.transition h.lastNode) s' * W (t + 1) (h.extend s')|
            ≤ β ^ n * K' := by
        calc |∑ s' : α, (P.transition h.lastNode) s' * W (t + 1) (h.extend s')|
            ≤ ∑ s' : α, |(P.transition h.lastNode) s' * W (t + 1) (h.extend s')| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ s' : α, (P.transition h.lastNode) s' * |W (t + 1) (h.extend s')| := by
              refine Finset.sum_congr rfl fun s' _ => ?_
              rw [abs_mul, abs_of_nonneg ((P.transition h.lastNode).nonneg s')]
          _ ≤ ∑ s' : α, (P.transition h.lastNode) s' * (β ^ n * K') := by
              refine Finset.sum_le_sum fun s' _ => ?_
              exact mul_le_mul_of_nonneg_left (ih _ _) ((P.transition h.lastNode).nonneg s')
          _ = β ^ n * K' := by
              rw [← Finset.sum_mul, (P.transition h.lastNode).sum_one, one_mul]
      have := mul_le_mul_of_nonneg_left hsum_bd hβ_nonneg
      calc β * |∑ s' : α, (P.transition h.lastNode) s' * W (t + 1) (h.extend s')|
          ≤ β * (β ^ n * K') := this
        _ = β ^ (n + 1) * K' := by ring
  -- Pass to the limit `n → ∞`.
  intro t h
  have hW_zero : W t h = 0 := by
    have habs_le : |W t h| ≤ 0 := by
      have hpow : Filter.Tendsto (fun n : ℕ => β ^ n * K') Filter.atTop (nhds 0) := by
        have := tendsto_pow_atTop_nhds_zero_of_lt_one hβ_nonneg hβ_lt
        simpa using this.mul_const K'
      refine ge_of_tendsto hpow ?_
      filter_upwards with n
      exact hW_pow n t h
    have h0 : 0 ≤ |W t h| := abs_nonneg _
    have habs_eq : |W t h| = 0 := le_antisymm habs_le h0
    exact abs_eq_zero.mp habs_eq
  have : V t h - presentValue P β X t h = 0 := hW_zero
  linarith

/-- Pointwise monotonicity of payoffs lifts to monotonicity of the present value. -/
theorem presentValue_mono (P : FiniteMarkovChain α) (β : ℝ)
    (hβ_nonneg : 0 ≤ β) (hβ_lt : β < 1) (X Y : AdaptedProcess α)
    {M : ℝ} (hX : X.Bounded M) (hY : Y.Bounded M)
    (hXY : ∀ t (h : History α t), X.val t h ≤ Y.val t h)
    (t : ℕ) (h : History α t) :
    presentValue P β X t h ≤ presentValue P β Y t h := by
  unfold presentValue
  refine Summable.tsum_le_tsum (fun τ => ?_)
    (presentValue_summable P β hβ_nonneg hβ_lt X hX t h)
    (presentValue_summable P β hβ_nonneg hβ_lt Y hY t h)
  exact mul_le_mul_of_nonneg_left (iterCondExp_mono P hXY τ t h)
    (pow_nonneg hβ_nonneg τ)

/-- The present value is itself an adapted process. -/
noncomputable def presentValue.adapted (P : FiniteMarkovChain α) (β : ℝ)
    (X : AdaptedProcess α) : AdaptedProcess α :=
  ⟨fun t h => presentValue P β X t h⟩

@[simp] theorem presentValue.adapted_val (P : FiniteMarkovChain α) (β : ℝ)
    (X : AdaptedProcess α) (t : ℕ) (h : History α t) :
    (presentValue.adapted P β X).val t h = presentValue P β X t h := rfl

end Econlib.Probability
