/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.DynamicProgramming.Budget.StochasticBudgetDP
public import Econlib.Optimization.DynamicProgramming.Core.Weighted

/-!
# Weighted value function for the generic stochastic budget DP (unbounded rewards)

The Blackwell **sup-norm** layer of `StochBudgetData` (`bddValueFunction`) requires a globally
bounded reward, which excludes unbounded payoffs such as `log` or CRRA utility. For those the value
function is itself unbounded on the unbounded continuous state, so the fixed point is represented
in a **weighted** space.

This file lifts the weighted Blackwell theory of
`Econlib.Optimization.DynamicProgramming.Core.Weighted` onto the generic `StochBudgetData` layer,
exactly once, taking the model-specific weight-growth and reward bounds as hypotheses. It mirrors
`WeightedCollateralDP` but at the generic level: The collateral file's `sum_trans_weight_le` (the
successor-weight bound) and `collateralBellman_weightedBounded` (the maps-weighted-bounded
discharge) are precisely the data that `h_succ` and `h_reward` abstract over here.

The construction is the classical Boyd / Stokey–Lucas weighted-contraction argument:

* **Successor-weight growth** `h_succ`: Along the budget set, the expected next-period weight grows
  by at most the factor `μ`, i.e. `Σ_{s'} π(s,s') ω(f a s', s') ≤ μ · ω(w, s)`.
* **Reward growth** `h_reward`: The reward is weight-bounded along the budget set,
  `|reward a| ≤ C · ω(w, s)`.
* **Contraction modulus** `β·μ < 1`: With these two bounds the generic Bellman operator is a
  weighted Blackwell operator of modulus `β·μ`, and `Weighted.fixedPointCertificate` delivers the
  unique weighted-bounded fixed point with no external Banach hypothesis.

## Main definitions

* `StochBudgetData.toWeightedBlackwell` — `bellmanOp` as a `WeightedBlackwell` operator of modulus
  `β·μ`
* `StochBudgetData.weightedValueFunction` — the unique weighted-bounded fixed point

## Main statements

* `StochBudgetData.weightedValueFunction_isFixedPt` — it solves the stochastic Bellman equation
* `StochBudgetData.weightedValueFunction_weightedBounded` — it is weighted bounded
* `StochBudgetData.weightedValueFunction_unique` — uniqueness among weighted-bounded fixed points
* `StochBudgetData.weightedValueFunction_hasDecreasingDifferences` — the weighted fixed point has
  decreasing differences, given the lattice rearrangement bound on every weighted-bounded iterate

## Tags

dynamic programing, stochastic, weighted norm, boyd, unbounded reward, bellman equation
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

open Filter Topology

namespace StochBudgetData

variable {n : ℕ} {A : Type*} (M : StochBudgetData n A)

/-! ### Weighted continuation and Bellman-set bounds -/

/-- **Weighted continuation bound.** Along the budget set, the continuation term
`β · Σ π v(f a s', s')` is bounded in absolute value by `β · Bv · μ · ω(w, s)`, whenever
`|v p| ≤ Bv · ω p`. The weighted analog of `abs_continuation_le`, built on `h_succ`. -/
lemma abs_continuation_weighted_le (ω : Weight (ℝ × Fin n)) {μ : ℝ}
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        ∑ s', M.trans s s' * ω (M.f a s', s') ≤ μ * ω (w, s))
    {v : ℝ × Fin n → ℝ} {Bv : ℝ} (hBv0 : 0 ≤ Bv)
    (hBv : ∀ p, |v p| ≤ Bv * ω p) {w : ℝ} {s : Fin n} {a : A} (ha : a ∈ M.Γ w s) :
    |M.β * ∑ s', M.trans s s' * v (M.f a s', s')| ≤ M.β * (Bv * (μ * ω (w, s))) := by
  rw [abs_mul, abs_of_nonneg M.β_nonneg]
  apply mul_le_mul_of_nonneg_left _ M.β_nonneg
  calc |∑ s', M.trans s s' * v (M.f a s', s')|
      ≤ ∑ s', |M.trans s s' * v (M.f a s', s')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', M.trans s s' * (Bv * ω (M.f a s', s')) := by
        apply Finset.sum_le_sum
        intro s' _
        rw [abs_mul, abs_of_nonneg (M.trans_nonneg s s')]
        exact mul_le_mul_of_nonneg_left (hBv _) (M.trans_nonneg s s')
    _ = Bv * ∑ s', M.trans s s' * ω (M.f a s', s') := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s' _; ring
    _ ≤ Bv * (μ * ω (w, s)) :=
        mul_le_mul_of_nonneg_left (h_succ w s a ha) hBv0

/-- **The weighted Bellman set is bounded above.** Every feasible objective is bounded by
`(C₀ + β · Bv · μ) · ω(w, s)` for `C₀ = max 0 C`, so the Bellman set is bounded above at each state
— the weighted analog of `bellmanSet_bddAbove`. The `max 0 C` is harmless (it only weakens the
bound) and keeps the constant nonnegative, as `WeightedBounded` requires. -/
lemma bellmanSet_bddAbove_weighted (ω : Weight (ℝ × Fin n)) {μ C : ℝ}
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        ∑ s', M.trans s s' * ω (M.f a s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        |M.reward a| ≤ C * ω (w, s))
    {v : ℝ × Fin n → ℝ} {Bv : ℝ} (hBv0 : 0 ≤ Bv)
    (hBv : ∀ p, |v p| ≤ Bv * ω p) (st : ℝ × Fin n) :
    BddAbove (M.bellmanSet v st) := by
  refine ⟨(max 0 C + M.β * Bv * μ) * ω st, ?_⟩
  rintro r ⟨a, ha, rfl⟩
  -- Reward bound via `h_reward` (relaxed to `max 0 C`), continuation via the weighted bound.
  have hrew : M.reward a ≤ max 0 C * ω st := by
    have h1 : M.reward a ≤ C * ω st :=
      (le_abs_self _).trans (by simpa using h_reward st.1 st.2 a ha)
    have h2 : C * ω st ≤ max 0 C * ω st :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (ω.pos st).le
    linarith
  have hcont : M.β * ∑ s', M.trans st.2 s' * v (M.f a s', s') ≤ M.β * (Bv * (μ * ω st)) :=
    (le_abs_self _).trans
      (by simpa using M.abs_continuation_weighted_le ω h_succ hBv0 hBv ha)
  nlinarith [hrew, hcont]

/-! ### The weighted Blackwell operator -/

/-- **`bellmanOp` is a weighted Blackwell operator** of modulus `β·μ`. The successor-weight growth
`h_succ` and the reward growth `h_reward` are the only model-specific inputs; they replace the
sup-norm reward bound of the bounded layer. -/
noncomputable def toWeightedBlackwell [NeZero n] [Nonempty A]
    (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : M.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        ∑ s', M.trans s s' * ω (M.f a s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        |M.reward a| ≤ C * ω (w, s)) :
    WeightedBlackwell ω M.bellmanOp (M.β * μ) where
  beta_nonneg := mul_nonneg M.β_nonneg hμ
  beta_lt_one := hβμ
  maps_weightedBounded := by
    rintro v ⟨Bv, hBv0, hBv⟩
    -- Bound constant `max 0 C + β·Bv·μ ≥ 0`: reward term (relaxed to `max 0 C`) plus the discounted
    -- continuation modulus.
    have hcont_nonneg : 0 ≤ M.β * Bv * μ :=
      mul_nonneg (mul_nonneg M.β_nonneg hBv0) hμ
    refine ⟨max 0 C + M.β * Bv * μ, by have := le_max_left (0 : ℝ) C; linarith, fun st => ?_⟩
    have hconst_nonneg : 0 ≤ (max 0 C + M.β * Bv * μ) * ω st :=
      mul_nonneg (by have := le_max_left (0 : ℝ) C; linarith) (ω.pos st).le
    rw [bellmanOp_eq_sSup, abs_le]
    rcases (M.Γ st.1 st.2).eq_empty_or_nonempty with hΓ | hΓ
    · -- Empty budget ⇒ sSup ∅ = 0, in the symmetric bound (RHS ≥ 0).
      rw [M.bellmanSet_eq_empty v hΓ, Real.sSup_empty]
      exact ⟨by linarith, by linarith⟩
    · have hne := M.bellmanSet_nonempty v hΓ
      have hbdd := M.bellmanSet_bddAbove_weighted ω h_succ h_reward hBv0 hBv st
      -- Each feasible objective lies in `[-(C₀·ω), C₀·ω]` (`C₀ = max 0 C + β·Bv·μ`).
      have hbound : ∀ r ∈ M.bellmanSet v st, |r| ≤ (max 0 C + M.β * Bv * μ) * ω st := by
        rintro r ⟨a, ha, rfl⟩
        have hrew : |M.reward a| ≤ max 0 C * ω st := by
          refine (h_reward st.1 st.2 a (by simpa using ha)).trans ?_
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (ω.pos st).le
        have hcont :
            |M.β * ∑ s', M.trans st.2 s' * v (M.f a s', s')| ≤ M.β * (Bv * (μ * ω st)) := by
          simpa using M.abs_continuation_weighted_le ω h_succ hBv0 hBv (by simpa using ha)
        calc |M.reward a + M.β * ∑ s', M.trans st.2 s' * v (M.f a s', s')|
            ≤ |M.reward a| + |M.β * ∑ s', M.trans st.2 s' * v (M.f a s', s')| := abs_add_le _ _
          _ ≤ max 0 C * ω st + M.β * (Bv * (μ * ω st)) := add_le_add hrew hcont
          _ = (max 0 C + M.β * Bv * μ) * ω st := by ring
      obtain ⟨r₀, hr₀⟩ := hne
      refine ⟨?_, csSup_le ⟨r₀, hr₀⟩ fun r hr => (le_abs_self r).trans (hbound r hr)⟩
      exact le_trans (neg_le_of_abs_le (hbound r₀ hr₀)) (le_csSup hbdd hr₀)
  monotone := by
    rintro v w ⟨Bv, hBv0, hBv⟩ ⟨Bw, hBw0, hBw⟩ hvw st
    rw [bellmanOp_eq_sSup, bellmanOp_eq_sSup]
    rcases (M.Γ st.1 st.2).eq_empty_or_nonempty with hΓ | hΓ
    · rw [M.bellmanSet_eq_empty v hΓ, M.bellmanSet_eq_empty w hΓ]
    · apply csSup_le (M.bellmanSet_nonempty v hΓ)
      rintro r ⟨a, ha, rfl⟩
      -- The `v`-objective at `a` is ≤ its `w`-value (monotone continuation), ≤ sSup (w-set).
      refine le_trans ?_ (le_csSup (M.bellmanSet_bddAbove_weighted ω h_succ h_reward hBw0 hBw st)
        (M.mem_bellmanSet ha))
      have hcont :
          ∑ s', M.trans st.2 s' * v (M.f a s', s') ≤
            ∑ s', M.trans st.2 s' * w (M.f a s', s') := by
        apply Finset.sum_le_sum
        intro s' _
        exact mul_le_mul_of_nonneg_left (hvw _) (M.trans_nonneg st.2 s')
      have := mul_le_mul_of_nonneg_left hcont M.β_nonneg
      linarith
  discounting := by
    rintro v c ⟨Bv, hBv0, hBv⟩ hc st
    rw [bellmanOp_eq_sSup, bellmanOp_eq_sSup]
    rcases (M.Γ st.1 st.2).eq_empty_or_nonempty with hΓ | hΓ
    · -- Both budgets empty ⇒ both sSups are 0; the goal `0 ≤ 0 + (β·μ)·c·ω` holds.
      rw [M.bellmanSet_eq_empty (fun p => v p + c * ω p) hΓ, M.bellmanSet_eq_empty v hΓ,
        Real.sSup_empty]
      have hμc : 0 ≤ M.β * μ * c * ω st :=
        mul_nonneg (mul_nonneg (mul_nonneg M.β_nonneg hμ) hc) (ω.pos st).le
      linarith
    · apply csSup_le (M.bellmanSet_nonempty (fun p => v p + c * ω p) hΓ)
      rintro r ⟨a, ha, rfl⟩
      -- The perturbed objective at `a` splits as `[v-objective at a] + β·c·(Σ π ω(f a s'))`.
      have hsum :
          ∑ s', M.trans st.2 s' * (v (M.f a s', s') + c * ω (M.f a s', s')) =
            (∑ s', M.trans st.2 s' * v (M.f a s', s')) +
            c * (∑ s', M.trans st.2 s' * ω (M.f a s', s')) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro s' _; ring
      have hsum_split :
          M.reward a + M.β *
              ∑ s', M.trans st.2 s' * ((fun p => v p + c * ω p) (M.f a s', s')) =
            (M.reward a + M.β * ∑ s', M.trans st.2 s' * v (M.f a s', s')) +
            M.β * c * (∑ s', M.trans st.2 s' * ω (M.f a s', s')) := by
        simp only [hsum]; ring
      rw [hsum_split]
      -- The v-objective at `a` is ≤ sSup (v-set) = T v st.
      have hle_v := le_csSup (M.bellmanSet_bddAbove_weighted ω h_succ h_reward hBv0 hBv st)
        (M.mem_bellmanSet (v := v) ha)
      -- The weight term ≤ μ·ω(st), scaled by `β·c ≥ 0`.
      have hβc_nonneg : 0 ≤ M.β * c := mul_nonneg M.β_nonneg hc
      have hweight_scaled :
          M.β * c * (∑ s', M.trans st.2 s' * ω (M.f a s', s')) ≤
            M.β * c * (μ * ω st) :=
        mul_le_mul_of_nonneg_left (by simpa using h_succ st.1 st.2 a (by simpa using ha))
          hβc_nonneg
      nlinarith [hle_v, hweight_scaled]

/-! ### The weighted value function -/

/-- The **weighted value function** of the generic stochastic budget DP: The unique
weighted-bounded fixed point of the stochastic Bellman operator. Defined for *any*
`StochBudgetData` whose reward and successor-weight growth satisfy the weighted bounds, in
particular for unbounded rewards such as `log` or CRRA. -/
noncomputable def weightedValueFunction [NeZero n] [Nonempty A]
    (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : M.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        ∑ s', M.trans s s' * ω (M.f a s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        |M.reward a| ≤ C * ω (w, s)) : ℝ × Fin n → ℝ :=
  (WeightedBlackwell.fixedPointCertificate
    (M.toWeightedBlackwell ω hμ hβμ h_succ h_reward)).value

/-- The weighted value function is weighted-bounded. -/
theorem weightedValueFunction_weightedBounded [NeZero n] [Nonempty A]
    (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : M.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        ∑ s', M.trans s s' * ω (M.f a s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        |M.reward a| ≤ C * ω (w, s)) :
    WeightedBounded ω (M.weightedValueFunction ω hμ hβμ h_succ h_reward) :=
  (WeightedBlackwell.fixedPointCertificate
    (M.toWeightedBlackwell ω hμ hβμ h_succ h_reward)).weighted_bounded

/-- The weighted value function solves the stochastic Bellman equation. -/
theorem weightedValueFunction_isFixedPt [NeZero n] [Nonempty A]
    (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : M.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        ∑ s', M.trans s s' * ω (M.f a s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        |M.reward a| ≤ C * ω (w, s)) (st : ℝ × Fin n) :
    M.weightedValueFunction ω hμ hβμ h_succ h_reward st =
      M.bellmanOp (M.weightedValueFunction ω hμ hβμ h_succ h_reward) st :=
  (WeightedBlackwell.fixedPointCertificate
    (M.toWeightedBlackwell ω hμ hβμ h_succ h_reward)).fixed st

/-- **Uniqueness** among weighted-bounded fixed points. -/
theorem weightedValueFunction_unique [NeZero n] [Nonempty A]
    (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : M.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        ∑ s', M.trans s s' * ω (M.f a s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        |M.reward a| ≤ C * ω (w, s))
    (w : ℝ × Fin n → ℝ) (hw : WeightedBounded ω w)
    (hwfix : ∀ st, w st = M.bellmanOp w st) :
    w = M.weightedValueFunction ω hμ hβμ h_succ h_reward :=
  (WeightedBlackwell.fixedPointCertificate
    (M.toWeightedBlackwell ω hμ hβμ h_succ h_reward)).unique w hw hwfix

/-! ### Decreasing differences for the weighted fixed point -/

/-- **The weighted fixed point has decreasing differences.** Routed through the weighted iterates
`iter bellmanOp k` (from zero): Each iterate is weighted bounded (`iter_weightedBounded`) and, by
induction, has decreasing differences — the base case is the zero function, and the inductive step
applies `bellmanOp_preserves_submodular` to the previous iterate. The lattice rearrangement bound
`h_rearrange_all` must hold for every weighted-bounded function with decreasing differences (each
iterate is such a function). The fixed point is the pointwise limit of the iterates
(`iter_tendsto_fixedPoint`), and `HasDecreasingDifferences.of_pointwise_tendsto` transfers the
property to the limit. -/
theorem weightedValueFunction_hasDecreasingDifferences [NeZero n] [Nonempty A]
    (ω : Weight (ℝ × Fin n)) {μ C : ℝ} (hμ : 0 ≤ μ) (hβμ : M.β * μ < 1)
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        ∑ s', M.trans s s' * ω (M.f a s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M.Γ w s →
        |M.reward a| ≤ C * ω (w, s))
    (hΓ_ne : ∀ (s : Fin n) ⦃w : ℝ⦄, 0 < w → (M.Γ w s).Nonempty)
    (h_rearrange_all : ∀ v : ℝ × Fin n → ℝ, WeightedBounded ω v → HasDecreasingDifferences v →
        (∀ (w₁ w₂ : ℝ) (s₁ s₂ : Fin n), w₁ ≤ w₂ → s₁ ≤ s₂ →
          ∀ a₁ ∈ M.Γ w₁ s₁, ∀ b₂ ∈ M.Γ w₂ s₂,
          (M.reward a₁ + M.β * ∑ s', M.trans s₁ s' * v (M.f a₁ s', s')) +
            (M.reward b₂ + M.β * ∑ s', M.trans s₂ s' * v (M.f b₂ s', s')) ≤
          M.bellmanOp v (w₂, s₁) + M.bellmanOp v (w₁, s₂))) :
    HasDecreasingDifferences (M.weightedValueFunction ω hμ hβμ h_succ h_reward) := by
  set H := M.toWeightedBlackwell ω hμ hβμ h_succ h_reward with hH
  -- Every iterate has decreasing differences, by induction on `k`.
  have h_iter_dd : ∀ k, HasDecreasingDifferences (WeightedBlackwell.iter M.bellmanOp k) := by
    intro k
    induction k with
    | zero =>
      -- `iter 0 = 0`, which trivially has decreasing differences.
      rw [WeightedBlackwell.iter_zero]
      intro w₁ w₂ s₁ s₂ _ _ _; simp
    | succ k ih =>
      -- `iter (k+1) = bellmanOp (iter k)`; apply the preservation lemma to `iter k`.
      rw [WeightedBlackwell.iter_succ]
      have hbdd_k : WeightedBounded ω (WeightedBlackwell.iter M.bellmanOp k) :=
        WeightedBlackwell.iter_weightedBounded H k
      exact M.bellmanOp_preserves_submodular _ hΓ_ne
        (h_rearrange_all _ hbdd_k ih)
  -- The fixed point is the pointwise limit of the iterates; transfer decreasing differences.
  apply HasDecreasingDifferences.of_pointwise_tendsto h_iter_dd
  intro p
  exact WeightedBlackwell.iter_tendsto_fixedPoint H p

/-! ### Monotone comparative statics of the weighted value function

A keep-side parameter that enlarges the budget set raises the weighted value function. The
engine is `WeightedBlackwell.fixedPoint_le_of_operator_le`: An ordered pair of weighted-discounting
operators has ordered weighted-bounded fixed points. This is the unbounded-reward analog of the
bounded-layer `bellmanOp_le_of_bellmanSet_subset` / `optionValueFunction_mono_of_bellmanOp_le`. -/

/-- **Keep-operator order from budget inclusion (weighted layer).** If at `(v, st)` every feasible
objective for `M₁` is feasible for `M₂` (`bellmanSet` inclusion) and `M₁`'s set is nonempty, then
`M₁`'s Bellman value is dominated by `M₂`'s. The weighted analog of
`bellmanOp_le_of_bellmanSet_subset`: `M₂`'s Bellman set is bounded above by the weighted bound
(`bellmanSet_bddAbove_weighted`), so unbounded rewards (log, CRRA) are admissible. -/
lemma bellmanOp_le_of_bellmanSet_subset_weighted {M₁ M₂ : StochBudgetData n A}
    (ω : Weight (ℝ × Fin n)) {μ C : ℝ}
    (h_succ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M₂.Γ w s →
        ∑ s', M₂.trans s s' * ω (M₂.f a s', s') ≤ μ * ω (w, s))
    (h_reward : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M₂.Γ w s →
        |M₂.reward a| ≤ C * ω (w, s))
    {v : ℝ × Fin n → ℝ} {Bv : ℝ} (hBv0 : 0 ≤ Bv) (hBv : ∀ p, |v p| ≤ Bv * ω p)
    {st : ℝ × Fin n} (h_ne : (M₁.bellmanSet v st).Nonempty)
    (h_sub : M₁.bellmanSet v st ⊆ M₂.bellmanSet v st) :
    M₁.bellmanOp v st ≤ M₂.bellmanOp v st :=
  csSup_le_csSup (M₂.bellmanSet_bddAbove_weighted ω h_succ h_reward hBv0 hBv st) h_ne h_sub

/-- **Weighted value function monotone in a keep-side parameter.** If `M₂`'s Bellman value
dominates `M₁`'s at `M₁`'s weighted value function (`h_op` — supplied by
`bellmanOp_le_of_bellmanSet_subset_weighted` under budget inclusion), then the whole weighted value
function rises: `V₁ ≤ V₂`. The weighted analog of `optionValueFunction_mono_of_bellmanOp_le`. -/
theorem weightedValueFunction_mono_of_bellmanOp_le [NeZero n] [Nonempty A]
    {M₁ M₂ : StochBudgetData n A} (ω : Weight (ℝ × Fin n)) {μ₁ C₁ μ₂ C₂ : ℝ}
    (hμ₁ : 0 ≤ μ₁) (hβμ₁ : M₁.β * μ₁ < 1)
    (h_succ₁ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M₁.Γ w s →
        ∑ s', M₁.trans s s' * ω (M₁.f a s', s') ≤ μ₁ * ω (w, s))
    (h_reward₁ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M₁.Γ w s →
        |M₁.reward a| ≤ C₁ * ω (w, s))
    (hμ₂ : 0 ≤ μ₂) (hβμ₂ : M₂.β * μ₂ < 1)
    (h_succ₂ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M₂.Γ w s →
        ∑ s', M₂.trans s s' * ω (M₂.f a s', s') ≤ μ₂ * ω (w, s))
    (h_reward₂ : ∀ (w : ℝ) (s : Fin n) (a : A), a ∈ M₂.Γ w s →
        |M₂.reward a| ≤ C₂ * ω (w, s))
    (h_op : ∀ st, M₁.bellmanOp (M₁.weightedValueFunction ω hμ₁ hβμ₁ h_succ₁ h_reward₁) st ≤
        M₂.bellmanOp (M₁.weightedValueFunction ω hμ₁ hβμ₁ h_succ₁ h_reward₁) st) :
    ∀ st, M₁.weightedValueFunction ω hμ₁ hβμ₁ h_succ₁ h_reward₁ st ≤
        M₂.weightedValueFunction ω hμ₂ hβμ₂ h_succ₂ h_reward₂ st :=
  (M₂.toWeightedBlackwell ω hμ₂ hβμ₂ h_succ₂ h_reward₂).fixedPoint_le_of_operator_le
    (T₁ := M₁.bellmanOp)
    (M₁.weightedValueFunction_weightedBounded ω hμ₁ hβμ₁ h_succ₁ h_reward₁)
    (M₂.weightedValueFunction_weightedBounded ω hμ₂ hβμ₂ h_succ₂ h_reward₂)
    (M₁.weightedValueFunction_isFixedPt ω hμ₁ hβμ₁ h_succ₁ h_reward₁)
    (M₂.weightedValueFunction_isFixedPt ω hμ₂ hβμ₂ h_succ₂ h_reward₂)
    h_op

end StochBudgetData

end Econlib.Optimization.DynamicProgramming
