/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.Convex.ConcaveOn
public import Econlib.Math.Order.CsSup
public import Econlib.Optimization.DynamicProgramming.Core.Bellman
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Generic stochastic budget dynamic programing

A stochastic Bellman operator on the mixed state `ℝ × Fin n` (a continuous component, e.g. net
worth, times a finite shock), parametrized by an arbitrary action type `A` and three model data:

* a **reward** `reward : A → ℝ` (the per-period payoff, e.g. `u c`),
* a **law of motion** `f : A → Fin n → ℝ` giving the next-period continuous state as a function of
  the chosen action and the realized next shock `s'`,
* a **budget correspondence** `Γ : ℝ → Fin n → Set A` (feasible actions at `(w, s)`).

The operator is `(Tv)(w, s) = sup_{a ∈ Γ(w, s)} [reward a + β Σ_{s'} π(s, s') v(f a s', s')]`.

This is the shared structure underlying the collateral consumption-savings model (`CollateralDP`,
one state-contingent instrument) and the two-instrument insurance model (`InsuranceDP`, a capped
private margin plus an uncapped public instrument): Both differ only in their `Γ` and `f`. The
Blackwell theory (monotonicity, discounting, boundedness, the sup-norm contraction, and the unique
bounded fixed point) is proved here **once** and reused by instantiation rather than re-derived per
model.

The continuation evaluates the value at the *shock-dependent* next state `(f a s', s')`, which no
existing generic operator captures: `Stochastic.finiteBellmanOperator` carries a purely finite next
state, and `ParametricDP.DiscreteContDP` carries a deterministic transition. This file fills that
gap.

## Main definitions

* `StochBudgetData n A` — the primitives `(β, trans, reward, f, Γ)` with the discount and
  row-stochastic conditions
* `StochBudgetData.bellmanSet` / `StochBudgetData.bellmanOp` — the canonical objective set and the
  stochastic Bellman operator
* `StochBudgetData.bddValueFunction` — the unique uniformly bounded fixed point (bounded-reward
  layer)

## Main statements

* `StochBudgetData.bellmanOp_monotone` / `bellmanOp_discounting` / `bellmanOp_bounded` —
  Blackwell's conditions
* `StochBudgetData.bellmanOp_apply_abs_sub_le` — the sup-norm contraction estimate
* `StochBudgetData.contractingWith_liftBellmanOp` — the lifted operator is a Banach contraction
* `StochBudgetData.existsUnique_bdd_fixedPoint` — unique uniformly bounded fixed point
* `StochBudgetData.feasible_value_le` — feasibility ⇒ Bellman inequality at the fixed point

## Tags

dynamic programing, stochastic, Bellman operator, budget correspondence, Blackwell, contraction
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

open Blackwell Filter Topology Set

/-! ### Decreasing differences (value-level submodularity)

A value-level characterization of antitone marginal, stated without derivatives — hence
preserved by uniform limits, which is what the closed-invariant-set argument needs. It is a
property of the value function alone, independent of the operator, so it lives at the namespace
level. -/

/-- The wealth increment `v(w₂, s) − v(w₁, s)` is antitone in `s`, on the **positive** domain
`0 < w₁ ≤ w₂`. Equivalent to antitone derivative for concave differentiable functions, but stated
without derivatives — hence preserved by uniform limits.

The positivity guard `0 < w₁` matters for the stochastic budget operator: At `w < 0` the budget set
is empty and `bellmanOp v (w, ·) = 0`, so decreasing differences over the whole line fails at the
budget boundary. The economically relevant — and `T`-invariant — domain is `w > 0`. -/
def HasDecreasingDifferences {n : ℕ} (v : ℝ × Fin n → ℝ) : Prop :=
  ∀ (w₁ w₂ : ℝ) (s₁ s₂ : Fin n), 0 < w₁ → w₁ ≤ w₂ → s₁ ≤ s₂ →
    v (w₂, s₂) - v (w₁, s₂) ≤ v (w₂, s₁) - v (w₁, s₁)

/-- Decreasing differences is preserved by pointwise limits of sequences. -/
theorem HasDecreasingDifferences.of_pointwise_tendsto {n : ℕ}
    {v : ℕ → ℝ × Fin n → ℝ} {v_lim : ℝ × Fin n → ℝ}
    (hv : ∀ k, HasDecreasingDifferences (v k))
    (h_lim : ∀ p, Tendsto (fun k => v k p) atTop (𝓝 (v_lim p))) :
    HasDecreasingDifferences v_lim := by
  intro w₁ w₂ s₁ s₂ hw0 hw hs
  exact le_of_tendsto_of_tendsto
    ((h_lim (w₂, s₂)).sub (h_lim (w₁, s₂)))
    ((h_lim (w₂, s₁)).sub (h_lim (w₁, s₁)))
    (Eventually.of_forall fun k => hv k w₁ w₂ s₁ s₂ hw0 hw hs)

/-- Decreasing differences implies antitone derivative: If `v` is submodular and differentiable in
`w`, then `w ↦ v_w(w, s)` is antitone in `s`, for `w > 0`. -/
theorem HasDecreasingDifferences.antitone_deriv {n : ℕ}
    {v : ℝ × Fin n → ℝ} (hsub : HasDecreasingDifferences v) {w : ℝ} (hw : 0 < w)
    (hdiff : ∀ s : Fin n, DifferentiableAt ℝ (fun w' => v (w', s)) w) :
    Antitone (fun s => deriv (fun w' => v (w', s)) w) := by
  intro s₁ s₂ hs
  have ht₁ := (hasDerivAt_iff_tendsto_slope_left_right.mp (hdiff s₁).hasDerivAt).2
  have ht₂ := (hasDerivAt_iff_tendsto_slope_left_right.mp (hdiff s₂).hasDerivAt).2
  -- For `y > w > 0`, decreasing differences gives slope(s₂) ≤ slope(s₁).
  have h_ord : ∀ᶠ y in 𝓝[>] w,
      slope (fun w' => v (w', s₂)) w y ≤ slope (fun w' => v (w', s₁)) w y := by
    filter_upwards [self_mem_nhdsWithin] with y (hy : w < y)
    simp only [slope_def_field]
    exact div_le_div_of_nonneg_right
      (hsub w y s₁ s₂ hw (le_of_lt hy) hs) (sub_nonneg.mpr (le_of_lt hy))
  exact le_of_tendsto_of_tendsto ht₂ ht₁ h_ord

/-- Primitives of a generic stochastic budget DP on the mixed state `ℝ × Fin n`: A discount factor
`β ∈ [0, 1)`, a row-stochastic shock transition `trans`, a per-period `reward`, an action-and-shock
law of motion `f`, and a budget correspondence `Γ`. -/
structure StochBudgetData (n : ℕ) (A : Type*) where
  /-- Discount factor. -/
  β : ℝ
  /-- Discount factor is non-negative. -/
  β_nonneg : 0 ≤ β
  /-- Discount factor is strictly less than one. -/
  β_lt_one : β < 1
  /-- Markov transition matrix for the discrete shock. -/
  trans : Fin n → Fin n → ℝ
  /-- Transition entries are non-negative. -/
  trans_nonneg : ∀ s s', 0 ≤ trans s s'
  /-- Each row of the transition matrix sums to one. -/
  trans_sum_one : ∀ s, ∑ s', trans s s' = 1
  /-- Per-period reward as a function of the action. -/
  reward : A → ℝ
  /-- Law of motion: Next-period continuous state given action `a` and realized next shock `s'`. -/
  f : A → Fin n → ℝ
  /-- Budget correspondence: Feasible actions at continuous state `w` and shock `s`. -/
  Γ : ℝ → Fin n → Set A

namespace StochBudgetData

variable {n : ℕ} {A : Type*} (M : StochBudgetData n A)

/-- The canonical Bellman objective set: One-step values over feasible actions. -/
def bellmanSet (v : ℝ × Fin n → ℝ) (st : ℝ × Fin n) : Set ℝ :=
  {r | ∃ a ∈ M.Γ st.1 st.2,
    r = M.reward a + M.β * ∑ s', M.trans st.2 s' * v (M.f a s', s')}

/-- The generic stochastic budget Bellman operator: The supremum of `bellmanSet`. -/
noncomputable def bellmanOp (v : ℝ × Fin n → ℝ) (st : ℝ × Fin n) : ℝ :=
  sSup (M.bellmanSet v st)

@[simp] lemma bellmanOp_eq_sSup (v : ℝ × Fin n → ℝ) (st : ℝ × Fin n) :
    M.bellmanOp v st = sSup (M.bellmanSet v st) := rfl

/-- A feasible action contributes its one-step objective to the Bellman set. -/
lemma mem_bellmanSet {v : ℝ × Fin n → ℝ} {st : ℝ × Fin n} {a : A}
    (ha : a ∈ M.Γ st.1 st.2) :
    M.reward a + M.β * ∑ s', M.trans st.2 s' * v (M.f a s', s') ∈ M.bellmanSet v st :=
  ⟨a, ha, rfl⟩

/-- The continuation term is bounded by `|β| · Bv` whenever `|v| ≤ Bv`. -/
lemma abs_continuation_le {v : ℝ × Fin n → ℝ} {Bv : ℝ} (hBv : ∀ p, |v p| ≤ Bv)
    (st : ℝ × Fin n) (a : A) :
    |M.β * ∑ s', M.trans st.2 s' * v (M.f a s', s')| ≤ |M.β| * Bv := by
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc |∑ s', M.trans st.2 s' * v (M.f a s', s')|
      ≤ ∑ s', |M.trans st.2 s' * v (M.f a s', s')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', M.trans st.2 s' * Bv := by
        apply Finset.sum_le_sum
        intro s' _
        rw [abs_mul, abs_of_nonneg (M.trans_nonneg st.2 s')]
        exact mul_le_mul_of_nonneg_left (hBv _) (M.trans_nonneg st.2 s')
    _ = Bv := by rw [← Finset.sum_mul, M.trans_sum_one st.2, one_mul]

/-- Each element of the Bellman set is bounded in absolute value by `Br + |β| · Bv`. -/
lemma abs_bellmanSet_le {Br Bv : ℝ} (hBr : ∀ a, |M.reward a| ≤ Br)
    {v : ℝ × Fin n → ℝ} (hBv : ∀ p, |v p| ≤ Bv)
    {st : ℝ × Fin n} {r : ℝ} (hr : r ∈ M.bellmanSet v st) :
    |r| ≤ Br + |M.β| * Bv := by
  obtain ⟨a, _, rfl⟩ := hr
  calc |M.reward a + M.β * ∑ s', M.trans st.2 s' * v (M.f a s', s')|
      ≤ |M.reward a| + |M.β * ∑ s', M.trans st.2 s' * v (M.f a s', s')| :=
        abs_add_le _ _
    _ ≤ Br + |M.β| * Bv :=
        add_le_add (hBr a) (M.abs_continuation_le hBv st a)

/-- The Bellman set is bounded above (uniformly in the state), given a reward bound and a uniform
bound on `v`. -/
lemma bellmanSet_bddAbove {Br : ℝ} (hBr : ∀ a, |M.reward a| ≤ Br)
    (v : ℝ × Fin n → ℝ) (hv_bdd : UniformBounded v) (st : ℝ × Fin n) :
    BddAbove (M.bellmanSet v st) := by
  obtain ⟨Bv, hBv⟩ := hv_bdd
  exact ⟨Br + |M.β| * Bv,
    fun r hr => (le_abs_self r).trans (M.abs_bellmanSet_le hBr hBv hr)⟩

/-- The Bellman set is nonempty whenever the budget correspondence is. -/
lemma bellmanSet_nonempty (v : ℝ × Fin n → ℝ) {st : ℝ × Fin n}
    (hΓ : (M.Γ st.1 st.2).Nonempty) : (M.bellmanSet v st).Nonempty := by
  obtain ⟨a, ha⟩ := hΓ
  exact ⟨_, M.mem_bellmanSet (v := v) ha⟩

/-- The Bellman set is empty whenever the budget correspondence is. -/
lemma bellmanSet_eq_empty (v : ℝ × Fin n → ℝ) {st : ℝ × Fin n}
    (hΓ : M.Γ st.1 st.2 = ∅) : M.bellmanSet v st = ∅ := by
  ext r
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨a, ha, rfl⟩
  rw [hΓ] at ha
  exact ha

/-- **`bellmanOp` maps bounded functions to bounded functions** (given a reward bound). -/
lemma bellmanOp_bounded [NeZero n] [Nonempty A] {Br : ℝ} (hBr : ∀ a, |M.reward a| ≤ Br)
    (v : ℝ × Fin n → ℝ) (hv_bdd : UniformBounded v) :
    UniformBounded (M.bellmanOp v) := by
  obtain ⟨Bv, hBv⟩ := hv_bdd
  have hBr_nonneg : 0 ≤ Br := le_trans (abs_nonneg _) (hBr (Classical.arbitrary A))
  have hβBv_nonneg : 0 ≤ |M.β| * Bv :=
    mul_nonneg (abs_nonneg _) (le_trans (abs_nonneg _) (hBv (0, Classical.arbitrary (Fin n))))
  refine ⟨Br + |M.β| * Bv, fun st => ?_⟩
  rw [bellmanOp_eq_sSup, abs_le]
  rcases (M.Γ st.1 st.2).eq_empty_or_nonempty with hΓ | hΓ
  · -- Empty budget ⇒ sSup ∅ = 0, which lies in the symmetric bound.
    rw [M.bellmanSet_eq_empty v hΓ, Real.sSup_empty]
    exact ⟨by linarith, by linarith⟩
  · have hne := M.bellmanSet_nonempty v hΓ
    have hbdd : BddAbove (M.bellmanSet v st) :=
      ⟨Br + |M.β| * Bv,
        fun r hr => (le_abs_self r).trans (M.abs_bellmanSet_le hBr hBv hr)⟩
    obtain ⟨r₀, hr₀⟩ := hne
    refine ⟨?_, csSup_le ⟨r₀, hr₀⟩ fun r hr =>
      (le_abs_self r).trans (M.abs_bellmanSet_le hBr hBv hr)⟩
    exact le_trans (neg_le_of_abs_le (M.abs_bellmanSet_le hBr hBv hr₀))
      (le_csSup hbdd hr₀)

/-- **Monotonicity (Blackwell condition 1).** -/
lemma bellmanOp_monotone {Br : ℝ} (hBr : ∀ a, |M.reward a| ≤ Br) (v w : ℝ × Fin n → ℝ)
    (hw_bdd : UniformBounded w) (hvw : ∀ p, v p ≤ w p) :
    ∀ st, M.bellmanOp v st ≤ M.bellmanOp w st := by
  intro st
  rw [bellmanOp_eq_sSup, bellmanOp_eq_sSup]
  rcases (M.Γ st.1 st.2).eq_empty_or_nonempty with hΓ | hΓ
  · rw [M.bellmanSet_eq_empty v hΓ, M.bellmanSet_eq_empty w hΓ]
  · apply csSup_le (M.bellmanSet_nonempty v hΓ)
    rintro r ⟨a, ha, rfl⟩
    refine le_trans ?_ (le_csSup (M.bellmanSet_bddAbove hBr w hw_bdd st)
      (M.mem_bellmanSet ha))
    have hcont :
        ∑ s', M.trans st.2 s' * v (M.f a s', s') ≤
          ∑ s', M.trans st.2 s' * w (M.f a s', s') := by
      apply Finset.sum_le_sum
      intro s' _
      exact mul_le_mul_of_nonneg_left (hvw _) (M.trans_nonneg st.2 s')
    have := mul_le_mul_of_nonneg_left hcont M.β_nonneg
    linarith

/-- **Discounting (Blackwell condition 2).** -/
lemma bellmanOp_discounting {Br : ℝ} (hBr : ∀ a, |M.reward a| ≤ Br)
    (v : ℝ × Fin n → ℝ) (c : ℝ) (hv_bdd : UniformBounded v) (hc : 0 ≤ c) :
    ∀ st, M.bellmanOp (fun p => v p + c) st ≤ M.bellmanOp v st + M.β * c := by
  intro st
  rw [bellmanOp_eq_sSup, bellmanOp_eq_sSup]
  rcases (M.Γ st.1 st.2).eq_empty_or_nonempty with hΓ | hΓ
  · rw [M.bellmanSet_eq_empty (fun p => v p + c) hΓ, M.bellmanSet_eq_empty v hΓ, Real.sSup_empty]
    have hβc : 0 ≤ M.β * c := mul_nonneg M.β_nonneg hc
    linarith
  · apply csSup_le (M.bellmanSet_nonempty (fun p => v p + c) hΓ)
    rintro r ⟨a, ha, rfl⟩
    have hsum_split :
        M.reward a + M.β * ∑ s', M.trans st.2 s' * (v (M.f a s', s') + c) =
          (M.reward a + M.β * ∑ s', M.trans st.2 s' * v (M.f a s', s')) + M.β * c := by
      have hsum :
          ∑ s', M.trans st.2 s' * (v (M.f a s', s') + c) =
            (∑ s', M.trans st.2 s' * v (M.f a s', s')) + c := by
        simp only [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, M.trans_sum_one st.2, one_mul]
      rw [hsum]; ring
    rw [hsum_split]
    have := le_csSup (M.bellmanSet_bddAbove hBr v hv_bdd st) (M.mem_bellmanSet ha)
    linarith

/-- The sup-norm contraction estimate. -/
lemma bellmanOp_apply_abs_sub_le {Br : ℝ} (hBr : ∀ a, |M.reward a| ≤ Br)
    (v w : ℝ × Fin n → ℝ) (hv_bdd : UniformBounded v) (hw_bdd : UniformBounded w)
    (st : ℝ × Fin n) :
    |M.bellmanOp v st - M.bellmanOp w st| ≤ M.β * ⨆ t, |v t - w t| :=
  Blackwell.abs_sub_le_of_monotone_discounting
    (fun a b _ hb hab => M.bellmanOp_monotone hBr a b hb hab)
    (fun a c hb hc => M.bellmanOp_discounting hBr a c hb hc) hv_bdd hw_bdd st

/-- The lifted operator is a Banach contraction with modulus `β`. -/
lemma contractingWith_liftBellmanOp [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) :
    ContractingWith ⟨M.β, M.β_nonneg⟩
      (Blackwell.liftBddFun M.bellmanOp (fun v hv => M.bellmanOp_bounded hBr v hv)) :=
  Blackwell.contractingWith_liftBddFun M.β_nonneg M.β_lt_one
    (M.bellmanOp_apply_abs_sub_le hBr)

/-- The **value function** of the bounded-reward layer: The unique uniformly bounded fixed point of
the generic stochastic budget Bellman operator. -/
noncomputable def bddValueFunction [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) : ℝ × Fin n → ℝ :=
  Blackwell.bddFixedPoint (M.contractingWith_liftBellmanOp hBr)

/-- The bounded-layer value function is uniformly bounded. -/
theorem bddValueFunction_bounded [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) : UniformBounded (M.bddValueFunction hBr) :=
  Blackwell.bddFixedPoint_bounded _

/-- The bounded-layer value function satisfies the Bellman equation. -/
theorem bddValueFunction_isFixedPt [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) (st : ℝ × Fin n) :
    M.bddValueFunction hBr st = M.bellmanOp (M.bddValueFunction hBr) st :=
  Blackwell.bddFixedPoint_isFixedPt _ st

/-- **Unique uniformly bounded fixed point** of the generic stochastic budget Bellman operator. -/
theorem existsUnique_bdd_fixedPoint [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br) :
    ∃! v : (ℝ × Fin n) → ℝ,
      UniformBounded v ∧ ∀ st, v st = M.bellmanOp v st :=
  Blackwell.existsUnique_bdd_fixedPoint (M.contractingWith_liftBellmanOp hBr)

/-! ### Concavity preservation -/

/-- **The generic operator preserves concavity in the continuous state.** If `v(·, s)` is concave
for each `s`, then `(Tv)(·, s)` is concave, given a nonempty budget on the positive domain
(`hΓ_ne`), graph-convexity of the budget correspondence (`h_Γ_convex`), and joint concavity of the
one-step objective (`h_obj_concave`). The action type must be an `ℝ`-module so that convex
combinations of actions make sense. -/
theorem bellmanOp_concaveOn [AddCommMonoid A] [Module ℝ A]
    (v : ℝ × Fin n → ℝ)
    -- Motivates the theorem but is not needed by the proof: `h_obj_concave` already encodes
    -- the joint concavity of the one-step objective that the argument below relies on.
    (_hv : ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => v (w, s)))
    (hbdd : ∀ st, BddAbove (M.bellmanSet v st))
    (hΓ_ne : ∀ (s : Fin n) ⦃w : ℝ⦄, 0 < w → (M.Γ w s).Nonempty)
    (h_Γ_convex : ∀ (s : Fin n) ⦃w₁ w₂ : ℝ⦄, 0 < w₁ → 0 < w₂ →
      ∀ ⦃a₁ a₂ : A⦄, a₁ ∈ M.Γ w₁ s → a₂ ∈ M.Γ w₂ s →
      ∀ ⦃α : ℝ⦄, 0 ≤ α → α ≤ 1 →
      α • a₁ + (1 - α) • a₂ ∈ M.Γ (α • w₁ + (1 - α) • w₂) s)
    -- The hypothesis names below (`_hw₁`, `_hw₂`, `_ha₁`, `_ha₂`, `_hα`, `_hα1`) are only used to
    -- state the feasibility/weight preconditions of the inequality; the conclusion refers only to
    -- the values `w₁, w₂, a₁, a₂, α`, so these proof binders are unused in the body.
    (h_obj_concave : ∀ (s : Fin n) ⦃w₁ w₂ : ℝ⦄ (_hw₁ : 0 < w₁) (_hw₂ : 0 < w₂)
      ⦃a₁ a₂ : A⦄ (_ha₁ : a₁ ∈ M.Γ w₁ s) (_ha₂ : a₂ ∈ M.Γ w₂ s)
      ⦃α : ℝ⦄ (_hα : 0 ≤ α) (_hα1 : α ≤ 1),
      α * (M.reward a₁ + M.β * ∑ s', M.trans s s' * v (M.f a₁ s', s')) +
        (1 - α) * (M.reward a₂ + M.β * ∑ s', M.trans s s' * v (M.f a₂ s', s')) ≤
      M.reward (α • a₁ + (1 - α) • a₂) +
        M.β * ∑ s', M.trans s s' * v (M.f (α • a₁ + (1 - α) • a₂) s', s')) :
    ∀ s : Fin n, ConcaveOn ℝ (Set.Ioi 0) (fun w => M.bellmanOp v (w, s)) := by
  intro s
  constructor
  · exact convex_Ioi 0
  · intro w₁ hw₁ w₂ hw₂ α β hα hβ hαβ
    simp only [smul_eq_mul]
    rw [bellmanOp_eq_sSup, bellmanOp_eq_sSup, bellmanOp_eq_sSup]
    apply mul_csSup_add_mul_csSup_le hα hβ
      (M.bellmanSet_nonempty v (hΓ_ne s (Set.mem_Ioi.mp hw₁)))
      (M.bellmanSet_nonempty v (hΓ_ne s (Set.mem_Ioi.mp hw₂)))
      (hbdd (w₁, s)) (hbdd (w₂, s))
    rintro r₁ ⟨a₁, ha₁, rfl⟩ r₂ ⟨a₂, ha₂, rfl⟩
    have hβ_eq : β = 1 - α := by linarith
    set ā := α • a₁ + (1 - α) • a₂ with hā_def
    have hā : ā ∈ M.Γ (α * w₁ + (1 - α) * w₂) s := by
      have := h_Γ_convex s hw₁ hw₂ ha₁ ha₂ hα (by linarith)
      simpa only [smul_eq_mul] using this
    have helem :
        M.reward ā + M.β * ∑ s', M.trans s s' * v (M.f ā s', s') ≤
        sSup (M.bellmanSet v (α * w₁ + (1 - α) * w₂, s)) :=
      le_csSup (hbdd _) (M.mem_bellmanSet hā)
    have h_conc := h_obj_concave s hw₁ hw₂ ha₁ ha₂ hα (by linarith)
    rw [hβ_eq]
    simp only [hā_def] at helem h_conc ⊢
    linarith

/-- **Feasibility ⇒ Bellman inequality.** For any feasible action, its one-step objective is
bounded by the value of the fixed point. -/
lemma feasible_value_le (v_star : ℝ × Fin n → ℝ)
    (hv_fp : ∀ p, v_star p = M.bellmanOp v_star p) (st : ℝ × Fin n)
    (hbdd_st : BddAbove (M.bellmanSet v_star st))
    (a : A) (ha : a ∈ M.Γ st.1 st.2) :
    M.reward a + M.β * ∑ s', M.trans st.2 s' * v_star (M.f a s', s') ≤ v_star st := by
  rw [hv_fp st, bellmanOp_eq_sSup]
  exact le_csSup hbdd_st (M.mem_bellmanSet ha)

/-! ### Decreasing-differences preservation and antitone marginal -/

/-- **The generic operator preserves decreasing differences** on the positive domain. Given a
lattice rearrangement bound `h_rearrange` — that for any diagonal pair of feasible actions, the sum
of off-diagonal Bellman values dominates — `bellmanOp` maps submodular functions to submodular
functions. The `hΓ_ne` premise keeps the budget sets on the positive domain nonempty. -/
theorem bellmanOp_preserves_submodular
    (v : ℝ × Fin n → ℝ)
    (hΓ_ne : ∀ (s : Fin n) ⦃w : ℝ⦄, 0 < w → (M.Γ w s).Nonempty)
    (h_rearrange :
      ∀ (w₁ w₂ : ℝ) (s₁ s₂ : Fin n), w₁ ≤ w₂ → s₁ ≤ s₂ →
        ∀ a₁ ∈ M.Γ w₁ s₁, ∀ b₂ ∈ M.Γ w₂ s₂,
        (M.reward a₁ + M.β * ∑ s', M.trans s₁ s' * v (M.f a₁ s', s')) +
          (M.reward b₂ + M.β * ∑ s', M.trans s₂ s' * v (M.f b₂ s', s')) ≤
        M.bellmanOp v (w₂, s₁) + M.bellmanOp v (w₁, s₂)) :
    HasDecreasingDifferences (fun p => M.bellmanOp v p) := by
  intro w₁ w₂ s₁ s₂ hw0 hw hs
  -- Suffices: diagonal sum ≤ off-diagonal sum (submodularity in additive form).
  suffices h_diag_le_offdiag :
      M.bellmanOp v (w₁, s₁) + M.bellmanOp v (w₂, s₂) ≤
      M.bellmanOp v (w₂, s₁) + M.bellmanOp v (w₁, s₂) by
    linarith
  set B₁₁ := M.bellmanSet v (w₁, s₁)
  set B₂₂ := M.bellmanSet v (w₂, s₂)
  set RHS := M.bellmanOp v (w₂, s₁) + M.bellmanOp v (w₁, s₂)
  change sSup B₁₁ + sSup B₂₂ ≤ RHS
  have h_bdd₂₂ : ∀ r₂ ∈ B₂₂, r₂ ≤ RHS - sSup B₁₁ := by
    rintro r₂ ⟨b₂, hb₂, hr₂⟩
    have h_bdd₁₁ : ∀ r₁ ∈ B₁₁, r₁ ≤ RHS - r₂ := by
      rintro r₁ ⟨a₁, ha₁, rfl⟩
      rw [hr₂]
      linarith [h_rearrange w₁ w₂ s₁ s₂ hw hs a₁ ha₁ b₂ hb₂]
    linarith [csSup_le (M.bellmanSet_nonempty v (hΓ_ne s₁ hw0)) h_bdd₁₁]
  linarith [csSup_le (M.bellmanSet_nonempty v (hΓ_ne s₂ (lt_of_lt_of_le hw0 hw))) h_bdd₂₂]

/-- **Antitone marginal value across shocks.** For the fixed point `v*` of the generic operator,
`∀ w > 0, s₁ ≤ s₂ → v*_w(w, s₂) ≤ v*_w(w, s₁)`, given differentiability of `v*` in the continuous
state (`hv_diff`) and the invariance premise `hT_sub` that the operator maps functions with
decreasing differences to functions with decreasing differences. -/
theorem value_marginal_antitone [NeZero n] [Nonempty A] {Br : ℝ}
    (hBr : ∀ a, |M.reward a| ≤ Br)
    (v_star : ℝ × Fin n → ℝ)
    (hv_fp : ∀ p, v_star p = M.bellmanOp v_star p)
    (hv_bdd : UniformBounded v_star)
    (hv_diff : ∀ s : Fin n, ∀ w > 0,
      DifferentiableAt ℝ (fun w' => v_star (w', s)) w)
    (hT_sub : ∀ (v : ℝ × Fin n → ℝ),
      UniformBounded v → HasDecreasingDifferences v →
      HasDecreasingDifferences (fun p => M.bellmanOp v p)) :
    ∀ w > 0, Antitone (fun s => deriv (fun w' => v_star (w', s)) w) := by
  set T : (ℝ × Fin n → ℝ) → ℝ × Fin n → ℝ := M.bellmanOp with hT_def
  set Tlift := Blackwell.liftBddFun T (fun v hv => M.bellmanOp_bounded hBr v hv) with hTlift_def
  set C : Set (@BddFun (ℝ × Fin n)) :=
    {f | HasDecreasingDifferences (f : @DState (ℝ × Fin n) → ℝ)}
  have hC_ne : C.Nonempty := ⟨0, fun _ _ _ _ _ _ _ => by
    have : ∀ p, (0 : @BddFun (ℝ × Fin n)) p = 0 :=
      fun p => congr_fun BoundedContinuousFunction.coe_zero p
    simp [this]⟩
  have hC_closed : IsClosed C := by
    apply IsSeqClosed.isClosed
    intro f g hf hconv
    exact HasDecreasingDifferences.of_pointwise_tendsto hf fun p => by
      apply Filter.Tendsto.comp
        (ContinuousEvalConst.continuous_eval_const p).continuousAt.tendsto
      exact hconv
  have hC_inv : Set.MapsTo Tlift C C := by
    intro f hf
    change HasDecreasingDifferences (Tlift f : @DState (ℝ × Fin n) → ℝ)
    have hf_bdd := bddFun_bounded f
    rw [show (Tlift f : @DState (ℝ × Fin n) → ℝ) =
      fun p => T (f : @DState (ℝ × Fin n) → ℝ) p from
      funext (Blackwell.liftBddFun_apply (T := T) f)]
    exact hT_sub _ hf_bdd hf
  have h_mem : toBddFun v_star hv_bdd ∈ C :=
    Blackwell.isFixedPt_mem_of_isClosed (M.contractingWith_liftBellmanOp hBr)
      hC_ne hC_closed hC_inv hv_bdd hv_fp
  have h_sub : HasDecreasingDifferences v_star := by
    have : HasDecreasingDifferences (toBddFun v_star hv_bdd : @DState (ℝ × Fin n) → ℝ) := h_mem
    rwa [show (toBddFun v_star hv_bdd : @DState (ℝ × Fin n) → ℝ) = v_star from
      toBddFun_coe v_star hv_bdd] at this
  intro w hw
  exact h_sub.antitone_deriv hw (fun s => hv_diff s w hw)

end StochBudgetData

end Econlib.Optimization.DynamicProgramming
