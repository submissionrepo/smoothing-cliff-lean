/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.DynamicProgramming.Core.Optimality

/-!
# Principle of optimality for unbounded rewards (transversality form)

The bounded principle of optimality (`Econlib.Optimization.DynamicProgramming.Core.Optimality`)
kills the tail term `β^N · v*(s_N)` using a uniform bound `|v*| ≤ B`. Canonical economic dynamic
programs — log cake-eating, Brock–Mirman optimal growth — have unbounded reward and unbounded
value, so no uniform bound exists. This module supplies the same chain of results with the tail
controlled by an explicit **transversality condition**
`Tendsto (fun N => β^N · v*(stateSeq … N)) atTop (𝓝 0)`, matching the standard Stokey–Lucas
formulation and this library's rule of passing boundary-decay conditions as explicit `Tendsto`
hypotheses.

## Main statements

* `value_ge_payoff_of_transversality`: `v*` dominates the discounted payoff of any feasible plan
  along which transversality holds.
* `principle_of_optimality_of_transversality`: `v*` equals the supremum of feasible-plan payoffs.
* `stationary_plan_payoff_eq_of_transversality`: A Bellman-achieving stationary policy attains `v*`.

## Notes

The `BddAbove` (`hbdd`) hypothesis records that the Bellman set is bounded above at `v*`, so that
`v* = T v*` really is a supremum identity: In a `ConditionallyCompleteLinearOrder`, `sSup` of an
unbounded set returns junk.

## References

* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive Methods in Economic
  Dynamics*. Harvard University Press. [https://doi.org/10.2307/j.ctvjnrt76](https://doi.org/10.2307/j.ctvjnrt76).

## Tags

dynamic programing, principle of optimality, transversality, unbounded reward, bellman equation
-/

@[expose] public section

namespace Econlib.Optimization.DynamicProgramming

open Econlib.Optimization Filter Topology

universe u_S
variable {S : Type u_S} {A : Type*} [Nonempty S]

namespace UnboundedDetMDP

variable (M : UnboundedDetMDP S A)

/-- Telescoping: `v*(s) ≥ Σ_{t<N} β^t r_t + β^N v*(s_N)` for any feasible plan, by iterating the
Bellman inequality `v*(s) ≥ r(s,a) + β v*(s')`. Requires the Bellman set to be bounded above at
`v*` (so the value really is the supremum). -/
lemma value_ge_partialPayoff_add_tail
    (v_star : S → ℝ) (hv : ∀ s, v_star s = M.bellmanOperator v_star s)
    (hbdd : ∀ s, BddAbove (M.bellmanSet v_star s))
    (s : S) (π : Plan A) (hπ : M.isFeasible s π) (N : ℕ) :
    v_star s ≥ ∑ t ∈ Finset.range N,
        M.β ^ t * M.reward (M.stateSeq s π t) (π t) +
      M.β ^ N * v_star (M.stateSeq s π N) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hstep : v_star (M.stateSeq s π n) ≥
        M.reward (M.stateSeq s π n) (π n) +
        M.β * v_star (M.stateSeq s π (n + 1)) := by
      rw [hv (M.stateSeq s π n)]
      apply le_csSup (hbdd _)
      exact ⟨π n, hπ n, by rw [stateSeq_succ]⟩
    have hβn : (0 : ℝ) ≤ M.β ^ n := pow_nonneg M.β_nonneg n
    have hmul : M.β ^ n * v_star (M.stateSeq s π n) ≥
        M.β ^ n * M.reward (M.stateSeq s π n) (π n) +
        M.β ^ (n + 1) * v_star (M.stateSeq s π (n + 1)) := by
      calc M.β ^ n * v_star (M.stateSeq s π n)
          ≥ M.β ^ n * (M.reward (M.stateSeq s π n) (π n) +
              M.β * v_star (M.stateSeq s π (n + 1))) := mul_le_mul_of_nonneg_left hstep hβn
        _ = M.β ^ n * M.reward (M.stateSeq s π n) (π n) +
              M.β ^ (n + 1) * v_star (M.stateSeq s π (n + 1)) := by ring
    calc v_star s ≥ ∑ t ∈ Finset.range n,
            M.β ^ t * M.reward (M.stateSeq s π t) (π t) +
          M.β ^ n * v_star (M.stateSeq s π n) := ih
      _ ≥ ∑ t ∈ Finset.range n,
            M.β ^ t * M.reward (M.stateSeq s π t) (π t) +
          (M.β ^ n * M.reward (M.stateSeq s π n) (π n) +
           M.β ^ (n + 1) * v_star (M.stateSeq s π (n + 1))) := by linarith
      _ = ∑ t ∈ Finset.range (n + 1),
            M.β ^ t * M.reward (M.stateSeq s π t) (π t) +
          M.β ^ (n + 1) * v_star (M.stateSeq s π (n + 1)) := by rw [Finset.sum_range_succ]; ring

/-- **Principle of optimality (≥ direction), transversality form.** `v*` dominates the discounted
payoff of any feasible plan along which the discounted value tail vanishes. -/
theorem value_ge_payoff_of_transversality
    (v_star : S → ℝ) (hv : ∀ s, v_star s = M.bellmanOperator v_star s)
    (hbdd : ∀ s, BddAbove (M.bellmanSet v_star s))
    (s : S) (π : Plan A) (hπ : M.isFeasible s π)
    (hsummable : Summable fun t ↦ M.β ^ t * M.reward (M.stateSeq s π t) (π t))
    (htrans : Tendsto (fun N ↦ M.β ^ N * v_star (M.stateSeq s π N)) atTop (𝓝 0)) :
    M.discountedPayoff s π ≤ v_star s := by
  have hpartial : Tendsto
      (fun N ↦ ∑ t ∈ Finset.range N, M.β ^ t * M.reward (M.stateSeq s π t) (π t))
      atTop (𝓝 (M.discountedPayoff s π)) :=
    hsummable.hasSum.tendsto_sum_nat
  -- `partialₙ + β^N v*(s_N) → discountedPayoff + 0`, and `v* ≥` each term,
  -- so `discountedPayoff ≤ v*`.
  have hlim : Tendsto
      (fun N ↦ ∑ t ∈ Finset.range N, M.β ^ t * M.reward (M.stateSeq s π t) (π t)
        + M.β ^ N * v_star (M.stateSeq s π N))
      atTop (𝓝 (M.discountedPayoff s π + 0)) := hpartial.add htrans
  rw [add_zero] at hlim
  refine le_of_tendsto_of_tendsto hlim tendsto_const_nhds (.of_forall fun N ↦ ?_)
  exact M.value_ge_partialPayoff_add_tail v_star hv hbdd s π hπ N

/-- **Principle of optimality, transversality form** (Stokey, Lucas, and Prescott 1989). The value
function equals the supremum of discounted payoffs over all feasible plans, given summability and
transversality along every feasible plan. -/
theorem principle_of_optimality_of_transversality
    (v_star : S → ℝ) (hv : ∀ s, v_star s = M.bellmanOperator v_star s)
    (hbdd : ∀ s, BddAbove (M.bellmanSet v_star s))
    (s : S)
    (hsummable : ∀ π, M.isFeasible s π →
      Summable fun t ↦ M.β ^ t * M.reward (M.stateSeq s π t) (π t))
    (htrans : ∀ π, M.isFeasible s π →
      Tendsto (fun N ↦ M.β ^ N * v_star (M.stateSeq s π N)) atTop (𝓝 0)) :
    v_star s = sSup {p : ℝ | ∃ π : Plan A, M.isFeasible s π ∧ p = M.discountedPayoff s π} := by
  set PayoffSet := {p : ℝ | ∃ π : Plan A, M.isFeasible s π ∧ p = M.discountedPayoff s π} with hPS
  have hS_ne : PayoffSet.Nonempty := by
    obtain ⟨π₀, hπ₀⟩ := M.exists_feasible_plan s
    exact ⟨M.discountedPayoff s π₀, π₀, hπ₀, rfl⟩
  have hS_bdd : BddAbove PayoffSet :=
    ⟨v_star s, fun p hp => by
      obtain ⟨π, hπ, rfl⟩ := hp
      exact M.value_ge_payoff_of_transversality v_star hv hbdd s π hπ
        (hsummable π hπ) (htrans π hπ)⟩
  apply le_antisymm
  · -- For every ε > 0, build a δ-greedy plan whose payoff is within ε of `v*(s)`.
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hone_sub_β_pos : 0 < 1 - M.β := by linarith [M.β_lt_one]
    set δ := ε * (1 - M.β) / 2 with hδ_def
    have hδ : 0 < δ := by positivity
    -- A δ-greedy feasible action exists at every state (sup is not attained but is approached).
    have h_near_opt : ∀ s' : S, ∃ a ∈ M.Γ s',
        v_star s' - δ < M.reward s' a + M.β * v_star (M.transition s' a) := by
      intro s'
      have hsup : v_star s' - δ < v_star s' := sub_lt_self _ hδ
      rw [hv s'] at hsup ⊢
      obtain ⟨r, ⟨a, ha, rfl⟩, hlt⟩ :=
        exists_lt_of_lt_csSup (M.bellmanSet_nonempty v_star s') hsup
      exact ⟨a, ha, hlt⟩
    choose σ hσ_mem hσ_near using h_near_opt
    set π_ε := extractPlan σ M.transition s with hπε_def
    have hπ_feas : M.isFeasible s π_ε := by
      intro t
      rw [hπε_def, extractPlan_eq_σ, M.stateSeq_eq_extractState]
      exact hσ_mem _
    -- Greedy one-step inequality along the generated trajectory.
    have h_step_le : ∀ t : ℕ,
        v_star (M.stateSeq s π_ε t) ≤
          M.reward (M.stateSeq s π_ε t) (π_ε t) +
          M.β * v_star (M.stateSeq s π_ε (t + 1)) + δ := by
      intro t
      have hact : π_ε t = σ (M.stateSeq s π_ε t) := by
        rw [hπε_def, extractPlan_eq_σ, M.stateSeq_eq_extractState]
      have hσ_near_step := hσ_near (M.stateSeq s π_ε t)
      have htrans_eq : M.transition (M.stateSeq s π_ε t) (π_ε t) =
          M.stateSeq s π_ε (t + 1) := (stateSeq_succ M s π_ε t).symm
      rw [← hact, htrans_eq] at hσ_near_step
      linarith
    -- Reverse telescoping: `v*(s) ≤ partialₙ + β^N v*(s_N) + δ·Σβ^t`.
    have h_rev_tel : ∀ N : ℕ,
        v_star s ≤ ∑ t ∈ Finset.range N,
            M.β ^ t * M.reward (M.stateSeq s π_ε t) (π_ε t) +
          M.β ^ N * v_star (M.stateSeq s π_ε N) +
          δ * ∑ t ∈ Finset.range N, M.β ^ t := by
      intro N
      induction N with
      | zero => simp
      | succ n ih =>
        have hβn : (0 : ℝ) ≤ M.β ^ n := pow_nonneg M.β_nonneg n
        have hmul : M.β ^ n * v_star (M.stateSeq s π_ε n) ≤
            M.β ^ n * M.reward (M.stateSeq s π_ε n) (π_ε n) +
            M.β ^ (n + 1) * v_star (M.stateSeq s π_ε (n + 1)) +
            M.β ^ n * δ := by
          have := h_step_le n
          calc M.β ^ n * v_star (M.stateSeq s π_ε n)
              ≤ M.β ^ n * (M.reward (M.stateSeq s π_ε n) (π_ε n) +
                  M.β * v_star (M.stateSeq s π_ε (n + 1)) + δ) :=
                mul_le_mul_of_nonneg_left this hβn
            _ = M.β ^ n * M.reward (M.stateSeq s π_ε n) (π_ε n) +
                M.β ^ (n + 1) * v_star (M.stateSeq s π_ε (n + 1)) +
                M.β ^ n * δ := by ring
        calc v_star s
            ≤ ∑ t ∈ Finset.range n,
                M.β ^ t * M.reward (M.stateSeq s π_ε t) (π_ε t) +
              M.β ^ n * v_star (M.stateSeq s π_ε n) +
              δ * ∑ t ∈ Finset.range n, M.β ^ t := ih
          _ ≤ ∑ t ∈ Finset.range n,
                M.β ^ t * M.reward (M.stateSeq s π_ε t) (π_ε t) +
              (M.β ^ n * M.reward (M.stateSeq s π_ε n) (π_ε n) +
               M.β ^ (n + 1) * v_star (M.stateSeq s π_ε (n + 1)) +
               M.β ^ n * δ) +
              δ * ∑ t ∈ Finset.range n, M.β ^ t := by linarith
          _ = ∑ t ∈ Finset.range (n + 1),
                M.β ^ t * M.reward (M.stateSeq s π_ε t) (π_ε t) +
              M.β ^ (n + 1) * v_star (M.stateSeq s π_ε (n + 1)) +
              δ * ∑ t ∈ Finset.range (n + 1), M.β ^ t := by
            rw [Finset.sum_range_succ, Finset.sum_range_succ]; ring
    -- Pass to the limit `N → ∞`.
    have hpartial : Tendsto
        (fun N ↦ ∑ t ∈ Finset.range N, M.β ^ t * M.reward (M.stateSeq s π_ε t) (π_ε t))
        atTop (𝓝 (M.discountedPayoff s π_ε)) :=
      (hsummable π_ε hπ_feas).hasSum.tendsto_sum_nat
    have htail : Tendsto (fun N ↦ M.β ^ N * v_star (M.stateSeq s π_ε N)) atTop (𝓝 0) :=
      htrans π_ε hπ_feas
    have hgeom : Tendsto (fun N ↦ δ * ∑ t ∈ Finset.range N, M.β ^ t)
        atTop (𝓝 (δ * (1 - M.β)⁻¹)) :=
      (hasSum_geometric_of_lt_one M.β_nonneg M.β_lt_one).tendsto_sum_nat.const_mul δ
    have hlim : Tendsto
        (fun N ↦ ∑ t ∈ Finset.range N,
            M.β ^ t * M.reward (M.stateSeq s π_ε t) (π_ε t) +
          M.β ^ N * v_star (M.stateSeq s π_ε N) +
          δ * ∑ t ∈ Finset.range N, M.β ^ t)
        atTop (𝓝 (M.discountedPayoff s π_ε + 0 + δ * (1 - M.β)⁻¹)) :=
      (hpartial.add htail).add hgeom
    rw [add_zero] at hlim
    have hv_le : v_star s ≤ M.discountedPayoff s π_ε + δ * (1 - M.β)⁻¹ :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim (.of_forall h_rev_tel)
    have hpay_le : M.discountedPayoff s π_ε ≤ sSup PayoffSet :=
      le_csSup hS_bdd ⟨π_ε, hπ_feas, rfl⟩
    have hδ_bound : δ * (1 - M.β)⁻¹ < ε := by
      rw [hδ_def, div_mul_eq_mul_div,
        show ε * (1 - M.β) * (1 - M.β)⁻¹ = ε * ((1 - M.β) * (1 - M.β)⁻¹) from by ring,
        mul_inv_cancel₀ hone_sub_β_pos.ne']
      linarith
    linarith
  · apply csSup_le hS_ne
    rintro p ⟨π, hπ, rfl⟩
    exact M.value_ge_payoff_of_transversality v_star hv hbdd s π hπ
      (hsummable π hπ) (htrans π hπ)

/-- **Stationary policy attains the value (transversality form).** If a stationary policy `σ`
achieves the Bellman value identity at every state, its discounted payoff equals `v*` along its own
trajectory, provided that trajectory is summable and satisfies transversality. -/
theorem stationary_plan_payoff_eq_of_transversality
    (v_star : S → ℝ) (σ : S → A)
    (hσ_opt : ∀ s, v_star s = M.reward s (σ s) + M.β * v_star (M.transition s (σ s)))
    (s : S)
    (hsummable : Summable fun t ↦
      M.β ^ t * M.reward (M.stateSeq s (extractPlan σ M.transition s) t)
        (extractPlan σ M.transition s t))
    (htrans : Tendsto (fun N ↦
      M.β ^ N * v_star (M.stateSeq s (extractPlan σ M.transition s) N)) atTop (𝓝 0)) :
    M.discountedPayoff s (extractPlan σ M.transition s) = v_star s := by
  set π := extractPlan σ M.transition s with hπ_def
  -- Exact telescoping `v*(s) = Σ_{t<N} β^t r_t + β^N v*(s_N)` along the stationary trajectory.
  have h_tel_eq : ∀ N : ℕ,
      v_star s = ∑ t ∈ Finset.range N,
          M.β ^ t * M.reward (M.stateSeq s π t) (π t) +
        M.β ^ N * v_star (M.stateSeq s π N) := by
    intro N
    induction N with
    | zero => simp
    | succ n ih =>
      have hact : π n = σ (M.stateSeq s π n) := by
        rw [hπ_def, extractPlan_eq_σ, M.stateSeq_eq_extractState]
      have hstep : v_star (M.stateSeq s π n) =
          M.reward (M.stateSeq s π n) (π n) +
          M.β * v_star (M.stateSeq s π (n + 1)) := by
        have hopt := hσ_opt (M.stateSeq s π n)
        rw [← hact, ← stateSeq_succ] at hopt
        exact hopt
      calc v_star s
          = ∑ t ∈ Finset.range n,
              M.β ^ t * M.reward (M.stateSeq s π t) (π t) +
            M.β ^ n * v_star (M.stateSeq s π n) := ih
        _ = ∑ t ∈ Finset.range n,
              M.β ^ t * M.reward (M.stateSeq s π t) (π t) +
            M.β ^ n * (M.reward (M.stateSeq s π n) (π n) +
              M.β * v_star (M.stateSeq s π (n + 1))) := by rw [hstep]
        _ = ∑ t ∈ Finset.range (n + 1),
              M.β ^ t * M.reward (M.stateSeq s π t) (π t) +
            M.β ^ (n + 1) * v_star (M.stateSeq s π (n + 1)) := by
          rw [Finset.sum_range_succ]; ring
  have hpartial : Tendsto
      (fun N ↦ ∑ t ∈ Finset.range N, M.β ^ t * M.reward (M.stateSeq s π t) (π t))
      atTop (𝓝 (M.discountedPayoff s π)) :=
    hsummable.hasSum.tendsto_sum_nat
  have hlim : Tendsto
      (fun N ↦ ∑ t ∈ Finset.range N, M.β ^ t * M.reward (M.stateSeq s π t) (π t)
        + M.β ^ N * v_star (M.stateSeq s π N))
      atTop (𝓝 (M.discountedPayoff s π + 0)) := hpartial.add htrans
  rw [add_zero] at hlim
  exact (tendsto_nhds_unique (tendsto_const_nhds.congr h_tel_eq) hlim).symm

end UnboundedDetMDP

end Econlib.Optimization.DynamicProgramming
