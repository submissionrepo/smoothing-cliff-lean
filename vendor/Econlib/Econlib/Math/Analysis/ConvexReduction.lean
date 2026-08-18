/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Carathéodory reduction of convex combinations

A convex combination of `m` points in `ℝ^d` can be reduced to a convex combination of at most
`d + 1` of those points with the same weighted sum. This is Carathéodory's theorem for convex
combinations. An augmented version carries an additional real value attached to each point,
reducing a simplex-valued combination while preserving both the barycenter and the weighted sum of
the attached values.

## Main statements

* `convex_combination_reduce` — given `∑ w_j = 1`, `w_j ≥ 0`, and points `y_j ∈ ℝ^d`, there exist
  at most `d + 1` indices with positive weights summing to `1` and the same barycenter.
* `convex_combination_reduce_simplex_augmented` — the same reduction for points in
  `stdSimplex ℝ (Fin n)` with attached values, preserving the barycenter and the value sum, using
  at most `n + 1` indices.
-/

@[expose] public section

variable {d : ℕ}

/-- **Carathéodory's theorem** for convex combinations: A convex combination in `Fin d → ℝ` can be
expressed using at most `d + 1` of the original points, with positive weights summing to `1` and
the same barycenter. -/
theorem convex_combination_reduce {m : ℕ}
    (w : Fin m → ℝ) (y : Fin m → (Fin d → ℝ))
    (hw_nn : ∀ j, 0 ≤ w j) (hw_sum : ∑ j, w j = 1) :
    ∃ (k : ℕ) (_ : k ≤ d + 1) (idx : Fin k → Fin m) (w' : Fin k → ℝ),
      (∀ j, 0 < w' j) ∧ (∑ j, w' j = 1) ∧
      (∑ j, w' j • y (idx j) = ∑ j, w j • y j) := by
  set x := ∑ j, w j • y j
  -- Step 1: x ∈ convexHull ℝ (Set.range y)
  have hx : x ∈ convexHull ℝ (Set.range y) := by
    rw [mem_convexHull_iff_exists_fintype]
    exact ⟨Fin m, inferInstance, w, fun i => y i,
      hw_nn, hw_sum, fun i => ⟨i, rfl⟩, rfl⟩
  -- Step 2: Carathéodory — x is a positive combination of affinely independent points
  obtain ⟨ι, hι_fin, z, w', hz_range, hz_indep, hw'_pos, hw'_sum, hw'_bary⟩ :=
    eq_pos_convex_span_of_mem_convexHull hx
  -- Step 3: card ι ≤ d + 1 (affine independence bounds the count)
  have h_card : Fintype.card ι ≤ d + 1 := by
    by_cases h_ne : Nonempty ι
    · have h_rank := hz_indep.finrank_vectorSpan_add_one (k := ℝ)
      have h_le : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤
          Module.finrank ℝ (Fin d → ℝ) :=
        Submodule.finrank_le _
      simp at h_le
      omega
    · rw [not_nonempty_iff] at h_ne
      simp [Fintype.card_eq_zero]
  -- Step 4: Extract indices — each z j equals y (idx j) for some idx j
  have h_idx : ∀ j : ι, ∃ i : Fin m, z j = y i := by
    intro j
    obtain ⟨i, hi⟩ := hz_range ⟨j, rfl⟩
    exact ⟨i, hi.symm⟩
  choose idx h_idx_eq using h_idx
  -- Step 5: Re-index from ι to Fin (card ι) and package the result
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, h_card, idx ∘ e, w' ∘ e, fun j => hw'_pos (e j), ?_, ?_⟩
  · -- Sum of re-indexed weights = 1
    change ∑ j : Fin (Fintype.card ι), w' (e j) = 1
    rw [← Equiv.sum_comp e.symm]
    simp [e, hw'_sum]
  · -- Barycenter preserved under re-indexing
    change ∑ j : Fin (Fintype.card ι), w' (e j) • y (idx (e j)) = x
    have : ∀ j : Fin (Fintype.card ι), w' (e j) • y (idx (e j)) = w' (e j) • z (e j) := by
      intro j; rw [← h_idx_eq]
    rw [Finset.sum_congr rfl (fun j _ => this j)]
    rw [← hw'_bary]
    rw [← Equiv.sum_comp e.symm]
    simp [e]

/-- When each `q j` lies on a simplex (its last coordinate is `1` minus the sum of the others), a
`c`-weighted sum of last coordinates equals `∑ c j` minus the `c`-weighted sums over the remaining
coordinates. Shared by the `w'`/`idx` and `w`/`id` branches of the augmented reduction below. -/
private lemma sum_mul_last_eq {p n' : ℕ} (c : Fin p → ℝ) (q : Fin p → Fin (n' + 1) → ℝ)
    (hq : ∀ j, q j (Fin.last n') = 1 - ∑ i' : Fin n', q j i'.castSucc) :
    ∑ j, c j * q j (Fin.last n')
      = ∑ j, c j - ∑ i' : Fin n', ∑ j, c j * q j i'.castSucc := by
  rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [hq, ← Finset.mul_sum]
  ring

/-- Augmented Carathéodory reduction: Given a convex combination of points in the standard simplex
`stdSimplex ℝ (Fin n)` together with attached real values `t j`, the combination reduces to at most
`n + 1` indices while preserving both the simplex barycenter and the weighted sum of the
`t`-values. -/
theorem convex_combination_reduce_simplex_augmented {n m : ℕ}
    (w : Fin m → ℝ) (μ : Fin m → Fin n → ℝ) (t : Fin m → ℝ)
    (hw_nn : ∀ j, 0 ≤ w j) (hw_sum : ∑ j, w j = 1)
    (hμ : ∀ j, μ j ∈ stdSimplex ℝ (Fin n)) :
    ∃ (k : ℕ) (_ : k ≤ n + 1) (idx : Fin k → Fin m) (w' : Fin k → ℝ),
      (∀ j, 0 < w' j) ∧ (∑ j, w' j = 1) ∧
      (∑ j, w' j • μ (idx j) = ∑ j, w j • μ j) ∧
      (∑ j, w' j * t (idx j) = ∑ j, w j * t j) := by
  classical
  -- Edge case: n = 0.  Then stdSimplex ℝ (Fin 0) is empty, so either m = 0
  -- (contradicting hw_sum = 1) or hμ 0 yields a contradiction.
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- m = 0: the empty sum ∑ w j = 0 contradicts hw_sum = 1.
    subst hm0
    simp at hw_sum
  · -- m > 0.
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- n = 0: stdSimplex ℝ (Fin 0) = ∅; the simplex sum constraint gives `0 = 1`.
      subst hn0
      have hsum : (∑ i : Fin 0, μ ⟨0, hmpos⟩ i) = 1 := (hμ ⟨0, hmpos⟩).2
      simp at hsum
    -- n = n' + 1: drop the last coord of μ, append t, embed into Fin n → ℝ.
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    -- The embedding: y j : Fin (n' + 1) → ℝ
    -- y j i = if i.val < n' then μ j i.castSucc (i.e., μ j with last dropped)
    --        else t j
    let y : Fin m → Fin (n' + 1) → ℝ :=
      fun j => Fin.snoc (fun i : Fin n' => μ j i.castSucc) (t j)
    -- Apply convex_combination_reduce with d := n' + 1.
    obtain ⟨k, hk_le, idx, w', hw'_pos, hw'_sum, hw'_bary⟩ :=
      convex_combination_reduce (d := n' + 1) w y hw_nn hw_sum
    refine ⟨k, hk_le, idx, w', hw'_pos, hw'_sum, ?_, ?_⟩
    · -- Recover μ-barycenter.  On the last coord (`Fin.last n'`), each μ j satisfies
      -- ∑ i : Fin (n' + 1), μ j i = 1, so μ j (last n') = 1 − ∑ (over castSucc).
      ext i
      have hbary_app := congrFun hw'_bary i
      -- Compute LHS: pointwise sum of weighted μ.
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hbary_app ⊢
      -- Split by whether i = last n' or i = castSucc i'.
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · -- i = i'.castSucc.
        have : ∀ j : Fin m, y j i'.castSucc = μ j i'.castSucc := by
          intro j
          simp [y, Fin.snoc_castSucc]
        simp only [this] at hbary_app
        exact hbary_app
      · -- i = Fin.last n'.  Use simplex constraint to recover the last coord.
        -- Strategy: ∑ j, w' j • μ (idx j) (last n')
        --       = ∑ j, w' j * (1 - ∑ i', μ (idx j) i'.castSucc)   (simplex)
        --       = ∑ j, w' j - ∑ j, w' j * ∑ i', μ (idx j) i'.castSucc
        --       = 1 - ∑ i', ∑ j, w' j * μ (idx j) i'.castSucc       (sum_comm)
        -- And similarly for the RHS.  Use that on castSucc coords, the
        -- equality already holds (from previous case applied informally),
        -- but we need to re-derive without recursion.
        --
        -- Direct route: subtract from `∑ i, ...` in two ways.
        -- We have the identity ∑_{i : Fin (n'+1)} (μ j i) = 1 for any μ j on
        -- the simplex.  So:
        --   μ j (last n') = 1 - ∑ i' : Fin n', μ j i'.castSucc.
        -- Apply to both sides.
        have hμ_last : ∀ j : Fin m,
            μ j (Fin.last n') = 1 - ∑ i' : Fin n', μ j i'.castSucc := by
          intro j
          have hsum : ∑ i : Fin (n' + 1), μ j i = 1 := (hμ j).2
          rw [Fin.sum_univ_castSucc (n := n')] at hsum
          linarith
        -- Both sides expand the last-coordinate sum via the simplex constraint.
        have hLHS := sum_mul_last_eq w' (fun j => μ (idx j)) (fun j => hμ_last (idx j))
        have hRHS := sum_mul_last_eq w μ (fun j => hμ_last j)
        -- Equality on castSucc coords transfers from hw'_bary on
        -- y, which on castSucc i' equals μ ?  i'.castSucc.
        have hcast : ∀ i' : Fin n',
            ∑ j, w' j * μ (idx j) i'.castSucc = ∑ j, w j * μ j i'.castSucc := by
          intro i'
          have happ := congrFun hw'_bary i'.castSucc
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at happ
          have hy_cast : ∀ j : Fin m, y j i'.castSucc = μ j i'.castSucc := by
            intro j
            simp [y, Fin.snoc_castSucc]
          simp only [hy_cast] at happ
          exact happ
        rw [hLHS, hRHS, hw'_sum, hw_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i' _hi
        exact hcast i'
    · -- t-barycenter: y j (last n') = t j, so the last-coord equation gives the
      -- t-sum equality.
      have happ := congrFun hw'_bary (Fin.last n')
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at happ
      have hy_last : ∀ j : Fin m, y j (Fin.last n') = t j := by
        intro j; simp [y, Fin.snoc_last]
      simp only [hy_last] at happ
      exact happ
