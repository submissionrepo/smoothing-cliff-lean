/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Data.Real.Basic

/-!
# Abel summation by parts on `Finset.range`

The multiplication form of **Abel summation** by parts on `Finset.range (m+1)` for real-valued
sequences, together with a bridging identity converting a partial sum of a `dite`-extended `ℕ → ℝ`
function on `range (k+1)` into a sum over a `Fin (m+1)` filter.

## Main statements

* `Finset.sum_range_mul_by_parts` — Abel summation by parts, multiplication form:
  `∑_{i<m+1} a(i) f(i) = (∑ a) · f(m) - ∑_{k<m} (∑_{i<k+1} a(i)) · (f(k+1) - f(k))`.
* `Finset.sum_range_dite_eq_sum_filter` — bridge between a `range`-indexed partial sum of a
  `dite`-extended function and a `Fin`-filter sum.

## Tags

big operators, Abel summation by parts, finset
-/

@[expose] public section

namespace Finset

/-- **Abel summation by parts** on `Finset.range (m+1)`, multiplication form of
`Finset.sum_range_by_parts`:
`∑_{i<m+1} a(i) f(i) = (∑_{i<m+1} a(i)) f(m) - ∑_{k<m} (∑_{i<k+1} a(i)) (f(k+1) - f(k))`. -/
lemma sum_range_mul_by_parts (m : ℕ) (a f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (m + 1), a i * f i =
    (∑ i ∈ Finset.range (m + 1), a i) * f m -
    ∑ k ∈ Finset.range m,
      (∑ i ∈ Finset.range (k + 1), a i) * (f (k + 1) - f k) := by
  have h := Finset.sum_range_by_parts f a (m + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at h
  calc ∑ i ∈ Finset.range (m + 1), a i * f i
      = ∑ i ∈ Finset.range (m + 1), f i * a i :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = (∑ i ∈ Finset.range (m + 1), a i) * f m -
        ∑ k ∈ Finset.range m,
          (∑ i ∈ Finset.range (k + 1), a i) * (f (k + 1) - f k) := by
        rw [h, mul_comm (f m)]
        congr 1
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Convert a partial sum of a `dite`-extended function on `range (k+1)` to a sum over a
`Fin (m+1)` filter. Bridges `range`-indexed Abel summation back to `Fin`-indexed sums. -/
lemma sum_range_dite_eq_sum_filter {m : ℕ} (g : Fin (m + 1) → ℝ) (k : ℕ)
    (hk : k < m + 1) :
    ∑ i ∈ Finset.range (k + 1),
      (fun j => if h : j < m + 1 then g ⟨j, h⟩ else 0) i =
    ∑ i ∈ Finset.univ.filter (fun j : Fin (m + 1) => j ≤ ⟨k, hk⟩), g i := by
  symm
  apply Finset.sum_nbij Fin.val
  · intro a hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.le_iff_val_le_val] at hmem
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hmem)
  · intro a b _ _ h; exact Fin.val_injective h
  · intro j hj
    have hj' : j < k + 1 := Finset.mem_range.mp hj
    have hjm : j < m + 1 := by omega
    refine ⟨⟨j, hjm⟩, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.le_iff_val_le_val]
    omega
  · intro a _
    show g a = if h : (a : ℕ) < m + 1 then g ⟨a, h⟩ else 0
    rw [dif_pos a.isLt]

end Finset
