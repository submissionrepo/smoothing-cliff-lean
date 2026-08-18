/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Tail integrals of integrable functions

Two tail-decay lemmas for an integrable real-valued function on `ℝ`: The integral over `Ioi n`
(resp. `Iic (-n)`) tends to zero as `n → ∞`. They support integration-by-parts boundary arguments
at `±∞`.

## Main statements

* `tail_Ioi_tendsto_zero` — `(∫ x in Ioi n, f x) → 0` as `n → ∞`.
* `tail_Iic_tendsto_zero` — `(∫ x in Iic (-n), f x) → 0` as `n → ∞`.

## Tags

measure theory, integration, tail decay, integrable
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace MeasureTheory

/-- The integral over the complement of a monotone family of sets exhausting the line tends to `0`,
when the integral over the family itself converges to the total integral. -/
private lemma tail_compl_tendsto_zero {f : ℝ → ℝ} (hf : Integrable f) {s : ℕ → Set ℝ}
    (hsm : ∀ n, MeasurableSet (s n))
    (h_lim : Tendsto (fun n : ℕ => ∫ x in s n, f x) atTop (𝓝 (∫ x, f x))) :
    Tendsto (fun n : ℕ => ∫ x in (s n)ᶜ, f x) atTop (𝓝 0) := by
  set c := ∫ x, f x
  have h_eq : ∀ n : ℕ, ∫ x in (s n)ᶜ, f x = c - ∫ x in s n, f x := fun n => by
    have := integral_add_compl (hsm n) hf; linarith
  simp_rw [h_eq, show (0 : ℝ) = c - c from (sub_self c).symm]
  exact tendsto_const_nhds.sub h_lim

/-- Tail integral of an integrable function on `Ioi n` tends to 0 as `n → ∞`. -/
lemma tail_Ioi_tendsto_zero (f : ℝ → ℝ) (hf : Integrable f) :
    Tendsto (fun n : ℕ => ∫ x in Ioi (↑n : ℝ), f x) atTop (𝓝 0) := by
  -- `Ioi n = (Iic n)ᶜ`; the family `Iic n` exhausts `univ` upward.
  have h_lim : Tendsto (fun n : ℕ => ∫ x in Iic (↑n : ℝ), f x) atTop (𝓝 (∫ x, f x)) := by
    have h_union : ⋃ n : ℕ, Iic (↑n : ℝ) = univ := by ext x; simp [exists_nat_ge x]
    rw [show (∫ x, f x) = ∫ x in ⋃ n : ℕ, Iic (↑n : ℝ), f x from by
      rw [h_union, setIntegral_univ]]
    exact tendsto_setIntegral_of_monotone (fun _ => measurableSet_Iic)
      (fun _ _ h => Iic_subset_Iic.mpr (Nat.cast_le.mpr h)) (h_union ▸ hf.integrableOn)
  simpa only [compl_Iic] using tail_compl_tendsto_zero hf (fun _ => measurableSet_Iic) h_lim

/-- Tail integral of an integrable function on `Iic (-n)` tends to 0 as `n → ∞`. -/
lemma tail_Iic_tendsto_zero (f : ℝ → ℝ) (hf : Integrable f) :
    Tendsto (fun n : ℕ => ∫ x in Iic (-(↑n : ℝ)), f x) atTop (𝓝 0) := by
  -- `Iic (-n) = (Ioi (-n))ᶜ`; the family `Ioi (-n)` exhausts `univ` upward.
  have h_lim : Tendsto (fun n : ℕ => ∫ x in Ioi (-(↑n : ℝ)), f x) atTop (𝓝 (∫ x, f x)) := by
    have h_union : ⋃ n : ℕ, Ioi (-(↑n : ℝ)) = univ := by
      ext x; simp only [mem_iUnion, mem_Ioi, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_gt (-x); exact ⟨n, by linarith⟩
    rw [show (∫ x, f x) = ∫ x in ⋃ n : ℕ, Ioi (-(↑n : ℝ)), f x from by
      rw [h_union, setIntegral_univ]]
    exact tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioi)
      (fun _ _ h => Ioi_subset_Ioi (neg_le_neg (Nat.cast_le.mpr h)))
      (h_union ▸ hf.integrableOn)
  simpa only [compl_Ioi] using tail_compl_tendsto_zero hf (fun _ => measurableSet_Ioi) h_lim

end MeasureTheory
