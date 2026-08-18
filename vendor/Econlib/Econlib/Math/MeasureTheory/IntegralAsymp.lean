/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Asymptotics of set integrals over growing / shrinking intervals

Two convergence facts for set integrals of an integrable real function as the integration window
moves: The left-tail primitive `x ↦ ∫ t in Iic x, f t` is right-continuous, and the set integrals
over the centered, expanding windows `Ioc (-n) n` converge to the global integral.

## Main results

* `MeasureTheory.tendsto_setIntegral_Iic_right` — right-continuity of `x ↦ ∫ t in Iic x, f t`.
* `MeasureTheory.tendsto_setIntegral_Ioc_neg` — set integrals over `Ioc (-n) n` tend to the total
  integral, against any measure.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace MeasureTheory

/-- For any integrable `f`, the primitive `x ↦ ∫ t in Iic x, f t` is right-continuous. -/
lemma tendsto_setIntegral_Iic_right
    {f : ℝ → ℝ} (hf : Integrable f) (x : ℝ) :
    Tendsto (fun y => ∫ t in Iic y, f t) (𝓝[≥] x) (𝓝 (∫ t in Iic x, f t)) := by
  simp_rw [← integral_indicator measurableSet_Iic]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖f t‖)
  · exact Eventually.of_forall (fun y => hf.aestronglyMeasurable.indicator measurableSet_Iic)
  · exact Eventually.of_forall (fun y => ae_of_all _ (fun t => by
      simp only [indicator]; split <;> simp))
  · exact hf.norm
  · apply ae_of_all; intro t
    simp only [mem_Iic, indicator]
    by_cases ht : t ≤ x
    · -- t ≤ x: t ∈ Iic y for all y ≥ x, indicator = f t constantly
      simp only [ht, ite_true]
      exact tendsto_const_nhds.congr'
        (eventually_nhdsWithin_of_forall
          (fun y (hy : x ≤ y) => by simp [show t ≤ y from le_trans ht hy]))
    · -- t > x: for y near x from right, t ∉ Iic y, indicator = 0
      push Not at ht
      simp only [show ¬(t ≤ x) from not_le.mpr ht, ite_false]
      exact tendsto_const_nhds.congr' (by
        have h_evt : ∀ᶠ y in 𝓝[≥] x, y < t :=
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht)
        exact h_evt.mono (fun y hy => by simp [show ¬(t ≤ y) from not_le.mpr hy]))

/-- Set integrals over the expanding intervals `Ioc(-n, n)` converge to the global integral, for
any integrable function against any measure. -/
lemma tendsto_setIntegral_Ioc_neg {μ : Measure ℝ} {φ : ℝ → ℝ} (hφ : Integrable φ μ) :
    Tendsto (fun n : ℕ => ∫ x in Ioc (-(↑n : ℝ)) (↑n : ℝ), φ x ∂μ) atTop (𝓝 (∫ x, φ x ∂μ)) := by
  set s := fun n : ℕ => Ioc (-(↑n : ℝ)) (↑n : ℝ) with s_def
  have hs_mono : Monotone s :=
    fun _ _ h => Ioc_subset_Ioc (neg_le_neg (Nat.cast_le.mpr h)) (Nat.cast_le.mpr h)
  have hs_union : ⋃ n, s n = univ := by
    ext x; simp only [s, mem_iUnion, mem_Ioc, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    exact ⟨n, neg_lt_of_abs_lt hn, le_of_lt (abs_lt.mp hn).2⟩
  rw [← setIntegral_univ, ← hs_union]
  exact tendsto_setIntegral_of_monotone (fun _ => measurableSet_Ioc) hs_mono
    (hs_union ▸ hφ.integrableOn)

end MeasureTheory
