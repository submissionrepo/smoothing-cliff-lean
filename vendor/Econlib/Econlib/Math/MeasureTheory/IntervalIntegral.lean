/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Inclusion–exclusion for interval integrals

For an integrand interval-integrable over the enclosing interval, the integrals over two
overlapping intervals sum to the integral over their union plus the integral over their
intersection.

## Main results

* `intervalIntegral.add_eq_union_add_inter` — interval inclusion–exclusion.
-/

@[expose] public section

open MeasureTheory

namespace intervalIntegral

/-- **Interval inclusion–exclusion** for a single interval-integrable integrand. If two intervals
`[p₁, q₁]`, `[p₂, q₂]` overlap (`max p₁ p₂ ≤ min q₁ q₂`), the sum of the integrals over them equals
the integral over the union plus the integral over the intersection. -/
lemma add_eq_union_add_inter {h : ℝ → ℝ} {p₁ q₁ p₂ q₂ : ℝ} (hp₁ : p₁ ≤ q₁) (hp₂ : p₂ ≤ q₂)
    (hov : max p₁ p₂ ≤ min q₁ q₂)
    (hint : IntervalIntegrable h volume (min p₁ p₂) (max q₁ q₂)) :
    (∫ t in p₁..q₁, h t) + (∫ t in p₂..q₂, h t)
      = (∫ t in (min p₁ p₂)..(max q₁ q₂), h t) + ∫ t in (max p₁ p₂)..(min q₁ q₂), h t := by
  have hmono : ∀ a c : ℝ, min p₁ p₂ ≤ a → c ≤ max q₁ q₂ → a ≤ c →
      IntervalIntegrable h volume a c := by
    intro a c ha hc hac
    refine hint.mono_set ?_
    rw [Set.uIcc_of_le hac,
      Set.uIcc_of_le (le_trans ha (le_trans hac hc))]
    exact Set.Icc_subset_Icc ha hc
  have hLp : min p₁ p₂ ≤ max p₁ p₂ := min_le_max
  have hMq : min q₁ q₂ ≤ max q₁ q₂ := min_le_max
  have hLfL : IntervalIntegrable h volume (min p₁ p₂) (max p₁ p₂) :=
    hmono _ _ le_rfl (le_trans hov hMq) hLp
  have hLR : IntervalIntegrable h volume (max p₁ p₂) (min q₁ q₂) :=
    hmono _ _ hLp hMq hov
  have hRRf : IntervalIntegrable h volume (min q₁ q₂) (max q₁ q₂) :=
    hmono _ _ (le_trans hLp hov) le_rfl hMq
  have key : ∀ {a m c : ℝ}, min p₁ p₂ ≤ a → c ≤ max q₁ q₂ → a ≤ m → m ≤ c →
      (∫ t in a..c, h t) = (∫ t in a..m, h t) + ∫ t in m..c, h t := by
    intro a m c ha hc ham hmc
    exact (intervalIntegral.integral_add_adjacent_intervals
      (hmono _ _ ha (le_trans hmc hc) ham) (hmono _ _ (le_trans ha ham) hc hmc)).symm
  have hsplit_full : (∫ t in (min p₁ p₂)..(max q₁ q₂), h t)
      = (∫ t in (min p₁ p₂)..(max p₁ p₂), h t) + (∫ t in (max p₁ p₂)..(min q₁ q₂), h t)
        + ∫ t in (min q₁ q₂)..(max q₁ q₂), h t := by
    rw [key le_rfl le_rfl hLp (le_trans hov hMq), key hLp le_rfl hov hMq]; ring
  rw [hsplit_full]
  have hov12 : p₁ ≤ q₂ :=
    le_trans (le_max_left p₁ p₂) (le_trans hov (min_le_right q₁ q₂))
  have hov21 : p₂ ≤ q₁ :=
    le_trans (le_max_right p₁ p₂) (le_trans hov (min_le_left q₁ q₂))
  rcases le_total p₁ p₂ with hpp | hpp <;> rcases le_total q₁ q₂ with hqq | hqq <;>
    simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, hpp, hqq]
  · rw [key (a := p₁) (m := p₂) (c := q₁) (by simp [hpp]) (by simp [hqq]) hpp hov21,
      key (a := p₂) (m := q₁) (c := q₂) (by simp [hpp]) (by simp [hqq]) hov21 hqq]; ring
  · rw [key (a := p₁) (m := p₂) (c := q₁) (by simp [hpp]) (by simp [hqq]) hpp
        (le_trans hp₂ hqq),
      key (a := p₂) (m := q₂) (c := q₁) (by simp [hpp]) (by simp [hqq]) hp₂ hqq]; ring
  · rw [key (a := p₂) (m := p₁) (c := q₂) (by simp [hpp]) (by simp [hqq]) hpp
        (le_trans hp₁ hqq),
      key (a := p₁) (m := q₁) (c := q₂) (by simp [hpp]) (by simp [hqq]) hp₁ hqq]; ring
  · rw [key (a := p₂) (m := p₁) (c := q₂) (by simp [hpp]) (by simp [hqq]) hpp hov12,
      key (a := p₁) (m := q₂) (c := q₁) (by simp [hpp]) (by simp [hqq]) hov12 hqq]; ring

end intervalIntegral
