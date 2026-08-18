/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Preferences.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Single-peaked preferences

This module defines **single-peaked** preferences on ordered domains, the standard domain
restriction of voting theory introduced by Black (1948). A preference is single-peaked when it has
an ideal point and utility strictly falls as alternatives move away from that point on either side,
so the peak is the unique maximizer. The left and right monotonicity fields use inclusive bounds at
the peak, making comparisons with the peak itself available directly.

## Main definitions

* `SinglePeakedRel` — the ordinal, relation-level notion on a linearly ordered outcome space, the
  right target for voting-domain and comparative-statics statements that do not use a utility scale.
* `SinglePeaked` — the concrete real-valued utility form on `ℝ`.
* `SinglePeaked.ofSymmetric`, `SinglePeaked.quadraticLoss` — constructors from a symmetric strictly
  decreasing function of distance, and from quadratic loss.
* `SinglePeakedFinite` — the analog for a finite ordered set of alternatives.

## Main statements

* `SinglePeakedRel.peak_is_max`, `SinglePeaked.peak_is_max`, `SinglePeaked.peak_unique_max` — the
  peak weakly dominates every alternative and is the unique maximizer.
* `SinglePeaked.closer_preferred`, `SinglePeaked.between_preferred` — distance and order
  comparisons on one side of the peak.
* `SinglePeaked.upper_contour_convex` — upper contour sets of a single-peaked utility on `ℝ` are
  convex (one-dimensional quasiconcavity).

## Notes

The median voter theorem holds when all voters have single-peaked preferences. For multidimensional
spatial models, use the convex upper-contour predicates of `Preferences.Geometry` rather than
encoding several dimensions as a line.

## References

* Black, Duncan. 1948. “On the Rationale of Group Decision-Making.” *Journal of Political Economy*
  56 (1): 23–34. [https://doi.org/10.1086/256633](https://doi.org/10.1086/256633).

## Tags

single-peaked, preferences, voting, median voter, quasiconcavity, ideal point
-/

@[expose] public section

namespace Econlib.Preferences

/-- Relation-level single-peakedness on a linearly ordered outcome space: The ordinal core of
single-peakedness, recording an ideal `peak` together with strict preference for alternatives
closer to it on each side. -/
structure SinglePeakedRel {X : Type*} [LinearOrder X] (R : PreferenceRel X) where
  /-- The ideal point (peak, bliss point). -/
  peak : X
  /-- To the left of the peak, alternatives closer to the peak are strictly preferred. -/
  left_of_peak : ∀ x y, x < y → y ≤ peak → y ≻[R] x
  /-- To the right of the peak, alternatives closer to the peak are strictly preferred. -/
  right_of_peak : ∀ x y, peak ≤ x → x < y → x ≻[R] y

namespace SinglePeakedRel

variable {X : Type*} [LinearOrder X] {R : PreferenceRel X} (sp : SinglePeakedRel R)

/-- The peak weakly dominates every alternative. -/
lemma peak_is_max (x : X) : sp.peak ≽[R] x := by
  rcases lt_trichotomy x sp.peak with hlt | heq | hgt
  · exact (sp.left_of_peak x sp.peak hlt le_rfl).1
  · rw [heq]; exact R.le_refl sp.peak
  · exact (sp.right_of_peak sp.peak x le_rfl hgt).1

end SinglePeakedRel

/-- A utility function `u : ℝ → ℝ` is **single-peaked** (Black 1948) when it is strictly increasing
up to a peak and strictly decreasing after it. The side conditions are inclusive at `peak`:
`left_of_peak` applies when `y = peak`, and `right_of_peak` applies when `x = peak`, making the
peak-comparison lemmas usable without separate boundary fields. -/
structure SinglePeaked (u : ℝ → ℝ) where
  /-- The ideal point (peak, bliss point). -/
  peak : ℝ
  /-- To the left of the peak, `u` is strictly increasing: If `x < y ≤ peak`, then `u(x) < u(y)`. -/
  left_of_peak : ∀ x y, x < y → y ≤ peak → u x < u y
  /-- To the right of the peak, `u` is strictly decreasing: If `peak ≤ x < y`, then
  `u(x) > u(y)`. -/
  right_of_peak : ∀ x y, peak ≤ x → x < y → u y < u x

namespace SinglePeaked

variable {u : ℝ → ℝ} (sp : SinglePeaked u)

/-- A real-valued single-peaked utility induces an ordinal single-peaked preference. -/
noncomputable def toRel : SinglePeakedRel (preferenceOfRealUtility u) where
  peak := sp.peak
  left_of_peak := fun x y hxy hyp =>
    ⟨(sp.left_of_peak x y hxy hyp).le, not_le.mpr (sp.left_of_peak x y hxy hyp)⟩
  right_of_peak := fun x y hpx hxy =>
    ⟨(sp.right_of_peak x y hpx hxy).le, not_le.mpr (sp.right_of_peak x y hpx hxy)⟩

/-- The peak weakly dominates every alternative. -/
lemma peak_is_max (x : ℝ) : u x ≤ u sp.peak := by
  rcases lt_trichotomy x sp.peak with hlt | rfl | hgt
  · exact le_of_lt (sp.left_of_peak x sp.peak hlt le_rfl)
  · exact le_refl _
  · exact le_of_lt (sp.right_of_peak sp.peak x le_rfl hgt)

/-- If an alternative attains peak utility, then it is the peak itself. -/
lemma peak_unique_max (x : ℝ) (h : u x = u sp.peak) : x = sp.peak := by
  rcases lt_trichotomy x sp.peak with hlt | heq | hgt
  · linarith [sp.left_of_peak x sp.peak hlt le_rfl]
  · exact heq
  · linarith [sp.right_of_peak sp.peak x le_rfl hgt]

/-- On a fixed side of the peak, the alternative closer to the peak is strictly preferred. -/
lemma closer_preferred {x y : ℝ}
    (h_side : (x ≤ sp.peak ∧ y ≤ sp.peak) ∨ (sp.peak ≤ x ∧ sp.peak ≤ y))
    (h_dist : |x - sp.peak| < |y - sp.peak|) :
    u y < u x := by
  rcases h_side with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hyx : y < x := by
      have h1 := abs_of_nonpos (sub_nonpos.mpr hx)
      have h2 := abs_of_nonpos (sub_nonpos.mpr hy)
      linarith
    exact sp.left_of_peak y x hyx hx
  · have hxy : x < y := by
      have h1 := abs_of_nonneg (sub_nonneg.mpr hx)
      have h2 := abs_of_nonneg (sub_nonneg.mpr hy)
      linarith
    exact sp.right_of_peak x y hx hxy

/-- Moving from an endpoint toward the peak weakly increases utility. -/
lemma between_preferred {x y : ℝ}
    (h : (x ≤ y ∧ y ≤ sp.peak) ∨ (sp.peak ≤ y ∧ y ≤ x)) :
    u x ≤ u y := by
  rcases h with ⟨hxy, hyp⟩ | ⟨hpy, hyx⟩
  · rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_refl _
    · exact le_of_lt (sp.left_of_peak x y hlt hyp)
  · rcases eq_or_lt_of_le hyx with rfl | hlt
    · exact le_refl _
    · exact le_of_lt (sp.right_of_peak y x hpy hlt)

include sp in
/-- Upper contour sets of a single-peaked utility are convex. This is the one-dimensional
quasi-concavity property: If two alternatives deliver at least `c`, then any convex combination
between them also delivers at least `c`. -/
lemma upper_contour_convex (c : ℝ) : Convex ℝ {x | u x ≥ c} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  have hcx : a * x + b * x = x := by rw [← add_mul, hab, one_mul]
  have hcy : a * y + b * y = y := by rw [← add_mul, hab, one_mul]
  rcases le_total x y with hxy | hyx <;>
    rcases le_total (a * x + b * y) sp.peak with hzp | hpz
  · have hxz : x ≤ a * x + b * y := by nlinarith [mul_le_mul_of_nonneg_left hxy hb]
    exact le_trans hx (sp.between_preferred (Or.inl ⟨hxz, hzp⟩))
  · have hzy : a * x + b * y ≤ y := by nlinarith [mul_le_mul_of_nonneg_left hxy ha]
    exact le_trans hy (sp.between_preferred (Or.inr ⟨hpz, hzy⟩))
  · have hyz : y ≤ a * x + b * y := by nlinarith [mul_le_mul_of_nonneg_left hyx ha]
    exact le_trans hy (sp.between_preferred (Or.inl ⟨hyz, hzp⟩))
  · have hzx : a * x + b * y ≤ x := by nlinarith [mul_le_mul_of_nonneg_left hyx hb]
    exact le_trans hx (sp.between_preferred (Or.inr ⟨hpz, hzx⟩))

end SinglePeaked

/-- Construct single-peaked preferences from a symmetric, strictly decreasing function of distance
from the peak.

Given `peak : ℝ` and `f : ℝ → ℝ` that is strictly decreasing on `[0, ∞)`, this constructs the
distance-based utility `u x = f |x - peak|`. -/
def SinglePeaked.ofSymmetric (peak : ℝ) (f : ℝ → ℝ)
    (hf : StrictAntiOn f (Set.Ici 0)) : SinglePeaked (fun x => f |x - peak|) where
  peak := peak
  left_of_peak := by
    intro x y hxy hy
    apply hf (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr (abs_nonneg _))
    rw [abs_of_nonpos (by linarith : y - peak ≤ 0), abs_of_nonpos (by linarith : x - peak ≤ 0)]
    linarith
  right_of_peak := by
    intro x y hx hxy
    apply hf (Set.mem_Ici.mpr (abs_nonneg _)) (Set.mem_Ici.mpr (abs_nonneg _))
    rw [abs_of_nonneg (by linarith : x - peak ≥ 0), abs_of_nonneg (by linarith : y - peak ≥ 0)]
    linarith

/-- Quadratic loss utility, `u x = - (x - peak) ^ 2`.

This is the canonical spatial-voting example: Utility is maximized at `peak` and falls strictly
with squared distance from the peak. -/
def SinglePeaked.quadraticLoss (peak : ℝ) :
    SinglePeaked (fun x => -(x - peak) ^ 2) where
  peak := peak
  left_of_peak := by
    intro x y hxy hy
    simp only [neg_lt_neg_iff]
    nlinarith [sq_abs (x - peak), sq_abs (y - peak)]
  right_of_peak := by
    intro x y hx hxy
    simp only [neg_lt_neg_iff]
    nlinarith [sq_abs (x - peak), sq_abs (y - peak)]

/-- Single-peaked preferences over a finite ordered set of alternatives.

The alternatives are indexed by `Fin m` and embedded in `ℝ` by a strictly monotone position map
`pos`. The utility fields mirror `SinglePeaked`: Utility strictly rises up to `peakIdx` and
strictly falls after it, with inclusive bounds at the peak. -/
structure SinglePeakedFinite (m : ℕ) (pos : Fin m → ℝ) (u : Fin m → ℝ) where
  /-- Alternative positions respect the canonical order on `Fin m`. -/
  strictMono_pos : StrictMono pos
  /-- The index of the peak alternative. -/
  peakIdx : Fin m
  /-- To the left: If `pos i < pos j ≤ pos peakIdx`, then `u i < u j`. -/
  left_of_peak : ∀ i j : Fin m, pos i < pos j → pos j ≤ pos peakIdx → u i < u j
  /-- To the right: If `pos peakIdx ≤ pos i < pos j`, then `u j < u i`. -/
  right_of_peak : ∀ i j : Fin m, pos peakIdx ≤ pos i → pos i < pos j → u j < u i

end Econlib.Preferences
