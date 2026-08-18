/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Right derivative of a convex function and its monotone extension

For `φ` convex on `[a, b]`, the right derivative `x ↦ derivWithin φ (Ioi x) x` is monotone on the
interior `(a, b)`. This file extends it to a globally `Monotone` function on all of `ℝ` and proves
the fundamental theorem of calculus for `φ` against its right derivative.

## Main definitions

* `ConvexOn.rightDerivExtend` — extension of the right derivative to all of `ℝ`.

## Main statements

* `ConvexOn.rightDerivExtend_monotone` — the extension is globally monotone, given boundedness of
  the right-derivative image on `(a, b)`.
* `ConvexOn.intervalIntegrable_rightDeriv` — the right derivative is interval-integrable on
  `[a, t]`.
* `ConvexOn.ftc_rightDeriv` — `φ(t) - φ(a) = ∫ₐᵗ φ'₊(s) ds`.
* `ConvexOn.continuousOn_Ioo` — a convex function is continuous on the open interior `(a, b)`.

## Notes

The right-derivative extension is stated independently of any Stieltjes measure construction.
-/

@[expose] public section

open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology

variable {φ : ℝ → ℝ} {a b : ℝ}

/-! ### The monotone extension -/

namespace ConvexOn

/-- Extend the right derivative of a convex function on `[a, b]` to all of `ℝ`. Uses `sInf`/`sSup`
of the image on the interior as constant extensions. -/
-- `hφ` and `hab` are unused in the body but drive the `hφ.rightDerivExtend hab` dot-notation API
-- shared by the lemmas below.
noncomputable def rightDerivExtend (_hφ : ConvexOn ℝ (Icc a b) φ)
    (_hab : a < b) : ℝ → ℝ :=
  let g := fun x => derivWithin φ (Ioi x) x
  fun x =>
    if x ≤ a then sInf (g '' Ioo a b)
    else if b ≤ x then sSup (g '' Ioo a b)
    else g x

/-- On `(a, b)`, the extension equals the actual right derivative. -/
lemma rightDerivExtend_eq_of_mem_Ioo (hφ : ConvexOn ℝ (Icc a b) φ)
    (hab : a < b) {x : ℝ} (hx : x ∈ Ioo a b) :
    hφ.rightDerivExtend hab x = derivWithin φ (Ioi x) x := by
  unfold rightDerivExtend
  simp only
  rw [if_neg (not_le.mpr hx.1), if_neg (not_le.mpr hx.2)]

/-- For `x ≤ a`, the extension is the infimum. -/
lemma rightDerivExtend_of_le_left (hφ : ConvexOn ℝ (Icc a b) φ)
    (hab : a < b) {x : ℝ} (hx : x ≤ a) :
    hφ.rightDerivExtend hab x = sInf ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b) := by
  unfold rightDerivExtend; simp only; rw [if_pos hx]

/-- For `b ≤ x`, the extension is the supremum. -/
lemma rightDerivExtend_of_right_le (hφ : ConvexOn ℝ (Icc a b) φ)
    (hab : a < b) {x : ℝ} (hx : b ≤ x) :
    hφ.rightDerivExtend hab x = sSup ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b) := by
  unfold rightDerivExtend; simp only
  rw [if_neg (not_le.mpr (lt_of_lt_of_le hab hx)), if_pos hx]

/-- The extended right derivative is globally monotone.

Requires explicit boundedness of the right-derivative image on `(a, b)` because convex functions
can have unbounded one-sided derivatives at boundary points (e.g. `φ(x) = -√x` has `φ'₊(x) → -∞` as
`x → 0⁺`). -/
theorem rightDerivExtend_monotone (hφ : ConvexOn ℝ (Icc a b) φ) (hab : a < b)
    (hbb : BddBelow ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b))
    (hba : BddAbove ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b)) :
    Monotone (hφ.rightDerivExtend hab) := by
  set g := fun x => derivWithin φ (Ioi x) x
  have hg_mono : MonotoneOn g (Ioo a b) := by
    rw [← interior_Icc]; exact hφ.monotoneOn_rightDeriv
  have hne : (g '' Ioo a b).Nonempty := Set.Nonempty.image g (nonempty_Ioo.mpr hab)
  intro x y hxy
  change hφ.rightDerivExtend hab x ≤ hφ.rightDerivExtend hab y
  by_cases hxa : x ≤ a
  · rw [hφ.rightDerivExtend_of_le_left hab hxa]
    by_cases hya : y ≤ a
    · rw [hφ.rightDerivExtend_of_le_left hab hya]
    · push Not at hya
      by_cases hyb : b ≤ y
      · rw [hφ.rightDerivExtend_of_right_le hab hyb]
        exact csInf_le_csSup hne hbb hba
      · push Not at hyb
        rw [hφ.rightDerivExtend_eq_of_mem_Ioo hab ⟨hya, hyb⟩]
        exact csInf_le_of_le hbb (mem_image_of_mem g ⟨hya, hyb⟩) le_rfl
  · push Not at hxa
    by_cases hxb : b ≤ x
    · rw [hφ.rightDerivExtend_of_right_le hab hxb,
          hφ.rightDerivExtend_of_right_le hab (le_trans hxb hxy)]
    · push Not at hxb
      rw [hφ.rightDerivExtend_eq_of_mem_Ioo hab ⟨hxa, hxb⟩]
      by_cases hyb : b ≤ y
      · rw [hφ.rightDerivExtend_of_right_le hab hyb]
        exact le_csSup_of_le hba (mem_image_of_mem g ⟨hxa, hxb⟩) le_rfl
      · push Not at hyb
        rw [hφ.rightDerivExtend_eq_of_mem_Ioo hab ⟨lt_of_lt_of_le hxa hxy, hyb⟩]
        exact hg_mono ⟨hxa, hxb⟩ ⟨lt_of_lt_of_le hxa hxy, hyb⟩ hxy

/-! ### Continuity and FTC -/

/-- A convex function on `[a, b]` is continuous on the open interior `(a, b)`. -/
-- `hab` is unused in the proof but kept for API consistency with the other `rightDerivExtend`
-- lemmas, all of which require `a < b`.
theorem continuousOn_Ioo (hφ : ConvexOn ℝ (Icc a b) φ) (_hab : a < b) :
    ContinuousOn φ (Ioo a b) := by
  rw [← interior_Icc]; exact hφ.continuousOn_interior

/-- The right derivative of a convex function is interval-integrable on `[a, t]`, given boundedness
of its image on `(a, b)`. -/
theorem intervalIntegrable_rightDeriv (hφ : ConvexOn ℝ (Icc a b) φ) (hab : a < b)
    (hbb : BddBelow ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b))
    (hba : BddAbove ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b))
    {t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    IntervalIntegrable (fun x => derivWithin φ (Ioi x) x) volume a t := by
  rcases eq_or_lt_of_le hat with rfl | hat_lt
  · exact IntervalIntegrable.refl
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hat_lt.le]
  -- The global monotone extension is locally integrable
  set g := fun x => derivWithin φ (Ioi x) x with hg_def
  set G := hφ.rightDerivExtend hab
  have hG_mono : Monotone G := hφ.rightDerivExtend_monotone hab hbb hba
  have hG_li : LocallyIntegrable G volume := hG_mono.locallyIntegrable
  -- G is integrable on the compact set Icc a t
  have hG_int : IntegrableOn G (Icc a t) volume :=
    hG_li.integrableOn_isCompact isCompact_Icc
  -- G agrees with g on Ioo a t ⊆ Ioo a b
  have hGg : EqOn G g (Ioo a t) := by
    intro x hx
    exact hφ.rightDerivExtend_eq_of_mem_Ioo hab ⟨hx.1, lt_of_lt_of_le hx.2 htb⟩
  -- G is integrable on Ioo a t (subset of Icc a t)
  have hG_int_oo : IntegrableOn G (Ioo a t) volume :=
    hG_int.mono_set Ioo_subset_Icc_self
  -- g is integrable on Ioo a t (by EqOn transfer)
  have hg_int_oo : IntegrableOn g (Ioo a t) volume :=
    hG_int_oo.congr_fun hGg measurableSet_Ioo
  -- Ioo a t =ᵐ Ioc a t under volume, so g is integrable on Ioc a t
  exact hg_int_oo.congr_set_ae Ioo_ae_eq_Ioc.symm

/-- **Fundamental theorem of calculus for convex functions**: For `φ` convex and continuous on
`[a, b]`, `∫ₐᵗ φ'₊(s) ds = φ(t) - φ(a)`, where `φ'₊` is the right derivative. -/
theorem ftc_rightDeriv (hφ : ConvexOn ℝ (Icc a b) φ) (hab : a < b)
    (hcont : ContinuousOn φ (Icc a b))
    (hbb : BddBelow ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b))
    (hba : BddAbove ((fun x => derivWithin φ (Ioi x) x) '' Ioo a b))
    {t : ℝ} (hat : a ≤ t) (htb : t ≤ b) :
    ∫ s in a..t, derivWithin φ (Ioi s) s = φ t - φ a := by
  rcases eq_or_lt_of_le hat with rfl | hat
  · simp
  exact integral_eq_sub_of_hasDeriv_right_of_le hat.le
    (hcont.mono (Icc_subset_Icc_right htb))
    (fun x hx => hφ.hasDerivWithinAt_rightDeriv_of_mem_interior
      (by rw [interior_Icc]; exact ⟨hx.1, lt_of_lt_of_le hx.2 htb⟩))
    (hφ.intervalIntegrable_rightDeriv hab hbb hba hat.le htb)

end ConvexOn
