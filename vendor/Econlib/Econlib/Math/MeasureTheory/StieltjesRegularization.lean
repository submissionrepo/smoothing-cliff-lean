/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.StieltjesIBP
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Stieltjes regularization of monotone functions

Generic plumbing facts about the right-continuous regularization `Monotone.stieltjesFunction f` of
a monotone real function `f`, exposed under the convenience abbreviations
`stieltjes`/`stieltjesMeasure` from `StieltjesIBP`:

* Stieltjes regularization is the identity on right-continuous functions and equals the `rightLim`
  everywhere; its `leftLim` then agrees with the original function almost everywhere (the set of
  discontinuities of a monotone function is countable, hence null).
* The Stieltjes function and Stieltjes measure of the identity coincide with the identity and
  Lebesgue measure respectively.

These statements are purely about monotone real functions and their Stieltjes measures, with no
reference to CDFs or distributions.

## Main statements

* `stieltjes_eq_of_rightCts` — right-continuity ⟹ Stieltjes regularization is the identity.
* `stieltjesMeasure_Ioo_eq_zero_of_constantOn` — an interval on which the function is constant
  carries no Stieltjes mass.
* `stieltjes_eq_ae` — `stieltjes u =ᵐ[volume] u` for monotone `u`.
* `leftLim_stieltjes_eq_ae` — `leftLim ∘ stieltjes u =ᵐ[volume] u` for monotone `u`.
* `stieltjes_id_eq`, `stieltjes_id_eq_sfId`, `stieltjesMeasure_id_eq_volume` — identity-Stieltjes
  identifications.

## Tags

stieltjes, monotone function, right-continuous regularization
-/

@[expose] public section

open MeasureTheory Set Filter Function
open scoped Topology Real

namespace Monotone

/-- For a right-continuous monotone function, Stieltjes regularization is the identity. -/
lemma stieltjes_eq_of_rightCts {f : ℝ → ℝ} (hf : Monotone f)
    (hrc : ∀ x, ContinuousWithinAt f (Ici x) x) (x : ℝ) :
    hf.stieltjesFunction x = f x := by
  rw [Monotone.stieltjesFunction_eq]
  exact rightLim_eq_of_tendsto (nhdsWithin_Ioi_neBot le_rfl).ne
    ((hrc x).mono_left (nhdsWithin_mono x Ioi_subset_Ici_self))

/-- A monotone function constant on an open interval assigns that interval zero Stieltjes mass: If
`f` is constant on `Ioo p r`, then `hf.stieltjesMeasure (Ioo p r) = 0`. -/
lemma stieltjesMeasure_Ioo_eq_zero_of_constantOn {f : ℝ → ℝ} (hf : Monotone f) {p r k : ℝ}
    (hpr : p < r) (hconst : ∀ x ∈ Set.Ioo p r, f x = k) :
    hf.stieltjesMeasure (Set.Ioo p r) = 0 := by
  -- `sf p = rightLim f p = k` and `leftLim sf r = k`, so `measure_Ioo`'s integrand
  -- `leftLim sf r − sf p` vanishes, hence `ofReal` of it is `0`.
  set sf := hf.stieltjes with hsf
  -- `sf y = rightLim f y = k` for every `y ∈ Ico p r`: `f = k` on the right-neighborhood `(y, r)`.
  have hsf_eq : ∀ y ∈ Set.Ico p r, sf y = k := by
    intro y hy
    rw [hsf, Monotone.stieltjesFunction_eq]
    refine rightLim_eq_of_tendsto (nhdsWithin_Ioi_neBot le_rfl).ne ?_
    have hev : ∀ᶠ z in nhdsWithin y (Set.Ioi y), f z = k := by
      filter_upwards [Ioo_mem_nhdsGT hy.2] with z hz
      exact hconst z ⟨lt_of_le_of_lt hy.1 hz.1, hz.2⟩
    exact (tendsto_congr' hev).mpr tendsto_const_nhds
  have hsfp : sf p = k := hsf_eq p ⟨le_rfl, hpr⟩
  -- `leftLim sf r = k`: `sf = k` on `[p, r)`, a left-neighborhood of `r`.
  have hleftLim : Function.leftLim (⇑sf) r = k := by
    refine leftLim_eq_of_tendsto (nhdsWithin_Iio_neBot le_rfl).ne ?_
    have hev : ∀ᶠ z in nhdsWithin r (Set.Iio r), sf z = k := by
      filter_upwards [Ioo_mem_nhdsLT hpr] with z hz
      exact hsf_eq z ⟨hz.1.le, hz.2⟩
    exact (tendsto_congr' hev).mpr tendsto_const_nhds
  change sf.measure (Set.Ioo p r) = 0
  rw [StieltjesFunction.measure_Ioo, hleftLim, hsfp, sub_self, ENNReal.ofReal_zero]

end Monotone

namespace MeasureTheory

/-- A monotone function agrees Lebesgue-a.e. with its right-continuous Stieltjes regularization. -/
lemma stieltjes_eq_ae {u : ℝ → ℝ} (hu : Monotone u) :
    ⇑(hu.stieltjes) =ᵐ[volume] u := by
  have hD : volume {x | ¬ContinuousAt u x} = 0 := hu.countable_not_continuousAt.measure_zero volume
  filter_upwards [compl_mem_ae_iff.mpr hD] with x hx
  have hcont : ContinuousAt u x := not_not.mp hx
  rw [Monotone.stieltjes, hu.stieltjesFunction_eq]
  exact hcont.continuousWithinAt.rightLim_eq

/-- The left limit of the Stieltjes regularization agrees Lebesgue-a.e. with the original monotone
function: `leftLim (stieltjes u) =ᵐ[volume] u`. -/
lemma leftLim_stieltjes_eq_ae (u : ℝ → ℝ) (hu : Monotone u) :
    leftLim (⇑(hu.stieltjes)) =ᵐ[volume] u := by
  rw [eventuallyEq_iff_exists_mem]
  refine ⟨{x | ContinuousAt u x}, ?_, ?_⟩
  · rw [mem_ae_iff]; exact hu.countable_not_continuousAt.measure_zero _
  · intro x (hx : ContinuousAt u x)
    have h_rc : (hu.stieltjes) x = u x := by
      rw [Monotone.stieltjesFunction_eq]
      exact rightLim_eq_of_tendsto (nhdsWithin_Ioi_neBot le_rfl).ne
        (hx.tendsto.mono_left nhdsWithin_le_nhds)
    have h_cont : ContinuousAt (⇑(hu.stieltjes)) x := by
      change ContinuousAt (⇑hu.stieltjesFunction) x
      have h_eq : rightLim u x = u x := h_rc ▸ Monotone.stieltjesFunction_eq hu x
      rw [ContinuousAt, funext (Monotone.stieltjesFunction_eq hu), h_eq,
          ← nhdsWithin_univ, ← Iio_union_Ici, nhdsWithin_union]
      exact Tendsto.sup
        (tendsto_of_tendsto_of_tendsto_of_le_of_le'
          (hx.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds
          (.of_forall fun y => hu.le_rightLim le_rfl)
          (eventually_nhdsWithin_of_forall fun y (hy : y < x) => hu.rightLim_le hy))
        (h_eq ▸ (funext (Monotone.stieltjesFunction_eq hu) ▸
          hu.stieltjesFunction.right_continuous x))
    rw [leftLim_eq_of_tendsto (nhdsWithin_Iio_neBot le_rfl).ne
        (h_cont.tendsto.mono_left nhdsWithin_le_nhds), h_rc]

/-- The Stieltjes function of the identity is the identity. -/
lemma stieltjes_id_eq : ⇑(Monotone.stieltjes monotone_id) = id := by
  ext y; change monotone_id.stieltjesFunction y = y
  rw [Monotone.stieltjesFunction_eq]
  exact rightLim_eq_of_tendsto (nhdsWithin_Ioi_neBot le_rfl).ne
    (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds)

/-- As a `StieltjesFunction`, the Stieltjes function of the identity equals
`StieltjesFunction.id`. -/
lemma stieltjes_id_eq_sfId : Monotone.stieltjes monotone_id = StieltjesFunction.id :=
  StieltjesFunction.ext (fun y => by rw [stieltjes_id_eq]; rfl)

/-- The Stieltjes measure of the identity is Lebesgue measure. -/
lemma stieltjesMeasure_id_eq_volume : Monotone.stieltjesMeasure monotone_id = volume := by
  change (Monotone.stieltjes monotone_id).measure = volume
  rw [stieltjes_id_eq_sfId, Real.volume_eq_stieltjes_id]

end MeasureTheory
