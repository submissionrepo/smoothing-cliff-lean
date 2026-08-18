/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Probability.ProbDist.Basic
public import Econlib.Probability.ProbDist.Support
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Lifting a `ProbDist` to a subtype

`ProbDist.toSubtype d hs hμ` lifts a probability distribution `d : ProbDist α` that is supported on
a measurable set `s : Set α` (i.e. `d.toMeasure s = 1`) to a probability distribution on the
subtype `↥s`. The underlying measure is `MeasureTheory.Measure.comap Subtype.val d.toMeasure`, the
measure inherited from the ambient space.

## Main definitions

* `ProbDist.toSubtype` — the lifted probability distribution on `↥s`.

## Main statements

* `ProbDist.map_subtype_val_toSubtype` — pushing the lift back along `Subtype.val` recovers `d`.
* `ProbDist.integral_toSubtype` — integration against the lift equals restricted integration
  against `d`.
* `ProbDist.measurePreserving_subtype_val` — `Subtype.val` is measure-preserving from the lifted
  measure on `↥s` to `d.toMeasure`.

## Tags

probability distribution, subtype, comap, measure-preserving
-/

@[expose] public section

open MeasureTheory Set

namespace Econlib.Probability

namespace ProbDist

variable {α : Type*} [MeasurableSpace α]

/-- A probability distribution `d` on `α` that assigns full mass to a measurable set `s` lifts to a
probability distribution on the subtype `↥s`. Concretely, the underlying measure is the comap of
`d.toMeasure` along `Subtype.val`. -/
noncomputable def toSubtype {s : Set α} (d : ProbDist α) (hs : MeasurableSet s)
    (hμ : d.toMeasure s = 1) : ProbDist s :=
  letI : IsProbabilityMeasure d.toMeasure := d.2
  have hemb : MeasurableEmbedding (Subtype.val : s → α) :=
    MeasurableEmbedding.subtype_coe hs
  have hae : ∀ᵐ a ∂d.toMeasure, a ∈ Set.range (Subtype.val : s → α) := by
    rw [Subtype.range_val]
    have hnull : d.toMeasure sᶜ = 0 :=
      (prob_compl_eq_zero_iff hs).mpr hμ
    simpa [ae_iff, Set.mem_compl_iff] using hnull
  ⟨Measure.comap Subtype.val d.toMeasure, hemb.isProbabilityMeasure_comap hae⟩

/-- The measure underlying `d.toSubtype` is the comap of `d.toMeasure` along `Subtype.val`. -/
@[simp] lemma toSubtype_toMeasure {s : Set α} (d : ProbDist α) (hs : MeasurableSet s)
    (hμ : d.toMeasure s = 1) :
    (d.toSubtype hs hμ).toMeasure = Measure.comap Subtype.val d.toMeasure := rfl

/-- Pushing forward `d.toSubtype` along `Subtype.val` recovers `d`. -/
theorem map_subtype_val_toSubtype {s : Set α} (d : ProbDist α)
    (hs : MeasurableSet s) (hμ : d.toMeasure s = 1) :
    ProbDist.map (d.toSubtype hs hμ) (Subtype.val : s → α) measurable_subtype_coe = d := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbDist.map_toMeasure, toSubtype_toMeasure]
  have hemb : MeasurableEmbedding (Subtype.val : s → α) :=
    MeasurableEmbedding.subtype_coe hs
  rw [hemb.map_comap d.toMeasure, Subtype.range_val]
  letI : IsProbabilityMeasure d.toMeasure := d.2
  have hae : ∀ᵐ a ∂d.toMeasure, a ∈ s := by
    have hnull : d.toMeasure sᶜ = 0 :=
      (prob_compl_eq_zero_iff hs).mpr hμ
    simpa [ae_iff, Set.mem_compl_iff] using hnull
  exact Measure.restrict_eq_self_of_ae_mem hae

/-- `Subtype.val` is measure-preserving from `d.toSubtype` to `d`. -/
theorem measurePreserving_subtype_val {s : Set α} (d : ProbDist α)
    (hs : MeasurableSet s) (hμ : d.toMeasure s = 1) :
    MeasurePreserving (Subtype.val : s → α)
      (d.toSubtype hs hμ).toMeasure d.toMeasure := by
  refine ⟨measurable_subtype_coe, ?_⟩
  have hmap := congr_arg ProbabilityMeasure.toMeasure (map_subtype_val_toSubtype d hs hμ)
  simpa [ProbDist.map_toMeasure] using hmap

/-- Integration against `d.toSubtype` equals restricted integration against `d`. -/
theorem integral_toSubtype {s : Set α} (d : ProbDist α)
    (hs : MeasurableSet s) (hμ : d.toMeasure s = 1)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : α → E) :
    ∫ x, f (Subtype.val x) ∂(d.toSubtype hs hμ).toMeasure
      = ∫ x in s, f x ∂d.toMeasure := by
  rw [toSubtype_toMeasure]
  exact MeasureTheory.integral_subtype_comap hs f

end ProbDist

end Econlib.Probability
