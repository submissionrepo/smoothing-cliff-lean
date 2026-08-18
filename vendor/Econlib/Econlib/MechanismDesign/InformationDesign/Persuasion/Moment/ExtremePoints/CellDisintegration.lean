/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.MeasureTheory.AbstractDisintegration
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.ContactFibre
public import Econlib.Probability.ProbDist.Borel

/-!
# Gradient-cell disintegration

Disintegration of a probability measure on `ℝⁿ × Ω` along the gradient-equivalence partition.

## Main definitions

* `cellEquiv`: The setoid on `ℝⁿ × Ω` that identifies points sharing the same first-coordinate
  gradient.
* `quotient_to_real`: Measurable injection from `Quotient (cellEquiv v)` into `ℝ`.
* `cellDisintegration`: Disintegration of a `ProbDist (ℝⁿ × Ω)` along `cellEquiv`.
* `cellRho`: Per-cell probability measure obtained by evaluating `cellDisintegration` at the
  gradient class of a point.

## Main statements

* `cellDisintegration_isStronglyConsistent`: `cellDisintegration` is strongly consistent via
  `quotient_to_real`.

## Tags

persuasion, moment persuasion, extreme points, disintegration
-/

@[expose] public section

open MeasureTheory Set Real
open scoped NNReal Topology ProbabilityTheory

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
variable {n : ℕ}
variable [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω]

/-! ### Disintegration along the gradient setoid -/

/-- Setoid on `ℝⁿ × Ω` identifying points `(x, ω)` and `(x', ω')` whenever
`fderiv ℝ v x = fderiv ℝ v x'`. The Ω-coordinate is irrelevant: This is the gradient-cell partition
of the moment space, lifted to the joint space via projection. -/
noncomputable def cellEquiv (v : EuclideanSpace ℝ (Fin n) → ℝ) :
    Setoid (EuclideanSpace ℝ (Fin n) × Ω) :=
  Setoid.ker (fun p : EuclideanSpace ℝ (Fin n) × Ω => fderiv ℝ v p.1)

/-- Measurable injection `Quotient (cellEquiv v) → ℝ`, obtained by composing `Quotient.lift` with
`MeasureTheory.embeddingReal`. The dual space `ℝⁿ →L[ℝ] ℝ` is a finite-dimensional Banach space
(Polish, hence standard Borel), which is why a measurable embedding into `ℝ` exists. -/
noncomputable def quotient_to_real
    (v : EuclideanSpace ℝ (Fin n) → ℝ) :
    Quotient (cellEquiv (Ω := Ω) v) → ℝ :=
  MeasureTheory.embeddingReal (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∘
    Quotient.lift (fun p : EuclideanSpace ℝ (Fin n) × Ω => fderiv ℝ v p.1)
      (fun _ _ h => h)

omit [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- `quotient_to_real v` is measurable when `v` is `C¹`. -/
lemma quotient_to_real_measurable
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_diff : ContDiff ℝ 1 v) :
    Measurable (quotient_to_real (Ω := Ω) v) := by
  unfold quotient_to_real
  refine (MeasureTheory.measurable_embeddingReal _).comp ?_
  rw [measurable_from_quotient]
  exact (hv_diff.continuous_fderiv one_ne_zero).measurable.comp measurable_fst

omit [PseudoMetricSpace Ω] [BorelSpace Ω] [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [MeasurableSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω] in
/-- `quotient_to_real v` is injective: Distinct gradient classes map to distinct reals. -/
lemma quotient_to_real_injective
    (v : EuclideanSpace ℝ (Fin n) → ℝ) :
    Function.Injective (quotient_to_real (Ω := Ω) v) := by
  intro α β h
  have h_emb_inj :
      Function.Injective
        (MeasureTheory.embeddingReal (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) :=
    (MeasureTheory.measurableEmbedding_embeddingReal _).injective
  have h_lift_eq := h_emb_inj h
  induction α, β using Quotient.inductionOn₂ with
  | h a b => exact Quotient.sound (s := cellEquiv (Ω := Ω) v) h_lift_eq

/-! #### Disintegration construction -/

/-- Disintegration of a probability measure on `ℝⁿ × Ω` along the gradient setoid. -/
noncomputable def cellDisintegration [Nonempty Ω]
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) :
    MeasureTheory.ConsistentDisintegration
      pi.toMeasure (cellEquiv (Ω := Ω) v) :=
  { μα := MeasureTheory.baseKernel pi.toMeasure (cellEquiv v)
    isProbabilityMeasure := fun _ => inferInstance
    measurable_apply := fun _ hE =>
      ProbabilityTheory.Kernel.measurable_coe
        (MeasureTheory.baseKernel pi.toMeasure (cellEquiv v)) hE
    apply_eq_setLIntegral := by
      intro E F hE hF
      letI : Setoid (EuclideanSpace ℝ (Fin n) × Ω) := cellEquiv v
      have hjoint :
          MeasureTheory.joint pi.toMeasure (cellEquiv v) (F ×ˢ E)
            = pi.toMeasure (E ∩ Quotient.mk' ⁻¹' F) :=
        MeasureTheory.joint_apply pi.toMeasure (cellEquiv v) hE hF
      have hcompProd :
          ((MeasureTheory.joint pi.toMeasure (cellEquiv v)).fst
              ⊗ₘ MeasureTheory.baseKernel pi.toMeasure (cellEquiv v))
              (F ×ˢ E)
            = ∫⁻ α in F,
                MeasureTheory.baseKernel pi.toMeasure (cellEquiv v) α E
                  ∂(MeasureTheory.joint pi.toMeasure (cellEquiv v)).fst :=
        MeasureTheory.Measure.compProd_apply_prod hF hE
      have hfst :
          (MeasureTheory.joint pi.toMeasure (cellEquiv v)).fst
            = pi.toMeasure.map Quotient.mk' :=
        MeasureTheory.joint_fst pi.toMeasure (cellEquiv v)
      calc pi.toMeasure (E ∩ Quotient.mk' ⁻¹' F)
          = MeasureTheory.joint pi.toMeasure (cellEquiv v) (F ×ˢ E) :=
            hjoint.symm
        _ = ((MeasureTheory.joint pi.toMeasure (cellEquiv v)).fst
                ⊗ₘ MeasureTheory.baseKernel pi.toMeasure (cellEquiv v))
                (F ×ˢ E) := by
            rw [MeasureTheory.baseKernel_disintegrate pi.toMeasure
              (cellEquiv v)]
        _ = ∫⁻ α in F,
              MeasureTheory.baseKernel pi.toMeasure (cellEquiv v) α E
                ∂(MeasureTheory.joint pi.toMeasure (cellEquiv v)).fst :=
            hcompProd
        _ = ∫⁻ α in F,
              MeasureTheory.baseKernel pi.toMeasure (cellEquiv v) α E
                ∂(pi.toMeasure.map Quotient.mk') := by
            rw [hfst] }

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- Strong consistency of `cellDisintegration` via the measurable injection `quotient_to_real`. -/
lemma cellDisintegration_isStronglyConsistent [Nonempty Ω]
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_diff : ContDiff ℝ 1 v)
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) :
    (cellDisintegration pi (v := v)).IsStronglyConsistent :=
  (cellDisintegration pi (v := v)).isStronglyConsistent_of_injection
    pi.toMeasure (quotient_to_real_measurable hv_diff)
    (quotient_to_real_injective v)

/-- Per-cell probability measure obtained from `cellDisintegration` at the gradient class of `x₀`.
The Ω-component in the quotient class representative is irrelevant: `cellEquiv v` is
`Setoid.ker (fderiv ℝ v ∘ Prod.fst)`, which depends only on the first coordinate. -/
noncomputable def cellRho [Nonempty Ω]
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ProbDist (EuclideanSpace ℝ (Fin n) × Ω) := by
  haveI : IsProbabilityMeasure
      ((cellDisintegration pi (v := v)).μα
        (Quotient.mk (cellEquiv v) (x₀, Classical.arbitrary Ω))) :=
    (cellDisintegration pi (v := v)).isProbabilityMeasure _
  exact ⟨(cellDisintegration pi (v := v)).μα
    (Quotient.mk (cellEquiv v) (x₀, Classical.arbitrary Ω)),
    inferInstance⟩

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
