/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib

/-!
# Probability measures inside the real weak-* dual of bounded continuous functions

Mathlib topologizes `ProbabilityMeasure Ω` through the ℝ≥0-valued pairing
(`FiniteMeasure.toWeakDualBCNN`), which does not provide the ambient real topological vector space
that fixed-point theorems need. This file embeds probability measures into `WeakDual ℝ (Ω →ᵇ ℝ)`
via integration, `μ ↦ (f ↦ ∫ f ∂μ)`, and records the transport facts for that embedding:

* the embedding is continuous (the weak topologies match test function by test function);
* it is injective on metrizable spaces (measures are determined by integrals of bounded continuous
  functions);
* convex combinations of probability measures map to convex combinations of functionals, so images
  of "measure-convex" sets are convex;
* on a compact set of measures the embedding is a topological embedding (compact-to-T2).

## Main definitions

* `MeasureTheory.ProbabilityMeasure.toWeakDualBCF`: The integration embedding.

## Tags

weak dual, weak convergence, probability measure, embedding
-/

@[expose] public section

open scoped ENNReal BoundedContinuousFunction
open TopologicalSpace

/-- The real weak-* dual of a seminormed space is locally convex: Its topology is induced by the
evaluation map into the (locally convex) product `F → ℝ`. Mathlib's `WeakBilin.locallyConvexSpace`
does not apply through the `WeakDual` type synonym because the `Module ℝ` instances differ
syntactically; this instance states it at the synonym directly. -/
noncomputable instance WeakDual.instLocallyConvexSpaceReal (F : Type*)
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] : LocallyConvexSpace ℝ (WeakDual ℝ F) :=
  Topology.IsInducing.locallyConvexSpace
    (f := { toFun := fun x : WeakDual ℝ F => (x : F → ℝ)
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl })
    ⟨rfl⟩

namespace MeasureTheory.ProbabilityMeasure

variable {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

/-- Integration against a probability measure, as an element of the real weak-* dual of bounded
continuous functions. This is the ℝ-linear sibling of `FiniteMeasure.toWeakDualBCNN`, providing the
ambient locally convex space for fixed-point arguments over sets of measures. -/
noncomputable def toWeakDualBCF (μ : ProbabilityMeasure Ω) : WeakDual ℝ (Ω →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ ω, f ω ∂(μ : Measure Ω)
      map_add' := fun f g => integral_add (f.integrable _) (g.integrable _)
      map_smul' := fun c f => by simpa using integral_smul c (f : Ω → ℝ) }
    1
    (fun f => by
      simpa using norm_integral_le_of_norm_le_const
        (μ := (μ : Measure Ω)) (ae_of_all _ fun ω => f.norm_coe_le_norm ω))

/-- `toWeakDualBCF μ` evaluated at `f` is the integral of `f` against `μ`. -/
@[simp] lemma toWeakDualBCF_apply (μ : ProbabilityMeasure Ω) (f : Ω →ᵇ ℝ) :
    toWeakDualBCF μ f = ∫ ω, f ω ∂(μ : Measure Ω) := rfl

/-- The integration embedding is continuous from the topology of weak convergence to the weak-*
topology. -/
lemma continuous_toWeakDualBCF :
    Continuous (toWeakDualBCF : ProbabilityMeasure Ω → WeakDual ℝ (Ω →ᵇ ℝ)) := by
  refine WeakDual.continuous_of_continuous_eval (fun f => ?_)
  simpa only [toWeakDualBCF_apply] using continuous_integral_boundedContinuousFunction f

/-- On a (pseudo-)metrizable space, integration against bounded continuous functions determines a
probability measure, so the embedding is injective. -/
lemma toWeakDualBCF_injective [BorelSpace Ω] [PseudoMetrizableSpace Ω] :
    Function.Injective (toWeakDualBCF : ProbabilityMeasure Ω → WeakDual ℝ (Ω →ᵇ ℝ)) := by
  intro μ ν hμν
  apply ProbabilityMeasure.toMeasure_injective
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  simpa only [toWeakDualBCF_apply] using DFunLike.congr_fun hμν f

/-- The image of a set of probability measures that is closed under convex combinations (taken at
the level of measures) is a convex subset of the weak dual. -/
lemma convex_image_toWeakDualBCF {D : Set (ProbabilityMeasure Ω)}
    (hD : ∀ μ ν : ProbabilityMeasure Ω, μ ∈ D → ν ∈ D → ∀ a b : ℝ≥0∞, a + b = 1 →
      ∃ ξ ∈ D, (ξ : Measure Ω) = a • (μ : Measure Ω) + b • (ν : Measure Ω)) :
    Convex ℝ (toWeakDualBCF '' D) := by
  rintro _ ⟨μ, hμ, rfl⟩ _ ⟨ν, hν, rfl⟩ a b ha hb hab
  have hsum : ENNReal.ofReal a + ENNReal.ofReal b = 1 := by
    rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]
  obtain ⟨ξ, hξD, hξ⟩ := hD μ ν hμ hν (ENNReal.ofReal a) (ENNReal.ofReal b) hsum
  refine ⟨ξ, hξD, ?_⟩
  have hintμ : ∀ f : Ω →ᵇ ℝ, Integrable (f : Ω → ℝ) (μ : Measure Ω) := fun f => f.integrable _
  have hintν : ∀ f : Ω →ᵇ ℝ, Integrable (f : Ω → ℝ) (ν : Measure Ω) := fun f => f.integrable _
  refine ContinuousLinearMap.ext (fun f => ?_)
  have hlhs : toWeakDualBCF ξ f
      = a * (∫ ω, f ω ∂(μ : Measure Ω)) + b * (∫ ω, f ω ∂(ν : Measure Ω)) := by
    rw [toWeakDualBCF_apply, hξ,
      integral_add_measure ((hintμ f).smul_measure (by simp)) ((hintν f).smul_measure (by simp)),
      integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal ha,
      ENNReal.toReal_ofReal hb, smul_eq_mul, smul_eq_mul]
  -- `WeakDual` add/smul are the underlying CLM operations, so evaluation distributes
  -- definitionally.
  have hrhs : (a • toWeakDualBCF μ + b • toWeakDualBCF ν) f
      = a * (∫ ω, f ω ∂(μ : Measure Ω)) + b * (∫ ω, f ω ∂(ν : Measure Ω)) := by
    have heval : ((a • toWeakDualBCF μ + b • toWeakDualBCF ν) : WeakDual ℝ (Ω →ᵇ ℝ)) f
        = a • (toWeakDualBCF μ f) + b • (toWeakDualBCF ν f) := rfl
    rw [heval, toWeakDualBCF_apply, toWeakDualBCF_apply, smul_eq_mul, smul_eq_mul]
  exact hlhs.trans hrhs.symm

/-- On a compact set of probability measures the integration embedding is a topological embedding
(continuous injection from a compact space to a T2 space). -/
lemma isEmbedding_restrict_toWeakDualBCF [BorelSpace Ω] [PseudoMetrizableSpace Ω]
    {D : Set (ProbabilityMeasure Ω)} (hD : IsCompact D) :
    Topology.IsEmbedding (fun μ : D => toWeakDualBCF (μ : ProbabilityMeasure Ω)) := by
  haveI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  exact (Continuous.isClosedEmbedding
    (continuous_toWeakDualBCF.comp continuous_subtype_val)
    (toWeakDualBCF_injective.comp Subtype.val_injective)).isEmbedding

end MeasureTheory.ProbabilityMeasure
