/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.ExtremePointsGDelta
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.DifferentiableUniqueness
public import Econlib.Probability.ProbDist.Borel

/-!
# Contact-set fiber `Γ_x`

Basic geometric properties of the contact-set fiber `Gamma_x s v S x`: Closedness, compactness,
convexity, and Borel measurability of its extreme points, all under the active-set hypothesis
`S ⊆ s.X`, `x ∈ S`, `v x = pStar v S x`.

## Main statements

* `Gamma_x_isCompact`: `Γ_x` is compact under the active-set hypothesis.
* `Gamma_x_isConvex`: `Γ_x` is convex under the active-set hypothesis.
* `Gamma_x_isClosed`: `Γ_x` is closed under the active-set hypothesis.
* `measurableSet_extremePoints_Gamma_x`: The extreme points of `Γ_x` form a Borel-measurable set.
* `mean_preserving_value_invariance`: Two couplings with the same `Prod.fst` marginal yield the
  same integral of any measurable function of the first coordinate.
* `integral_pStar_eq_value_at_mean_on_Gamma_x`: If `ν` is supported on `Γ_x` with mean `x`, then
  `∫ y, pStar v S y ∂ν = v x`.

## Tags

persuasion, moment persuasion, extreme points, contact set
-/

@[expose] public section

open MeasureTheory Set Real
open scoped NNReal Topology ProbabilityTheory

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two probability distributions on `ℝⁿ × Ω` with the same `Prod.fst` marginal yield the same
integral of any measurable `v ∘ Prod.fst`. -/
lemma mean_preserving_value_invariance
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_meas : Measurable v)
    {pi pi' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (h_marg :
      ProbDist.map pi Prod.fst measurable_fst
        = ProbDist.map pi' Prod.fst measurable_fst) :
    ∫ p, v p.1 ∂pi.toMeasure = ∫ p, v p.1 ∂pi'.toMeasure := by
  -- Push `v ∘ fst` through the marginal pushforward; the marginals agree, so the integrals do.
  have push : ∀ q : ProbDist (EuclideanSpace ℝ (Fin n) × Ω),
      ∫ p, v p.1 ∂q.toMeasure
        = ∫ x, v x ∂(ProbDist.map q Prod.fst measurable_fst).toMeasure := fun q => by
    rw [ProbDist.map_toMeasure]
    exact (MeasureTheory.integral_map measurable_fst.aemeasurable
      hv_meas.aestronglyMeasurable).symm
  rw [push pi, push pi', h_marg]

variable [PseudoMetricSpace Ω] [BorelSpace Ω]

variable {n : ℕ}

/-- The contact-set fiber sits inside the moment image `s.X`. -/
lemma Gamma_x_subset_X (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    Gamma_x s v S x ⊆ s.X := fun _ hy => hy.1

/-- On `Γ_x`, the dual price `pStar v S` agrees with the tangent hyperplane to `v` at `x`. -/
lemma pStar_eq_affine_minorant_on_Gamma_x (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    {x y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ Gamma_x s v S x) :
    pStar v S y = v x + (fderiv ℝ v x) (y - x) := hy.2

/-- Any joint `π` satisfying condition (M) is supported on the contact-set graph
`{(x, ω) | s.m ω ∈ Γ_x}`. -/
lemma optimal_pi_Gamma_x_ae (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hM : ConditionM s v pi S) :
    ∀ᵐ p ∂pi.toMeasure, s.m p.2 ∈ Gamma_x s v S p.1 := by
  filter_upwards [hM.active_ae] with p hp using ⟨s.m_mem_X p.2, hp⟩

variable [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω]

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- `Γ_x` is compact whenever `S ⊆ s.X`, `x ∈ S`, and `x` is active (`v x = pStar v S x`). -/
lemma Gamma_x_isCompact (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_diff : ContDiff ℝ 1 v)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ⊆ s.X)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S)
    (hx_active : v x = pStar v S x) :
    IsCompact (Gamma_x s v S x) :=
  (Gamma_x_isCompact_isConvex_mem_argMin s hv_diff hS hx hx_active).1

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- `Γ_x` is convex under the same hypotheses as `Gamma_x_isCompact`. -/
lemma Gamma_x_isConvex (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_diff : ContDiff ℝ 1 v)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ⊆ s.X)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S)
    (hx_active : v x = pStar v S x) :
    Convex ℝ (Gamma_x s v S x) :=
  (Gamma_x_isCompact_isConvex_mem_argMin s hv_diff hS hx hx_active).2.1

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- `Γ_x` is closed whenever it is compact. -/
lemma Gamma_x_isClosed (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_diff : ContDiff ℝ 1 v)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ⊆ s.X)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S)
    (hx_active : v x = pStar v S x) :
    IsClosed (Gamma_x s v S x) :=
  (Gamma_x_isCompact s hv_diff hS hx hx_active).isClosed

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- The extreme points of `Γ_x` form a Borel-measurable set. -/
lemma measurableSet_extremePoints_Gamma_x (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_diff : ContDiff ℝ 1 v)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ⊆ s.X)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S)
    (hx_active : v x = pStar v S x) :
    MeasurableSet (Set.extremePoints ℝ (Gamma_x s v S x)) :=
  measurableSet_extremePoints_of_compact_convex
    (Gamma_x_isCompact s hv_diff hS hx hx_active)
    (Gamma_x_isConvex s hv_diff hS hx hx_active)

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- If `ν` is a probability measure supported on `Γ_x` with mean `x`, then
`∫ y, pStar v S y ∂ν = v x`. -/
lemma integral_pStar_eq_value_at_mean_on_Gamma_x (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_diff : ContDiff ℝ 1 v)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : S ⊆ s.X)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ S)
    (hx_active : v x = pStar v S x)
    {ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))}
    [MeasureTheory.IsProbabilityMeasure ν]
    (hν_supp : ν (Gamma_x s v S x) = 1)
    (hν_mean : ∫ y, y ∂ν = x)
    (hν_int : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin n) => y) ν) :
    ∫ y, pStar v S y ∂ν = v x := by
  have h_meas : MeasurableSet (Gamma_x s v S x) :=
    (Gamma_x_isClosed s hv_diff hS hx hx_active).measurableSet
  have h_ae_eq : ∀ᵐ y ∂ν, pStar v S y = v x + (fderiv ℝ v x) (y - x) := by
    have h_ae_Gamma : ∀ᵐ y ∂ν, y ∈ Gamma_x s v S x :=
      (MeasureTheory.mem_ae_iff_prob_eq_one h_meas).mpr hν_supp
    filter_upwards [h_ae_Gamma] with y hy using
      pStar_eq_affine_minorant_on_Gamma_x s hy
  rw [MeasureTheory.integral_congr_ae h_ae_eq]
  set L := fderiv ℝ v x
  have h_int_y_minus_x :
      MeasureTheory.Integrable
        (fun y : EuclideanSpace ℝ (Fin n) => y - x) ν :=
    hν_int.sub (MeasureTheory.integrable_const x)
  have h_int_L_y_minus_x :
      MeasureTheory.Integrable
        (fun y : EuclideanSpace ℝ (Fin n) => L (y - x)) ν :=
    L.integrable_comp h_int_y_minus_x
  have h_int_const :
      MeasureTheory.Integrable
        (fun _ : EuclideanSpace ℝ (Fin n) => v x) ν :=
    MeasureTheory.integrable_const _
  rw [MeasureTheory.integral_add h_int_const h_int_L_y_minus_x,
    MeasureTheory.integral_const,
    ContinuousLinearMap.integral_comp_comm L h_int_y_minus_x,
    MeasureTheory.integral_sub hν_int (MeasureTheory.integrable_const x),
    MeasureTheory.integral_const, hν_mean]
  simp

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
