/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.MeasurableCaratheodory
public import Econlib.Math.Analysis.MinkowskiCaratheodory
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.ContactFibre
public import Econlib.Probability.ProbDist.Borel

/-!
# Measurable Choquet kernel for extreme-point selection

Carathéodory representatives on compact convex sets and a measurable Choquet kernel that selects
extreme-point support for optimal signals in moment persuasion.

## Main definitions

* `extremePoint_caratheodory_finite_dim`: Every point of a compact convex set in `ℝⁿ` is the
  barycenter of a probability measure supported on the extreme points.
* `measurable_choquet_kernel`: A measurable Markov kernel `κ` such that for a.e. `x` in a closed
  active set, `κ x` is supported on the extreme points of the contact fiber `Gamma_x s v S x` with
  mean `x`.

## Tags

persuasion, moment persuasion, extreme points, Choquet, Carathéodory
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

/-- For any compact convex `K ⊆ ℝⁿ` and any `x ∈ K`, there exists a probability measure `ν` on `ℝⁿ`
supported on `Set.extremePoints ℝ K` with `∫ y dν = x`. -/
lemma extremePoint_caratheodory_finite_dim
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ K) :
    ∃ ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)),
      MeasureTheory.IsProbabilityMeasure ν ∧
      ν (Set.extremePoints ℝ K) = 1 ∧
      ∫ y, y ∂ν = x :=
  exists_extremePoint_measure_of_compact_convex
    hK_compact hK_convex hx

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- Measurable Choquet/Carathéodory selection in an a.e. form.  For a closed active set `S` and any
finite reference measure `ν` supported on `S`, there is a measurable Markov kernel
`κ : ℝⁿ → Measure ℝⁿ` such that, for `ν`-a.e. `x`, `κ x` is supported on
`Set.extremePoints ℝ (Gamma_x s v S x)` with mean `x`. -/
lemma measurable_choquet_kernel (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_diff : ContDiff ℝ 1 v)
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hS_closed : IsClosed S)
    (hS_sub : S ⊆ s.X)
    (hS_active : ∀ x ∈ S, v x = pStar v S x)
    (hpStar_cont : Continuous (pStar v S))
    (ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
    [MeasureTheory.IsFiniteMeasure ν]
    (hν_supp : ν Sᶜ = 0) :
    ∃ κ : EuclideanSpace ℝ (Fin n) →
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)),
      Measurable κ ∧
      (∀ x, MeasureTheory.IsProbabilityMeasure (κ x)) ∧
      ∀ᵐ x ∂ν,
        (κ x) (Set.extremePoints ℝ (Gamma_x s v S x)) = 1 ∧
        ∫ y, y ∂(κ x) = x := by
  classical
  haveI : PolishSpace (↥S) := hS_closed.polishSpace
  haveI : MeasureTheory.IsFiniteMeasure
      (MeasureTheory.Measure.comap
        (Subtype.val : ↥S → EuclideanSpace ℝ (Fin n)) ν) :=
    MeasureTheory.IsFiniteMeasure_comap _
  set c : EuclideanSpace ℝ (Fin n) := s.X_interior.some
  let F : ↥S → Set (EuclideanSpace ℝ (Fin n)) :=
    fun y => Gamma_x s v S (y : EuclideanSpace ℝ (Fin n))
  let z₀ : ↥S → EuclideanSpace ℝ (Fin n) :=
    fun y => (y : EuclideanSpace ℝ (Fin n))
  have hF_sub_K : ∀ y : ↥S, F y ⊆ s.X := fun y => Gamma_x_subset_X s v S y.val
  have hF_graph_closed :
      IsClosed {p : ↥S × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1} := by
    have h_global := Gamma_x_graph_isClosed s hv_diff S hpStar_cont
    have h_cont :
        Continuous fun p : ↥S × EuclideanSpace ℝ (Fin n) =>
          ((p.1 : EuclideanSpace ℝ (Fin n)), p.2) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact h_global.preimage h_cont
  have hF_convex : ∀ y : ↥S, Convex ℝ (F y) := fun y =>
    Gamma_x_isConvex s hv_diff hS_sub y.2 (hS_active y.val y.2)
  have hz₀_meas : Measurable z₀ := continuous_subtype_val.measurable
  have hz₀_mem : ∀ y : ↥S, z₀ y ∈ F y := by
    intro y
    refine ⟨hS_sub y.2, ?_⟩
    have h_active : v y.val = pStar v S y.val := hS_active y.val y.2
    rw [sub_self, map_zero, add_zero, h_active]
  set ν' : MeasureTheory.Measure (↥S) :=
    MeasureTheory.Measure.comap
      (Subtype.val : ↥S → EuclideanSpace ℝ (Fin n)) ν
  obtain ⟨κ_S, hκ_meas, hκ_prob, hκ_ae⟩ :=
    AuxiliaryOptimization.exists_measurable_caratheodory_kernel_ae
      (Y := ↥S) (F := F) (K := s.X) (z₀ := z₀)
      s.X_compact hF_sub_K hF_graph_closed hF_convex
      hz₀_meas hz₀_mem ν'
  set κ : EuclideanSpace ℝ (Fin n) →
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) := fun x =>
    if h : x ∈ S then κ_S ⟨x, h⟩ else MeasureTheory.Measure.dirac c
  refine ⟨κ, ?_, ?_, ?_⟩
  · exact Measurable.dite hκ_meas measurable_const hS_closed.measurableSet
  · intro x
    by_cases hx : x ∈ S
    · simp only [hx, ↓reduceDIte, κ]; exact hκ_prob ⟨x, hx⟩
    · simp only [hx, ↓reduceDIte, κ]; infer_instance
  · have h_S_meas : MeasurableSet S := hS_closed.measurableSet
    have hκ_eq_on_S : ∀ y : ↥S, κ (Subtype.val y) = κ_S y := by
      intro y
      simp [κ, y.2]
    have hκ_ae_S :
        ∀ᵐ y ∂ν',
          (κ (Subtype.val y))
              (Set.extremePoints ℝ (Gamma_x s v S (Subtype.val y))) = 1 ∧
          ∫ z, z ∂(κ (Subtype.val y)) = Subtype.val y := by
      filter_upwards [hκ_ae] with y hy
      rw [hκ_eq_on_S y]
      exact hy
    have hκ_restrict :
        ∀ᵐ x ∂(ν.restrict S),
          (κ x) (Set.extremePoints ℝ (Gamma_x s v S x)) = 1 ∧
          ∫ z, z ∂(κ x) = x :=
      (ae_restrict_iff_subtype h_S_meas).mpr hκ_ae_S
    have h_ae_in_S : ∀ᵐ x ∂ν, x ∈ S := by
      rw [MeasureTheory.ae_iff]
      simpa using hν_supp
    exact MeasureTheory.Measure.restrict_eq_self_of_ae_mem h_ae_in_S ▸ hκ_restrict

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
