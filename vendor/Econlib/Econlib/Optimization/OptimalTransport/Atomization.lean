/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Optimization.OptimalTransport.KantorovichRubinstein
public import Mathlib.Topology.MetricSpace.Cover

/-!
# Finite atomizations of compact metric laws

This file defines the ε-net atomization interface for compact metric laws. Given a compact metric
space and `ε > 0`, `exists_eps_partition` produces a finite measurable nearest-net map `V : Ω → S`.
Pushing a law forward through `V` yields a finitely supported **atomized** law within ε in both the
KR dual distance and the primal transport cost.

## Main definitions

* `atomize` — the pushforward of a law along the net selector `V`.
* `atomizeCoupling` — the graph coupling `(id, V)_* μ` between a law and its atomization.

## Main statements

* `exists_eps_partition` — a compact metric space admits a measurable finite ε-net selector.
* `atomizeCoupling_isCoupling` — the graph coupling has marginals `μ` and `atomize μ V`.
* `atomize_krTransportCost_le`, `atomize_krDist_le` — atomization moves mass by at most the
  selector radius in primal transport cost and KR distance.

## Tags

atomization, epsilon-net, kantorovich-rubinstein, coupling, optimal transport
-/

@[expose] public section

open MeasureTheory Set BoundedContinuousFunction
open Econlib.Probability Econlib.Probability.ProbDist

namespace Econlib.Optimization.OptimalTransport

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A measurable finite ε-net selector on a compact metric space. -/
theorem exists_eps_partition [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω] [CompactSpace Ω]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : Finset Ω) (V : Ω → S), Measurable V ∧ ∀ x, dist x (V x : Ω) < ε := by
  classical
  -- A direct first-hit selector for a nonempty finite list of centers.
  have selector_cons :
      ∀ (a : Ω) (l : List Ω),
        ∃ g : Ω → Ω, Measurable g ∧ (∀ x, g x ∈ a :: l) ∧
          ∀ x, (∃ y ∈ a :: l, dist x y < ε) → dist x (g x) < ε := by
    intro a l
    induction l generalizing a with
    | nil =>
        refine ⟨fun _ => a, measurable_const, ?_, ?_⟩
        · intro x
          simp
        · intro x hx
          rcases hx with ⟨y, hy, hyε⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          subst y
          simpa using hyε
    | cons b l ih =>
        obtain ⟨g_tail, hg_tail_meas, hg_tail_mem, hg_tail_dist⟩ := ih b
        let g : Ω → Ω := fun x => if x ∈ Metric.ball a ε then a else g_tail x
        refine ⟨g, ?_, ?_, ?_⟩
        · dsimp [g]
          have hball : MeasurableSet (Metric.ball a ε) :=
            measurableSet_ball
          exact Measurable.ite hball measurable_const hg_tail_meas
        · intro x
          dsimp [g]
          by_cases hx : x ∈ Metric.ball a ε
          · simp [hx]
          · have htail : g_tail x ∈ b :: l := hg_tail_mem x
            simp [hx, htail]
        · intro x hxcover
          dsimp [g]
          by_cases hx : x ∈ Metric.ball a ε
          · have hxdist : dist x a < ε := by
              simpa [Metric.mem_ball] using hx
            simpa [hx] using hxdist
          · have htail_cover : ∃ y ∈ b :: l, dist x y < ε := by
              rcases hxcover with ⟨y, hy, hyε⟩
              simp only [List.mem_cons] at hy
              rcases hy with rfl | hy
              · exact False.elim (hx (by simpa [Metric.mem_ball] using hyε))
              · exact ⟨y, by simpa [List.mem_cons] using hy, hyε⟩
            simpa [hx] using hg_tail_dist x htail_cover
  by_cases hΩ : Nonempty Ω
  · let U : Ω → Set Ω := fun y => Metric.ball y ε
    have hUo : ∀ y, IsOpen (U y) := fun y => Metric.isOpen_ball
    have hcover : (Set.univ : Set Ω) ⊆ ⋃ y, U y := by
      intro x hx
      refine mem_iUnion.mpr ⟨x, ?_⟩
      simp [U, hε]
    obtain ⟨S₀, hS₀_cover⟩ :=
      isCompact_univ.elim_finite_subcover U hUo hcover
    have hS₀_cover' : ∀ x, ∃ y ∈ S₀, dist x y < ε := by
      intro x
      have hx : x ∈ ⋃ y ∈ S₀, U y := hS₀_cover (by simp)
      simpa [U, Metric.mem_ball] using hx
    obtain ⟨x₀⟩ := hΩ
    obtain ⟨a, haS₀, -⟩ := hS₀_cover' x₀
    let l : List Ω := (S₀.erase a).toList
    have hcover_list : ∀ x, ∃ y ∈ a :: l, dist x y < ε := by
      intro x
      obtain ⟨y, hyS₀, hyε⟩ := hS₀_cover' x
      by_cases hya : y = a
      · subst y
        exact ⟨a, by simp, hyε⟩
      · have hyerase : y ∈ S₀.erase a := by
          simp [Finset.mem_erase, hya, hyS₀]
        exact ⟨y, by simp [l, hyerase], hyε⟩
    obtain ⟨g, hg_meas, hg_mem, hg_dist⟩ := selector_cons a l
    let S : Finset Ω := insert a (S₀.erase a)
    have hg_mem_S : ∀ x, g x ∈ S := by
      intro x
      have hxmem := hg_mem x
      simpa [S, l] using hxmem
    let V : Ω → S := fun x => ⟨g x, hg_mem_S x⟩
    refine ⟨S, V, ?_, ?_⟩
    · exact hg_meas.subtype_mk
    · intro x
      exact hg_dist x (hcover_list x)
  · let S : Finset Ω := ∅
    let V : Ω → S := fun x => False.elim (hΩ ⟨x⟩)
    refine ⟨S, V, ?_, ?_⟩
    · exact measurable_of_subsingleton_codomain V
    · intro x
      exact False.elim (hΩ ⟨x⟩)

/-- Push `μ` onto the finite set selected by `V`. -/
noncomputable def atomize (μ : ProbabilityMeasure Ω) {S : Finset Ω}
    (V : Ω → S) (hV : Measurable V) : ProbabilityMeasure Ω :=
  map μ (fun x => (V x : Ω)) hV.subtype_val

/-- The atomized law is supported on the finite net. -/
lemma atomize_support [MeasurableSingletonClass Ω] (μ : ProbabilityMeasure Ω)
    {S : Finset Ω} (V : Ω → S) (hV : Measurable V) :
    (atomize μ V hV).toMeasure (S : Set Ω) = 1 := by
  unfold atomize
  rw [map_toMeasure]
  rw [Measure.map_apply hV.subtype_val (Finset.measurableSet S)]
  have hpre : (fun x : Ω => (V x : Ω)) ⁻¹' (S : Set Ω) = Set.univ := by
    ext x
    simp
  rw [hpre]
  simp

/-- The explicit coupling `(id, V)_* μ` between `μ` and its atomization. -/
noncomputable def atomizeCoupling (μ : ProbabilityMeasure Ω) {S : Finset Ω}
    (V : Ω → S) (hV : Measurable V) : ProbabilityMeasure (Ω × Ω) :=
  map μ (fun x => (x, (V x : Ω))) (measurable_id.prod hV.subtype_val)

/-- The graph coupling has marginals `μ` and `atomize μ V`. -/
lemma atomizeCoupling_isCoupling (μ : ProbabilityMeasure Ω)
    {S : Finset Ω} (V : Ω → S) (hV : Measurable V) :
    atomizeCoupling μ V hV ∈ couplings μ (atomize μ V hV) := by
  refine ⟨?_, ?_⟩
  · apply ProbabilityMeasure.toMeasure_injective
    unfold atomizeCoupling
    rw [map_toMeasure, map_toMeasure,
        Measure.map_map measurable_fst (measurable_id.prod hV.subtype_val)]
    change Measure.map id μ.toMeasure = μ.toMeasure
    simp
  · apply ProbabilityMeasure.toMeasure_injective
    unfold atomizeCoupling atomize
    rw [map_toMeasure, map_toMeasure, map_toMeasure,
        Measure.map_map measurable_snd (measurable_id.prod hV.subtype_val)]
    rfl

section Bounds

variable [PseudoMetricSpace Ω] [OpensMeasurableSpace Ω] [SecondCountableTopology Ω]
   [CompactSpace Ω]

/-- Atomization moves mass by at most the selector radius in primal transport cost. -/
lemma atomize_krTransportCost_le (μ : ProbabilityMeasure Ω)
    {S : Finset Ω} (V : Ω → S) (hV : Measurable V) {ε : ℝ}
    (hε : ∀ x, dist x (V x : Ω) ≤ ε) :
    krTransportCost μ (atomize μ V hV) ≤ ε := by
  let π : ProbabilityMeasure (Ω × Ω) := atomizeCoupling μ V hV
  let dBC : (Ω × Ω) →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun z => dist z.1 z.2, continuous_dist⟩
  have hπ : π ∈ couplings μ (atomize μ V hV) :=
    atomizeCoupling_isCoupling μ V hV
  have htc_le : krTransportCost μ (atomize μ V hV)
      ≤ ∫ z, dist z.1 z.2 ∂π.toMeasure := by
    unfold krTransportCost
    refine transportCost_le_integral_of_bdd
      (continuous_dist (α := Ω)).measurable μ (atomize μ V hV)
      (fun z => le_trans (neg_nonpos.mpr (norm_nonneg dBC)) dist_nonneg)
      ?_ hπ
    intro z
    have h := BoundedContinuousFunction.norm_coe_le_norm dBC z
    simpa [dBC, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using h
  have hgraph_meas : Measurable (fun x : Ω => (x, (V x : Ω))) :=
    measurable_id.prod hV.subtype_val
  have hcost_eq :
      ∫ z, dist z.1 z.2 ∂π.toMeasure =
        ∫ x, dist x (V x : Ω) ∂μ.toMeasure := by
    unfold π atomizeCoupling
    rw [map_toMeasure]
    rw [MeasureTheory.integral_map hgraph_meas.aemeasurable
      (continuous_dist.aestronglyMeasurable)]
  have hdist_meas : Measurable (fun x : Ω => dist x (V x : Ω)) :=
    continuous_dist.measurable.comp hgraph_meas
  have hdist_int : Integrable (fun x : Ω => dist x (V x : Ω)) μ.toMeasure :=
    (integrable_const ε).mono' hdist_meas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg]; exact hε x)
  have hcost_le :
      ∫ x, dist x (V x : Ω) ∂μ.toMeasure ≤ ε := by
    calc ∫ x, dist x (V x : Ω) ∂μ.toMeasure
        ≤ ∫ _x, ε ∂μ.toMeasure :=
          integral_mono_ae hdist_int (integrable_const ε)
            (Filter.Eventually.of_forall hε)
      _ = ε := by
        rw [integral_const, MeasureTheory.probReal_univ, one_smul]
  linarith

/-- Atomization moves mass by at most the selector radius in KR distance. -/
lemma atomize_krDist_le [BorelSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω] [T2Space Ω]
    (μ : ProbabilityMeasure Ω) {S : Finset Ω} (V : Ω → S) (hV : Measurable V) {ε : ℝ}
    (hε : ∀ x, dist x (V x : Ω) ≤ ε) :
    krDist μ (atomize μ V hV) ≤ ε := by
  exact le_trans (krDist_le_krTransportCost μ (atomize μ V hV))
    (atomize_krTransportCost_le μ V hV hε)

end Bounds

end Econlib.Optimization.OptimalTransport
