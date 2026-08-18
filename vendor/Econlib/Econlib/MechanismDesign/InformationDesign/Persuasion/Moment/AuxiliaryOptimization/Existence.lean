/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization.Compactness

/-!
# Existence of a cost-maximizing admissible joint measure

This file combines closedness and compactness of the admissible set with a feasibility witness and
cost continuity to prove the existence of a cost-maximizing admissible joint measure in the
Dworczak–Kolotilin auxiliary optimization.

The cost functional is the integral of `‖x‖²`. On admissible measures, whose support lies in a
compact set `Y × K`, this agrees with the integral of a bounded continuous truncation, which makes
the functional weak-* continuous and lets the compactness of the admissible set deliver a maximizer.

## Main definitions

* `truncNormSqBcf M`: The bounded continuous truncation `(y, x) ↦ min (‖x‖²) M²` on `Y × ℝⁿ`, which
  agrees with the cost on the support `Y × K`.
* `feasibilityWitness z₀ ν`: The joint measure `ν.map (y ↦ (y, z₀ y))`, supported on the graph of
  `z₀` and lying in the admissible set.

## Main statements

* `exists_admissibleJointMeasure_max_ctf`: Existence of an admissible joint measure of maximum
  cost, in the continuous-test-function formulation.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Appendix A.10.

## Tags

persuasion, moment persuasion, auxiliary optimization, existence, weak convergence
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization

open MeasureTheory Set ProbabilityTheory
open scoped Topology BoundedContinuousFunction ENNReal

variable {n : ℕ} {Y : Type*}
  [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]

/-! ## Truncated norm-squared as a bounded continuous test function -/

/-- The truncated norm-squared `(y, x) ↦ min (‖x‖²) M²`, as a bounded continuous function on
`Y × ℝⁿ`. -/
private noncomputable def truncNormSqBcf (M : ℝ) :
    (Y × EuclideanSpace ℝ (Fin n)) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => min (‖p.2‖^2) (M^2))
    (by
      have h1 : Continuous
          fun p : Y × EuclideanSpace ℝ (Fin n) => ‖p.2‖^2 := by fun_prop
      exact h1.min continuous_const)
    (M^2)
    (fun p => by
      rw [Real.norm_eq_abs]
      have h_nn : 0 ≤ min (‖p.2‖^2) (M^2) :=
        le_min (sq_nonneg _) (sq_nonneg _)
      rw [abs_of_nonneg h_nn]
      exact min_le_right _ _)

omit [MeasurableSpace Y] [PolishSpace Y] [BorelSpace Y] in
/-- Evaluation of `truncNormSqBcf` at a point. -/
@[simp] private lemma truncNormSqBcf_apply (M : ℝ)
    (p : Y × EuclideanSpace ℝ (Fin n)) :
    truncNormSqBcf (Y := Y) M p = min (‖p.2‖^2) (M^2) := rfl

omit [MeasurableSpace Y] [PolishSpace Y] [BorelSpace Y] in
/-- For `p` with `‖p.2‖ ≤ M`, the truncated norm-squared agrees with `‖p.2‖²`. -/
private lemma truncNormSqBcf_eq_of_norm_le (M : ℝ)
    (p : Y × EuclideanSpace ℝ (Fin n)) (hp : ‖p.2‖ ≤ M) :
    truncNormSqBcf (Y := Y) M p = ‖p.2‖^2 := by
  rw [truncNormSqBcf_apply]
  exact min_eq_left (pow_le_pow_left₀ (norm_nonneg _) hp 2)

omit [PolishSpace Y] [BorelSpace Y] in
/-- For a measure `π` supported on `Y × K` (with `K ⊆ closedBall(0, M)`), the
truncated-norm-squared integral equals the cost integral. -/
private lemma integral_truncNormSqBcf_eq_cost
    {K : Set (EuclideanSpace ℝ (Fin n))} {M : ℝ}
    (hM_K : ∀ x ∈ K, ‖x‖ ≤ M)
    {π : Measure (Y × EuclideanSpace ℝ (Fin n))}
    (hπ_supp_K : ∀ᵐ p ∂π, p.2 ∈ K) :
    ∫ p, truncNormSqBcf M p ∂π = ∫ p, ‖p.2‖^2 ∂π := by
  refine integral_congr_ae ?_
  filter_upwards [hπ_supp_K] with p hp
  exact truncNormSqBcf_eq_of_norm_le M p (hM_K _ hp)

omit [PolishSpace Y] in
/-- Weak-* continuity of the truncated-norm-squared integral functional on
`FiniteMeasure (Y × ℝⁿ)`. -/
private lemma continuous_integral_truncNormSqBcf (M : ℝ) :
    Continuous fun μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) =>
        ∫ p, truncNormSqBcf M p ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) :=
  FiniteMeasure.continuous_integral_boundedContinuousFunction _

/-! ## Feasibility witness `π₀ = ν.map (y ↦ (y, z₀ y))` -/

/-- The feasibility witness `π₀ := ν.map (y ↦ (y, z₀ y))`, supported on the graph of `z₀`. -/
private noncomputable def feasibilityWitness
    (z₀ : Y → EuclideanSpace ℝ (Fin n))
    (ν : Measure Y) : Measure (Y × EuclideanSpace ℝ (Fin n)) :=
  ν.map (fun y => (y, z₀ y))

/-- The feasibility witness is a finite measure whenever `ν` is. -/
private instance feasibilityWitness_isFiniteMeasure
    (z₀ : Y → EuclideanSpace ℝ (Fin n))
    (ν : Measure Y) [IsFiniteMeasure ν] :
    IsFiniteMeasure (feasibilityWitness z₀ ν) := by
  unfold feasibilityWitness
  infer_instance

omit [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y] in
/-- The first marginal of the feasibility witness is `ν`. -/
private lemma feasibilityWitness_fst
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (ν : Measure Y) :
    (feasibilityWitness z₀ ν).fst = ν := by
  unfold feasibilityWitness Measure.fst
  have h_meas : Measurable fun y => (y, z₀ y) :=
    measurable_id.prodMk hz₀_meas
  rw [Measure.map_map measurable_fst h_meas]
  simp [Function.comp_def]

omit [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y] in
/-- The feasibility witness is supported on the graph of `F`. -/
private lemma feasibilityWitness_supp_graph
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (hz₀_mem_F : ∀ y, z₀ y ∈ F y)
    (hF_graph_meas : MeasurableSet
      {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    (ν : Measure Y) :
    (feasibilityWitness z₀ ν)
        {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} = 0 := by
  unfold feasibilityWitness
  have h_meas : Measurable fun y : Y => (y, z₀ y) :=
    measurable_id.prodMk hz₀_meas
  have h_set_meas :
      MeasurableSet {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} :=
    hF_graph_meas.compl
  rw [Measure.map_apply h_meas h_set_meas]
  have h_preimg : (fun y : Y => (y, z₀ y)) ⁻¹'
      {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} = ∅ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, not_not]
    exact hz₀_mem_F y
  rw [h_preimg, measure_empty]

omit [PolishSpace Y] in
/-- The continuous-test-function mean-preservation identity holds for the feasibility witness. -/
private lemma feasibilityWitness_ctf
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (ν : Measure Y) (φ : Y →ᵇ ℝ) :
    ∫ p, φ p.1 • p.2 ∂feasibilityWitness z₀ ν =
      ∫ y, φ y • z₀ y ∂ν := by
  unfold feasibilityWitness
  have h_meas : Measurable fun y : Y => (y, z₀ y) :=
    measurable_id.prodMk hz₀_meas
  have h_aestrong : AEStronglyMeasurable
      (fun p : Y × EuclideanSpace ℝ (Fin n) => φ p.1 • p.2)
      (ν.map (fun y => (y, z₀ y))) := by
    refine ((φ.continuous.comp continuous_fst).aestronglyMeasurable).smul ?_
    exact measurable_snd.aestronglyMeasurable
  rw [integral_map h_meas.aemeasurable h_aestrong]

/-! ## Main existence theorem -/

/-- **Existence of a cost-maximizing admissible joint measure (continuous-test form).** There is an
admissible joint measure of maximum cost, where admissibility means first marginal `ν`, support in
the graph of `F`, and continuous-test-function mean preservation.

The cost is expressed via the bounded continuous truncation `truncNormSqBcf M`; on admissible
measures, whose support lies in `Y × K` with `K ⊆ closedBall(0, M)`, this agrees with the true cost
`∫ ‖p.2‖² dπ`. -/
theorem exists_admissibleJointMeasure_max_ctf
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (hz₀_mem_F : ∀ y, z₀ y ∈ F y)
    (ν : Measure Y) [IsFiniteMeasure ν] :
    ∃ μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)),
      (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν ∧
      (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
          {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} = 0 ∧
      (∀ φ : Y →ᵇ ℝ,
          ∫ p, φ p.1 • p.2 ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) =
            ∫ y, φ y • z₀ y ∂ν) ∧
      ∀ μ' : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)),
        (μ' : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν →
        (μ' : Measure (Y × EuclideanSpace ℝ (Fin n)))
            {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} = 0 →
        (∀ φ : Y →ᵇ ℝ,
            ∫ p, φ p.1 • p.2 ∂(μ' : Measure (Y × EuclideanSpace ℝ (Fin n))) =
              ∫ y, φ y • z₀ y ∂ν) →
        ∫ p, ‖p.2‖^2 ∂(μ' : Measure (Y × EuclideanSpace ℝ (Fin n))) ≤
          ∫ p, ‖p.2‖^2 ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) := by
  -- Bound K by M.
  obtain ⟨M, hM_K⟩ : ∃ M : ℝ, ∀ x ∈ K, ‖x‖ ≤ M :=
    hK_compact.isBounded.exists_norm_le
  have hF_graph_meas : MeasurableSet
      {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1} :=
    hF_graph_closed.measurableSet
  -- The admissible set, in the continuous-test-function form, inside `FiniteMeasure (Y × ℝⁿ)`.
  set 𝒜 : Set (FiniteMeasure (Y × EuclideanSpace ℝ (Fin n))) :=
    {μ |
      (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν ∧
      (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
          {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} = 0 ∧
      ∀ φ : Y →ᵇ ℝ,
        ∫ p, φ p.1 • p.2 ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) =
          ∫ y, φ y • z₀ y ∂ν} with h𝒜_def
  have h_compact : IsCompact 𝒜 :=
    isCompact_admissibleSet hK_compact hF_sub_K hF_graph_closed hz₀_meas
      hz₀_mem_F ν
  -- Nonemptiness comes from the feasibility witness.
  haveI : IsFiniteMeasure (feasibilityWitness z₀ ν) :=
    feasibilityWitness_isFiniteMeasure z₀ ν
  let π₀ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) :=
    ⟨feasibilityWitness z₀ ν, inferInstance⟩
  have h_π₀_mem : π₀ ∈ 𝒜 := by
    refine ⟨?_, ?_, ?_⟩
    · exact feasibilityWitness_fst hz₀_meas ν
    · exact feasibilityWitness_supp_graph hz₀_meas hz₀_mem_F hF_graph_meas ν
    · exact feasibilityWitness_ctf hz₀_meas ν
  -- The truncated cost is weak-* continuous, so a maximizer exists on the compact admissible set.
  have h_J_cont : Continuous fun μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) =>
      ∫ p, truncNormSqBcf M p ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) :=
    continuous_integral_truncNormSqBcf M
  obtain ⟨μ_star, hμ_star_mem, hμ_star_max⟩ :=
    h_compact.exists_isMaxOn ⟨π₀, h_π₀_mem⟩ h_J_cont.continuousOn
  refine ⟨μ_star, hμ_star_mem.1, hμ_star_mem.2.1, hμ_star_mem.2.2, ?_⟩
  intro μ' hμ'_marg hμ'_graph hμ'_ctf
  have hμ'_mem : μ' ∈ 𝒜 := ⟨hμ'_marg, hμ'_graph, hμ'_ctf⟩
  have h_truncEq_star : ∀ μ ∈ 𝒜,
      ∫ p, ‖p.2‖^2 ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) =
        ∫ p, truncNormSqBcf M p ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) := by
    intro μ ⟨_, h_graph, _⟩
    have hπ_supp_K : ∀ᵐ p ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))), p.2 ∈ K := by
      have h_F_sub_K_set : {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ K} ⊆
          {p | p.2 ∉ F p.1} := by
        intro p hp
        simp only [Set.mem_setOf_eq] at hp ⊢
        intro hpF; exact hp (hF_sub_K _ hpF)
      rw [MeasureTheory.ae_iff]
      exact measure_mono_null h_F_sub_K_set h_graph
    exact (integral_truncNormSqBcf_eq_cost hM_K hπ_supp_K).symm
  rw [h_truncEq_star μ' hμ'_mem, h_truncEq_star μ_star hμ_star_mem]
  exact hμ_star_max hμ'_mem

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization
