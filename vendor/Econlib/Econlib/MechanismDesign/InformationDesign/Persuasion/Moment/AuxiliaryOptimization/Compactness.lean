/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization.Closedness
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Narrow compactness of the Dworczak–Kolotilin admissible joint measure set

The set of admissible joint measures over `Y × ℝⁿ` is narrow-compact in `FiniteMeasure (Y × ℝⁿ)`.
Compactness follows from the Prokhorov theorem: The admissible set is tight, since each admissible
measure concentrates on a common sequence of compact boxes `Kν k × K`, and it is narrow-closed
(from `Closedness.lean`). Here `K` is a compact set bounding the support of the `F`-fibers, and
`Kν k` is a compact subset of `Y` carrying all but `1/(k+1)` of the finite marginal `ν`, which
exists because `ν` is finite on the Polish space `Y`, hence tight.

## Main statements

* `isCompact_admissibleSet`: The admissible joint measure set is narrow-compact in
  `FiniteMeasure (Y × ℝⁿ)`.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Appendix A.10.

## Tags

persuasion, tightness, prokhorov, narrow compactness, admissible measures
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization

open MeasureTheory Set ProbabilityTheory
open scoped Topology BoundedContinuousFunction ENNReal

variable {n : ℕ} {Y : Type*}
  [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]

/-- The tightness level `1/(k+1)` is positive in `ℝ≥0∞`. -/
private lemma one_div_succ_pos_ennreal (k : ℕ) :
    (0 : ℝ≥0∞) < 1 / (k + 1 : ℝ≥0∞) :=
  ENNReal.div_pos_iff.mpr ⟨one_ne_zero, by finiteness⟩

/-- Tightness of the singleton `{ν}` at level `1/(k+1)`: There is a compact `Kν` with
`ν Kνᶜ ≤ 1/(k+1)`. -/
private lemma exists_isCompact_measure_compl_le_one_div_succ
    (ν : Measure Y) [IsFiniteMeasure ν] (k : ℕ) :
    ∃ Kν : Set Y, IsCompact Kν ∧ ∀ μ ∈ ({ν} : Set (Measure Y)),
      μ Kνᶜ ≤ 1 / (k + 1 : ℝ≥0∞) :=
  (isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (isTightMeasureSet_singleton (μ := ν)))
    (1 / (k + 1 : ℝ≥0∞))
    (one_div_succ_pos_ennreal k)

/-- Compact approximation of the support of `ν` at level `1/(k+1)`: For each `k`, a compact
`Kν k ⊆ Y` with `ν (Kν k)ᶜ ≤ 1/(k+1)`. -/
private noncomputable def nuTightCompact
    (ν : Measure Y) [IsFiniteMeasure ν] (k : ℕ) : Set Y :=
  Classical.choose (exists_isCompact_measure_compl_le_one_div_succ ν k)

/-- The set `nuTightCompact ν k` is compact. -/
private lemma isCompact_nuTightCompact
    (ν : Measure Y) [IsFiniteMeasure ν] (k : ℕ) :
    IsCompact (nuTightCompact ν k) :=
  (Classical.choose_spec (exists_isCompact_measure_compl_le_one_div_succ ν k)).1

/-- The mass of `ν` outside `nuTightCompact ν k` is at most `1/(k+1)`. -/
private lemma measure_compl_nuTightCompact
    (ν : Measure Y) [IsFiniteMeasure ν] (k : ℕ) :
    ν (nuTightCompact ν k)ᶜ ≤ 1 / (k + 1 : ℝ≥0∞) :=
  (Classical.choose_spec (exists_isCompact_measure_compl_le_one_div_succ ν k)).2 ν rfl

/-- The compact tight box `Kν k × K` in `Y × ℝⁿ`. -/
private noncomputable def tightBox
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (ν : Measure Y) [IsFiniteMeasure ν] (k : ℕ) :
    Set (Y × EuclideanSpace ℝ (Fin n)) :=
  nuTightCompact ν k ×ˢ K

/-- The tight box `tightBox ν k = Kν k × K` is compact when `K` is compact. -/
private lemma isCompact_tightBox
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    (ν : Measure Y) [IsFiniteMeasure ν] (k : ℕ) :
    IsCompact (tightBox (K := K) ν k) :=
  (isCompact_nuTightCompact ν k).prod hK_compact

/-- For an admissible joint measure `μ`, the mass outside the tight box `Kν k × K` is at most
`1/(k+1)`. -/
private lemma measure_compl_tightBox_of_admissible
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hF_sub_K : ∀ y, F y ⊆ K)
    (ν : Measure Y) [IsFiniteMeasure ν]
    {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n))}
    (h_marg : (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν)
    (h_graph :
      (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
        {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} = 0)
    (k : ℕ) :
    (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
        (tightBox (K := K) ν k)ᶜ ≤ 1 / (k + 1 : ℝ≥0∞) := by
  -- (Kν k × K)ᶜ ⊆ (Kν kᶜ × univ) ∪ (univ × Kᶜ).
  set Q := tightBox (K := K) ν k
  set Kν := nuTightCompact ν k
  have h_subset :
      (Q : Set (Y × EuclideanSpace ℝ (Fin n)))ᶜ ⊆
        (Kνᶜ ×ˢ Set.univ : Set (Y × EuclideanSpace ℝ (Fin n))) ∪
          {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} := by
    intro p hp
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, Set.mem_compl_iff,
      Set.mem_setOf_eq, and_true, Q, tightBox] at hp ⊢
    rcases p with ⟨y, x⟩
    by_cases hy : y ∈ Kν
    · -- With `y ∈ Kν`, the point escapes the box only through `x ∉ K`, hence `x ∉ F y`.
      right
      intro hxF
      have hxK : x ∈ K := hF_sub_K y hxF
      exact hp ⟨hy, hxK⟩
    · left; exact hy
  have h_meas_bound :
      (μ : Measure (Y × EuclideanSpace ℝ (Fin n))) Qᶜ ≤
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
            ((Kνᶜ ×ˢ Set.univ : Set (Y × EuclideanSpace ℝ (Fin n))) ∪
              {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1}) :=
    measure_mono h_subset
  have h_union_le :
      (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
          ((Kνᶜ ×ˢ Set.univ : Set (Y × EuclideanSpace ℝ (Fin n))) ∪
            {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1}) ≤
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
            (Kνᶜ ×ˢ Set.univ : Set (Y × EuclideanSpace ℝ (Fin n))) +
          (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
            {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} :=
    measure_union_le _ _
  have h_fst_eq :
      (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
          (Kνᶜ ×ˢ Set.univ : Set (Y × EuclideanSpace ℝ (Fin n))) =
        ν Kνᶜ := by
    have hKν_meas : MeasurableSet Kν :=
      (isCompact_nuTightCompact ν k).isClosed.measurableSet
    have h_set_eq : (Kνᶜ ×ˢ Set.univ : Set (Y × EuclideanSpace ℝ (Fin n)))
        = Prod.fst ⁻¹' Kνᶜ := by
      ext p; simp
    rw [h_set_eq, ← Measure.fst_apply hKν_meas.compl, h_marg]
  rw [h_fst_eq] at h_union_le
  rw [h_graph, add_zero] at h_union_le
  have h_ν_bd : ν Kνᶜ ≤ 1 / (k + 1 : ℝ≥0∞) := measure_compl_nuTightCompact ν k
  exact h_meas_bound.trans (h_union_le.trans h_ν_bd)

/-- The set of admissible joint measures sits inside the bounded-mass, tight subset of
`FiniteMeasure (Y × ℝⁿ)` to which the Prokhorov theorem applies. -/
private lemma admissibleSet_subset_prokhorov_compact
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (hF_sub_K : ∀ y, F y ⊆ K)
    (ν : Measure Y) [hν_fin : IsFiniteMeasure ν] :
    let ν_FM : FiniteMeasure Y := ⟨ν, hν_fin⟩
    {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν ∧
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
            {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} = 0} ⊆
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
          μ.mass ≤ ν_FM.mass ∧
          ∀ k : ℕ,
            μ (tightBox (K := K) ν k)ᶜ ≤
              (1 : NNReal) / ((k : NNReal) + 1)} := by
  intro ν_FM μ ⟨h_marg, h_graph⟩
  refine ⟨?_, fun k => ?_⟩
  · -- Mass equality from marginal.
    have h_mass_eq : (μ.mass : ℝ≥0∞) = (ν_FM.mass : ℝ≥0∞) := by
      rw [FiniteMeasure.ennreal_mass, FiniteMeasure.ennreal_mass]
      have hfst_univ :
          (μ : Measure (Y × EuclideanSpace ℝ (Fin n))) Set.univ =
            (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst Set.univ := by
        rw [Measure.fst_apply MeasurableSet.univ]; congr
      rw [hfst_univ, h_marg]; rfl
    exact_mod_cast h_mass_eq.le
  · -- Tightness bound, converting from `ℝ≥0∞` to `ℝ≥0`.
    have h_ennreal := measure_compl_tightBox_of_admissible
      hF_sub_K ν h_marg h_graph k
    have h_coe :
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n))) (tightBox (K := K) ν k)ᶜ =
          ((μ (tightBox (K := K) ν k)ᶜ : NNReal) : ℝ≥0∞) :=
      (FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure μ _).symm
    rw [h_coe] at h_ennreal
    have h_one_div :
        (1 : ℝ≥0∞) / (↑k + 1) = (((1 : NNReal) / ((k : NNReal) + 1) : NNReal) : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by positivity), ENNReal.coe_one]
      congr 1
    rw [h_one_div] at h_ennreal
    exact_mod_cast h_ennreal

/-- The bounded-mass, tight-box subset of `FiniteMeasure (Y × ℝⁿ)` is narrow-compact, with the
tightness bound stated through `FiniteMeasure`'s `ℝ≥0`-valued application. -/
private lemma isCompact_prokhorov_box
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    (ν : Measure Y) [hν_fin : IsFiniteMeasure ν] :
    let ν_FM : FiniteMeasure Y := ⟨ν, hν_fin⟩
    IsCompact
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
        μ.mass ≤ ν_FM.mass ∧
        ∀ k : ℕ,
          μ (tightBox (K := K) ν k)ᶜ ≤ (1 : NNReal) / ((k : NNReal) + 1)} := by
  intro ν_FM
  refine isCompact_setOf_finiteMeasure_mass_le_compl_isCompact_le
    (C := ν_FM.mass)
    (u := fun k : ℕ => (1 : NNReal) / ((k : NNReal) + 1))
    (K := fun k => tightBox (K := K) ν k) ?_
    (fun k => isCompact_tightBox hK_compact ν k) ?_
  · simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := NNReal)
  · left; infer_instance

/-- **Narrow compactness of the admissible set.** The set of admissible joint measures over
`Y × ℝⁿ` — those with first marginal `ν`, support inside the graph of `F`, and moment matching the
benchmark `z₀` against every bounded continuous test function — is narrow-compact in
`FiniteMeasure (Y × ℝⁿ)`. -/
lemma isCompact_admissibleSet
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (hz₀_mem_F : ∀ y, z₀ y ∈ F y)
    (ν : Measure Y) [hν_fin : IsFiniteMeasure ν] :
    IsCompact
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν ∧
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
            {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} = 0 ∧
        ∀ φ : Y →ᵇ ℝ,
          ∫ p, φ p.1 • p.2 ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) =
            ∫ y, φ y • z₀ y ∂ν} := by
  let ν_FM : FiniteMeasure Y := ⟨ν, hν_fin⟩
  have h_closed := isClosed_admissibleSet
    hK_compact hF_sub_K hF_graph_closed hz₀_meas hz₀_mem_F ν
  have h_subset :
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
          (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν ∧
          (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
              {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} = 0 ∧
          ∀ φ : Y →ᵇ ℝ,
            ∫ p, φ p.1 • p.2 ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) =
              ∫ y, φ y • z₀ y ∂ν} ⊆
        {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
            μ.mass ≤ ν_FM.mass ∧
            ∀ k : ℕ,
              μ (tightBox (K := K) ν k)ᶜ ≤
                (1 : NNReal) / ((k : NNReal) + 1)} := by
    intro μ ⟨h_marg, h_graph, _⟩
    exact admissibleSet_subset_prokhorov_compact hF_sub_K ν ⟨h_marg, h_graph⟩
  exact (isCompact_prokhorov_box hK_compact ν).of_isClosed_subset h_closed h_subset

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization
