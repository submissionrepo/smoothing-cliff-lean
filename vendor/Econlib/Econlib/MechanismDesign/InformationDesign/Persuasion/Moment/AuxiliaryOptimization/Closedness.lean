/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Narrow closedness of the Dworczak–Kolotilin admissible joint measure set

This file proves that the admissible joint-measure set `𝒜 ⊆ FiniteMeasure (Y × ℝⁿ)` in the
Dworczak–Kolotilin auxiliary optimization is narrowly closed. The admissibility constraints combine
a fixed first marginal, compact graph support, and the continuous-test form of conditional mean
preservation:

`∀ φ : Y →ᵇ ℝ, ∫ p, φ p.1 • p.2 ∂π = ∫ y, φ y • z₀ y ∂ν`.

Closedness of this set is the compactness input for existence of an optimal auxiliary joint measure.

## Main statements

* `isClosed_supp_and_ctf`: The set of finite measures whose support lies in `Y × K` and whose CTF
  mean-preservation identity holds is narrowly closed.
* `isClosed_admissibleSet`: The set of finite measures satisfying all admissibility constraints
  (first-marginal equals `ν`, support contained in the graph of `F`, and CTF mean-preservation) is
  narrowly closed.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Appendix A.10.

## Tags

persuasion, mean preservation, finite measure, narrow topology, closedness
-/

@[expose] public section

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization

open MeasureTheory Set ProbabilityTheory
open scoped Topology BoundedContinuousFunction ENNReal

variable {n : ℕ} {Y : Type*}
  [MeasurableSpace Y] [TopologicalSpace Y] [PolishSpace Y] [BorelSpace Y]

/-- The clamp function `t ↦ max (-M) (min M t)`. Lipschitz, bounded by `|M|` (equal to `M` when
`M ≥ 0`). -/
private def clamp (M t : ℝ) : ℝ := max (-M) (min M t)

private lemma continuous_clamp (M : ℝ) : Continuous (clamp M) := by
  unfold clamp; fun_prop

private lemma clamp_abs_le (M : ℝ) (hM : 0 ≤ M) (t : ℝ) : |clamp M t| ≤ M := by
  unfold clamp
  have h1 : -M ≤ max (-M) (min M t) := le_max_left _ _
  have h2 : max (-M) (min M t) ≤ M :=
    max_le (by linarith) (min_le_left _ _)
  exact abs_le.mpr ⟨h1, h2⟩

private lemma clamp_eq_of_abs_le (M t : ℝ) (ht : |t| ≤ M) : clamp M t = t := by
  unfold clamp
  rw [abs_le] at ht
  rw [min_eq_right ht.2, max_eq_right ht.1]

/-- Clamped `i`-th coordinate projection `(y, x) ↦ clamp M (x i)`, as a bounded continuous function
on `Y × EuclideanSpace ℝ (Fin n)`. The factor on `Y` is trivial; packaging it this way allows later
multiplication by a `Y →ᵇ ℝ` test function. -/
private noncomputable def coordClampBcf (M : ℝ) (hM : 0 ≤ M) (i : Fin n) :
    (Y × EuclideanSpace ℝ (Fin n)) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => clamp M (p.2 i))
    (by
      have hcont_proj : Continuous fun p : Y × EuclideanSpace ℝ (Fin n) => p.2 i := by
        fun_prop
      exact (continuous_clamp M).comp hcont_proj)
    M
    (fun p => by rw [Real.norm_eq_abs]; exact clamp_abs_le M hM _)

omit [MeasurableSpace Y] [PolishSpace Y] [BorelSpace Y] in
@[simp] private lemma coordClampBcf_apply (M : ℝ) (hM : 0 ≤ M) (i : Fin n)
    (p : Y × EuclideanSpace ℝ (Fin n)) :
    coordClampBcf M hM i p = clamp M (p.2 i) := rfl

/-- Bounded continuous test integrand: `(y, x) ↦ φ y * clamp M (x i)`, as an element of
`(Y × ℝⁿ) →ᵇ ℝ`. -/
private noncomputable def testProductBcf (φ : Y →ᵇ ℝ) (M : ℝ) (hM : 0 ≤ M)
    (i : Fin n) : (Y × EuclideanSpace ℝ (Fin n)) →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun p => φ p.1 * clamp M (p.2 i))
    (by
      have hφ_cont : Continuous fun p : Y × EuclideanSpace ℝ (Fin n) => φ p.1 := by
        exact φ.continuous.comp continuous_fst
      have h_clamp_cont :
          Continuous fun p : Y × EuclideanSpace ℝ (Fin n) => clamp M (p.2 i) := by
        have hproj : Continuous fun p : Y × EuclideanSpace ℝ (Fin n) => p.2 i := by
          fun_prop
        exact (continuous_clamp M).comp hproj
      exact hφ_cont.mul h_clamp_cont)
    (‖φ‖ * M)
    (fun p => by
      rw [Real.norm_eq_abs, abs_mul]
      gcongr
      · exact BoundedContinuousFunction.norm_coe_le_norm φ p.1
      · exact clamp_abs_le M hM _)

omit [MeasurableSpace Y] [PolishSpace Y] [BorelSpace Y] in
@[simp] private lemma testProductBcf_apply (φ : Y →ᵇ ℝ) (M : ℝ) (hM : 0 ≤ M)
    (i : Fin n) (p : Y × EuclideanSpace ℝ (Fin n)) :
    testProductBcf φ M hM i p = φ p.1 * clamp M (p.2 i) := rfl

omit [PolishSpace Y] [BorelSpace Y] in
/-- For `π` (a.e.-)supported on `{p : ‖p.2 i‖ ≤ M}`, the bounded-test integral agrees with the
standard coordinate integral. -/
private lemma integral_testProductBcf_eq_of_coord_bdd
    (φ : Y →ᵇ ℝ) (M : ℝ) (hM : 0 ≤ M) (i : Fin n)
    (π : Measure (Y × EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure π]
    (hπ_bd : ∀ᵐ p ∂π, |p.2 i| ≤ M) :
    ∫ p, testProductBcf φ M hM i p ∂π = ∫ p, φ p.1 * (p.2 i) ∂π := by
  refine integral_congr_ae ?_
  filter_upwards [hπ_bd] with p hp
  simp [testProductBcf_apply, clamp_eq_of_abs_le M (p.2 i) hp]

omit [PolishSpace Y] in
/-- Narrow continuity of the bounded-test integral functional on `FiniteMeasure (Y × ℝⁿ)`. -/
private lemma continuous_integral_testProductBcf (φ : Y →ᵇ ℝ) (M : ℝ) (hM : 0 ≤ M)
    (i : Fin n) :
    Continuous fun μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) =>
        ∫ p, testProductBcf φ M hM i p ∂(μ : Measure _) :=
  FiniteMeasure.continuous_integral_boundedContinuousFunction _

/-! ## Bridge: CTF ↔ coordinate-wise clamped-test equations -/

omit [PolishSpace Y] in
/-- Integrability of `(y, x) ↦ φ y • x` against `π` when the support lies in `Y × K` with `K`
compact. -/
private lemma integrable_proj_smul_snd_of_supp
    {K : Set (EuclideanSpace ℝ (Fin n))} {M : ℝ} (hM_K : ∀ x ∈ K, ‖x‖ ≤ M)
    {π : Measure (Y × EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure π]
    (hπ_supp_K : ∀ᵐ p ∂π, p.2 ∈ K) (φ : Y →ᵇ ℝ) :
    Integrable (fun p : Y × EuclideanSpace ℝ (Fin n) => φ p.1 • p.2) π := by
  have hφ_aesm : AEStronglyMeasurable
      (fun p : Y × EuclideanSpace ℝ (Fin n) => φ p.1) π := by
    exact (φ.continuous.comp continuous_fst).aestronglyMeasurable
  have hp2_aesm : AEStronglyMeasurable
      (fun p : Y × EuclideanSpace ℝ (Fin n) => p.2) π :=
    measurable_snd.aestronglyMeasurable
  refine Integrable.of_bound (hφ_aesm.smul hp2_aesm) (‖φ‖ * M) ?_
  filter_upwards [hπ_supp_K] with p hp
  rw [norm_smul]
  exact mul_le_mul (BoundedContinuousFunction.norm_coe_le_norm φ p.1)
    (hM_K _ hp) (norm_nonneg _) (norm_nonneg _)

/-- Coordinate of a vector integral equals the integral of the coordinate. -/
private lemma integral_coord_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → EuclideanSpace ℝ (Fin n)} (hf : Integrable f μ) (i : Fin n) :
    (∫ x, f x ∂μ) i = ∫ x, f x i ∂μ := by
  have h := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i) hf
  simp only [EuclideanSpace.coe_proj] at h
  exact h.symm

/-- For `c : ℝ` and `v : EuclideanSpace ℝ (Fin n)`, `(c • v) i = c * (v i)`. -/
private lemma smul_euclidean_apply (c : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (i : Fin n) : (c • v) i = c * (v i) := rfl

omit [PolishSpace Y] in
/-- On a measure `π` supported on `Y × K` (with `K ⊆ closedBall 0 M`), the vector mean-preservation
identity CTF is equivalent to a coordinate-wise clamped-test identity. -/
private lemma ctf_iff_clampTest_of_supp
    {K : Set (EuclideanSpace ℝ (Fin n))} {M : ℝ} (hM_nn : 0 ≤ M)
    (hM_K : ∀ x ∈ K, ‖x‖ ≤ M)
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (hz₀_mem_K : ∀ y, z₀ y ∈ K)
    (ν : Measure Y) [IsFiniteMeasure ν]
    {π : Measure (Y × EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure π]
    (hπ_supp_K : ∀ᵐ p ∂π, p.2 ∈ K) :
    (∀ φ : Y →ᵇ ℝ,
        ∫ p, φ p.1 • p.2 ∂π = ∫ y, φ y • z₀ y ∂ν) ↔
    (∀ (i : Fin n) (φ : Y →ᵇ ℝ),
        ∫ p, testProductBcf φ M hM_nn i p ∂π =
          ∫ y, φ y * (z₀ y i) ∂ν) := by
  have hπ_coord_bd : ∀ (i : Fin n), ∀ᵐ p ∂π, |p.2 i| ≤ M := by
    intro i
    filter_upwards [hπ_supp_K] with p hp
    have hcoord : |p.2 i| ≤ ‖p.2‖ := by
      have h := PiLp.norm_apply_le p.2 i
      simpa [Real.norm_eq_abs] using h
    exact hcoord.trans (hM_K _ hp)
  have hp_int : ∀ φ : Y →ᵇ ℝ,
      Integrable (fun p : Y × EuclideanSpace ℝ (Fin n) => φ p.1 • p.2) π :=
    fun φ => integrable_proj_smul_snd_of_supp hM_K hπ_supp_K φ
  have hz₀_smul_int : ∀ φ : Y →ᵇ ℝ,
      Integrable (fun y => φ y • z₀ y) ν := by
    intro φ
    refine Integrable.of_bound
      ((φ.continuous.aestronglyMeasurable).smul hz₀_meas.aestronglyMeasurable)
      (‖φ‖ * M) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [norm_smul]
    exact mul_le_mul (BoundedContinuousFunction.norm_coe_le_norm φ y)
      (hM_K _ (hz₀_mem_K y)) (norm_nonneg _) (norm_nonneg _)
  have h_lhs_coord : ∀ (φ : Y →ᵇ ℝ) (i : Fin n),
      (∫ p, φ p.1 • p.2 ∂π) i = ∫ p, φ p.1 * (p.2 i) ∂π := by
    intro φ i
    rw [integral_coord_eq (hp_int φ) i]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    exact smul_euclidean_apply (φ p.1) p.2 i
  have h_rhs_coord : ∀ (φ : Y →ᵇ ℝ) (i : Fin n),
      (∫ y, φ y • z₀ y ∂ν) i = ∫ y, φ y * (z₀ y i) ∂ν := by
    intro φ i
    rw [integral_coord_eq (hz₀_smul_int φ) i]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    exact smul_euclidean_apply (φ y) (z₀ y) i
  have h_clamp_eq : ∀ (φ : Y →ᵇ ℝ) (i : Fin n),
      ∫ p, testProductBcf φ M hM_nn i p ∂π = ∫ p, φ p.1 * (p.2 i) ∂π :=
    fun φ i => integral_testProductBcf_eq_of_coord_bdd φ M hM_nn i π (hπ_coord_bd i)
  refine ⟨fun hCTF i φ => ?_, fun hClamp φ => ?_⟩
  · -- Forward direction: extract the `i`-th coordinate of CTF.
    calc ∫ p, testProductBcf φ M hM_nn i p ∂π
        = ∫ p, φ p.1 * (p.2 i) ∂π := h_clamp_eq φ i
      _ = (∫ p, φ p.1 • p.2 ∂π) i := (h_lhs_coord φ i).symm
      _ = (∫ y, φ y • z₀ y ∂ν) i := by rw [hCTF]
      _ = ∫ y, φ y * (z₀ y i) ∂ν := h_rhs_coord φ i
  · -- Backward direction: reassemble the vector identity from its coordinates.
    refine PiLp.ext fun i => ?_
    change (∫ p, φ p.1 • p.2 ∂π) i = (∫ y, φ y • z₀ y ∂ν) i
    rw [h_lhs_coord φ i, h_rhs_coord φ i, ← h_clamp_eq φ i]
    exact hClamp i φ

/-! ## Narrow closedness of the constraint set -/

omit [PolishSpace Y] in
/-- The set of finite measures on `Y × ℝⁿ` whose clamped-test integrals equal the required
constants (for every coordinate and every `Y →ᵇ ℝ` test) is narrowly closed. -/
private lemma isClosed_clampTest_set (M : ℝ) (hM_nn : 0 ≤ M)
    {z₀ : Y → EuclideanSpace ℝ (Fin n)}
    (ν : Measure Y) [IsFiniteMeasure ν] :
    IsClosed
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
        ∀ (i : Fin n) (φ : Y →ᵇ ℝ),
          ∫ p, testProductBcf φ M hM_nn i p ∂(μ : Measure _) =
            ∫ y, φ y * (z₀ y i) ∂ν} := by
  -- Rewrite the constraint set as an intersection over coordinates and test functions.
  have h_setOf_iInter :
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
          ∀ (i : Fin n) (φ : Y →ᵇ ℝ),
            ∫ p, testProductBcf φ M hM_nn i p ∂(μ : Measure _) =
              ∫ y, φ y * (z₀ y i) ∂ν}
        = ⋂ (i : Fin n), ⋂ (φ : Y →ᵇ ℝ),
            {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
              ∫ p, testProductBcf φ M hM_nn i p ∂(μ : Measure _) =
                ∫ y, φ y * (z₀ y i) ∂ν} := by
    ext μ; simp
  rw [h_setOf_iInter]
  refine isClosed_iInter fun i => isClosed_iInter fun φ => ?_
  exact isClosed_eq (continuous_integral_testProductBcf φ M hM_nn i) continuous_const

/-- Generic null-set closedness: If an open set `O` and a closed set `Γ` partition the space
(`O ∪ Γ = univ`, `Disjoint O Γ`), then `{μ | μ O = 0}` is narrowly closed. This is the shared
portmanteau core behind the support and graph constraints below. -/
private lemma isClosed_measure_open_eq_zero {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [HasOuterApproxClosed X] [OpensMeasurableSpace X] {O Γ : Set X} (hΓ_closed : IsClosed Γ)
    (hO_union_Γ : O ∪ Γ = Set.univ) (hOΓ_disjoint : Disjoint O Γ) :
    IsClosed {μ : FiniteMeasure X | (μ : Measure X) O = 0} := by
  -- For any finite measure, the total mass splits across the partition.
  have h_mass_split : ∀ μ : FiniteMeasure X,
      (μ : Measure X) Set.univ = (μ : Measure X) O + (μ : Measure X) Γ := fun μ => by
    rw [← hO_union_Γ, measure_union hOΓ_disjoint hΓ_closed.measurableSet]
  rw [isClosed_iff_clusterPt]
  intro μ hμ
  -- Work along the cluster filter `L = 𝓝 μ ⊓ 𝓟 S`, where `S` is the constraint set.
  set S : Set (FiniteMeasure X) := {μ | (μ : Measure X) O = 0} with hS_def
  set L := 𝓝 μ ⊓ Filter.principal S with hL_def
  haveI hL_neBot : L.NeBot := hμ
  have h_tendsto : Filter.Tendsto (id : FiniteMeasure X → _) L (𝓝 μ) :=
    Filter.tendsto_inf_left Filter.tendsto_id
  have h_evt_zero : ∀ᶠ ν : FiniteMeasure X in L, (ν : Measure X) O = 0 :=
    Filter.eventually_iff_exists_mem.mpr
      ⟨S, Filter.mem_inf_of_right (Filter.mem_principal_self _), fun ν hν => hν⟩
  -- On `S`, the closed companion `Γ` carries the full mass.
  have h_Γ_eq_univ : ∀ᶠ ν : FiniteMeasure X in L,
      (ν : Measure X) Γ = (ν : Measure X) Set.univ := by
    filter_upwards [h_evt_zero] with ν hν
    rw [h_mass_split ν, hν, zero_add]
  -- Closed-set portmanteau: `limsup ν Γ ≤ μ Γ`.
  have h_closed_bd : L.limsup (fun ν : FiniteMeasure X => (ν : Measure X) Γ) ≤
      (μ : Measure X) Γ :=
    FiniteMeasure.limsup_measure_closed_le_of_tendsto h_tendsto hΓ_closed
  -- Total mass is narrow-continuous, so `ν univ → μ univ`.
  have h_mass_tendsto : Filter.Tendsto
      (fun ν : FiniteMeasure X => (ν : Measure X) Set.univ) L
      (𝓝 ((μ : Measure X) Set.univ)) := by
    have hmass_cont : Filter.Tendsto (fun ν : FiniteMeasure X => ν.mass) L (𝓝 μ.mass) :=
      (FiniteMeasure.continuous_mass.tendsto μ).comp h_tendsto
    have hcast : Filter.Tendsto (fun ν : FiniteMeasure X => (ν.mass : ℝ≥0∞)) L
        (𝓝 (μ.mass : ℝ≥0∞)) :=
      (ENNReal.continuous_coe.tendsto _).comp hmass_cont
    simpa only [FiniteMeasure.ennreal_mass] using hcast
  -- Combine the two limits: `μ univ ≤ μ Γ`.
  have h_univ_le_Γ : (μ : Measure X) Set.univ ≤ (μ : Measure X) Γ := by
    have h_limsup_eq : Filter.limsup (fun ν : FiniteMeasure X => (ν : Measure X) Set.univ) L =
        (μ : Measure X) Set.univ := h_mass_tendsto.limsup_eq
    have h_eq_Γ : Filter.limsup (fun ν : FiniteMeasure X => (ν : Measure X) Set.univ) L =
        Filter.limsup (fun ν : FiniteMeasure X => (ν : Measure X) Γ) L :=
      Filter.limsup_congr (h_Γ_eq_univ.mono fun _ h => h.symm)
    calc (μ : Measure X) Set.univ
        = Filter.limsup (fun ν : FiniteMeasure X => (ν : Measure X) Set.univ) L := h_limsup_eq.symm
      _ = Filter.limsup (fun ν : FiniteMeasure X => (ν : Measure X) Γ) L := h_eq_Γ
      _ ≤ (μ : Measure X) Γ := h_closed_bd
  have h_Γ_eq : (μ : Measure X) Γ = (μ : Measure X) Set.univ :=
    le_antisymm (measure_mono (Set.subset_univ _)) h_univ_le_Γ
  -- Cancel the finite total mass in `μ univ = μ O + μ Γ` to conclude `μ O = 0`.
  change (μ : Measure X) O = 0
  have h_split := h_mass_split μ
  rw [h_Γ_eq] at h_split
  refine WithTop.add_right_cancel (measure_lt_top (μ : Measure X) Set.univ).ne ?_
  exact h_split.symm.trans (zero_add _).symm

/-- The set of finite measures on `Y × ℝⁿ` whose support is contained in `Y × K` (with `K` closed)
is narrowly closed. The support constraint is characterized as `μ (Y × Kᶜ) = 0`, viewing the
complement of the closed product `Y × K` as the open set `univ ×ˢ Kᶜ`. -/
private lemma isClosed_support_in_prod
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_closed : IsClosed K) :
    IsClosed
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
            (Set.univ ×ˢ Kᶜ : Set (Y × EuclideanSpace ℝ (Fin n))) = 0} := by
  -- The closed companion is `univ ×ˢ K`; it partitions the space with the open `univ ×ˢ Kᶜ`.
  refine isClosed_measure_open_eq_zero (isClosed_univ.prod hK_closed) ?_ ?_
  · rw [← Set.prod_union]; simp
  · rw [Set.disjoint_iff_inter_eq_empty, ← Set.prod_inter]; simp

/-! ## Additional admissibility closedness pieces -/

/-- The first-marginal constraint `(μ : Measure _).fst = ν` is narrowly closed in
`FiniteMeasure (Y × ℝⁿ)`. -/
private lemma isClosed_marginal_eq
    (ν : Measure Y) [hν_fin : IsFiniteMeasure ν] :
    IsClosed
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν} := by
  -- ν as a `FiniteMeasure Y`.
  let ν_FM : FiniteMeasure Y := ⟨ν, hν_fin⟩
  -- The map `μ ↦ μ.map Prod.fst` is narrow-continuous.
  have hmap_cont :
      Continuous (fun μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) =>
        μ.map Prod.fst) :=
    FiniteMeasure.continuous_map continuous_fst
  -- The constraint set equals `{μ | μ.map Prod.fst = ν_FM}`.
  have h_to_measure :
      ∀ μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)),
        ((μ.map Prod.fst : FiniteMeasure Y) : Measure Y) =
          (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst :=
    fun μ => FiniteMeasure.toMeasure_map μ Prod.fst
  have h_eq_set :
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
          (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν} =
        {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) | μ.map Prod.fst = ν_FM} := by
    ext μ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · apply Subtype.ext
      change ((μ.map Prod.fst : FiniteMeasure Y) : Measure Y) = ν
      rw [h_to_measure μ]; exact h
    · change (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν
      rw [← h_to_measure μ]
      exact congr_arg (·.toMeasure) h
  rw [h_eq_set]
  exact isClosed_singleton.preimage hmap_cont

/-- The graph constraint `∀ᵐ p ∂μ, p.2 ∈ F p.1` is narrowly closed in `FiniteMeasure (Y × ℝⁿ)`,
assuming the graph of `F` is closed. -/
private lemma isClosed_graph_constraint
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1}) :
    IsClosed
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
          ({p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1}) = 0} := by
  -- The open constraint set is the complement of the (closed) graph; they partition the space.
  refine isClosed_measure_open_eq_zero hF_graph_closed ?_ ?_
  · ext p; simp; tauto
  · rw [Set.disjoint_iff_inter_eq_empty]; ext p; simp

/-- The set of finite measures on `Y × ℝⁿ` whose support lies in `Y × K` and whose CTF
mean-preservation identity holds is narrowly closed. -/
lemma isClosed_supp_and_ctf
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (hz₀_mem_K : ∀ y, z₀ y ∈ K)
    (ν : Measure Y) [IsFiniteMeasure ν] :
    IsClosed
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
            (Set.univ ×ˢ Kᶜ : Set (Y × EuclideanSpace ℝ (Fin n))) = 0 ∧
        ∀ φ : Y →ᵇ ℝ,
          ∫ p, φ p.1 • p.2 ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) =
            ∫ y, φ y • z₀ y ∂ν} := by
  -- Choose a uniform norm bound `M` for the compact set `K`.
  obtain ⟨M, hM_pos, hM_K⟩ : ∃ M : ℝ, 0 < M ∧ ∀ x ∈ K, ‖x‖ ≤ M := by
    obtain ⟨M, hM_K⟩ := hK_compact.isBounded.exists_norm_le
    exact ⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
      fun x hx => (hM_K x hx).trans (le_max_left _ _)⟩
  have hM_nn : 0 ≤ M := hM_pos.le
  have hK_closed : IsClosed K := hK_compact.isClosed
  -- The target set is the intersection of the support set and the clamp-test set.
  set S_supp :
      Set (FiniteMeasure (Y × EuclideanSpace ℝ (Fin n))) :=
    {μ | (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
        (Set.univ ×ˢ Kᶜ : Set (Y × EuclideanSpace ℝ (Fin n))) = 0}
  set S_clamp :
      Set (FiniteMeasure (Y × EuclideanSpace ℝ (Fin n))) :=
    {μ | ∀ (i : Fin n) (φ : Y →ᵇ ℝ),
        ∫ p, testProductBcf φ M hM_nn i p ∂(μ : Measure _) =
          ∫ y, φ y * (z₀ y i) ∂ν}
  have h_target_eq :
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
          (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
              (Set.univ ×ˢ Kᶜ : Set (Y × EuclideanSpace ℝ (Fin n))) = 0 ∧
          ∀ φ : Y →ᵇ ℝ,
            ∫ p, φ p.1 • p.2 ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) =
              ∫ y, φ y • z₀ y ∂ν} =
        S_supp ∩ S_clamp := by
    ext μ
    have h_set_eq :
        {a : Y × EuclideanSpace ℝ (Fin n) | a.2 ∉ K} =
          Set.univ ×ˢ (Kᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
      ext a; simp [Set.mem_prod]
    refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
    · -- supp + CTF → supp + clamp-test
      have hπ_supp : ∀ᵐ p ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))), p.2 ∈ K := by
        rw [MeasureTheory.ae_iff, h_set_eq]; exact h.1
      haveI : IsFiniteMeasure (μ : Measure (Y × EuclideanSpace ℝ (Fin n))) :=
        inferInstance
      exact (ctf_iff_clampTest_of_supp hM_nn hM_K hz₀_meas hz₀_mem_K ν hπ_supp).mp h.2
    · -- supp + clamp-test → supp + CTF
      have hπ_supp : ∀ᵐ p ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))), p.2 ∈ K := by
        rw [MeasureTheory.ae_iff, h_set_eq]; exact h.1
      haveI : IsFiniteMeasure (μ : Measure (Y × EuclideanSpace ℝ (Fin n))) :=
        inferInstance
      exact (ctf_iff_clampTest_of_supp hM_nn hM_K hz₀_meas hz₀_mem_K ν hπ_supp).mpr h.2
  rw [h_target_eq]
  exact (isClosed_support_in_prod hK_closed).inter
    (isClosed_clampTest_set M hM_nn ν)

/-- The set of finite measures on `Y × ℝⁿ` satisfying all admissibility constraints (first-marginal
equals `ν`, support contained in the graph of `F`, and CTF mean-preservation) is narrowly closed.
The graph constraint subsumes the `Y × K`-support constraint since `F y ⊆ K`. -/
lemma isClosed_admissibleSet
    {F : Y → Set (EuclideanSpace ℝ (Fin n))}
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK_compact : IsCompact K)
    (hF_sub_K : ∀ y, F y ⊆ K)
    (hF_graph_closed :
      IsClosed {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∈ F p.1})
    {z₀ : Y → EuclideanSpace ℝ (Fin n)} (hz₀_meas : Measurable z₀)
    (hz₀_mem_F : ∀ y, z₀ y ∈ F y)
    (ν : Measure Y) [IsFiniteMeasure ν] :
    IsClosed
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν ∧
        (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
            ({p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1}) = 0 ∧
        ∀ φ : Y →ᵇ ℝ,
          ∫ p, φ p.1 • p.2 ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) =
            ∫ y, φ y • z₀ y ∂ν} := by
  have hz₀_mem_K : ∀ y, z₀ y ∈ K := fun y => hF_sub_K y (hz₀_mem_F y)
  -- Express as intersection of three closed sets.
  have h_decomp :
      {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
          (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν ∧
          (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
              ({p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1}) = 0 ∧
          ∀ φ : Y →ᵇ ℝ,
            ∫ p, φ p.1 • p.2 ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) =
              ∫ y, φ y • z₀ y ∂ν} =
        {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
            (μ : Measure (Y × EuclideanSpace ℝ (Fin n))).fst = ν} ∩
          ({μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
              (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
                ({p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1}) = 0} ∩
            {μ : FiniteMeasure (Y × EuclideanSpace ℝ (Fin n)) |
              (μ : Measure (Y × EuclideanSpace ℝ (Fin n)))
                  (Set.univ ×ˢ Kᶜ : Set _) = 0 ∧
              ∀ φ : Y →ᵇ ℝ,
                ∫ p, φ p.1 • p.2 ∂(μ : Measure (Y × EuclideanSpace ℝ (Fin n))) =
                  ∫ y, φ y • z₀ y ∂ν}) := by
    ext μ
    constructor
    · rintro ⟨h_marg, h_graph, h_ctf⟩
      refine ⟨h_marg, h_graph, ?_, h_ctf⟩
      -- supp_F → supp_K (since F y ⊆ K).
      have h_subset :
          (Set.univ ×ˢ Kᶜ : Set (Y × EuclideanSpace ℝ (Fin n))) ⊆
            {p : Y × EuclideanSpace ℝ (Fin n) | p.2 ∉ F p.1} := by
        intro p hp
        simp only [Set.mem_prod, Set.mem_univ, Set.mem_compl_iff, true_and] at hp
        simp only [Set.mem_setOf_eq]
        intro hF; exact hp (hF_sub_K _ hF)
      exact le_antisymm
        ((measure_mono h_subset).trans h_graph.le)
        (zero_le)
    · rintro ⟨h_marg, h_graph, _, h_ctf⟩
      exact ⟨h_marg, h_graph, h_ctf⟩
  rw [h_decomp]
  exact (isClosed_marginal_eq ν).inter
    ((isClosed_graph_constraint hF_graph_closed).inter
      (isClosed_supp_and_ctf hK_compact hz₀_meas hz₀_mem_K ν))

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.AuxiliaryOptimization
