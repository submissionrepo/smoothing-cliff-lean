/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Analysis.StrictJensenNormSq
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.AuxiliaryMinimizer
public import Econlib.Probability.ProbDist.Borel

/-!
# Non-extreme locus and local Carathéodory perturbations

`nonExtremeLocus` records the points where `Sx` fails to coincide with the extreme points of its
closed convex hull. At such a point the support admits a non-trivial Carathéodory decomposition,
and from that data we build a same-cell competitor whose squared-norm cost is strictly smaller —
witnessing that a cell-conditional measure with non-extreme support is not auxiliary-minimal.

## Main definitions

* `nonExtremeLocus`: The set of `x` where `Sx s v S pi x` differs from the extreme points of
  `closure (convexHull ℝ (Sx s v S pi x))`.

## Main statements

* `exists_caratheodory_decomp_of_mem_nonExtremeLocus`: At a point of `nonExtremeLocus`, some
  `y₀ ∈ Sx` is a non-trivial positive convex combination of points of `Sx`.
* `exists_strict_local_improvement_of_caratheodory_data`: Given such Carathéodory data, there is a
  same-cell competitor with strictly smaller squared-norm cost.

## Tags

persuasion, moment persuasion, extreme points, local perturbation
-/

@[expose] public section

open MeasureTheory Set Real TopologicalSpace
open scoped NNReal Topology ProbabilityTheory

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
variable {n : ℕ}
variable [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω]

/-! ### The non-extreme locus and local perturbations -/

/-- The points where `Sx s v S pi x` fails to equal the extreme points of
`closure (convexHull ℝ (Sx s v S pi x))`. -/
def nonExtremeLocus (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  { x | Sx s v S pi x ≠
        Set.extremePoints ℝ (closure (convexHull ℝ (Sx s v S pi x))) }

omit [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- At a point of `nonExtremeLocus`, some `y₀ ∈ Sx_{x₀}` is a non-trivial positive convex
combination of points of `Sx_{x₀}`.  The returned data records the points, positive weights,
barycenter identity, non-triviality, and injectivity of the chosen point family. -/
lemma exists_caratheodory_decomp_of_mem_nonExtremeLocus
    (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx_bad : x₀ ∈ nonExtremeLocus s v S pi) :
    ∃ (y₀ : EuclideanSpace ℝ (Fin n))
      (ι : Type) (_ : Fintype ι)
      (yi : ι → EuclideanSpace ℝ (Fin n)) (lam : ι → ℝ),
      y₀ ∈ Sx s v S pi x₀ ∧
      (∀ i, yi i ∈ Sx s v S pi x₀) ∧
      (∀ i, 0 < lam i) ∧
      (∑ i, lam i = 1) ∧
      (∑ i, lam i • yi i = y₀) ∧
      (∃ i, yi i ≠ y₀) ∧
      Function.Injective yi := by
  have hSx_compact : IsCompact (Sx s v S pi x₀) := Sx_isCompact s v S pi x₀
  have h_cl_eq : closure (convexHull ℝ (Sx s v S pi x₀))
                  = convexHull ℝ (Sx s v S pi x₀) :=
    closure_convexHull_of_isCompact hSx_compact
  have h_clconv_compact :
      IsCompact (closure (convexHull ℝ (Sx s v S pi x₀))) := by
    rw [h_cl_eq]
    exact isCompact_convexHull_of_isCompact hSx_compact
  have h_clconv_convex :
      Convex ℝ (closure (convexHull ℝ (Sx s v S pi x₀))) :=
    (convex_convexHull ℝ _).closure
  have h_milman :
      Set.extremePoints ℝ (closure (convexHull ℝ (Sx s v S pi x₀)))
        ⊆ Sx s v S pi x₀ :=
    extremePoints_closure_convexHull_subset_of_isCompact hSx_compact
  have h_ne : Sx s v S pi x₀ ≠ Set.extremePoints ℝ
                (closure (convexHull ℝ (Sx s v S pi x₀))) := hx_bad
  have h_not_subset :
      ¬ Sx s v S pi x₀ ⊆
          Set.extremePoints ℝ (closure (convexHull ℝ (Sx s v S pi x₀))) := by
    intro h_subset
    exact h_ne (Set.Subset.antisymm h_subset h_milman)
  obtain ⟨y₀, hy₀_Sx, hy₀_not_ext⟩ := Set.not_subset.mp h_not_subset
  have hy₀_clconv : y₀ ∈ closure (convexHull ℝ (Sx s v S pi x₀)) :=
    subset_closure (subset_convexHull ℝ _ hy₀_Sx)
  have hy₀_in_hull :
      y₀ ∈ convexHull ℝ (Set.extremePoints ℝ
            (closure (convexHull ℝ (Sx s v S pi x₀)))) :=
    subset_convexHull_extremePoints_of_compact_convex
      h_clconv_compact h_clconv_convex hy₀_clconv
  obtain ⟨ι, hι_fin, z, w, hzs, hzi, hw_pos, hw_sum, hw_combo⟩ :=
    eq_pos_convex_span_of_mem_convexHull hy₀_in_hull
  letI : Fintype ι := hι_fin
  have hz_Sx : ∀ i, z i ∈ Sx s v S pi x₀ :=
    fun i => h_milman (hzs (Set.mem_range_self i))
  have h_nontriv : ∃ i, z i ≠ y₀ := by
    by_contra h_all_eq
    push Not at h_all_eq
    have hι_nonempty : Nonempty ι := by
      by_contra h_empty
      rw [not_nonempty_iff] at h_empty
      have h_univ_empty : (Finset.univ : Finset ι) = ∅ :=
        Finset.univ_eq_empty_iff.mpr h_empty
      rw [h_univ_empty, Finset.sum_empty] at hw_sum
      exact one_ne_zero hw_sum.symm
    obtain ⟨i⟩ := hι_nonempty
    have hz_i_ext : z i ∈ Set.extremePoints ℝ
        (closure (convexHull ℝ (Sx s v S pi x₀))) :=
      hzs (Set.mem_range_self i)
    rw [h_all_eq i] at hz_i_ext
    exact hy₀_not_ext hz_i_ext
  exact ⟨y₀, ι, hι_fin, z, w, hy₀_Sx, hz_Sx, hw_pos, hw_sum, hw_combo, h_nontriv,
    hzi.injective⟩

omit [PseudoMetrizableSpace Ω] [Inhabited Ω] [T2Space Ω] in
/-- Given `CellConditionalData` at `x₀` and a non-extreme point `y₀ ∈ Sx_{x₀}`, construct a
same-cell competitor `rho'` whose squared-norm cost is strictly smaller than `cell.rho`'s.  The
Carathéodory witnesses in the signature certify the non-extremality of `y₀`. -/
lemma exists_strict_local_improvement_of_caratheodory_data
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hv_diff : ContDiff ℝ 1 v)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hpi_M : ConditionM s v pi S)
    (hS_sub : S ⊆ S_star s v S)
    (hpStar_cont : Continuous (pStar v S))
    {x₀ y₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀_S : x₀ ∈ S)
    (cell : CellConditionalData s v S pi x₀)
    {ι : Type} [Fintype ι]
    {yi : ι → EuclideanSpace ℝ (Fin n)} {lam : ι → ℝ}
    (hy₀_Sx : y₀ ∈ Sx s v S pi x₀)
    (hyi_Sx : ∀ i, yi i ∈ Sx s v S pi x₀)
    (hlam_pos : ∀ i, 0 < lam i)
    (hlam_sum : ∑ i, lam i = 1)
    (h_combo : ∑ i, lam i • yi i = y₀)
    (h_nontriv : ∃ i, yi i ≠ y₀) :
    ∃ rho' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω),
      SameCellCompetitor s v S x₀ cell.rho rho' ∧
      ∫ p, ‖p.1‖ ^ 2 ∂rho'.toMeasure <
        ∫ p, ‖p.1‖ ^ 2 ∂cell.rho.toMeasure := by
  have hpi_feas : pi ∈ feasibleJoint s := hpi_M.feasible
  have h_y₀_nonext :
      y₀ ∉ Set.extremePoints ℝ (closure (convexHull ℝ (Sx s v S pi x₀))) := by
    intro hy₀_ext
    obtain ⟨i₀, hi₀_ne⟩ := h_nontriv
    have hy_subset : Sx s v S pi x₀ ⊆ closure (convexHull ℝ (Sx s v S pi x₀)) :=
      (subset_convexHull ℝ _).trans subset_closure
    have h_yi_mem : ∀ j, yi j ∈ closure (convexHull ℝ (Sx s v S pi x₀)) :=
      fun j => hy_subset (hyi_Sx j)
    have h_conv :
        Convex ℝ (closure (convexHull ℝ (Sx s v S pi x₀))) :=
      (convex_convexHull ℝ _).closure
    have h_combo_real :
        (Finset.univ : Finset ι).centerMass lam yi = y₀ := by
      unfold Finset.centerMass
      rw [hlam_sum, inv_one, one_smul]
      simpa [smul_eq_mul] using h_combo
    apply hi₀_ne
    classical
    have h_lam_i₀_pos : (0 : ℝ) < lam i₀ := hlam_pos i₀
    have h_lam_i₀_le_one : lam i₀ ≤ 1 := by
      have h_split :
          ∑ k, lam k = lam i₀ + ∑ k ∈ Finset.univ.erase i₀, lam k :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
      have h_others_nonneg : (0 : ℝ) ≤ ∑ k ∈ Finset.univ.erase i₀, lam k :=
        Finset.sum_nonneg fun k _ => (hlam_pos k).le
      linarith [h_split ▸ hlam_sum]
    by_cases h_lam_i₀_eq_one : lam i₀ = 1
    · -- `lam i₀ = 1`: all other weights are zero, contradicting `hlam_pos`.
      have h_no_other : ∀ j, j = i₀ := by
        intro j
        by_contra hj
        have h_split :
            ∑ k, lam k = lam i₀ + ∑ k ∈ Finset.univ.erase i₀, lam k :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
        have h_others_zero : ∑ k ∈ Finset.univ.erase i₀, lam k = 0 := by
          linarith [h_split.symm.trans hlam_sum]
        have h_j_in : j ∈ Finset.univ.erase i₀ :=
          Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
        have h_others_pos :
            (0 : ℝ) < ∑ k ∈ Finset.univ.erase i₀, lam k :=
          Finset.sum_pos (fun k _ => hlam_pos k) ⟨j, h_j_in⟩
        linarith
      have h_sum_collapse : ∑ k, lam k • yi k = lam i₀ • yi i₀ := by
        rw [show (Finset.univ : Finset ι) = {i₀} from ?_]
        · simp
        · ext j; simp [h_no_other j]
      have h_y₀_eq : y₀ = lam i₀ • yi i₀ := by
        rw [← h_combo, h_sum_collapse]
      rw [h_y₀_eq, h_lam_i₀_eq_one, one_smul]
    · -- `0 < lam i₀ < 1`: split off `i₀` and average the rest.
      have h_lam_i₀_lt_one : lam i₀ < 1 := lt_of_le_of_ne h_lam_i₀_le_one h_lam_i₀_eq_one
      have h_one_sub_pos : (0 : ℝ) < 1 - lam i₀ := by linarith
      have h_others_sum :
          ∑ k ∈ Finset.univ.erase i₀, lam k = 1 - lam i₀ := by
        have h_split :
            ∑ k, lam k = lam i₀ + ∑ k ∈ Finset.univ.erase i₀, lam k :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
        linarith [h_split ▸ hlam_sum]
      set y' : EuclideanSpace ℝ (Fin n) :=
          (Finset.univ.erase i₀).centerMass lam yi with hy'_def
      have h_y'_mem : y' ∈ closure (convexHull ℝ (Sx s v S pi x₀)) := by
        refine h_conv.centerMass_mem ?_ ?_ ?_
        · intro k hk; exact (hlam_pos k).le
        · rw [h_others_sum]; exact h_one_sub_pos
        · intro k _; exact h_yi_mem k
      have h_y₀_decomp :
          y₀ = lam i₀ • yi i₀ + (1 - lam i₀) • y' := by
        have h_combo_split :
            ∑ k, lam k • yi k =
              lam i₀ • yi i₀ + ∑ k ∈ Finset.univ.erase i₀, lam k • yi k :=
          (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
        have h_smul_centerMass :
            (1 - lam i₀) • y' = ∑ k ∈ Finset.univ.erase i₀, lam k • yi k := by
          rw [hy'_def, Finset.centerMass, h_others_sum, smul_smul,
              mul_inv_cancel₀ h_one_sub_pos.ne', one_smul]
        rw [← h_combo, h_combo_split, h_smul_centerMass]
      have h_y₀_open :
          y₀ ∈ openSegment ℝ (yi i₀) y' :=
        ⟨lam i₀, 1 - lam i₀, h_lam_i₀_pos, h_one_sub_pos,
          by linarith, h_y₀_decomp.symm⟩
      exact hy₀_ext.2 (h_yi_mem i₀) h_y'_mem h_y₀_open
  obtain ⟨α, hα_ne, hα_le, hα_supp, hα_atom, hα_mean⟩ :=
    cell.barycentric_decomposability y₀ hy₀_Sx h_y₀_nonext
  set ν_cell : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)) :=
    (ProbDist.map cell.rho Prod.fst measurable_fst).toMeasure with hν_cell_def
  have hα_ac : α.AbsolutelyContinuous ν_cell :=
    MeasureTheory.Measure.absolutelyContinuous_of_le hα_le
  set f : EuclideanSpace ℝ (Fin n) → ENNReal := α.rnDeriv ν_cell with hf_def
  have hf_meas : Measurable f := MeasureTheory.Measure.measurable_rnDeriv α ν_cell
  have hf_le_one_νcell : f ≤ᵐ[ν_cell] 1 :=
    MeasureTheory.Measure.rnDeriv_le_one_of_le hα_le
  have hf_fst_le_one : (fun p : EuclideanSpace ℝ (Fin n) × Ω => f p.1)
      ≤ᵐ[cell.rho.toMeasure] (fun _ => 1) := by
    have h_map_eq : ν_cell = cell.rho.toMeasure.map Prod.fst := by
      simp [hν_cell_def]
    have h_νcell_ae : ∀ᵐ y ∂(cell.rho.toMeasure.map Prod.fst), f y ≤ 1 := by
      rw [← h_map_eq]; exact hf_le_one_νcell
    exact (MeasureTheory.ae_map_iff (μ := cell.rho.toMeasure)
      (f := Prod.fst) measurable_fst.aemeasurable
      (p := fun x => f x ≤ 1) (measurableSet_le hf_meas measurable_const)).mp
      h_νcell_ae
  set ᾱ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n) × Ω) :=
    cell.rho.toMeasure.withDensity (fun p => f p.1) with hbar_α_def
  set ᾱ_Ω : MeasureTheory.Measure Ω := ᾱ.map Prod.snd with hᾱ_Ω_def
  set Mα : ENNReal := α Set.univ with hMα_def
  set μtilde : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n) × Ω) :=
    (cell.rho.toMeasure - ᾱ) +
      (MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω with hμtilde_def
  have hbar_α_le : ᾱ ≤ cell.rho.toMeasure := by
    calc ᾱ = cell.rho.toMeasure.withDensity (fun p => f p.1) := hbar_α_def
      _ ≤ cell.rho.toMeasure.withDensity (fun _ => 1) :=
          MeasureTheory.withDensity_mono hf_fst_le_one
      _ = cell.rho.toMeasure := MeasureTheory.withDensity_one
  have hbar_α_map_fst : ᾱ.map Prod.fst = α := by
    have h_step : ᾱ.map Prod.fst = ν_cell.withDensity f := by
      apply MeasureTheory.Measure.ext
      intro B hB
      rw [MeasureTheory.Measure.map_apply measurable_fst hB, hbar_α_def,
          MeasureTheory.withDensity_apply _ (hB.preimage measurable_fst),
          MeasureTheory.withDensity_apply _ hB]
      rw [hν_cell_def]
      simp only [ProbDist.map_toMeasure]
      rw [MeasureTheory.setLIntegral_map hB hf_meas measurable_fst]
    rw [h_step]
    haveI : MeasureTheory.IsFiniteMeasure ν_cell := by
      rw [hν_cell_def]; infer_instance
    haveI : MeasureTheory.IsFiniteMeasure α :=
      MeasureTheory.isFiniteMeasure_of_le ν_cell hα_le
    haveI : MeasureTheory.SigmaFinite ν_cell := inferInstance
    haveI : MeasureTheory.SFinite α := inferInstance
    haveI : α.HaveLebesgueDecomposition ν_cell :=
      MeasureTheory.Measure.haveLebesgueDecomposition_of_sigmaFinite α ν_cell
    exact MeasureTheory.Measure.withDensity_rnDeriv_eq α ν_cell hα_ac
  have hbar_α_univ : ᾱ Set.univ = Mα := by
    rw [← Set.preimage_univ (f := Prod.fst), ← MeasureTheory.Measure.map_apply
      measurable_fst MeasurableSet.univ, hbar_α_map_fst]
  have hbar_α_Ω_univ : ᾱ_Ω Set.univ = Mα := by
    rw [hᾱ_Ω_def, MeasureTheory.Measure.map_apply measurable_snd MeasurableSet.univ,
        Set.preimage_univ, hbar_α_univ]
  have hMα_le_one : Mα ≤ 1 := by
    rw [← hbar_α_univ, ← MeasureTheory.measure_univ (μ := cell.rho.toMeasure)]
    exact hbar_α_le _
  have hμtilde_univ : μtilde Set.univ = 1 := by
    have h_prod_univ_eq :
        ((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω) Set.univ
          = (MeasureTheory.Measure.dirac y₀) Set.univ * ᾱ_Ω Set.univ := by
      rw [← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod]
    haveI : MeasureTheory.IsFiniteMeasure ᾱ :=
      MeasureTheory.isFiniteMeasure_of_le cell.rho.toMeasure hbar_α_le
    rw [hμtilde_def, MeasureTheory.Measure.add_apply, h_prod_univ_eq,
        MeasureTheory.measure_univ (μ := MeasureTheory.Measure.dirac y₀), one_mul,
        hbar_α_Ω_univ,
        MeasureTheory.Measure.sub_apply MeasurableSet.univ hbar_α_le,
        MeasureTheory.measure_univ (μ := cell.rho.toMeasure), hbar_α_univ]
    exact tsub_add_cancel_of_le hMα_le_one
  haveI hμtilde_prob : MeasureTheory.IsProbabilityMeasure μtilde :=
    ⟨hμtilde_univ⟩
  let rho' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω) :=
    ⟨μtilde, hμtilde_prob⟩
  have hrho'_toMeasure : rho'.toMeasure = μtilde := rfl
  have hX_closed : IsClosed (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
    s.X_compact.isClosed
  have hX_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
    hX_closed.measurableSet
  have h_fst_X_cell_rho_zero :
      cell.rho.toMeasure ((Prod.fst ⁻¹' s.X : Set _)ᶜ) = 0 := by
    have h_supp_X :
        (ProbDist.map cell.rho Prod.fst measurable_fst).toMeasure.support
          ⊆ (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
      cell.fst_support_subset_Sx.trans (Sx_subset_X s v S pi x₀)
    rw [← Set.preimage_compl,
        ← MeasureTheory.Measure.map_apply measurable_fst hX_meas.compl]
    have h_compl_sub :
        (s.X : Set (EuclideanSpace ℝ (Fin n)))ᶜ
          ⊆ ((ProbDist.map cell.rho Prod.fst measurable_fst).toMeasure.support)ᶜ :=
      Set.compl_subset_compl.mpr h_supp_X
    have := (MeasureTheory.measure_mono h_compl_sub).trans_eq
      MeasureTheory.Measure.measure_compl_support
    rw [ProbDist.map_toMeasure] at this
    exact le_antisymm this (zero_le)
  refine ⟨rho', ?_, ?_⟩
  · refine
      { same_snd_marginal := ?_
        fst_supportsOn_X := ?_
        local_martingale := ?_
        contact_support := ?_ }
    · simp only [ProbDist.map_toMeasure, hrho'_toMeasure]
      haveI hbar_α_fin : MeasureTheory.IsFiniteMeasure ᾱ :=
        MeasureTheory.isFiniteMeasure_of_le _ hbar_α_le
      have h_dirac_snd_marg :
          ((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω).map Prod.snd = ᾱ_Ω := by
        rw [MeasureTheory.Measure.map_snd_prod, MeasureTheory.measure_univ, one_smul]
      have h_bar_α_Ω_le :
          ᾱ.map Prod.snd ≤ cell.rho.toMeasure.map Prod.snd :=
        MeasureTheory.Measure.map_mono hbar_α_le measurable_snd
      ext B hB
      have h_sub_map_B :
          (cell.rho.toMeasure - ᾱ).map Prod.snd B
            = cell.rho.toMeasure.map Prod.snd B - ᾱ.map Prod.snd B := by
        rw [MeasureTheory.Measure.map_apply measurable_snd hB,
            MeasureTheory.Measure.sub_apply (hB.preimage measurable_snd) hbar_α_le,
            ← MeasureTheory.Measure.map_apply measurable_snd hB,
            ← MeasureTheory.Measure.map_apply measurable_snd hB]
      rw [MeasureTheory.Measure.map_add _ _ measurable_snd,
          MeasureTheory.Measure.add_apply, h_sub_map_B, h_dirac_snd_marg]
      have h_ᾱ_Ω_le_B : ᾱ_Ω B ≤ cell.rho.toMeasure.map Prod.snd B := by
        rw [hᾱ_Ω_def]; exact h_bar_α_Ω_le B
      rw [hᾱ_Ω_def] at h_ᾱ_Ω_le_B
      rw [hᾱ_Ω_def, tsub_add_cancel_of_le h_ᾱ_Ω_le_B]
    · simp only [hrho'_toMeasure]
      haveI hbar_α_fin : MeasureTheory.IsFiniteMeasure ᾱ :=
        MeasureTheory.isFiniteMeasure_of_le _ hbar_α_le
      have h_fst_X_bar_α_zero : ᾱ ((Prod.fst ⁻¹' s.X : Set _)ᶜ) = 0 :=
        le_antisymm
          ((hbar_α_le _).trans h_fst_X_cell_rho_zero.le) (zero_le)
      have h_fst_X_sub_zero :
          (cell.rho.toMeasure - ᾱ) ((Prod.fst ⁻¹' s.X : Set _)ᶜ) = 0 := by
        rw [MeasureTheory.Measure.sub_apply
              (MeasurableSet.compl (measurable_fst hX_meas)) hbar_α_le,
            h_fst_X_cell_rho_zero, h_fst_X_bar_α_zero, tsub_zero]
      have hy₀_X : y₀ ∈ (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
        Sx_subset_X s v S pi x₀ hy₀_Sx
      have h_fst_X_dirac_prod_zero :
          ((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω)
              ((Prod.fst ⁻¹' s.X : Set _)ᶜ) = 0 := by
        rw [show ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' s.X)ᶜ
              = ((s.X : Set (EuclideanSpace ℝ (Fin n)))ᶜ) ×ˢ (Set.univ : Set Ω) from by
              ext ⟨a, b⟩; simp,
            MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.dirac_apply' _ hX_meas.compl,
            Set.indicator_of_notMem (by simpa using hy₀_X), zero_mul]
      rw [MeasureTheory.Measure.add_apply, h_fst_X_sub_zero, h_fst_X_dirac_prod_zero,
          add_zero]
    · intro A hA
      simp only [hrho'_toMeasure]
      haveI hbar_α_fin : MeasureTheory.IsFiniteMeasure ᾱ :=
        MeasureTheory.isFiniteMeasure_of_le _ hbar_α_le
      haveI hᾱ_Ω_fin : MeasureTheory.IsFiniteMeasure ᾱ_Ω := by
        rw [hᾱ_Ω_def]; exact MeasureTheory.Measure.isFiniteMeasure_map _ _
      haveI hμsub_fin : MeasureTheory.IsFiniteMeasure (cell.rho.toMeasure - ᾱ) :=
        MeasureTheory.Measure.isFiniteMeasure_sub
      haveI hprod_fin :
          MeasureTheory.IsFiniteMeasure
            ((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω) := inferInstance
      obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x ∈ s.X, ‖x‖ ≤ R :=
        s.X_compact.isBounded.exists_norm_le
      have hR_nonneg : 0 ≤ R :=
        (norm_nonneg _).trans (hR _ (Sx_subset_X s v S pi x₀ hy₀_Sx))
      have h_m_norm : ∀ ω : Ω, ‖s.m ω‖ ≤ R := fun ω => hR _ (s.m_mem_X ω)
      have h_int_cont :
          Continuous fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1 :=
        (s.m_continuous.comp continuous_snd).sub continuous_fst
      have h_int_meas :
          Measurable fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1 :=
        h_int_cont.measurable
      have h_int_aesm :
          ∀ {μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n) × Ω)},
            AEStronglyMeasurable
              (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1) μ :=
        h_int_cont.aestronglyMeasurable
      have h_ae_p1_X_cell : ∀ᵐ p ∂cell.rho.toMeasure, p.1 ∈ s.X := by
        rw [MeasureTheory.ae_iff]; exact h_fst_X_cell_rho_zero
      have h_ae_p1_X_bar : ∀ᵐ p ∂ᾱ, p.1 ∈ s.X := by
        have : ᾱ ((Prod.fst ⁻¹' s.X : Set _)ᶜ) = 0 :=
          le_antisymm ((hbar_α_le _).trans h_fst_X_cell_rho_zero.le) (zero_le)
        rw [MeasureTheory.ae_iff]; exact this
      have h_ae_p1_X_sub :
          ∀ᵐ p ∂(cell.rho.toMeasure - ᾱ), p.1 ∈ s.X := by
        have h_le :=
          MeasureTheory.Measure.sub_le (μ := cell.rho.toMeasure) (ν := ᾱ)
            {p : EuclideanSpace ℝ (Fin n) × Ω | ¬ p.1 ∈ s.X}
        rw [MeasureTheory.ae_iff]
        exact le_antisymm (h_le.trans h_fst_X_cell_rho_zero.le) (zero_le)
      have h_norm_bound :
          ∀ {p : EuclideanSpace ℝ (Fin n) × Ω}, p.1 ∈ s.X →
            ‖s.m p.2 - p.1‖ ≤ R + R := fun {p} hp => by
        calc ‖s.m p.2 - p.1‖ ≤ ‖s.m p.2‖ + ‖p.1‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add (h_m_norm _) (hR _ hp)
      have h_int_cell :
          MeasureTheory.Integrable
            (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1)
            cell.rho.toMeasure := by
        refine MeasureTheory.Integrable.of_bound h_int_aesm (R + R) ?_
        filter_upwards [h_ae_p1_X_cell] with p hp using h_norm_bound hp
      have h_int_bar :
          MeasureTheory.Integrable
            (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1) ᾱ := by
        refine MeasureTheory.Integrable.of_bound h_int_aesm (R + R) ?_
        filter_upwards [h_ae_p1_X_bar] with p hp using h_norm_bound hp
      have h_int_sub :
          MeasureTheory.Integrable
            (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1)
            (cell.rho.toMeasure - ᾱ) := by
        refine MeasureTheory.Integrable.of_bound h_int_aesm (R + R) ?_
        filter_upwards [h_ae_p1_X_sub] with p hp using h_norm_bound hp
      have hy₀_X : y₀ ∈ (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
        Sx_subset_X s v S pi x₀ hy₀_Sx
      have h_ae_p1_X_prod :
          ∀ᵐ p ∂((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω), p.1 ∈ s.X := by
        rw [MeasureTheory.Measure.dirac_prod,
            MeasureTheory.ae_map_iff measurable_prodMk_left.aemeasurable
              (measurable_fst hX_meas)]
        exact MeasureTheory.ae_of_all _ (fun _ => hy₀_X)
      have h_int_prod :
          MeasureTheory.Integrable
            (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1)
            ((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω) := by
        refine MeasureTheory.Integrable.of_bound h_int_aesm (R + R) ?_
        filter_upwards [h_ae_p1_X_prod] with p hp using h_norm_bound hp
      have h_int_sub_set :
          MeasureTheory.IntegrableOn
            (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1)
            (A ×ˢ (Set.univ : Set Ω)) (cell.rho.toMeasure - ᾱ) :=
        h_int_sub.integrableOn
      have h_int_prod_set :
          MeasureTheory.IntegrableOn
            (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1)
            (A ×ˢ (Set.univ : Set Ω))
            ((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω) :=
        h_int_prod.integrableOn
      have h_split :
          ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂(cell.rho.toMeasure - ᾱ
              + (MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω)
            = ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂(cell.rho.toMeasure - ᾱ)
              + ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1)
                  ∂((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω) := by
        rw [MeasureTheory.Measure.restrict_add]
        exact MeasureTheory.integral_add_measure h_int_sub_set h_int_prod_set
      rw [h_split]
      have h_cell_eq :
          ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂cell.rho.toMeasure = 0 :=
        cell.local_martingale A hA
      have h_decomp_cell :
          ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂cell.rho.toMeasure
            = ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂(cell.rho.toMeasure - ᾱ)
              + ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂ᾱ := by
        conv_lhs => rw [← MeasureTheory.Measure.sub_add_cancel_of_le hbar_α_le]
        rw [MeasureTheory.Measure.restrict_add]
        exact MeasureTheory.integral_add_measure h_int_sub_set h_int_bar.integrableOn
      have h_bar_int_at :
          ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B →
            ∫ p in B ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂ᾱ = 0 := by
        intro B hB
        have hf_fst_lt_top :
            ∀ᵐ p ∂cell.rho.toMeasure, f p.1 < ⊤ := by
          filter_upwards [hf_fst_le_one] with p hp
          exact lt_of_le_of_lt hp (by norm_num : (1 : ENNReal) < ⊤)
        have hf_fst_meas : Measurable fun p : EuclideanSpace ℝ (Fin n) × Ω => f p.1 :=
          hf_meas.comp measurable_fst
        have hB_prod : MeasurableSet (B ×ˢ (Set.univ : Set Ω)) :=
          hB.prod MeasurableSet.univ
        have h_top_restrict :
            ∀ᵐ p ∂(cell.rho.toMeasure.restrict (B ×ˢ (Set.univ : Set Ω))), f p.1 < ⊤ :=
          MeasureTheory.ae_restrict_of_ae hf_fst_lt_top
        rw [hbar_α_def,
            setIntegral_withDensity_eq_setIntegral_toReal_smul
              hf_fst_meas h_top_restrict _ hB_prod]
        set Fk : ℕ → EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n) :=
          fun k p => ((MeasureTheory.SimpleFunc.eapprox f k) p.1).toReal •
            (s.m p.2 - p.1) with hFk_def
        set Finf : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n) :=
          fun p => (f p.1).toReal • (s.m p.2 - p.1) with hFinf_def
        have h_pointwise :
            ∀ᵐ p ∂cell.rho.toMeasure,
              Filter.Tendsto (fun k => Fk k p) Filter.atTop (nhds (Finf p)) := by
          filter_upwards [hf_fst_lt_top] with p hp
          have h_tendsto_enn :
              Filter.Tendsto
                (fun k => (MeasureTheory.SimpleFunc.eapprox f k) p.1)
                Filter.atTop (nhds (f p.1)) :=
            MeasureTheory.SimpleFunc.tendsto_eapprox hf_meas p.1
          have h_tendsto_real :
              Filter.Tendsto
                (fun k => ((MeasureTheory.SimpleFunc.eapprox f k) p.1).toReal)
                Filter.atTop (nhds (f p.1).toReal) :=
            (ENNReal.continuousAt_toReal hp.ne).tendsto.comp h_tendsto_enn
          exact h_tendsto_real.smul tendsto_const_nhds
        have h_eapprox_le_f :
            ∀ (k : ℕ) (p : EuclideanSpace ℝ (Fin n) × Ω),
              (MeasureTheory.SimpleFunc.eapprox f k) p.1 ≤ f p.1 := by
          intro k p
          have h_iSup : ⨆ j, (MeasureTheory.SimpleFunc.eapprox f j) p.1 = f p.1 :=
            MeasureTheory.SimpleFunc.iSup_eapprox_apply hf_meas p.1
          exact h_iSup ▸ le_iSup
            (f := fun j => (MeasureTheory.SimpleFunc.eapprox f j) p.1) k
        have h_eapprox_toReal_le_one :
            ∀ᵐ p ∂cell.rho.toMeasure, ∀ k : ℕ,
              ((MeasureTheory.SimpleFunc.eapprox f k) p.1).toReal ≤ 1 := by
          filter_upwards [hf_fst_le_one] with p hp k
          have hle : (MeasureTheory.SimpleFunc.eapprox f k) p.1 ≤ 1 :=
            (h_eapprox_le_f k p).trans hp
          have : ((MeasureTheory.SimpleFunc.eapprox f k) p.1).toReal ≤ (1 : ENNReal).toReal :=
            ENNReal.toReal_mono (by norm_num) hle
          simpa using this
        have h_eapprox_toReal_nonneg :
            ∀ (k : ℕ) (p : EuclideanSpace ℝ (Fin n) × Ω),
              0 ≤ ((MeasureTheory.SimpleFunc.eapprox f k) p.1).toReal :=
          fun _ _ => ENNReal.toReal_nonneg
        have h_norm_Fk_bound :
            ∀ k : ℕ, ∀ᵐ p ∂cell.rho.toMeasure, ‖Fk k p‖ ≤ R + R := by
          intro k
          filter_upwards [h_ae_p1_X_cell, h_eapprox_toReal_le_one] with p hp_X hp_bound
          have hbnd : ((MeasureTheory.SimpleFunc.eapprox f k) p.1).toReal ≤ 1 :=
            hp_bound k
          have hnn : 0 ≤ ((MeasureTheory.SimpleFunc.eapprox f k) p.1).toReal :=
            h_eapprox_toReal_nonneg k p
          have hnorm : ‖Fk k p‖ =
              ((MeasureTheory.SimpleFunc.eapprox f k) p.1).toReal * ‖s.m p.2 - p.1‖ := by
            simp [hFk_def, norm_smul, abs_of_nonneg hnn]
          rw [hnorm]
          have h1 : ‖s.m p.2 - p.1‖ ≤ R + R := h_norm_bound hp_X
          have h2 : 0 ≤ ‖s.m p.2 - p.1‖ := norm_nonneg _
          calc ((MeasureTheory.SimpleFunc.eapprox f k) p.1).toReal * ‖s.m p.2 - p.1‖
              ≤ 1 * ‖s.m p.2 - p.1‖ := by
                exact mul_le_mul_of_nonneg_right hbnd h2
            _ = ‖s.m p.2 - p.1‖ := one_mul _
            _ ≤ R + R := h1
        have h_bound_integrable :
            MeasureTheory.Integrable (fun _ : EuclideanSpace ℝ (Fin n) × Ω => R + R)
              cell.rho.toMeasure := MeasureTheory.integrable_const _
        have hFk_aesm : ∀ k : ℕ, AEStronglyMeasurable (Fk k) cell.rho.toMeasure := by
          intro k
          have h_meas_real :
              Measurable
                fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                  ((MeasureTheory.SimpleFunc.eapprox f k) p.1).toReal := by
            exact ((MeasureTheory.SimpleFunc.eapprox f k).measurable.comp
              measurable_fst).ennreal_toReal
          have h_meas_g :
              Measurable fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1 := h_int_meas
          exact (h_meas_real.smul h_meas_g).aestronglyMeasurable
        have h_Fk_int_zero :
            ∀ k : ℕ, ∫ p in B ×ˢ (Set.univ : Set Ω), Fk k p ∂cell.rho.toMeasure = 0 := by
          intro k
          set sk := MeasureTheory.SimpleFunc.eapprox f k
          have h_decomp_pt :
              ∀ x : EuclideanSpace ℝ (Fin n),
                (sk x).toReal =
                  ∑ c ∈ sk.range, c.toReal * (sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) x := by
            intro x
            have hx_mem : sk x ∈ sk.range := MeasureTheory.SimpleFunc.mem_range_self sk x
            rw [Finset.sum_eq_single_of_mem (sk x) hx_mem]
            · have : (sk ⁻¹' {sk x}).indicator (fun _ => (1 : ℝ)) x = 1 := by
                rw [Set.indicator_of_mem (by rfl : x ∈ sk ⁻¹' {sk x})]
              rw [this, mul_one]
            · intro c _ hc_ne
              have hx_notin : x ∉ sk ⁻¹' {c} := by
                intro hmem
                exact hc_ne (Set.mem_singleton_iff.mp hmem).symm
              rw [Set.indicator_of_notMem hx_notin, mul_zero]
          have h_integrand_eq :
              ∀ p : EuclideanSpace ℝ (Fin n) × Ω,
                Fk k p
                  = ∑ c ∈ sk.range,
                      (c.toReal * (sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) p.1)
                        • (s.m p.2 - p.1) := by
            intro p
            simp only [hFk_def]
            rw [h_decomp_pt p.1, Finset.sum_smul]
          calc ∫ p in B ×ˢ (Set.univ : Set Ω), Fk k p ∂cell.rho.toMeasure
              = ∫ p in B ×ˢ (Set.univ : Set Ω),
                  (∑ c ∈ sk.range,
                    (c.toReal * (sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) p.1)
                      • (s.m p.2 - p.1)) ∂cell.rho.toMeasure := by
                  refine MeasureTheory.setIntegral_congr_ae hB_prod ?_
                  exact MeasureTheory.ae_of_all _ (fun p _ => h_integrand_eq p)
            _ = ∑ c ∈ sk.range,
                  ∫ p in B ×ˢ (Set.univ : Set Ω),
                    (c.toReal * (sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) p.1)
                      • (s.m p.2 - p.1) ∂cell.rho.toMeasure := by
                  refine MeasureTheory.integral_finset_sum sk.range ?_
                  intro c _
                  refine MeasureTheory.Integrable.integrableOn ?_
                  refine MeasureTheory.Integrable.of_bound ?_ (c.toReal * (R + R)) ?_
                  · refine AEStronglyMeasurable.smul ?_ h_int_aesm
                    refine (Measurable.mul measurable_const ?_).aestronglyMeasurable
                    exact (measurable_const.indicator
                      ((sk.measurableSet_preimage {c}).preimage measurable_fst))
                  · filter_upwards [h_ae_p1_X_cell] with p hp
                    have h1 : ‖s.m p.2 - p.1‖ ≤ R + R := h_norm_bound hp
                    have h_ind_le :
                        |(sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) p.1| ≤ 1 := by
                      rcases Classical.em (p.1 ∈ sk ⁻¹' {c}) with hin | hnin
                      · rw [Set.indicator_of_mem hin]; simp
                      · rw [Set.indicator_of_notMem hnin]; simp
                    have h_ctoReal_nn : 0 ≤ c.toReal := ENNReal.toReal_nonneg
                    have h_norm_smul :
                        ‖(c.toReal * (sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) p.1)
                          • (s.m p.2 - p.1)‖
                          = |c.toReal * (sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) p.1|
                            * ‖s.m p.2 - p.1‖ := by rw [norm_smul]; rfl
                    rw [h_norm_smul, abs_mul, abs_of_nonneg h_ctoReal_nn]
                    have h2 : 0 ≤ ‖s.m p.2 - p.1‖ := norm_nonneg _
                    have h_first' :
                        c.toReal *
                          |(sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) p.1| ≤ c.toReal := by
                      simpa using mul_le_mul_of_nonneg_left h_ind_le h_ctoReal_nn
                    exact mul_le_mul h_first' h1 h2 h_ctoReal_nn
            _ = ∑ c ∈ sk.range,
                  c.toReal • ∫ p in B ×ˢ (Set.univ : Set Ω),
                    ((sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) p.1) •
                      (s.m p.2 - p.1) ∂cell.rho.toMeasure := by
                  refine Finset.sum_congr rfl ?_
                  intro c _
                  rw [show (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                      (c.toReal * (sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) p.1)
                        • (s.m p.2 - p.1)) =
                      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                        c.toReal • (((sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) p.1)
                          • (s.m p.2 - p.1))) from ?_]
                  · rw [MeasureTheory.integral_smul]
                  · funext p
                    rw [smul_smul]
            _ = ∑ c ∈ sk.range, c.toReal •
                  ∫ p in (B ∩ sk ⁻¹' {c}) ×ˢ (Set.univ : Set Ω),
                    (s.m p.2 - p.1) ∂cell.rho.toMeasure := by
                  refine Finset.sum_congr rfl ?_
                  intro c _
                  congr 1
                  have h_indicator_eq :
                      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                        ((sk ⁻¹' {c}).indicator (fun _ => (1 : ℝ)) p.1) •
                          (s.m p.2 - p.1))
                        = ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹'
                            (sk ⁻¹' {c})).indicator
                              (fun p => s.m p.2 - p.1) := by
                    funext p
                    rcases Classical.em (p.1 ∈ sk ⁻¹' {c}) with hin | hnin
                    · have hp_fst :
                          p ∈ (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹'
                            (sk ⁻¹' {c}) := hin
                      rw [Set.indicator_of_mem hin, Set.indicator_of_mem hp_fst, one_smul]
                    · have hp_fst :
                          p ∉ (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹'
                            (sk ⁻¹' {c}) := hnin
                      rw [Set.indicator_of_notMem hnin, Set.indicator_of_notMem hp_fst,
                        zero_smul]
                  rw [h_indicator_eq]
                  have h_pre_meas : MeasurableSet
                      ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' (sk ⁻¹' {c})) :=
                    (sk.measurableSet_preimage {c}).preimage measurable_fst
                  rw [MeasureTheory.setIntegral_indicator h_pre_meas]
                  have h_set_eq :
                      B ×ˢ (Set.univ : Set Ω) ∩
                          (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' (sk ⁻¹' {c})
                        = (B ∩ sk ⁻¹' {c}) ×ˢ (Set.univ : Set Ω) := by
                    ext p
                    simp [Set.mem_inter_iff, Set.mem_prod, Set.mem_preimage, and_comm]
                  rw [h_set_eq]
            _ = ∑ c ∈ sk.range,
                  (c.toReal • (0 : EuclideanSpace ℝ (Fin n))) := by
                  refine Finset.sum_congr rfl ?_
                  intro c _
                  rw [cell.local_martingale (B ∩ sk ⁻¹' {c})
                    (hB.inter (sk.measurableSet_preimage {c}))]
            _ = 0 := by simp
        have h_lim :
            Filter.Tendsto
              (fun k => ∫ p in B ×ˢ (Set.univ : Set Ω), Fk k p ∂cell.rho.toMeasure)
              Filter.atTop
              (nhds (∫ p in B ×ˢ (Set.univ : Set Ω), Finf p ∂cell.rho.toMeasure)) := by
          refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
            (fun _ : EuclideanSpace ℝ (Fin n) × Ω => R + R) ?_ ?_ ?_ ?_
          · exact Filter.Eventually.of_forall fun k => (hFk_aesm k).restrict
          · refine Filter.Eventually.of_forall fun k => ?_
            exact MeasureTheory.ae_restrict_of_ae (h_norm_Fk_bound k)
          · exact h_bound_integrable.restrict
          · refine MeasureTheory.ae_restrict_of_ae ?_
            exact h_pointwise
        have h_lim_zero :
            Filter.Tendsto (fun k => ∫ p in B ×ˢ (Set.univ : Set Ω), Fk k p ∂cell.rho.toMeasure)
              Filter.atTop (nhds 0) := by simp [h_Fk_int_zero]
        have h_eq_zero :
            ∫ p in B ×ˢ (Set.univ : Set Ω), Finf p ∂cell.rho.toMeasure = 0 :=
          tendsto_nhds_unique h_lim h_lim_zero
        simpa [hFinf_def] using h_eq_zero
      have h_bar_int_eq :
          ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂ᾱ = 0 :=
        h_bar_int_at A hA
      have h_sub_eq :
          ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂(cell.rho.toMeasure - ᾱ) = 0 := by
        rw [h_cell_eq, h_bar_int_eq, add_zero] at h_decomp_cell
        exact h_decomp_cell.symm
      have h_bar_int_univ_eq :
          ∫ p in (Set.univ : Set (EuclideanSpace ℝ (Fin n)))
              ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1) ∂ᾱ = 0 :=
        h_bar_int_at Set.univ MeasurableSet.univ
      have h_prod_eq :
          ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1)
              ∂((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω) = 0 := by
        have hA_meas : MeasurableSet (A ×ˢ (Set.univ : Set Ω)) :=
          hA.prod MeasurableSet.univ
        rw [← MeasureTheory.integral_indicator hA_meas]
        rw [MeasureTheory.Measure.dirac_prod]
        rw [MeasureTheory.integral_map measurable_prodMk_left.aemeasurable]
        · have h_indic_eq :
              (fun ω : Ω =>
                  (A ×ˢ (Set.univ : Set Ω)).indicator
                    (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1) (y₀, ω))
                = fun ω : Ω =>
                    (A.indicator (fun _ => (1 : ℝ)) y₀) • (s.m ω - y₀) := by
            funext ω
            by_cases hy₀_A : y₀ ∈ A
            · have hpair : (y₀, ω) ∈ A ×ˢ (Set.univ : Set Ω) := ⟨hy₀_A, trivial⟩
              rw [Set.indicator_of_mem hpair, Set.indicator_of_mem hy₀_A]
              simp
            · have hpair : (y₀, ω) ∉ A ×ˢ (Set.univ : Set Ω) := by
                intro hmem; exact hy₀_A hmem.1
              rw [Set.indicator_of_notMem hpair, Set.indicator_of_notMem hy₀_A]
              simp
          rw [h_indic_eq]
          rw [MeasureTheory.integral_smul]
          have h_int_smy₀_aesm :
              AEStronglyMeasurable
                (fun ω : Ω => s.m ω - y₀) ᾱ_Ω :=
            (s.m_continuous.sub continuous_const).aestronglyMeasurable
          have h_omega_int :
              ∫ ω, (s.m ω - y₀) ∂ᾱ_Ω
                = ∫ p, (s.m p.2 - y₀) ∂ᾱ := by
            rw [hᾱ_Ω_def]
            exact MeasureTheory.integral_map measurable_snd.aemeasurable
              h_int_smy₀_aesm
          have h_id_int_bar :
              MeasureTheory.Integrable
                (fun p : EuclideanSpace ℝ (Fin n) × Ω => p.1) ᾱ := by
            refine MeasureTheory.Integrable.of_bound
              (continuous_fst.aestronglyMeasurable) R ?_
            filter_upwards [h_ae_p1_X_bar] with p hp using hR _ hp
          have h_const_int_bar :
              MeasureTheory.Integrable
                (fun _ : EuclideanSpace ℝ (Fin n) × Ω => y₀) ᾱ :=
            MeasureTheory.integrable_const _
          have h_sub_y₀_int_bar :
              MeasureTheory.Integrable
                (fun p : EuclideanSpace ℝ (Fin n) × Ω => p.1 - y₀) ᾱ :=
            h_id_int_bar.sub h_const_int_bar
          have h_smy₀_int_bar :
              MeasureTheory.Integrable
                (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - y₀) ᾱ := by
            refine MeasureTheory.Integrable.of_bound
              ((s.m_continuous.comp continuous_snd).sub
                continuous_const).aestronglyMeasurable (R + R) ?_
            refine MeasureTheory.ae_of_all _ (fun p => ?_)
            calc ‖s.m p.2 - y₀‖ ≤ ‖s.m p.2‖ + ‖y₀‖ := norm_sub_le _ _
              _ ≤ R + R := add_le_add (h_m_norm _) (hR _ hy₀_X)
          have h_split_smy₀ :
              ∫ p, (s.m p.2 - y₀) ∂ᾱ
                = ∫ p, (s.m p.2 - p.1) ∂ᾱ + ∫ p, (p.1 - y₀) ∂ᾱ := by
            rw [← MeasureTheory.integral_add h_int_bar h_sub_y₀_int_bar]
            congr 1
            funext p; abel
          have h_first_zero : ∫ p, (s.m p.2 - p.1) ∂ᾱ = 0 := by
            simpa only [univ_prod_univ, Measure.restrict_univ] using h_bar_int_univ_eq
          have h_second :
              ∫ p, (p.1 - y₀) ∂ᾱ = 0 := by
            rw [MeasureTheory.integral_sub h_id_int_bar h_const_int_bar]
            rw [MeasureTheory.integral_const]
            have h_pull : ∫ p, p.1 ∂ᾱ = ∫ z, z ∂α := by
              rw [← hbar_α_map_fst,
                  MeasureTheory.integral_map measurable_fst.aemeasurable
                    (f := fun z : EuclideanSpace ℝ (Fin n) => z)
                    continuous_id.aestronglyMeasurable]
            rw [h_pull, hα_mean]
            rw [MeasureTheory.measureReal_def, hbar_α_univ, sub_self]
          rw [h_omega_int, h_split_smy₀, h_first_zero, h_second, add_zero, smul_zero]
        · refine ((aestronglyMeasurable_indicator_iff hA_meas).mpr ?_)
          exact h_int_cont.aestronglyMeasurable.restrict
      rw [h_sub_eq, h_prod_eq, add_zero]
    · simp only [hrho'_toMeasure]
      haveI hbar_α_fin : MeasureTheory.IsFiniteMeasure ᾱ :=
        MeasureTheory.isFiniteMeasure_of_le _ hbar_α_le
      have h_fst_in_Sx :
          ∀ᵐ p ∂cell.rho.toMeasure, p.1 ∈ Sx s v S pi x₀ := by
        have h_supp_Sx :
            (ProbDist.map cell.rho Prod.fst measurable_fst).toMeasure.support
              ⊆ Sx s v S pi x₀ := cell.fst_support_subset_Sx
        have hSx_closed : IsClosed (Sx s v S pi x₀) := isClosed_closure
        have h_Sx_ae :
            (Sx s v S pi x₀) ∈ MeasureTheory.ae
              (ProbDist.map cell.rho Prod.fst measurable_fst).toMeasure := by
          rw [MeasureTheory.mem_ae_iff]
          have h_compl_sub :
              (Sx s v S pi x₀)ᶜ
                ⊆ ((ProbDist.map cell.rho Prod.fst measurable_fst).toMeasure.support)ᶜ :=
            Set.compl_subset_compl.mpr h_supp_Sx
          exact le_antisymm
            ((MeasureTheory.measure_mono h_compl_sub).trans_eq
              MeasureTheory.Measure.measure_compl_support) (zero_le)
        rw [MeasureTheory.mem_ae_iff, ProbDist.map_toMeasure,
            MeasureTheory.Measure.map_apply measurable_fst
              hSx_closed.measurableSet.compl] at h_Sx_ae
        rw [MeasureTheory.ae_iff]
        convert h_Sx_ae using 2
      have h_cell_contact :
          ∀ᵐ p ∂cell.rho.toMeasure, s.m p.2 ∈ Gamma_x s v S p.1 := by
        filter_upwards [cell.m_state_mem_cell, h_fst_in_Sx] with p hp_m hp_fst
        exact Gamma_x_subset_Gamma_of_mem_Sx s hv_diff hpi_M hS_sub
          hx₀_S hp_fst hp_m
      have h_sub_contact :
          ∀ᵐ p ∂(cell.rho.toMeasure - ᾱ), s.m p.2 ∈ Gamma_x s v S p.1 := by
        rw [MeasureTheory.ae_iff] at h_cell_contact ⊢
        have h_le := MeasureTheory.Measure.sub_le
          (μ := cell.rho.toMeasure) (ν := ᾱ)
          {p | ¬ s.m p.2 ∈ Gamma_x s v S p.1}
        rw [h_cell_contact] at h_le
        exact le_antisymm h_le (zero_le)
      have h_dirac_contact :
          ∀ᵐ p ∂((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω),
            s.m p.2 ∈ Gamma_x s v S p.1 := by
        have h_pre_closed_X : IsClosed (Prod.fst ⁻¹' s.X :
            Set (EuclideanSpace ℝ (Fin n) × Ω)) :=
          s.X_compact.isClosed.preimage continuous_fst
        have h_pre_ae_X : Prod.fst ⁻¹' s.X ∈ MeasureTheory.ae pi.toMeasure := by
          rw [MeasureTheory.mem_ae_iff]
          exact (MeasureTheory.prob_compl_eq_zero_iff
            h_pre_closed_X.measurableSet).mpr hpi_feas.fst_supportsOn
        have h_supp_pi_sub_pre :
            pi.toMeasure.support ⊆ Prod.fst ⁻¹' s.X :=
          MeasureTheory.Measure.support_subset_of_isClosed h_pre_closed_X h_pre_ae_X
        have hS_subX_loc : S ⊆ s.X := by
          rw [hpi_M.S_eq_support]
          rintro z ⟨p, hp_supp, rfl⟩
          exact h_supp_pi_sub_pre hp_supp
        have hx₀_active_loc : v x₀ = pStar v S x₀ := (hS_sub hx₀_S).2
        have hΓ_x₀_closed : IsClosed (Gamma_x s v S x₀) :=
          Gamma_x_isClosed s hv_diff hS_subX_loc hx₀_S hx₀_active_loc
        have h_cell_snd_inΓx₀ :
            ∀ᵐ ω ∂cell.rho.toMeasure.map Prod.snd,
              s.m ω ∈ Gamma_x s v S x₀ := by
          rw [MeasureTheory.ae_iff]
          have h_set_eq :
              {a : Ω | s.m a ∉ Gamma_x s v S x₀}
                = s.m ⁻¹' (Gamma_x s v S x₀)ᶜ := rfl
          rw [h_set_eq, MeasureTheory.Measure.map_apply measurable_snd
                (s.m_measurable hΓ_x₀_closed.measurableSet.compl)]
          have h_pre_eq :
              (Prod.snd ⁻¹' (s.m ⁻¹' (Gamma_x s v S x₀)ᶜ) :
                Set (EuclideanSpace ℝ (Fin n) × Ω))
              = {p : EuclideanSpace ℝ (Fin n) × Ω | ¬ s.m p.2 ∈
                Gamma_x s v S x₀} := rfl
          rw [h_pre_eq, ← MeasureTheory.ae_iff]
          exact cell.m_state_mem_cell
        have h_ᾱ_Ω_le_snd : ᾱ_Ω ≤ cell.rho.toMeasure.map Prod.snd := by
          rw [hᾱ_Ω_def]
          exact MeasureTheory.Measure.map_mono hbar_α_le measurable_snd
        have h_ᾱ_Ω_inΓx₀ :
            ∀ᵐ ω ∂ᾱ_Ω, s.m ω ∈ Gamma_x s v S x₀ := by
          rw [MeasureTheory.ae_iff] at h_cell_snd_inΓx₀ ⊢
          have h_mono := h_ᾱ_Ω_le_snd
            {ω | ¬ s.m ω ∈ Gamma_x s v S x₀}
          rw [h_cell_snd_inΓx₀] at h_mono
          exact le_antisymm h_mono (zero_le)
        have hΓ_chain : Gamma_x s v S x₀ ⊆ Gamma_x s v S y₀ :=
          Gamma_x_subset_Gamma_of_mem_Sx s hv_diff hpi_M hS_sub
            hx₀_S hy₀_Sx
        have h_ᾱ_Ω_inΓy₀ :
            ∀ᵐ ω ∂ᾱ_Ω, s.m ω ∈ Gamma_x s v S y₀ := by
          filter_upwards [h_ᾱ_Ω_inΓx₀] with ω hω
          exact hΓ_chain hω
        have hgraph_closed :
            IsClosed {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)
                | q.2 ∈ Gamma_x s v S q.1} :=
          Gamma_x_graph_isClosed s hv_diff S hpStar_cont
        have h_pre_cont :
            Continuous fun p : EuclideanSpace ℝ (Fin n) × Ω =>
                ((p.1, s.m p.2) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
          continuous_fst.prodMk (s.m_continuous.comp continuous_snd)
        have h_good_closed : IsClosed
            {p : EuclideanSpace ℝ (Fin n) × Ω | s.m p.2 ∈ Gamma_x s v S p.1} :=
          hgraph_closed.preimage h_pre_cont
        have hgood_meas :
            MeasurableSet {p : EuclideanSpace ℝ (Fin n) × Ω
                | s.m p.2 ∈ Gamma_x s v S p.1} :=
          h_good_closed.measurableSet
        rw [MeasureTheory.Measure.dirac_prod,
            MeasureTheory.ae_map_iff measurable_prodMk_left.aemeasurable hgood_meas]
        exact h_ᾱ_Ω_inΓy₀
      rw [MeasureTheory.ae_iff, MeasureTheory.Measure.add_apply]
      rw [MeasureTheory.ae_iff] at h_sub_contact h_dirac_contact
      rw [h_sub_contact, h_dirac_contact, add_zero]
  · simp only [hrho'_toMeasure]
    haveI hbar_α_fin : MeasureTheory.IsFiniteMeasure ᾱ :=
      MeasureTheory.isFiniteMeasure_of_le _ hbar_α_le
    haveI hα_fin : MeasureTheory.IsFiniteMeasure α :=
      MeasureTheory.isFiniteMeasure_of_le _ hα_le
    haveI hᾱ_Ω_fin : MeasureTheory.IsFiniteMeasure ᾱ_Ω := by
      rw [hᾱ_Ω_def]; exact MeasureTheory.Measure.isFiniteMeasure_map _ _
    obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x ∈ s.X, ‖x‖ ≤ R :=
      s.X_compact.isBounded.exists_norm_le
    have hR_nonneg : 0 ≤ R :=
      (norm_nonneg _).trans (hR _ (Sx_subset_X s v S pi x₀ hy₀_Sx))
    have h_ae_p1_X_cell : ∀ᵐ p ∂cell.rho.toMeasure, p.1 ∈ s.X := by
      rw [MeasureTheory.ae_iff]; exact h_fst_X_cell_rho_zero
    have h_ae_p1_X_bar : ∀ᵐ p ∂ᾱ, p.1 ∈ s.X := by
      have : ᾱ ((Prod.fst ⁻¹' s.X : Set _)ᶜ) = 0 :=
        le_antisymm ((hbar_α_le _).trans h_fst_X_cell_rho_zero.le) (zero_le)
      rw [MeasureTheory.ae_iff]; exact this
    have h_ae_z_X_α : ∀ᵐ z ∂α, z ∈ s.X := by
      rw [MeasureTheory.ae_iff]
      apply le_antisymm _ (zero_le)
      have h_supp_X : α ((s.X : Set (EuclideanSpace ℝ (Fin n)))ᶜ) = 0 :=
        le_antisymm
          ((MeasureTheory.measure_mono (Set.compl_subset_compl.mpr
              (Sx_subset_X s v S pi x₀))).trans hα_supp.le) (zero_le)
      exact h_supp_X.le
    have h_norm_sq_cont :
        Continuous fun p : EuclideanSpace ℝ (Fin n) × Ω => ‖p.1‖ ^ 2 :=
      (continuous_norm.comp continuous_fst).pow 2
    have h_norm_sq_z_cont : Continuous fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 :=
      continuous_norm.pow 2
    have h_id_cont : Continuous fun z : EuclideanSpace ℝ (Fin n) => z := continuous_id
    have h_norm_sub_sq_cont :
        Continuous fun z : EuclideanSpace ℝ (Fin n) => ‖z - y₀‖ ^ 2 :=
      ((continuous_id.sub continuous_const).norm).pow 2
    have h_norm_sq_int_cell :
        MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) × Ω => ‖p.1‖ ^ 2)
          cell.rho.toMeasure := by
      refine MeasureTheory.Integrable.of_bound h_norm_sq_cont.aestronglyMeasurable
        (R ^ 2) ?_
      filter_upwards [h_ae_p1_X_cell] with p hp
      have hnorm : ‖p.1‖ ≤ R := hR _ hp
      have : ‖‖p.1‖ ^ 2‖ = ‖p.1‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [this]
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have h_norm_sq_int_bar :
        MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) × Ω => ‖p.1‖ ^ 2)
          ᾱ := by
      refine MeasureTheory.Integrable.of_bound h_norm_sq_cont.aestronglyMeasurable
        (R ^ 2) ?_
      filter_upwards [h_ae_p1_X_bar] with p hp
      have hnorm : ‖p.1‖ ≤ R := hR _ hp
      have : ‖‖p.1‖ ^ 2‖ = ‖p.1‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [this]
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have h_norm_sq_int_α :
        MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2) α := by
      refine MeasureTheory.Integrable.of_bound h_norm_sq_z_cont.aestronglyMeasurable
        (R ^ 2) ?_
      filter_upwards [h_ae_z_X_α] with z hz
      have hnorm : ‖z‖ ≤ R := hR _ hz
      have : ‖‖z‖ ^ 2‖ = ‖z‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [this]
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have h_id_int_α : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin n) => z) α := by
      refine MeasureTheory.Integrable.of_bound h_id_cont.aestronglyMeasurable R ?_
      filter_upwards [h_ae_z_X_α] with z hz
      exact hR _ hz
    have h_norm_sub_sq_int_α :
        MeasureTheory.Integrable
          (fun z : EuclideanSpace ℝ (Fin n) => ‖z - y₀‖ ^ 2) α := by
      refine MeasureTheory.Integrable.of_bound h_norm_sub_sq_cont.aestronglyMeasurable
        ((R + R) ^ 2) ?_
      filter_upwards [h_ae_z_X_α] with z hz
      have hnorm : ‖z‖ ≤ R := hR _ hz
      have hy₀_norm : ‖y₀‖ ≤ R := hR _ (Sx_subset_X s v S pi x₀ hy₀_Sx)
      have : ‖z - y₀‖ ≤ R + R := by
        calc ‖z - y₀‖ ≤ ‖z‖ + ‖y₀‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add hnorm hy₀_norm
      have hpos : (0 : ℝ) ≤ ‖z - y₀‖ ^ 2 := by positivity
      have : ‖‖z - y₀‖ ^ 2‖ = ‖z - y₀‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hpos]
      rw [this]
      have hR2 : (0 : ℝ) ≤ R + R := by linarith
      exact pow_le_pow_left₀ (norm_nonneg _) ‹‖z - y₀‖ ≤ R + R› 2
    have h_variance_identity :
        ∫ z, ‖z - y₀‖ ^ 2 ∂α =
          (∫ z, ‖z‖ ^ 2 ∂α) - Mα.toReal * ‖y₀‖ ^ 2 := by
      have h_expand : ∀ z : EuclideanSpace ℝ (Fin n),
          ‖z - y₀‖ ^ 2 = ‖z‖ ^ 2 - 2 * inner ℝ z y₀ + ‖y₀‖ ^ 2 :=
        fun z => norm_sub_sq_real z y₀
      have h_inner_int :
          MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
            inner ℝ z y₀) α := by
        have h_inner_cont :
            Continuous fun z : EuclideanSpace ℝ (Fin n) => inner ℝ z y₀ := by
          exact (continuous_inner.comp (Continuous.prodMk continuous_id continuous_const))
        refine MeasureTheory.Integrable.of_bound h_inner_cont.aestronglyMeasurable
          (R * R) ?_
        filter_upwards [h_ae_z_X_α] with z hz
        have hz_norm : ‖z‖ ≤ R := hR _ hz
        have hy₀_norm : ‖y₀‖ ≤ R := hR _ (Sx_subset_X s v S pi x₀ hy₀_Sx)
        have h_inn_bd : |inner ℝ z y₀| ≤ ‖z‖ * ‖y₀‖ := abs_real_inner_le_norm _ _
        have : ‖inner ℝ z y₀‖ = |inner ℝ z y₀| := Real.norm_eq_abs _
        rw [this]
        exact h_inn_bd.trans (mul_le_mul hz_norm hy₀_norm (norm_nonneg _) hR_nonneg)
      have h_int_inner_eq :
          ∫ z, inner ℝ z y₀ ∂α = Mα.toReal * ‖y₀‖ ^ 2 := by
        have h_swap : ∀ z : EuclideanSpace ℝ (Fin n),
            inner ℝ z y₀ = inner ℝ y₀ z := fun z => real_inner_comm _ _
        calc ∫ z, inner ℝ z y₀ ∂α
            = ∫ z, inner ℝ y₀ z ∂α := by simp_rw [h_swap]
          _ = inner ℝ y₀ (∫ z, z ∂α) := integral_inner h_id_int_α y₀
          _ = inner ℝ y₀ (Mα.toReal • y₀) := by rw [hα_mean]
          _ = Mα.toReal * inner ℝ y₀ y₀ := by
              rw [real_inner_comm, real_inner_smul_left, real_inner_comm]
          _ = Mα.toReal * ‖y₀‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
      have h_int_const_eq :
          ∫ _ : EuclideanSpace ℝ (Fin n), ‖y₀‖ ^ 2 ∂α = Mα.toReal * ‖y₀‖ ^ 2 := by
        rw [MeasureTheory.integral_const, MeasureTheory.measureReal_def, ← hMα_def,
            smul_eq_mul]
      have h_int_mul_inner :
          ∫ z, 2 * inner ℝ z y₀ ∂α = 2 * (Mα.toReal * ‖y₀‖ ^ 2) := by
        rw [MeasureTheory.integral_const_mul, h_int_inner_eq]
      have h_int_2inner_integrable :
          MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
            2 * inner ℝ z y₀) α := h_inner_int.const_mul 2
      have h_int_diff :
          ∫ z, (‖z‖ ^ 2 - 2 * inner ℝ z y₀) ∂α
            = (∫ z, ‖z‖ ^ 2 ∂α) - 2 * (Mα.toReal * ‖y₀‖ ^ 2) := by
        rw [MeasureTheory.integral_sub h_norm_sq_int_α h_int_2inner_integrable,
            h_int_mul_inner]
      have h_int_diff_integrable :
          MeasureTheory.Integrable
            (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 - 2 * inner ℝ z y₀) α :=
        h_norm_sq_int_α.sub h_int_2inner_integrable
      calc ∫ z, ‖z - y₀‖ ^ 2 ∂α
          = ∫ z, (‖z‖ ^ 2 - 2 * inner ℝ z y₀ + ‖y₀‖ ^ 2) ∂α := by
            simp_rw [h_expand]
        _ = (∫ z, (‖z‖ ^ 2 - 2 * inner ℝ z y₀) ∂α)
              + ∫ _, ‖y₀‖ ^ 2 ∂α :=
            MeasureTheory.integral_add h_int_diff_integrable
              (MeasureTheory.integrable_const _)
        _ = ((∫ z, ‖z‖ ^ 2 ∂α) - 2 * (Mα.toReal * ‖y₀‖ ^ 2))
              + Mα.toReal * ‖y₀‖ ^ 2 := by rw [h_int_diff, h_int_const_eq]
        _ = (∫ z, ‖z‖ ^ 2 ∂α) - Mα.toReal * ‖y₀‖ ^ 2 := by ring
    have h_norm_sub_sq_nonneg :
        ∀ᵐ z ∂α, 0 ≤ ‖z - y₀‖ ^ 2 :=
      Filter.Eventually.of_forall (fun _ => by positivity)
    have h_Mα_pos : (0 : ENNReal) < Mα := by
      rw [hMα_def]
      exact (MeasureTheory.Measure.measure_univ_pos).mpr hα_ne
    have h_var_pos : 0 < ∫ z, ‖z - y₀‖ ^ 2 ∂α := by
      rw [(MeasureTheory.integral_pos_iff_support_of_nonneg_ae
        h_norm_sub_sq_nonneg h_norm_sub_sq_int_α)]
      have h_supp_eq : Function.support (fun z : EuclideanSpace ℝ (Fin n) =>
            ‖z - y₀‖ ^ 2) = {y₀}ᶜ := by
        ext z
        simp only [Function.mem_support, Set.mem_compl_iff, Set.mem_singleton_iff]
        constructor
        · intro hne hz; apply hne; subst hz; simp
        · intro hne
          have : ‖z - y₀‖ ≠ 0 := by
            rw [norm_ne_zero_iff, sub_ne_zero]; exact hne
          exact pow_ne_zero 2 this
      rw [h_supp_eq]
      have h_compl : α ({y₀}ᶜ) = Mα := by
        have h_meas_y0 : MeasurableSet ({y₀} : Set (EuclideanSpace ℝ (Fin n))) :=
          measurableSet_singleton y₀
        have h_split2 : α {y₀} + α ({y₀}ᶜ) = α Set.univ :=
          MeasureTheory.measure_add_measure_compl h_meas_y0
        rw [hα_atom, zero_add] at h_split2
        rw [h_split2, hMα_def]
      rw [h_compl]; exact h_Mα_pos
    have h_strict_α :
        Mα.toReal * ‖y₀‖ ^ 2 < ∫ z, ‖z‖ ^ 2 ∂α := by
      linarith [h_var_pos, h_variance_identity]
    have h_marginal :
        ∫ p, ‖p.1‖ ^ 2 ∂ᾱ = ∫ z, ‖z‖ ^ 2 ∂α := by
      have h_step :
          ∫ p, ‖p.1‖ ^ 2 ∂ᾱ = ∫ z, ‖z‖ ^ 2 ∂(ᾱ.map Prod.fst) := by
        rw [MeasureTheory.integral_map measurable_fst.aemeasurable]
        exact h_norm_sq_z_cont.aestronglyMeasurable
      rw [h_step, hbar_α_map_fst]
    have h_dirac_prod_int :
        ∫ p, ‖p.1‖ ^ 2 ∂((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω)
          = Mα.toReal * ‖y₀‖ ^ 2 := by
      rw [MeasureTheory.Measure.dirac_prod,
          MeasureTheory.integral_map (φ := Prod.mk y₀)
            measurable_prodMk_left.aemeasurable
            h_norm_sq_cont.aestronglyMeasurable]
      simp only
      rw [MeasureTheory.integral_const, MeasureTheory.measureReal_def,
          hbar_α_Ω_univ, smul_eq_mul, mul_comm]
    have h_sub_eq : cell.rho.toMeasure - ᾱ + ᾱ = cell.rho.toMeasure :=
      MeasureTheory.Measure.sub_add_cancel_of_le hbar_α_le
    have h_norm_sq_int_sub :
        MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) × Ω => ‖p.1‖ ^ 2)
          (cell.rho.toMeasure - ᾱ) :=
      MeasureTheory.Integrable.mono_measure h_norm_sq_int_cell
        (MeasureTheory.Measure.sub_le)
    have h_int_sub_eq :
        ∫ p, ‖p.1‖ ^ 2 ∂(cell.rho.toMeasure - ᾱ)
          = (∫ p, ‖p.1‖ ^ 2 ∂cell.rho.toMeasure) - ∫ p, ‖p.1‖ ^ 2 ∂ᾱ := by
      have hsum := MeasureTheory.integral_add_measure h_norm_sq_int_sub h_norm_sq_int_bar
      rw [h_sub_eq] at hsum
      linarith
    have h_norm_sq_int_dirac :
        MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin n) × Ω => ‖p.1‖ ^ 2)
          ((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω) := by
      rw [MeasureTheory.Measure.dirac_prod]
      refine (MeasureTheory.integrable_map_measure
        h_norm_sq_cont.aestronglyMeasurable
        measurable_prodMk_left.aemeasurable).mpr ?_
      exact (MeasureTheory.integrable_const (‖y₀‖ ^ 2) : MeasureTheory.Integrable
        (fun _ : Ω => ‖y₀‖ ^ 2) ᾱ_Ω)
    have h_int_μtilde :
        ∫ p, ‖p.1‖ ^ 2 ∂μtilde
          = (∫ p, ‖p.1‖ ^ 2 ∂(cell.rho.toMeasure - ᾱ))
            + ∫ p, ‖p.1‖ ^ 2 ∂((MeasureTheory.Measure.dirac y₀).prod ᾱ_Ω) := by
      rw [hμtilde_def]
      exact MeasureTheory.integral_add_measure h_norm_sq_int_sub h_norm_sq_int_dirac
    rw [h_int_μtilde, h_int_sub_eq, h_dirac_prod_int, h_marginal]
    linarith

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
