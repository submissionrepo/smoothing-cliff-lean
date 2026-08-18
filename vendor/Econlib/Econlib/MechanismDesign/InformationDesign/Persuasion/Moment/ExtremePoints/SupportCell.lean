/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.ContactFibre

/-!
# Support cell `S_x`

Defines the support-cell set `Sx s v S pi x := cl(supp(π_X) ∩ relint(Γ_x))` and establishes its
basic properties.

## Main definitions

* `Sx`: The support-cell set `cl(supp(π_X) ∩ relint(Γ_x))`.

## Main statements

* `Sx_subset_X`: `Sx` is contained in `s.X`.
* `Sx_isCompact`: `Sx` is compact.
* `Sx_subset_support_piX`: `Sx` is contained in `supp(π_X)`.
* `pos_piX_of_mem_Sx`: Every open neighborhood of a point of `Sx` has positive `π_X`-mass.
* `Gamma_x_subset_Gamma_of_mem_Sx`: If `y ∈ Sx_{x₀}`, then `Γ_{x₀} ⊆ Γ_y`.
* `Gamma_cell_subset_Gamma_of_mem_Sx`: If `y ∈ Sx_{x₀}`, then `closure (relint Γ_{x₀}) ⊆ Γ_y`.

## Tags

persuasion, moment persuasion, extreme points, support cell
-/

@[expose] public section

open MeasureTheory Set Real
open scoped NNReal Topology ProbabilityTheory

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
variable {n : ℕ}

/-! ## Support cell -/

/-- The support-cell set `S_x := cl(supp(π_X) ∩ relint(Γ_x))`.  The relative interior is rendered
as Mathlib's `intrinsicInterior ℝ`. -/
noncomputable def Sx (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    (x : EuclideanSpace ℝ (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  closure ((ProbDist.map pi Prod.fst measurable_fst).toMeasure.support
    ∩ intrinsicInterior ℝ (Gamma_x s v S x))

/-- `Sx` is contained in `s.X`. -/
lemma Sx_subset_X (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    (x : EuclideanSpace ℝ (Fin n)) :
    Sx s v S pi x ⊆ s.X := by
  have h_inner_sub :
      ((ProbDist.map pi Prod.fst measurable_fst).toMeasure.support
        ∩ intrinsicInterior ℝ (Gamma_x s v S x)) ⊆ s.X := by
    rintro y ⟨_, hy_relint⟩
    exact Gamma_x_subset_X s v S x (intrinsicInterior_subset hy_relint)
  calc Sx s v S pi x ⊆ closure s.X :=
        closure_mono h_inner_sub
    _ = s.X := s.X_compact.isClosed.closure_eq

/-- `Sx` is compact (closed subset of compact `s.X`). -/
lemma Sx_isCompact (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    (x : EuclideanSpace ℝ (Fin n)) :
    IsCompact (Sx s v S pi x) :=
  s.X_compact.of_isClosed_subset isClosed_closure (Sx_subset_X s v S pi x)

/-- `Sx s v S pi x ⊆ supp(π_X)`. -/
lemma Sx_subset_support_piX (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    (x : EuclideanSpace ℝ (Fin n)) :
    Sx s v S pi x ⊆
      (ProbDist.map pi Prod.fst measurable_fst).toMeasure.support := by
  have h_inter_sub :
      ((ProbDist.map pi Prod.fst measurable_fst).toMeasure.support
        ∩ intrinsicInterior ℝ (Gamma_x s v S x))
      ⊆ (ProbDist.map pi Prod.fst measurable_fst).toMeasure.support :=
    Set.inter_subset_left
  calc Sx s v S pi x
      ⊆ closure (ProbDist.map pi Prod.fst measurable_fst).toMeasure.support :=
        closure_mono h_inter_sub
    _ = (ProbDist.map pi Prod.fst measurable_fst).toMeasure.support :=
        MeasureTheory.Measure.isClosed_support.closure_eq

/-- Every open neighborhood of a point of `Sx` has positive `π_X`-mass. -/
lemma pos_piX_of_mem_Sx
    (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    (x : EuclideanSpace ℝ (Fin n))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Sx s v S pi x)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : U ∈ nhds y) :
    0 < (ProbDist.map pi Prod.fst measurable_fst).toMeasure U := by
  have hy_supp : y ∈
      (ProbDist.map pi Prod.fst measurable_fst).toMeasure.support :=
    Sx_subset_support_piX s v S pi x hy
  exact (MeasureTheory.Measure.mem_support_iff_forall y).mp hy_supp U hU

/-- Every open ball around a point of `Sx` has positive `π_X`-mass. -/
lemma pos_piX_ball_of_mem_Sx
    (s : MomentSetup Ω n)
    (v : EuclideanSpace ℝ (Fin n) → ℝ)
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    (x : EuclideanSpace ℝ (Fin n))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ Sx s v S pi x)
    {δ : ℝ} (hδ : 0 < δ) :
    0 < (ProbDist.map pi Prod.fst measurable_fst).toMeasure
          (Metric.ball y δ) :=
  pos_piX_of_mem_Sx s v S pi x hy (Metric.ball_mem_nhds y hδ)

variable [CompactSpace Ω] [SecondCountableTopology Ω]

/-- If `y ∈ Sx s v S pi x₀`, then `Gamma_x s v S x₀ ⊆ Gamma_x s v S y`. -/
lemma Gamma_x_subset_Gamma_of_mem_Sx
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hv_diff : ContDiff ℝ 1 v)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hpi_M : ConditionM s v pi S)
    (hS_sub : S ⊆ S_star s v S)
    {x₀ y : EuclideanSpace ℝ (Fin n)}
    (hx₀_S : x₀ ∈ S)
    (hy : y ∈ Sx s v S pi x₀) :
    Gamma_x s v S x₀ ⊆ Gamma_x s v S y := by
  have hπ_feas : IsFeasibleJoint s pi := hpi_M.feasible
  have hX_closed : IsClosed (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
    s.X_compact.isClosed
  have h_pre_closed : IsClosed
      (Prod.fst ⁻¹' s.X : Set (EuclideanSpace ℝ (Fin n) × Ω)) :=
    hX_closed.preimage continuous_fst
  have h_pre_meas : MeasurableSet
      (Prod.fst ⁻¹' s.X : Set (EuclideanSpace ℝ (Fin n) × Ω)) :=
    h_pre_closed.measurableSet
  have h_pre_ae : Prod.fst ⁻¹' s.X ∈ MeasureTheory.ae pi.toMeasure := by
    rw [MeasureTheory.mem_ae_iff]
    exact (MeasureTheory.prob_compl_eq_zero_iff h_pre_meas).mpr hπ_feas.fst_supportsOn
  have h_supp_pi_sub_pre :
      pi.toMeasure.support ⊆ Prod.fst ⁻¹' s.X :=
    MeasureTheory.Measure.support_subset_of_isClosed h_pre_closed h_pre_ae
  have hS_subX : S ⊆ s.X := by
    rw [hpi_M.S_eq_support]
    rintro z ⟨p, hp_supp, rfl⟩
    exact h_supp_pi_sub_pre hp_supp
  have hx₀_active : v x₀ = pStar v S x₀ := (hS_sub hx₀_S).2
  have hfderiv_cont : Continuous (fderiv ℝ v) :=
    hv_diff.continuous_fderiv one_ne_zero
  have hfderiv_norm_cont :
      Continuous (fun y : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ v y‖) :=
    continuous_norm.comp hfderiv_cont
  obtain ⟨L₀, hL_nn, hL_bd⟩ :
      ∃ L₀ : ℝ, 0 ≤ L₀ ∧ ∀ x ∈ s.X, ‖fderiv ℝ v x‖ ≤ L₀ := by
    have h_image_cpt : IsCompact
        ((fun x : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ v x‖) '' s.X) :=
      s.X_compact.image hfderiv_norm_cont
    obtain ⟨L₀, hL₀⟩ := h_image_cpt.bddAbove
    refine ⟨max L₀ 0, le_max_right _ _, fun x hx => ?_⟩
    have h_in : ‖fderiv ℝ v x‖ ∈
        (fun x : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ v x‖) '' s.X :=
      ⟨x, hx, rfl⟩
    exact le_max_of_le_left (hL₀ h_in)
  set L : NNReal := ⟨L₀, hL_nn⟩ with hL_def
  have hL_on_S : ∀ x ∈ S, ‖fderiv ℝ v x‖ ≤ (L : ℝ) :=
    fun x hx => hL_bd x (hS_subX hx)
  have h_pStar_lip : LipschitzWith L (pStar v S) :=
    pStar_lipschitzWith s hv_diff hS_subX hL_on_S
  have h_pStar_cont : Continuous (pStar v S) := h_pStar_lip.continuous
  have h_XΩ_cpt : IsCompact
      (s.X ×ˢ (Set.univ : Set Ω) :
        Set (EuclideanSpace ℝ (Fin n) × Ω)) :=
    s.X_compact.prod CompactSpace.isCompact_univ
  have h_supp_pi_in_XΩ :
      pi.toMeasure.support ⊆ s.X ×ˢ (Set.univ : Set Ω) :=
    fun p hp => ⟨h_supp_pi_sub_pre hp, Set.mem_univ _⟩
  have h_supp_pi_cpt : IsCompact pi.toMeasure.support :=
    h_XΩ_cpt.of_isClosed_subset MeasureTheory.Measure.isClosed_support
      h_supp_pi_in_XΩ
  have h_S_eq : S = Prod.fst '' pi.toMeasure.support := hpi_M.S_eq_support
  have h_S_cpt : IsCompact S :=
    h_S_eq ▸ h_supp_pi_cpt.image continuous_fst
  have h_S_closed : IsClosed S := h_S_cpt.isClosed
  have h_S_meas : MeasurableSet S := h_S_closed.measurableSet
  have h_supp_pi_in_pre_S :
      pi.toMeasure.support ⊆ Prod.fst ⁻¹' S := by
    intro p hp; exact h_S_eq ▸ ⟨p, hp, rfl⟩
  -- `Prod.fst ⁻¹' S` contains the support, which is itself a.e.
  have h_pre_S_ae : Prod.fst ⁻¹' S ∈ MeasureTheory.ae pi.toMeasure :=
    Filter.mem_of_superset MeasureTheory.Measure.support_mem_ae h_supp_pi_in_pre_S
  have h_πX_S_ae :
      S ∈ MeasureTheory.ae (ProbDist.map pi Prod.fst measurable_fst).toMeasure :=
    (MeasureTheory.mem_ae_map_iff measurable_fst.aemeasurable h_S_meas).mpr h_pre_S_ae
  have h_πX_supp_sub_S :
      (ProbDist.map pi Prod.fst measurable_fst).toMeasure.support ⊆ S :=
    MeasureTheory.Measure.support_subset_of_isClosed h_S_closed h_πX_S_ae
  intro ω hω_in_Γ_x₀
  have hy_closure :
      y ∈ closure
        ((ProbDist.map pi Prod.fst measurable_fst).toMeasure.support
          ∩ intrinsicInterior ℝ (Gamma_x s v S x₀)) := hy
  rw [mem_closure_iff_seq_limit] at hy_closure
  obtain ⟨z, hz_mem, hz_tendsto⟩ := hy_closure
  have hz_S : ∀ k, z k ∈ S := fun k => h_πX_supp_sub_S (hz_mem k).1
  have hz_active : ∀ k, v (z k) = pStar v S (z k) :=
    fun k => (hS_sub (hz_S k)).2
  have hz_relint : ∀ k, z k ∈ intrinsicInterior ℝ (Gamma_x s v S x₀) :=
    fun k => (hz_mem k).2
  have hz_Γ_self : ∀ k, z k ∈ Gamma_x s v S (z k) := fun k => by
    obtain ⟨_, _, h_self, _⟩ :=
      Gamma_x_isCompact_isConvex_mem_argMin s hv_diff hS_subX (hz_S k) (hz_active k)
    exact h_self
  have h_Γ_sub : ∀ k, Gamma_x s v S x₀ ⊆ Gamma_x s v S (z k) := fun k =>
    Gamma_x_subset_of_intrinsicInterior_inter_nonempty s hv_diff hS_subX
      hx₀_S (hz_S k) hx₀_active (hz_active k)
      ⟨z k, hz_relint k, hz_Γ_self k⟩
  have hω_in_Γ_zk : ∀ k, ω ∈ Gamma_x s v S (z k) :=
    fun k => h_Γ_sub k hω_in_Γ_x₀
  have h_graph_closed : IsClosed
      {p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
          p.2 ∈ Gamma_x s v S p.1} :=
    Gamma_x_graph_isClosed s hv_diff S h_pStar_cont
  have h_pair_tendsto :
      Filter.Tendsto (fun k => (z k, ω)) Filter.atTop (nhds (y, ω)) :=
    hz_tendsto.prodMk_nhds tendsto_const_nhds
  exact h_graph_closed.mem_of_tendsto h_pair_tendsto
    (Filter.Eventually.of_forall hω_in_Γ_zk)

/-- For every `y ∈ Sx_{x₀}`, `closure (intrinsicInterior Γ_{x₀}) ⊆ Γ_y`. -/
lemma Gamma_cell_subset_Gamma_of_mem_Sx
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hv_diff : ContDiff ℝ 1 v)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hpi_M : ConditionM s v pi S)
    (hS_sub : S ⊆ S_star s v S)
    {x₀ y : EuclideanSpace ℝ (Fin n)}
    (hx₀_S : x₀ ∈ S)
    (hy : y ∈ Sx s v S pi x₀) :
    closure (intrinsicInterior ℝ (Gamma_x s v S x₀)) ⊆ Gamma_x s v S y := by
  have hπ_feas : IsFeasibleJoint s pi := hpi_M.feasible
  have h_pre_closed : IsClosed (Prod.fst ⁻¹' s.X :
      Set (EuclideanSpace ℝ (Fin n) × Ω)) :=
    s.X_compact.isClosed.preimage continuous_fst
  have h_pre_meas : MeasurableSet (Prod.fst ⁻¹' s.X :
      Set (EuclideanSpace ℝ (Fin n) × Ω)) :=
    h_pre_closed.measurableSet
  have h_pre_ae : Prod.fst ⁻¹' s.X ∈ MeasureTheory.ae pi.toMeasure := by
    rw [MeasureTheory.mem_ae_iff]
    exact (MeasureTheory.prob_compl_eq_zero_iff h_pre_meas).mpr hπ_feas.fst_supportsOn
  have h_supp_pi_sub_pre :
      pi.toMeasure.support ⊆ Prod.fst ⁻¹' s.X :=
    MeasureTheory.Measure.support_subset_of_isClosed h_pre_closed h_pre_ae
  have hS_subX : S ⊆ s.X := by
    rw [hpi_M.S_eq_support]
    rintro z ⟨p, hp_supp, rfl⟩
    exact h_supp_pi_sub_pre hp_supp
  have hx₀_active : v x₀ = pStar v S x₀ := (hS_sub hx₀_S).2
  have h_Γ_x₀_closed : IsClosed (Gamma_x s v S x₀) :=
    Gamma_x_isClosed s hv_diff hS_subX hx₀_S hx₀_active
  intro ω hω_closure
  have hω_in_Γ_x₀ : ω ∈ Gamma_x s v S x₀ :=
    closure_minimal intrinsicInterior_subset h_Γ_x₀_closed hω_closure
  exact Gamma_x_subset_Gamma_of_mem_Sx s hv_diff hpi_M hS_sub hx₀_S hy
    hω_in_Γ_x₀

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
