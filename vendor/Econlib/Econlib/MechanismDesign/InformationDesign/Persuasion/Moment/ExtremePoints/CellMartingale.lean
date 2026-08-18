/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.CellDisintegration
public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.ContactSupportPrimal
public import Econlib.Probability.ProbDist.Borel

/-!
# Per-cell properties of `cellRho`

This file establishes three families of almost-everywhere properties for the cell-conditional
measure `cellRho`: Support containment, gradient consistency, and the local martingale identity
`∫ (s.m p.2 - p.1) ∂(cellRho pi x₀) = 0`.

## Main statements

* `cellRho_m_state_mem_cell_ae`: For `π_X`-a.e. `x₀`, the state image lies in `Γ_{x₀}` for
  `cellRho`-a.e. points.
* `cellRho_local_martingale_at_set_ae`: For each measurable `A`, the vector martingale identity
  holds `π_X`-a.e.
* `cellRho_local_martingale_ae`: The universal-quantifier-inside form of the martingale identity
  holds `π_X`-a.e.

## Tags

persuasion, moment persuasion, extreme points, martingale
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

/-! #### Per-cell properties of `cellRho` -/

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- For any measurable predicate `Q` that holds `pi`-a.e., it holds `cellRho pi x₀`-a.e. for
`π_X`-a.e. `x₀`. -/
private lemma cellRho_ae_of_pi_ae [Nonempty Ω]
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω))
    {Q : EuclideanSpace ℝ (Fin n) × Ω → Prop} (hQ_meas : MeasurableSet {p | Q p})
    (hπQ : ∀ᵐ p ∂pi.toMeasure, Q p) :
    ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
      ∀ᵐ p ∂(cellRho pi x₀ (v := v)).toMeasure, Q p := by
  set bad : Set (EuclideanSpace ℝ (Fin n) × Ω) := {p | ¬ Q p}
  have hbad_meas : MeasurableSet bad := hQ_meas.compl
  have hbad_pi_zero : pi.toMeasure bad = 0 := by
    rwa [MeasureTheory.ae_iff] at hπQ
  set D := cellDisintegration (v := v) pi with hD_def
  have h_meas_int :
      Measurable fun α : Quotient (cellEquiv v) => D.μα α bad :=
    D.measurable_apply hbad_meas
  have hd :
      pi.toMeasure bad =
        ∫⁻ α, D.μα α bad ∂(pi.toMeasure.map
          (Quotient.mk'' : _ → Quotient (cellEquiv v))) := by
    have h := D.apply_eq_setLIntegral hbad_meas MeasurableSet.univ
    rw [Set.preimage_univ, Set.inter_univ,
        MeasureTheory.setLIntegral_univ] at h
    exact h
  rw [hbad_pi_zero] at hd
  have h_ae_zero :
      ∀ᵐ α ∂(pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v))),
        D.μα α bad = 0 :=
    (MeasureTheory.lintegral_eq_zero_iff h_meas_int).mp hd.symm
  let qfst : EuclideanSpace ℝ (Fin n) → Quotient (cellEquiv v) :=
    fun x => Quotient.mk'' (x, Classical.arbitrary Ω)
  have h_factor : ∀ p : EuclideanSpace ℝ (Fin n) × Ω,
      (Quotient.mk'' p : Quotient (cellEquiv v)) = qfst p.1 := by
    intro p
    apply Quotient.sound
    rfl
  have h_qfst_meas : Measurable qfst :=
    measurable_quotient_mk''.comp (measurable_id.prodMk measurable_const)
  have h_map_eq :
      pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v))
        = (pi.toMeasure.map Prod.fst).map qfst := by
    rw [MeasureTheory.Measure.map_map h_qfst_meas measurable_fst]
    congr 1
    funext p
    exact h_factor p
  have h_πX :
      pi.toMeasure.map Prod.fst
        = (ProbDist.map pi Prod.fst measurable_fst).toMeasure := by
    rw [ProbDist.map_toMeasure]
  rw [h_map_eq, h_πX] at h_ae_zero
  have h_set_meas :
      MeasurableSet {α : Quotient (cellEquiv v) | D.μα α bad = 0} :=
    h_meas_int (measurableSet_singleton 0)
  rw [MeasureTheory.ae_map_iff h_qfst_meas.aemeasurable h_set_meas] at h_ae_zero
  filter_upwards [h_ae_zero] with x₀ hx₀
  rw [MeasureTheory.ae_iff]
  exact hx₀

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- For `π_X`-a.e. `x₀`, the gradient `fderiv ℝ v p.1` is `cellRho pi x₀`-a.e. equal to
`fderiv ℝ v x₀`. -/
private lemma cellRho_strong_consistency_ae [Nonempty Ω]
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_diff : ContDiff ℝ 1 v)
    (pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)) :
    ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
      ∀ᵐ p ∂(cellRho pi x₀ (v := v)).toMeasure,
        fderiv ℝ v p.1 = fderiv ℝ v x₀ := by
  set D := cellDisintegration (v := v) pi with hD_def
  have hsc :
      ∀ᵐ α ∂(pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v))),
        D.μα α {p | (Quotient.mk'' p : Quotient (cellEquiv v)) ≠ α} = 0 :=
    cellDisintegration_isStronglyConsistent hv_diff pi
  let qfst : EuclideanSpace ℝ (Fin n) → Quotient (cellEquiv v) :=
    fun x => Quotient.mk'' (x, Classical.arbitrary Ω)
  have h_factor : ∀ p : EuclideanSpace ℝ (Fin n) × Ω,
      (Quotient.mk'' p : Quotient (cellEquiv v)) = qfst p.1 := by
    intro p
    apply Quotient.sound
    rfl
  have h_qfst_meas : Measurable qfst :=
    measurable_quotient_mk''.comp (measurable_id.prodMk measurable_const)
  have h_map_eq :
      pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v))
        = (pi.toMeasure.map Prod.fst).map qfst := by
    rw [MeasureTheory.Measure.map_map h_qfst_meas measurable_fst]
    congr 1
    funext p
    exact h_factor p
  have h_πX :
      pi.toMeasure.map Prod.fst
        = (ProbDist.map pi Prod.fst measurable_fst).toMeasure := by
    rw [ProbDist.map_toMeasure]
  rw [h_map_eq, h_πX] at hsc
  have hsc' :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        D.μα (qfst x₀)
            {p | (Quotient.mk'' p : Quotient (cellEquiv v)) ≠ qfst x₀} = 0 :=
    MeasureTheory.ae_of_ae_map h_qfst_meas.aemeasurable hsc
  filter_upwards [hsc'] with x₀ hx₀
  rw [MeasureTheory.ae_iff]
  have h_set_eq :
      {p : EuclideanSpace ℝ (Fin n) × Ω | ¬ fderiv ℝ v p.1 = fderiv ℝ v x₀}
        = {p | (Quotient.mk'' p : Quotient (cellEquiv v)) ≠ qfst x₀} := by
    ext p
    simp only [Set.mem_setOf_eq, ne_eq]
    refine ⟨?_, ?_⟩
    · intro h_grad_ne h_quot_eq
      apply h_grad_ne
      exact Quotient.exact h_quot_eq
    · intro h_quot_ne h_grad_eq
      apply h_quot_ne
      exact Quotient.sound (show fderiv ℝ v p.1 = fderiv ℝ v x₀ from h_grad_eq)
  rw [h_set_eq]
  exact hx₀

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- For `π_X`-a.e. `x₀`, the state image `s.m p.2` lies in `Γ_{x₀}` for `cellRho`-a.e. `(x, ω)`. -/
lemma cellRho_m_state_mem_cell_ae [Nonempty Ω]
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hv_diff : ContDiff ℝ 1 v)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hpi_M : ConditionM s v pi S)
    (hS_sub : S ⊆ S_star s v S) :
    ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
      ∀ᵐ p ∂(cellRho pi x₀ (v := v)).toMeasure,
        s.m p.2 ∈ Gamma_x s v S x₀ := by
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
  have hS_meas : MeasurableSet S := by
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
    exact (h_S_eq ▸ h_supp_pi_cpt.image continuous_fst).isClosed.measurableSet
  have h_fst_in_S_pi : ∀ᵐ p ∂pi.toMeasure, p.1 ∈ S := by
    have h_supp_sub : pi.toMeasure.support ⊆ Prod.fst ⁻¹' S := by
      intro p hp
      rw [hpi_M.S_eq_support]
      exact ⟨p, hp, rfl⟩
    rw [MeasureTheory.ae_iff]
    have h_subset : (Prod.fst ⁻¹' S)ᶜ ⊆ pi.toMeasure.supportᶜ :=
      Set.compl_subset_compl.mpr h_supp_sub
    have h_compl_zero : pi.toMeasure pi.toMeasure.supportᶜ = 0 :=
      MeasureTheory.Measure.measure_compl_support
    exact le_antisymm
      ((MeasureTheory.measure_mono h_subset).trans_eq h_compl_zero) (zero_le)
  have h_active_pi : ∀ᵐ p ∂pi.toMeasure, v p.1 = pStar v S p.1 := by
    filter_upwards [h_fst_in_S_pi] with p hp
    exact (hS_sub hp).2
  have h_gamma_pi : ∀ᵐ p ∂pi.toMeasure, s.m p.2 ∈ Gamma_x s v S p.1 :=
    optimal_pi_Gamma_x_ae s hpi_M
  have hS_meas_set : MeasurableSet {p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ S} :=
    measurable_fst hS_meas
  -- `pStar v S` is continuous: a Lipschitz bound from the compact fderiv-norm on `s.X`.
  have h_pStar_cont : Continuous (pStar v S) := by
    have hfderiv_norm_cont :
        Continuous (fun y : EuclideanSpace ℝ (Fin n) => ‖fderiv ℝ v y‖) :=
      continuous_norm.comp (hv_diff.continuous_fderiv one_ne_zero)
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
    set L : NNReal := ⟨L₀, hL_nn⟩
    have hL_on_S : ∀ x ∈ S, ‖fderiv ℝ v x‖ ≤ (L : ℝ) :=
      fun x hx => hL_bd x (hS_subX hx)
    exact (pStar_lipschitzWith (L := L) s hv_diff hS_subX hL_on_S).continuous
  have h_active_meas_set :
      MeasurableSet {p : EuclideanSpace ℝ (Fin n) × Ω | v p.1 = pStar v S p.1} := by
    have h_v_fst : Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) :=
      hv_diff.continuous.measurable.comp measurable_fst
    have h_pStar_fst : Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => pStar v S p.1) :=
      h_pStar_cont.measurable.comp measurable_fst
    exact measurableSet_eq_fun h_v_fst h_pStar_fst
  have h_gamma_meas_set :
      MeasurableSet {p : EuclideanSpace ℝ (Fin n) × Ω | s.m p.2 ∈ Gamma_x s v S p.1} := by
    have h_graph_closed : IsClosed
        {q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
            q.2 ∈ Gamma_x s v S q.1} :=
      Gamma_x_graph_isClosed s hv_diff S h_pStar_cont
    have h_pair_meas :
        Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
          ((p.1, s.m p.2) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) :=
      measurable_fst.prodMk (s.m_measurable.comp measurable_snd)
    exact h_pair_meas h_graph_closed.measurableSet
  have h_fst_in_S_cell :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        ∀ᵐ p ∂(cellRho pi x₀ (v := v)).toMeasure, p.1 ∈ S :=
    cellRho_ae_of_pi_ae pi hS_meas_set h_fst_in_S_pi
  have h_active_cell :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        ∀ᵐ p ∂(cellRho pi x₀ (v := v)).toMeasure, v p.1 = pStar v S p.1 :=
    cellRho_ae_of_pi_ae pi h_active_meas_set h_active_pi
  have h_gamma_cell :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        ∀ᵐ p ∂(cellRho pi x₀ (v := v)).toMeasure,
          s.m p.2 ∈ Gamma_x s v S p.1 :=
    cellRho_ae_of_pi_ae pi h_gamma_meas_set h_gamma_pi
  have h_grad_cell := cellRho_strong_consistency_ae hv_diff pi
  have h_πX_x0_S :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure, x₀ ∈ S := by
    rw [ProbDist.map_toMeasure]
    exact (MeasureTheory.mem_ae_map_iff measurable_fst.aemeasurable hS_meas).mpr
      h_fst_in_S_pi
  have h_πX_x0_active :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        v x₀ = pStar v S x₀ := by
    filter_upwards [h_πX_x0_S] with x₀ hx₀
    exact (hS_sub hx₀).2
  filter_upwards [h_fst_in_S_cell, h_active_cell, h_gamma_cell, h_grad_cell,
                  h_πX_x0_S, h_πX_x0_active]
    with x₀ h_fst h_active h_gamma h_grad hx₀_S hx₀_active
  filter_upwards [h_fst, h_active, h_gamma, h_grad]
    with p hp_S hp_active hp_gamma hp_grad
  have h_Γ_eq :
      Gamma_x s v S p.1 = Gamma_x s v S x₀ :=
    Gamma_x_eq_of_fderiv_eq s hv_diff hS_subX hp_S hx₀_S hp_active hx₀_active hp_grad
  rw [← h_Γ_eq]
  exact hp_gamma

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- For each measurable `A ⊆ ℝⁿ` and each coordinate `i`, the scalar set martingale identity holds
`π_X`-a.e. on the cell-conditional measure:
`∫ p in A ×ˢ univ, (s.m p.2 i − p.1 i) ∂(cellRho pi x₀) = 0`. -/
private lemma cellRho_local_martingale_at_set_coord_ae [Nonempty Ω]
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi : pi ∈ feasibleJoint s)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (i : Fin n) :
    ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
      ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 i - p.1 i)
        ∂(cellRho pi x₀ (v := v)).toMeasure = 0 := by
  letI : Setoid (EuclideanSpace ℝ (Fin n) × Ω) := cellEquiv v
  have hπ_feas : IsFeasibleJoint s pi := hpi
  set D := cellDisintegration (v := v) pi with hD_def
  set μ : Measure (Quotient (cellEquiv (Ω := Ω) v)) :=
    pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v)) with hμ_def
  set κ : ProbabilityTheory.Kernel (Quotient (cellEquiv (Ω := Ω) v))
      (EuclideanSpace ℝ (Fin n) × Ω) :=
    MeasureTheory.baseKernel pi.toMeasure (cellEquiv v) with hκ_def
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  have hR_nn : 0 ≤ R := by
    rcases s.X_interior.mono interior_subset with ⟨x_int, hx_int⟩
    exact le_trans (norm_nonneg _) (hR _ hx_int)
  have h_proj : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) :=
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))
  have h_k_meas : Measurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 i - p.1 i) :=
    ((h_proj.measurable.comp s.m_continuous.measurable).comp measurable_snd).sub
      (h_proj.measurable.comp measurable_fst)
  have h_X_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
    s.X_compact.isClosed.measurableSet
  have h_fst_meas : MeasurableSet
      ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
    h_X_meas.preimage measurable_fst
  have h_ae_p1 : ∀ᵐ p ∂pi.toMeasure, p.1 ∈ s.X := by
    rw [MeasureTheory.ae_iff]
    exact (MeasureTheory.prob_compl_eq_zero_iff h_fst_meas).mpr hπ_feas.fst_supportsOn
  have h_kernel_bdd : ∀ᵐ p ∂pi.toMeasure, |s.m p.2 i - p.1 i| ≤ R + R := by
    filter_upwards [h_ae_p1] with p hp1
    have h_m_i : ‖(s.m p.2).ofLp i‖ ≤ R :=
      (PiLp.norm_apply_le (s.m p.2) i).trans (hR _ (s.m_mem_X p.2))
    have h_p_i : ‖p.1.ofLp i‖ ≤ R :=
      (PiLp.norm_apply_le p.1 i).trans (hR _ hp1)
    rw [Real.norm_eq_abs] at h_m_i h_p_i
    have h := abs_sub (s.m p.2 i) (p.1 i)
    linarith
  set f : Quotient (cellEquiv (Ω := Ω) v) → ℝ := fun α =>
    ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 i - p.1 i) ∂(κ α) with hf_def
  let qfst : EuclideanSpace ℝ (Fin n) → Quotient (cellEquiv v) :=
    fun x => Quotient.mk'' (x, Classical.arbitrary Ω)
  have h_factor : ∀ p : EuclideanSpace ℝ (Fin n) × Ω,
      (Quotient.mk'' p : Quotient (cellEquiv v)) = qfst p.1 := by
    intro p
    apply Quotient.sound
    rfl
  have h_qfst_meas : Measurable qfst :=
    measurable_quotient_mk''.comp (measurable_id.prodMk measurable_const)
  have h_map_eq :
      pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v))
        = (pi.toMeasure.map Prod.fst).map qfst := by
    rw [MeasureTheory.Measure.map_map h_qfst_meas measurable_fst]
    congr 1
    funext p
    exact h_factor p
  have h_πX :
      pi.toMeasure.map Prod.fst
        = (ProbDist.map pi Prod.fst measurable_fst).toMeasure := by
    rw [ProbDist.map_toMeasure]
  have h_joint_eq :
      MeasureTheory.joint pi.toMeasure (cellEquiv v) = μ ⊗ₘ κ := by
    letI : Setoid (EuclideanSpace ℝ (Fin n) × Ω) := cellEquiv v
    change MeasureTheory.joint pi.toMeasure (cellEquiv v) =
      pi.toMeasure.map (Quotient.mk' : _ → Quotient (cellEquiv v)) ⊗ₘ
        MeasureTheory.baseKernel pi.toMeasure (cellEquiv v)
    rw [← MeasureTheory.joint_fst pi.toMeasure (cellEquiv v),
        MeasureTheory.baseKernel_disintegrate pi.toMeasure (cellEquiv v)]
  have h_prod_meas : MeasurableSet (A ×ˢ (Set.univ : Set Ω)) :=
    hA.prod MeasurableSet.univ
  have h_pi_compl_zero :
      pi.toMeasure ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' s.X)ᶜ = 0 :=
    (MeasureTheory.prob_compl_eq_zero_iff h_fst_meas).mpr hπ_feas.fst_supportsOn
  have h_kernel_supp_ae :
      ∀ᵐ α ∂μ, κ α ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' s.X)ᶜ = 0 := by
    have h_meas_int :
        Measurable (fun α : Quotient (cellEquiv v) =>
          κ α ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' s.X)ᶜ) :=
      D.measurable_apply h_fst_meas.compl
    have hd :
        pi.toMeasure ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' s.X)ᶜ
          = ∫⁻ α, κ α ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' s.X)ᶜ ∂μ := by
      have h := D.apply_eq_setLIntegral h_fst_meas.compl MeasurableSet.univ
      rw [Set.preimage_univ, Set.inter_univ,
          MeasureTheory.setLIntegral_univ] at h
      exact h
    rw [h_pi_compl_zero] at hd
    exact (MeasureTheory.lintegral_eq_zero_iff h_meas_int).mp hd.symm
  have h_f_bdd_ae : ∀ᵐ α ∂μ, |f α| ≤ R + R := by
    filter_upwards [h_kernel_supp_ae] with α hα
    have hαX : ∀ᵐ p ∂(κ α), p.1 ∈ s.X := by
      rw [MeasureTheory.ae_iff]; exact hα
    have hα_bdd : ∀ᵐ p ∂(κ α), |s.m p.2 i - p.1 i| ≤ R + R := by
      filter_upwards [hαX] with p hp1
      have h_m_i : ‖(s.m p.2).ofLp i‖ ≤ R :=
        (PiLp.norm_apply_le (s.m p.2) i).trans (hR _ (s.m_mem_X p.2))
      have h_p_i : ‖p.1.ofLp i‖ ≤ R :=
        (PiLp.norm_apply_le p.1 i).trans (hR _ hp1)
      rw [Real.norm_eq_abs] at h_m_i h_p_i
      have h := abs_sub (s.m p.2 i) (p.1 i)
      linarith
    have h_norm_le :
        ‖∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 i - p.1 i) ∂(κ α)‖ ≤
          ∫ p in A ×ˢ (Set.univ : Set Ω), ‖(s.m p.2 i - p.1 i)‖ ∂(κ α) :=
      MeasureTheory.norm_integral_le_integral_norm _
    have hκα_prob : IsProbabilityMeasure (κ α) := D.isProbabilityMeasure α
    have hα_bdd_on : ∀ᵐ p ∂((κ α).restrict (A ×ˢ (Set.univ : Set Ω))),
        ‖(s.m p.2 i - p.1 i)‖ ≤ R + R := by
      refine (MeasureTheory.ae_restrict_iff' h_prod_meas).mpr ?_
      filter_upwards [hα_bdd] with p hp _
      rw [Real.norm_eq_abs]; exact hp
    have h_bound :
        ∫ p in A ×ˢ (Set.univ : Set Ω), ‖(s.m p.2 i - p.1 i)‖ ∂(κ α) ≤
          ∫ _ in A ×ˢ (Set.univ : Set Ω), (R + R) ∂(κ α) := by
      apply MeasureTheory.integral_mono_ae
      · refine Integrable.integrableOn ?_
        refine Integrable.of_bound h_k_meas.norm.aestronglyMeasurable (R + R) ?_
        filter_upwards [hα_bdd] with p hp
        rw [norm_norm, Real.norm_eq_abs]; exact hp
      · exact MeasureTheory.integrable_const _
      · exact hα_bdd_on
    have h_const :
        ∫ _ in A ×ˢ (Set.univ : Set Ω), (R + R) ∂(κ α) ≤ R + R := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul]
      have h_mass : (κ α).real (A ×ˢ (Set.univ : Set Ω)) ≤ 1 := by
        have h_le : (κ α) (A ×ˢ (Set.univ : Set Ω)) ≤ 1 :=
          MeasureTheory.prob_le_one
        unfold MeasureTheory.Measure.real
        exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr h_le
      have h2R_nn : 0 ≤ R + R := by linarith
      nlinarith [h_mass]
    rw [Real.norm_eq_abs] at h_norm_le
    linarith [(h_norm_le.trans h_bound).trans h_const]
  have h_f_meas : StronglyMeasurable f := by
    have h_ind_meas : Measurable
        (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
          (A ×ˢ (Set.univ : Set Ω)).indicator
            (fun q : EuclideanSpace ℝ (Fin n) × Ω => s.m q.2 i - q.1 i) p) :=
      h_k_meas.indicator h_prod_meas
    have h_g_meas :
        StronglyMeasurable
          (Function.uncurry
            (fun (_ : Quotient (cellEquiv (Ω := Ω) v))
                (p : EuclideanSpace ℝ (Fin n) × Ω) =>
              (A ×ˢ (Set.univ : Set Ω)).indicator
                (fun q : EuclideanSpace ℝ (Fin n) × Ω => s.m q.2 i - q.1 i) p)) :=
      (h_ind_meas.comp measurable_snd).stronglyMeasurable
    have h :=
      MeasureTheory.StronglyMeasurable.integral_kernel_prod_right (κ := κ) h_g_meas
    have h_eq :
        (fun α : Quotient (cellEquiv (Ω := Ω) v) =>
            ∫ p, (A ×ˢ (Set.univ : Set Ω)).indicator
              (fun q : EuclideanSpace ℝ (Fin n) × Ω => s.m q.2 i - q.1 i) p ∂(κ α)) = f := by
      funext α
      rw [MeasureTheory.integral_indicator h_prod_meas]
    rw [← h_eq]; exact h
  have h_setint_zero :
      ∀ F : Set (Quotient (cellEquiv (Ω := Ω) v)), MeasurableSet F →
        μ F ≠ ⊤ → ∫ α in F, f α ∂μ = 0 := by
    intro F hF _
    have h_int_eq :
        ∫ α in F, f α ∂μ =
          ∫ x in F ×ˢ (A ×ˢ (Set.univ : Set Ω)),
            (s.m x.2.2 i - x.2.1 i) ∂(μ ⊗ₘ κ) := by
      have h_int_on :
          IntegrableOn
            (fun x : Quotient (cellEquiv (Ω := Ω) v) × (EuclideanSpace ℝ (Fin n) × Ω) =>
              s.m x.2.2 i - x.2.1 i)
            (F ×ˢ (A ×ˢ (Set.univ : Set Ω))) (μ ⊗ₘ κ) := by
        refine MeasureTheory.Integrable.integrableOn ?_
        have h_meas_x :
            @Measurable _ ℝ _ _
              (fun x : Quotient (cellEquiv (Ω := Ω) v) × (EuclideanSpace ℝ (Fin n) × Ω) =>
                s.m x.2.2 i - x.2.1 i) := h_k_meas.comp measurable_snd
        refine Integrable.of_bound h_meas_x.aestronglyMeasurable (R + R) ?_
        rw [show (μ ⊗ₘ κ) = MeasureTheory.joint pi.toMeasure (cellEquiv v)
            from h_joint_eq.symm]
        rw [MeasureTheory.joint, MeasureTheory.ae_map_iff
              MeasureTheory.measurable_joint_map.aemeasurable]
        · filter_upwards [h_kernel_bdd] with p hp
          rw [Real.norm_eq_abs]; exact hp
        · refine measurableSet_le ?_ measurable_const
          exact (h_k_meas.comp measurable_snd).norm
      have h_setint :=
        MeasureTheory.Measure.setIntegral_compProd hF h_prod_meas h_int_on
      rw [show f = fun α =>
            ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 i - p.1 i) ∂(κ α) from rfl]
      exact h_setint.symm
    have h_prod_F_meas :
        MeasurableSet
          (F ×ˢ (A ×ˢ (Set.univ : Set Ω)) :
            Set (Quotient (cellEquiv v) × (EuclideanSpace ℝ (Fin n) × Ω))) :=
      hF.prod h_prod_meas
    have h_joint_def :
        MeasureTheory.joint pi.toMeasure (cellEquiv v)
          = pi.toMeasure.map (fun p =>
              ((Quotient.mk' p : Quotient (cellEquiv v)), p)) := rfl
    have h_int_joint_eq :
        ∫ x in F ×ˢ (A ×ˢ (Set.univ : Set Ω)),
          (s.m x.2.2 i - x.2.1 i) ∂(μ ⊗ₘ κ)
          = ∫ p in (qfst ⁻¹' F ∩ A) ×ˢ (Set.univ : Set Ω),
              (s.m p.2 i - p.1 i) ∂pi.toMeasure := by
      rw [show (μ ⊗ₘ κ) = MeasureTheory.joint pi.toMeasure (cellEquiv v)
          from h_joint_eq.symm,
          ← MeasureTheory.integral_indicator h_prod_F_meas, h_joint_def]
      have h_aem : AEStronglyMeasurable
          ((F ×ˢ (A ×ˢ (Set.univ : Set Ω))).indicator
            (fun x : Quotient (cellEquiv (Ω := Ω) v) × (EuclideanSpace ℝ (Fin n) × Ω) =>
              s.m x.2.2 i - x.2.1 i))
          (pi.toMeasure.map (fun p =>
              ((Quotient.mk' p : Quotient (cellEquiv v)), p))) :=
        (((h_k_meas.comp measurable_snd).indicator h_prod_F_meas).aestronglyMeasurable)
      rw [MeasureTheory.integral_map
        MeasureTheory.measurable_joint_map.aemeasurable h_aem]
      have h_inter_meas :
          MeasurableSet ((qfst ⁻¹' F ∩ A) ×ˢ (Set.univ : Set Ω) :
              Set (EuclideanSpace ℝ (Fin n) × Ω)) :=
        ((h_qfst_meas hF).inter hA).prod MeasurableSet.univ
      rw [← MeasureTheory.integral_indicator h_inter_meas]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with p
      have h_mem_iff :
          p ∈ (qfst ⁻¹' F ∩ A) ×ˢ (Set.univ : Set Ω) ↔
            ((Quotient.mk' p : Quotient (cellEquiv v)), p) ∈
              F ×ˢ (A ×ˢ (Set.univ : Set Ω)) := by
        constructor
        · rintro ⟨⟨hp_F, hp_A⟩, _⟩
          refine ⟨?_, hp_A, Set.mem_univ _⟩
          have hfact := h_factor p
          rw [show (Quotient.mk' p : Quotient (cellEquiv v)) = qfst p.1 from hfact]
          exact hp_F
        · rintro ⟨h1, h2, _⟩
          refine ⟨⟨?_, h2⟩, Set.mem_univ _⟩
          have hfact := h_factor p
          rw [show (Quotient.mk' p : Quotient (cellEquiv v)) = qfst p.1 from hfact] at h1
          exact h1
      by_cases hp_in : p ∈ (qfst ⁻¹' F ∩ A) ×ˢ (Set.univ : Set Ω)
      · have hp_pair := h_mem_iff.mp hp_in
        rw [Set.indicator_of_mem hp_pair, Set.indicator_of_mem hp_in]
      · have hp_pair := mt h_mem_iff.mpr hp_in
        rw [Set.indicator_of_notMem hp_pair, Set.indicator_of_notMem hp_in]
    rw [h_int_eq, h_int_joint_eq]
    have h_inter_meas :
        MeasurableSet (qfst ⁻¹' F ∩ A : Set (EuclideanSpace ℝ (Fin n))) :=
      (h_qfst_meas hF).inter hA
    have h_m_int :
        Integrable (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 i) pi.toMeasure := by
      refine
        Integrable.of_bound
          ((h_proj.measurable.comp s.m_continuous.measurable).comp
            measurable_snd).aestronglyMeasurable R ?_
      filter_upwards with p
      exact (PiLp.norm_apply_le (s.m p.2) i).trans (hR _ (s.m_mem_X p.2))
    have h_p1_int :
        Integrable (fun p : EuclideanSpace ℝ (Fin n) × Ω => p.1 i) pi.toMeasure := by
      refine
        Integrable.of_bound (h_proj.measurable.comp measurable_fst).aestronglyMeasurable R ?_
      filter_upwards [h_ae_p1] with p hp1
      exact (PiLp.norm_apply_le p.1 i).trans (hR _ hp1)
    rw [show
          (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 i - p.1 i)
            = fun p => (fun q => s.m q.2 i) p - (fun q => q.1 i) p from rfl]
    rw [MeasureTheory.integral_sub h_m_int.integrableOn h_p1_int.integrableOn]
    linarith [hπ_feas.setIntegral_m_eq_setIntegral_fst_ofLp h_inter_meas i]
  haveI : IsFiniteMeasure μ := by
    rw [hμ_def]; exact MeasureTheory.Measure.isFiniteMeasure_map _ _
  have h_f_zero_ae : f =ᵐ[μ] 0 := by
    have h_int_fin : ∀ s, MeasurableSet s → μ s < ⊤ → IntegrableOn f s μ := by
      intro s hs _
      refine MeasureTheory.Integrable.integrableOn ?_
      refine (MeasureTheory.Integrable.of_bound h_f_meas.aestronglyMeasurable (R + R)
        ?_)
      filter_upwards [h_f_bdd_ae] with α hα
      rw [Real.norm_eq_abs]; exact hα
    exact MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite h_int_fin
      (fun s hs hμs => h_setint_zero s hs hμs.ne)
  have h_f_zero_πX :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure, f (qfst x₀) = 0 := by
    rw [show ((ProbDist.map pi Prod.fst measurable_fst).toMeasure
        : Measure (EuclideanSpace ℝ (Fin n)))
        = pi.toMeasure.map Prod.fst from h_πX.symm]
    have h_via_map : ∀ᵐ α ∂((pi.toMeasure.map Prod.fst).map qfst), f α = 0 := by
      rw [← h_map_eq]; exact h_f_zero_ae
    exact MeasureTheory.ae_of_ae_map h_qfst_meas.aemeasurable h_via_map
  filter_upwards [h_f_zero_πX] with x₀ hx₀
  -- `(cellRho pi x₀).toMeasure` is definitionally `κ (qfst x₀)`.
  exact hx₀

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- For each measurable `A`, the vector martingale identity holds `π_X`-a.e.  The exceptional null
set depends on `A`. -/
lemma cellRho_local_martingale_at_set_ae [Nonempty Ω]
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi : pi ∈ feasibleJoint s)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) :
    ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
      ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1)
        ∂(cellRho pi x₀ (v := v)).toMeasure = 0 := by
  have h_per_coord : ∀ i : Fin n,
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 i - p.1 i)
          ∂(cellRho pi x₀ (v := v)).toMeasure = 0 :=
    fun i => cellRho_local_martingale_at_set_coord_ae s hpi hA i
  have h_all_coord :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        ∀ i : Fin n,
          ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 i - p.1 i)
            ∂(cellRho pi x₀ (v := v)).toMeasure = 0 :=
    (MeasureTheory.ae_all_iff (p := fun x₀ i =>
      ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 i - p.1 i)
        ∂(cellRho pi x₀ (v := v)).toMeasure = 0)).mpr h_per_coord
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  have hR_nn : 0 ≤ R := by
    rcases s.X_interior.mono interior_subset with ⟨x_int, hx_int⟩
    exact le_trans (norm_nonneg _) (hR _ hx_int)
  have h_proj : ∀ i : Fin n,
      Continuous (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) :=
    fun i => (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin n => ℝ))
  have h_X_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
    s.X_compact.isClosed.measurableSet
  have h_cellRho_in_X :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        ∀ᵐ p ∂(cellRho pi x₀ (v := v)).toMeasure, p.1 ∈ s.X := by
    have h_pi_in_X : ∀ᵐ p ∂pi.toMeasure, p.1 ∈ s.X := by
      rw [MeasureTheory.ae_iff]
      exact (MeasureTheory.prob_compl_eq_zero_iff (h_X_meas.preimage measurable_fst)).mpr
        (hpi : IsFeasibleJoint s pi).fst_supportsOn
    have h_mset :
        MeasurableSet {p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X} :=
      h_X_meas.preimage measurable_fst
    set D := cellDisintegration (v := v) pi
    have h_meas_int :
        Measurable
          (fun α : Quotient (cellEquiv v) =>
            D.μα α ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ)) :=
      D.measurable_apply h_mset.compl
    have hd :
        pi.toMeasure ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ)
          = ∫⁻ α, D.μα α ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ)
              ∂(pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v))) := by
      have h := D.apply_eq_setLIntegral h_mset.compl MeasurableSet.univ
      rw [Set.preimage_univ, Set.inter_univ,
          MeasureTheory.setLIntegral_univ] at h
      exact h
    have h_bad_zero :
        pi.toMeasure ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ) = 0 := by
      rwa [MeasureTheory.ae_iff] at h_pi_in_X
    rw [h_bad_zero] at hd
    have h_ae_zero :
        ∀ᵐ α ∂(pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v))),
          D.μα α ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ) = 0 :=
      (MeasureTheory.lintegral_eq_zero_iff h_meas_int).mp hd.symm
    let qfst : EuclideanSpace ℝ (Fin n) → Quotient (cellEquiv v) :=
      fun x => Quotient.mk'' (x, Classical.arbitrary Ω)
    have h_factor : ∀ p : EuclideanSpace ℝ (Fin n) × Ω,
        (Quotient.mk'' p : Quotient (cellEquiv v)) = qfst p.1 := fun p => by
      apply Quotient.sound; rfl
    have h_qfst_meas : Measurable qfst :=
      measurable_quotient_mk''.comp (measurable_id.prodMk measurable_const)
    have h_map_eq :
        pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v))
          = (pi.toMeasure.map Prod.fst).map qfst := by
      rw [MeasureTheory.Measure.map_map h_qfst_meas measurable_fst]
      congr 1; funext p; exact h_factor p
    have h_πX :
        pi.toMeasure.map Prod.fst
          = (ProbDist.map pi Prod.fst measurable_fst).toMeasure := by
      rw [ProbDist.map_toMeasure]
    rw [h_map_eq, h_πX] at h_ae_zero
    have h_set_meas :
        MeasurableSet
          {α : Quotient (cellEquiv v) |
            D.μα α ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ) = 0} :=
      h_meas_int (measurableSet_singleton 0)
    rw [MeasureTheory.ae_map_iff h_qfst_meas.aemeasurable h_set_meas] at h_ae_zero
    filter_upwards [h_ae_zero] with x₀ hx₀
    rw [MeasureTheory.ae_iff]
    exact hx₀
  filter_upwards [h_all_coord, h_cellRho_in_X] with x₀ hx₀_coord hx₀_X
  have h_int :
      Integrable (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1)
        ((cellRho pi x₀ (v := v)).toMeasure.restrict (A ×ˢ (Set.univ : Set Ω))) := by
    refine
      Integrable.of_bound
        ((s.m_continuous.measurable.comp measurable_snd).sub measurable_fst).aestronglyMeasurable
        (R + R) ?_
    rw [MeasureTheory.ae_restrict_iff' (hA.prod MeasurableSet.univ)]
    filter_upwards [hx₀_X] with p hp _
    have h_m : ‖s.m p.2‖ ≤ R := hR _ (s.m_mem_X p.2)
    have h_p : ‖p.1‖ ≤ R := hR _ hp
    have := norm_sub_le (s.m p.2) p.1
    linarith
  apply PiLp.ext
  intro i
  set L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i with hL_def
  have h_L_apply : ∀ x : EuclideanSpace ℝ (Fin n), L x = x.ofLp i := fun x => rfl
  change (∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1)
          ∂(cellRho pi x₀ (v := v)).toMeasure).ofLp i = (0 : EuclideanSpace ℝ (Fin n)).ofLp i
  rw [show ((0 : EuclideanSpace ℝ (Fin n)).ofLp i : ℝ) = 0 from rfl,
      ← h_L_apply,
      ← ContinuousLinearMap.integral_comp_comm L h_int]
  have h_eq :
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => L (s.m p.2 - p.1))
        = (fun p => s.m p.2 i - p.1 i) := by
    funext p; exact h_L_apply _
  rw [h_eq]
  exact hx₀_coord i

omit [TopologicalSpace.PseudoMetrizableSpace Ω] [Inhabited Ω] in
/-- For `π_X`-a.e. `x₀`, the cell-conditional local martingale identity holds for every measurable
`A`. -/
lemma cellRho_local_martingale_ae [Nonempty Ω]
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi : pi ∈ feasibleJoint s) :
    ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
      ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
        ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1)
          ∂(cellRho pi x₀ (v := v)).toMeasure = 0 := by
  set C : Set (Set (EuclideanSpace ℝ (Fin n))) :=
    MeasurableSpace.countableGeneratingSet (EuclideanSpace ℝ (Fin n)) with hC_def
  set T : Set (Set (EuclideanSpace ℝ (Fin n))) := generatePiSystem C with hT_def
  have hC_count : C.Countable := MeasurableSpace.countable_countableGeneratingSet
  have hC_meas : ∀ B ∈ C, MeasurableSet B := fun _ hB =>
    MeasurableSpace.measurableSet_countableGeneratingSet hB
  have hT_pi : IsPiSystem T := isPiSystem_generatePiSystem C
  have hT_gen : MeasurableSpace.generateFrom T = (inferInstance : MeasurableSpace _) := by
    rw [hT_def, generateFrom_generatePiSystem_eq]
    exact MeasurableSpace.generateFrom_countableGeneratingSet
  have hT_meas : ∀ B ∈ T, MeasurableSet B := by
    intro B hB
    have h1 : @MeasurableSet _ (MeasurableSpace.generateFrom T) B := by
      exact MeasurableSpace.measurableSet_generateFrom hB
    rw [hT_gen] at h1
    exact h1
  have h_finset_rep : ∀ B ∈ T, ∃ S : Finset (Set (EuclideanSpace ℝ (Fin n))),
      ↑S ⊆ C ∧ S.Nonempty ∧ B = ⋂ s ∈ S, s := by
    intro B hB
    induction hB with
    | @base s' h_s' =>
      refine ⟨{s'}, ?_, ⟨s', Finset.mem_singleton.mpr rfl⟩, ?_⟩
      · intro x hx
        rw [Finset.coe_singleton, Set.mem_singleton_iff] at hx
        rw [hx]; exact h_s'
      · simp
    | @inter s' t' _ _ _ ih_s ih_t =>
      obtain ⟨S₁, hS₁_sub, hS₁_ne, hS₁_eq⟩ := ih_s
      obtain ⟨S₂, hS₂_sub, _, hS₂_eq⟩ := ih_t
      refine ⟨S₁ ∪ S₂, ?_, hS₁_ne.mono Finset.subset_union_left, ?_⟩
      · intro x hx
        rw [Finset.coe_union, Set.mem_union] at hx
        rcases hx with h | h
        · exact hS₁_sub h
        · exact hS₂_sub h
      · classical
        rw [Finset.set_biInter_inter, ← hS₁_eq, ← hS₂_eq]
  have hT_count : T.Countable := by
    classical
    have h_finset_count :
        {t : Set (Set (EuclideanSpace ℝ (Fin n))) | t.Finite ∧ t ⊆ C}.Countable :=
      Set.countable_setOf_finite_subset hC_count
    refine (h_finset_count.image
      (fun t : Set (Set (EuclideanSpace ℝ (Fin n))) => ⋂ s ∈ t, s)).mono ?_
    rintro B hB
    obtain ⟨S, hS_sub, _, hS_eq⟩ := h_finset_rep B hB
    refine ⟨(↑S : Set _), ⟨S.finite_toSet, hS_sub⟩, ?_⟩
    change ⋂ s ∈ (↑S : Set _), s = B
    rw [Finset.set_biInter_coe, ← hS_eq]
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  have hR_nn : 0 ≤ R := by
    rcases s.X_interior.mono interior_subset with ⟨x_int, hx_int⟩
    exact le_trans (norm_nonneg _) (hR _ hx_int)
  have h_X_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
    s.X_compact.isClosed.measurableSet
  have h_cellRho_in_X :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        ∀ᵐ p ∂(cellRho pi x₀ (v := v)).toMeasure, p.1 ∈ s.X := by
    have h_pi_in_X : ∀ᵐ p ∂pi.toMeasure, p.1 ∈ s.X := by
      rw [MeasureTheory.ae_iff]
      exact (MeasureTheory.prob_compl_eq_zero_iff (h_X_meas.preimage measurable_fst)).mpr
        (hpi : IsFeasibleJoint s pi).fst_supportsOn
    have h_mset :
        MeasurableSet {p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X} :=
      h_X_meas.preimage measurable_fst
    set D := cellDisintegration (v := v) pi
    have h_meas_int :
        Measurable
          (fun α : Quotient (cellEquiv v) =>
            D.μα α ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ)) :=
      D.measurable_apply h_mset.compl
    have hd :
        pi.toMeasure ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ)
          = ∫⁻ α, D.μα α ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ)
              ∂(pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v))) := by
      have h := D.apply_eq_setLIntegral h_mset.compl MeasurableSet.univ
      rw [Set.preimage_univ, Set.inter_univ,
          MeasureTheory.setLIntegral_univ] at h
      exact h
    have h_bad_zero :
        pi.toMeasure ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ) = 0 := by
      rwa [MeasureTheory.ae_iff] at h_pi_in_X
    rw [h_bad_zero] at hd
    have h_ae_zero :
        ∀ᵐ α ∂(pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v))),
          D.μα α ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ) = 0 :=
      (MeasureTheory.lintegral_eq_zero_iff h_meas_int).mp hd.symm
    let qfst : EuclideanSpace ℝ (Fin n) → Quotient (cellEquiv v) :=
      fun x => Quotient.mk'' (x, Classical.arbitrary Ω)
    have h_factor : ∀ p : EuclideanSpace ℝ (Fin n) × Ω,
        (Quotient.mk'' p : Quotient (cellEquiv v)) = qfst p.1 := fun p => by
      apply Quotient.sound; rfl
    have h_qfst_meas : Measurable qfst :=
      measurable_quotient_mk''.comp (measurable_id.prodMk measurable_const)
    have h_map_eq :
        pi.toMeasure.map (Quotient.mk'' : _ → Quotient (cellEquiv v))
          = (pi.toMeasure.map Prod.fst).map qfst := by
      rw [MeasureTheory.Measure.map_map h_qfst_meas measurable_fst]
      congr 1; funext p; exact h_factor p
    have h_πX :
        pi.toMeasure.map Prod.fst
          = (ProbDist.map pi Prod.fst measurable_fst).toMeasure := by
      rw [ProbDist.map_toMeasure]
    rw [h_map_eq, h_πX] at h_ae_zero
    have h_set_meas :
        MeasurableSet
          {α : Quotient (cellEquiv v) |
            D.μα α ({p : EuclideanSpace ℝ (Fin n) × Ω | p.1 ∈ s.X}ᶜ) = 0} :=
      h_meas_int (measurableSet_singleton 0)
    rw [MeasureTheory.ae_map_iff h_qfst_meas.aemeasurable h_set_meas] at h_ae_zero
    filter_upwards [h_ae_zero] with x₀ hx₀
    rw [MeasureTheory.ae_iff]
    exact hx₀
  have h_per_B :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        ∀ B ∈ T,
          ∫ p in B ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1)
            ∂(cellRho pi x₀ (v := v)).toMeasure = 0 := by
    refine (MeasureTheory.ae_ball_iff (S := T) hT_count).mpr ?_
    intro B hB
    exact cellRho_local_martingale_at_set_ae s hpi (hT_meas B hB)
  have h_univ :
      ∀ᵐ x₀ ∂(ProbDist.map pi Prod.fst measurable_fst).toMeasure,
        ∫ p in (Set.univ : Set (EuclideanSpace ℝ (Fin n))) ×ˢ (Set.univ : Set Ω),
            (s.m p.2 - p.1)
          ∂(cellRho pi x₀ (v := v)).toMeasure = 0 :=
    cellRho_local_martingale_at_set_ae s hpi MeasurableSet.univ
  filter_upwards [h_per_B, h_univ, h_cellRho_in_X]
    with x₀ hx₀_B hx₀_univ hx₀_X
  have h_f_meas :
      Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1) :=
    (s.m_continuous.measurable.comp measurable_snd).sub measurable_fst
  have h_f_int :
      Integrable (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1)
        (cellRho pi x₀ (v := v)).toMeasure := by
    refine Integrable.of_bound h_f_meas.aestronglyMeasurable (R + R) ?_
    filter_upwards [hx₀_X] with p hp
    have h_m : ‖s.m p.2‖ ≤ R := hR _ (s.m_mem_X p.2)
    have h_p : ‖p.1‖ ≤ R := hR _ hp
    have := norm_sub_le (s.m p.2) p.1
    linarith
  have h_univ_int :
      ∫ p, (s.m p.2 - p.1) ∂(cellRho pi x₀ (v := v)).toMeasure = 0 := by
    have := hx₀_univ
    rw [Set.univ_prod_univ, MeasureTheory.setIntegral_univ] at this
    exact this
  intro A hA
  have h_eq_gen :
      (inferInstance : MeasurableSpace (EuclideanSpace ℝ (Fin n)))
        = MeasurableSpace.generateFrom T := hT_gen.symm
  refine MeasurableSpace.induction_on_inter
    (m := inferInstance) (s := T)
    (C := fun A _ => ∫ p in A ×ˢ (Set.univ : Set Ω), (s.m p.2 - p.1)
      ∂(cellRho pi x₀ (v := v)).toMeasure = 0)
    h_eq_gen hT_pi ?_ ?_ ?_ ?_ A hA
  · simp
  · intro B hB
    exact hx₀_B B hB
  · intro B hB hB_int
    have h_compl_eq :
        (Bᶜ ×ˢ (Set.univ : Set Ω))
          = (B ×ˢ (Set.univ : Set Ω))ᶜ := by
      ext p; simp [Set.mem_prod, Set.mem_compl_iff]
    rw [h_compl_eq]
    have hBu_meas :
        MeasurableSet (B ×ˢ (Set.univ : Set Ω)) := hB.prod MeasurableSet.univ
    rw [MeasureTheory.setIntegral_compl hBu_meas h_f_int]
    rw [h_univ_int, hB_int]
    simp
  · intro f hf_disj hf_meas hf_eq
    have h_prod_iUnion :
        ((⋃ i, f i) ×ˢ (Set.univ : Set Ω))
          = ⋃ i, (f i ×ˢ (Set.univ : Set Ω)) := by
      ext p; simp [Set.mem_iUnion, Set.mem_prod]
    have hfm_prod : ∀ i, MeasurableSet (f i ×ˢ (Set.univ : Set Ω)) :=
      fun i => (hf_meas i).prod MeasurableSet.univ
    have hf_disj_prod :
        Pairwise (Function.onFun Disjoint
          (fun i => f i ×ˢ (Set.univ : Set Ω))) := by
      intro i j hij
      have := hf_disj hij
      simp only [Function.onFun] at this ⊢
      rw [Set.disjoint_left] at this ⊢
      intro p hpi hpj
      exact this hpi.1 hpj.1
    have h_int_on :
        MeasureTheory.IntegrableOn
          (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1)
          (⋃ i, (f i ×ˢ (Set.univ : Set Ω)))
          (cellRho pi x₀ (v := v)).toMeasure := h_f_int.integrableOn
    rw [h_prod_iUnion]
    rw [MeasureTheory.integral_iUnion hfm_prod hf_disj_prod h_int_on]
    simp only [hf_eq, tsum_zero]

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
