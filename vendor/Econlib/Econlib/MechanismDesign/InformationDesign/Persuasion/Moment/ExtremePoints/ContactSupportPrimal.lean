/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.ExtremePoints.ContactFibre
public import Econlib.Probability.ProbDist.Borel

/-!
# Contact-support primal value

A feasible joint whose support lies in the contact graph attains the same primal value as the
original optimal joint.

## Main statements

* `primal_eq_of_contact_support_and_M`: If a feasible joint `pi'` has its support contained in the
  contact graph `Γ_{p.1}` for a.e. `p`, then it achieves the same primal objective value as any
  primal-optimal joint.

## Tags

persuasion, moment persuasion, extreme points, contact graph
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

omit [CompactSpace Ω] [T2Space Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω] in
/-- A feasible joint `pi'` whose support lies in the contact graph `∀ᵐ p, s.m p.2 ∈ Γ_{p.1}`
attains the same primal value as the original primal-optimal joint `pi`. -/
lemma primal_eq_of_contact_support_and_M
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L v) (hv_diff : ContDiff ℝ 1 v)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (h_pi_opt : ∫ p, v p.1 ∂pi.toMeasure = momentPrimal s v)
    {pi' : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi' : pi' ∈ feasibleJoint s)
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (hM_pi : ConditionM s v pi S)
    (h_contact : ∀ᵐ p ∂pi'.toMeasure, s.m p.2 ∈ Gamma_x s v S p.1) :
    ∫ p, v p.1 ∂pi'.toMeasure = momentPrimal s v := by
  have hpi : pi ∈ feasibleJoint s := hM_pi.feasible
  have hX_closed : IsClosed (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
    s.X_compact.isClosed
  have h_pre_closed : IsClosed
      ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' s.X) :=
    hX_closed.preimage continuous_fst
  have h_pre_ae_pi :
      (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' s.X
        ∈ MeasureTheory.ae pi.toMeasure := by
    rw [MeasureTheory.mem_ae_iff]
    exact (MeasureTheory.prob_compl_eq_zero_iff
      h_pre_closed.measurableSet).mpr hpi.fst_supportsOn
  have h_supp_pi_sub :
      pi.toMeasure.support ⊆
        (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' s.X :=
    MeasureTheory.Measure.support_subset_of_isClosed h_pre_closed h_pre_ae_pi
  have hS_subX : S ⊆ s.X := by
    rw [hM_pi.S_eq_support]
    rintro y ⟨p, hp_supp, rfl⟩
    exact h_supp_pi_sub hp_supp
  have h_active' : ∀ᵐ p ∂pi'.toMeasure,
      pStar v S (s.m p.2) = v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1) := by
    filter_upwards [h_contact] with p hp using pStar_eq_affine_minorant_on_Gamma_x s hp
  have h_slope : ∀ x ∈ S, ‖fderiv ℝ v x‖ ≤ (L : ℝ) :=
    fun x _ => norm_fderiv_le_of_lipschitz ℝ hv_lip
  have h_pStar_lip : LipschitzWith L (pStar v S) :=
    pStar_lipschitzWith s hv_diff hS_subX h_slope
  have h_pStar_cont : Continuous (pStar v S) := h_pStar_lip.continuous
  have h_pStarm_cont : Continuous (fun ω => pStar v S (s.m ω)) :=
    h_pStar_cont.comp s.m_continuous
  have h_pStarm_p_cont :
      Continuous (fun p : EuclideanSpace ℝ (Fin n) × Ω => pStar v S (s.m p.2)) :=
    h_pStarm_cont.comp continuous_snd
  have h_v_p_cont :
      Continuous (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) :=
    hv_lip.continuous.comp continuous_fst
  have h_fd_p_cont :
      Continuous (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        (fderiv ℝ v p.1) (s.m p.2 - p.1)) := by
    have h_joint :
        Continuous fun q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          (fderiv ℝ v q.1) q.2 :=
      hv_diff.continuous_fderiv_apply one_ne_zero
    refine h_joint.comp (Continuous.prodMk continuous_fst ?_)
    exact (s.m_continuous.comp continuous_snd).sub continuous_fst
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x ∈ s.X, ‖x‖ ≤ R :=
    s.X_compact.isBounded.exists_norm_le
  have h_X_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
    hX_closed.measurableSet
  have h_pre_meas : MeasurableSet
      ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → _) ⁻¹' s.X) :=
    h_X_meas.preimage measurable_fst
  have h_ae_p1_pi' : ∀ᵐ p ∂pi'.toMeasure, p.1 ∈ s.X := by
    rw [MeasureTheory.ae_iff]
    exact (MeasureTheory.prob_compl_eq_zero_iff h_pre_meas).mpr hpi'.fst_supportsOn
  have h_pStar_compact_image : IsCompact (pStar v S '' s.X) := s.X_compact.image h_pStar_cont
  obtain ⟨K_pStar, hK_pStar⟩ := h_pStar_compact_image.isBounded.exists_norm_le
  have h_pStarm_int :
      MeasureTheory.Integrable
        (fun p : EuclideanSpace ℝ (Fin n) × Ω => pStar v S (s.m p.2)) pi'.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_pStarm_p_cont.aestronglyMeasurable K_pStar ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    simpa using hK_pStar (pStar v S (s.m p.2)) ⟨s.m p.2, s.m_mem_X p.2, rfl⟩
  have h_v_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) pi'.toMeasure := by
    have h_v_compact_image : IsCompact (v '' s.X) := s.X_compact.image hv_lip.continuous
    obtain ⟨K_v, hK_v⟩ := h_v_compact_image.isBounded.exists_norm_le
    refine MeasureTheory.Integrable.of_bound h_v_p_cont.aestronglyMeasurable K_v ?_
    filter_upwards [h_ae_p1_pi'] with p hp
    simpa using hK_v (v p.1) ⟨p.1, hp, rfl⟩
  have h_fd_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        (fderiv ℝ v p.1) (s.m p.2 - p.1)) pi'.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_fd_p_cont.aestronglyMeasurable
      ((L : ℝ) * (R + R)) ?_
    filter_upwards [h_ae_p1_pi'] with p hp
    have h_fd_norm : ‖fderiv ℝ v p.1‖ ≤ (L : ℝ) := norm_fderiv_le_of_lipschitz ℝ hv_lip
    have h_diff_norm : ‖s.m p.2 - p.1‖ ≤ R + R :=
      (norm_sub_le _ _).trans (add_le_add (hR _ (s.m_mem_X p.2)) (hR _ hp))
    calc ‖(fderiv ℝ v p.1) (s.m p.2 - p.1)‖
        ≤ ‖fderiv ℝ v p.1‖ * ‖s.m p.2 - p.1‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L : ℝ) * (R + R) :=
          mul_le_mul h_fd_norm h_diff_norm (norm_nonneg _) L.coe_nonneg
  have h_active_int : ∫ p, pStar v S (s.m p.2) ∂pi'.toMeasure
      = ∫ p, v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1) ∂pi'.toMeasure :=
    MeasureTheory.integral_congr_ae h_active'
  have h_lin : ∫ p, v p.1 + (fderiv ℝ v p.1) (s.m p.2 - p.1) ∂pi'.toMeasure
      = ∫ p, v p.1 ∂pi'.toMeasure
        + ∫ p, (fderiv ℝ v p.1) (s.m p.2 - p.1) ∂pi'.toMeasure :=
    MeasureTheory.integral_add h_v_int h_fd_int
  have h_cross_pi' :=
    feasibleJoint_fderiv_cross_zero s hpi' hv_lip hv_diff
  have h_marg_pi' : ∫ ω, pStar v S (s.m ω) ∂s.prior.toMeasure
      = ∫ p, pStar v S (s.m p.2) ∂pi'.toMeasure :=
    hpi'.marginal ▸ ProbDist.expect_map pi' Prod.snd measurable_snd
      (fun ω => pStar v S (s.m ω)) h_pStarm_cont.aestronglyMeasurable
  have h_pi_obj : ∫ p, v p.1 ∂pi.toMeasure
      = ∫ ω, pStar v S (s.m ω) ∂s.prior.toMeasure :=
    objective_eq_pStar_integral_of_conditionM s hv_lip hv_diff hS_subX hM_pi
  have h_pi'_eq : ∫ p, v p.1 ∂pi'.toMeasure
      = ∫ ω, pStar v S (s.m ω) ∂s.prior.toMeasure := by
    linarith [h_active_int, h_lin, h_cross_pi', h_marg_pi']
  linarith [h_pi'_eq, h_pi_obj, h_pi_opt]

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
