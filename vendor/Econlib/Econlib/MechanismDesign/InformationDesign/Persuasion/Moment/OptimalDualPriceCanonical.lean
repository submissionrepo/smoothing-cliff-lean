/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.MechanismDesign.InformationDesign.Persuasion.Moment.OptimalDualPriceForward
public import Econlib.Probability.ProbDist.Borel

/-!
# Canonical-pbar identifications on the active support

These lemmas identify the canonical dual price `pbar` with `v` and with the formula-S envelope on
the projection-of-support active set.

## Main statements

* `pbar_eq_v_on_active_support` — `pbar = v` on the projection of the support.
* `pbar_eq_pStar_on_active_support` — `pbar` agrees with the formula-S envelope on all of `s.X` at
  an optimal joint.

## References

* Dworczak, Piotr, and Anton Kolotilin. 2024. “The Persuasion Duality.” *Theoretical Economics* 19
  (4): 1701–55. [https://doi.org/10.3982/te5900](https://doi.org/10.3982/te5900). Theorem 7.

## Tags

persuasion, moment persuasion, dual price, uniqueness
-/

@[expose] public section

open MeasureTheory Set Real Filter
open scoped NNReal Topology

namespace Econlib.MechanismDesign.InformationDesign.Persuasion.Moment

open Econlib.Probability
open Econlib.MechanismDesign.InformationDesign.Persuasion.Duality

variable {Ω : Type*} [MeasurableSpace Ω] [PseudoMetricSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] [T2Space Ω] [SecondCountableTopology Ω]
  [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω]

variable {n : ℕ}

/-! ## Canonical-pbar identifications for uniqueness -/

omit [T2Space Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω] in
/-- **Canonical pbar is `v`-active on the projection-of-support of any optimal joint.**

Every point of `Prod.fst '' pi.toMeasure.support` satisfies `pbar x = v x`, given that `pi` is
feasible and satisfies the complementary-slackness identity at the canonical structured prices
`(pbar, q)`. -/
lemma pbar_eq_v_on_active_support
    (s : MomentSetup Ω n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_meas : Measurable v) (hv_bdd : ∃ M, ∀ x, |v x| ≤ M)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi : pi ∈ feasibleJoint s)
    {pbar : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h_struct : HasMomentPrices s v L pbar q)
    (h_slack_pi : ∀ᵐ p ∂pi.toMeasure,
      pbar (s.m p.2) = v p.1 + inner ℝ (q p.1) (s.m p.2 - p.1)) :
    ∀ x ∈ Prod.fst '' pi.toMeasure.support, pbar x = v x := by
  obtain ⟨K_pbar, h_pbar_lip⟩ := h_struct.pbar_lipschitz
  obtain ⟨K_q, h_K_q_nn, h_q_norm⟩ := h_struct.q_norm_bound
  have h_pbar_cont : Continuous pbar := h_pbar_lip.continuous
  have h_v_cont : Continuous v := hv_lip.continuous
  have h_X_meas : MeasurableSet (s.X : Set (EuclideanSpace ℝ (Fin n))) :=
    s.X_compact.isClosed.measurableSet
  have h_fst_meas : MeasurableSet
      ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
    h_X_meas.preimage measurable_fst
  -- `{p | ¬ p.1 ∈ s.X}` is definitionally the complement of the fst-preimage of `s.X`.
  have h_ae_p1 : ∀ᵐ p ∂pi.toMeasure, p.1 ∈ s.X := by
    rw [MeasureTheory.ae_iff]
    change pi.toMeasure ((Prod.fst ⁻¹' s.X)ᶜ) = 0
    rw [MeasureTheory.prob_compl_eq_zero_iff h_fst_meas]
    exact hpi.fst_supportsOn
  obtain ⟨R, hR⟩ := s.X_compact.isBounded.exists_norm_le
  obtain ⟨M_v, hM_v⟩ := hv_bdd
  have h_pbar_compact : IsCompact (pbar '' s.X) := s.X_compact.image h_pbar_cont
  obtain ⟨M_pbar, hM_pbar⟩ := h_pbar_compact.isBounded.exists_norm_le
  have h_pbar_fst_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1) pi.toMeasure :=
    (h_pbar_cont.comp continuous_fst).aestronglyMeasurable
  have h_v_fst_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) pi.toMeasure :=
    (hv_meas.comp measurable_fst).aestronglyMeasurable
  have h_pbar_m_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar (s.m p.2)) pi.toMeasure :=
    (h_pbar_cont.comp (s.m_continuous.comp continuous_snd)).aestronglyMeasurable
  have h_pbar_fst_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_pbar_fst_aem M_pbar ?_
    filter_upwards [h_ae_p1] with p hp1
    have := hM_pbar (pbar p.1) ⟨p.1, hp1, rfl⟩
    simpa using this
  have h_v_fst_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => v p.1) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_v_fst_aem M_v ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    rw [Real.norm_eq_abs]; exact hM_v _
  have h_pbar_m_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar (s.m p.2)) pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_pbar_m_aem M_pbar ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have := hM_pbar (pbar (s.m p.2)) ⟨s.m p.2, s.m_mem_X p.2, rfl⟩
    simpa using this
  have h_inner_aem : MeasureTheory.AEStronglyMeasurable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        inner ℝ (q p.1) (s.m p.2 - p.1)) pi.toMeasure := by
    have h_q_meas : Measurable (fun p : EuclideanSpace ℝ (Fin n) × Ω => q p.1) :=
      h_struct.q_measurable.comp measurable_fst
    have h_m_meas : Measurable
        (fun p : EuclideanSpace ℝ (Fin n) × Ω => s.m p.2 - p.1) :=
      (s.m_continuous.comp continuous_snd).measurable.sub measurable_fst
    exact (continuous_inner.measurable.comp (h_q_meas.prodMk h_m_meas)).aestronglyMeasurable
  have h_inner_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => inner ℝ (q p.1) (s.m p.2 - p.1))
      pi.toMeasure := by
    refine MeasureTheory.Integrable.of_bound h_inner_aem (K_q * (R + R)) ?_
    filter_upwards [h_ae_p1] with p hp1
    have h_cs : ‖inner ℝ (q p.1) (s.m p.2 - p.1)‖
        ≤ ‖q p.1‖ * ‖s.m p.2 - p.1‖ := norm_inner_le_norm _ _
    have h_diff_norm : ‖s.m p.2 - p.1‖ ≤ R + R := by
      calc ‖s.m p.2 - p.1‖
          ≤ ‖s.m p.2‖ + ‖p.1‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (hR _ (s.m_mem_X p.2)) (hR _ hp1)
    have h_diff_nn : 0 ≤ ‖s.m p.2 - p.1‖ := norm_nonneg _
    exact h_cs.trans (mul_le_mul (h_q_norm p.1) h_diff_norm h_diff_nn h_K_q_nn)
  have h_pbar_lip_on : LipschitzOnWith K_pbar pbar s.X := h_pbar_lip.lipschitzOnWith
  have h_jensen_pbar : ∫ p, pbar p.1 ∂pi.toMeasure
      ≤ ∫ p, pbar (s.m p.2) ∂pi.toMeasure :=
    MomentSetup.integral_fst_le_integral_m_of_convexOn s hpi h_struct.pbar_convex h_pbar_lip_on
  have h_cross_zero : ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure = 0 :=
    hpi.martingale_inner_measurable h_struct.q_measurable ⟨K_q, h_q_norm⟩
  have h_slack_integ : ∫ p, pbar (s.m p.2) ∂pi.toMeasure
      = ∫ p, v p.1 ∂pi.toMeasure
        + ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure := by
    rw [MeasureTheory.integral_congr_ae h_slack_pi,
      MeasureTheory.integral_add h_v_fst_int h_inner_int]
  have h_pbar_ge_v_ae : ∀ᵐ p ∂pi.toMeasure, v p.1 ≤ pbar p.1 := by
    filter_upwards [h_ae_p1] with p hp1 using h_struct.pbar_ge_v _ hp1
  have h_int_v_le_int_pbar : ∫ p, v p.1 ∂pi.toMeasure
      ≤ ∫ p, pbar p.1 ∂pi.toMeasure :=
    MeasureTheory.integral_mono_ae h_v_fst_int h_pbar_fst_int h_pbar_ge_v_ae
  have h_int_pbar_eq_v : ∫ p, pbar p.1 ∂pi.toMeasure = ∫ p, v p.1 ∂pi.toMeasure :=
    le_antisymm
      (calc ∫ p, pbar p.1 ∂pi.toMeasure
            ≤ ∫ p, pbar (s.m p.2) ∂pi.toMeasure := h_jensen_pbar
          _ = ∫ p, v p.1 ∂pi.toMeasure
              + ∫ p, inner ℝ (q p.1) (s.m p.2 - p.1) ∂pi.toMeasure := h_slack_integ
          _ = ∫ p, v p.1 ∂pi.toMeasure := by rw [h_cross_zero, add_zero])
      h_int_v_le_int_pbar
  have h_diff_int : MeasureTheory.Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1 - v p.1) pi.toMeasure :=
    h_pbar_fst_int.sub h_v_fst_int
  have h_diff_nonneg : ∀ᵐ p ∂pi.toMeasure, 0 ≤ pbar p.1 - v p.1 := by
    filter_upwards [h_pbar_ge_v_ae] with p hp using by linarith
  have h_diff_int_zero : ∫ p, (pbar p.1 - v p.1) ∂pi.toMeasure = 0 := by
    rw [MeasureTheory.integral_sub h_pbar_fst_int h_v_fst_int, h_int_pbar_eq_v, sub_self]
  have h_diff_zero_ae : (fun p : EuclideanSpace ℝ (Fin n) × Ω => pbar p.1 - v p.1)
      =ᵐ[pi.toMeasure] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae h_diff_nonneg h_diff_int).mp
      h_diff_int_zero
  have h_active_set_closed : IsClosed
      {p : EuclideanSpace ℝ (Fin n) × Ω | pbar p.1 - v p.1 = 0} := by
    have h_cont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × Ω =>
        pbar p.1 - v p.1) :=
      (h_pbar_cont.comp continuous_fst).sub (h_v_cont.comp continuous_fst)
    exact isClosed_eq h_cont continuous_const
  have h_active_set_ae :
      {p : EuclideanSpace ℝ (Fin n) × Ω | pbar p.1 - v p.1 = 0}
        ∈ MeasureTheory.ae pi.toMeasure := by
    filter_upwards [h_diff_zero_ae] with p hp using hp
  have h_supp_sub : pi.toMeasure.support ⊆
      {p : EuclideanSpace ℝ (Fin n) × Ω | pbar p.1 - v p.1 = 0} :=
    MeasureTheory.Measure.support_subset_of_isClosed h_active_set_closed h_active_set_ae
  rintro x ⟨p, hp_supp, rfl⟩
  exact sub_eq_zero.mp (h_supp_sub hp_supp)

omit [T2Space Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [Inhabited Ω] in
/-- **Canonical pbar agrees with the formula-S envelope on `s.X` at any optimal joint.**

For any feasible joint `pi` that is optimal for `momentPrimal s v`, the canonical dual price `pbar`
coincides with the formula-S envelope `pStar v S` on all of `s.X`, where
`S = Prod.fst '' pi.toMeasure.support`. -/
lemma pbar_eq_pStar_on_active_support
    (s : MomentSetup Ω n) (hm_lip : s.IsCoordLipschitz)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hv_lip : LipschitzWith L (fun x : EuclideanSpace ℝ (Fin n) => v x))
    (hv_diff : ContDiff ℝ 1 v)
    (hv_meas : Measurable v) (hv_bdd : ∃ M, ∀ x, |v x| ≤ M)
    {pi : ProbDist (EuclideanSpace ℝ (Fin n) × Ω)}
    (hpi : pi ∈ feasibleJoint s)
    (h_opt : ∫ p, v p.1 ∂pi.toMeasure = momentPrimal s v)
    {pbar : EuclideanSpace ℝ (Fin n) → ℝ}
    {q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (h_struct : HasMomentPrices s v L pbar q)
    (h_dual : IsDualFeasible (s.composedValue v) (fun ω => pbar (s.m ω)))
    (h_value : dualObjective s.prior (fun ω => pbar (s.m ω))
        = dualValue (s.composedValue v) s.prior)
    (h_slack_pi : ∀ᵐ p ∂pi.toMeasure,
      pbar (s.m p.2) = v p.1 + inner ℝ (q p.1) (s.m p.2 - p.1))
    [s.prior.toMeasure.IsOpenPosMeasure]
    (h_dense : s.X ⊆ closure (Set.range s.m)) :
    ∀ y ∈ s.X, pbar y = pStar v (Prod.fst '' pi.toMeasure.support) y := by
  have hS_active : ∀ x ∈ Prod.fst '' pi.toMeasure.support, pbar x = v x :=
    pbar_eq_v_on_active_support s hv_lip hv_meas hv_bdd hpi h_struct h_slack_pi
  have h_pre_X_closed : IsClosed
      ((Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X) :=
    s.X_compact.isClosed.preimage continuous_fst
  have h_pre_X_ae : (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n))
      ⁻¹' s.X ∈ MeasureTheory.ae pi.toMeasure := by
    rw [MeasureTheory.mem_ae_iff]
    exact (MeasureTheory.prob_compl_eq_zero_iff
      (h_pre_X_closed.measurableSet)).mpr hpi.fst_supportsOn
  have h_supp_sub_X : pi.toMeasure.support ⊆
      (Prod.fst : EuclideanSpace ℝ (Fin n) × Ω → EuclideanSpace ℝ (Fin n)) ⁻¹' s.X :=
    MeasureTheory.Measure.support_subset_of_isClosed h_pre_X_closed h_pre_X_ae
  have hS_subX : (Prod.fst '' pi.toMeasure.support : Set _) ⊆ s.X := by
    rintro x ⟨p, hp_supp, rfl⟩
    exact h_supp_sub_X hp_supp
  -- S nonempty (probability measure has nonempty support).
  have hS_ne : (Prod.fst '' pi.toMeasure.support : Set _).Nonempty := by
    have h_pi_ne_zero : pi.toMeasure ≠ 0 :=
      MeasureTheory.IsProbabilityMeasure.ne_zero pi.toMeasure
    have h_supp_ne : pi.toMeasure.support.Nonempty :=
      MeasureTheory.Measure.nonempty_support h_pi_ne_zero
    exact h_supp_ne.image _
  intro y hy
  refine le_antisymm ?_ ?_
  · exact MomentSetup.pbar_le_pStar_on_X s hm_lip hv_lip hv_diff hv_meas hv_bdd
      hpi h_opt h_struct h_dual h_value h_slack_pi h_dense y hy
  · unfold pStar
    refine csSup_le (hS_ne.image _) ?_
    rintro _ ⟨x, hxS, rfl⟩
    exact HasMomentPrices.fderiv_isSubgradient_of_active s hv_diff h_struct x (hS_subX hxS)
      (hS_active x hxS).symm y hy

end Econlib.MechanismDesign.InformationDesign.Persuasion.Moment
